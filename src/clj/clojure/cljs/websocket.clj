;   Copyright (c) Rich Hickey. All rights reserved.
;   The use and distribution terms for this software are covered by the
;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;   which can be found in the file epl-v10.html at the root of this distribution.
;   By using this software in any fashion, you are agreeing to be bound by
;   the terms of this license.
;   You must not remove this notice, or any other, from this software.

(ns ^{:doc "A listener whose every connection is a websocket. doc/cljs-repl.md 6.

  The framing is clojure.cljs.ws, which is Java and came from shadow-http; this is
  the fifty lines around it that a socket needs and an HTTP server does not give.

  WHY THIS IS NOT A HANDLER ON THE ASSET SERVER. com.sun.net.httpserver has no way
  to hand back a connection: it frames every response itself, and the bytes it has
  already buffered past the request headers are exactly the first frame. So the
  socket needs a listener of its own - and once it has one, the HTTP it must speak
  is a request line, some headers, and either a 101 or a refusal. No bodies, no
  chunked encoding, no keep-alive, because a connection here upgrades immediately
  and never speaks HTTP again. That is the whole reason this is small.

  The asset server stays where it is. Serving the output directory with an ETag
  and a 304 is not a transport concern and has nothing to gain from a socket.

  A TOKEN, BECAUSE A WEBSOCKET IS NOT SUBJECT TO THE SAME-ORIGIN POLICY. Any page
  on the internet may open a socket to a port on this machine - no preflight, no
  CORS, and an Origin header it writes itself. A REPL that accepted such a
  connection would evaluate the developer's forms in a stranger's page and hand
  back what they printed. So the URL carries a secret that only something served
  by this process can know, and a connection without it is refused before the
  upgrade. shadow-cljs reaches the same conclusion by the same route (its
  server-token); Replique did not need one, because a long-poll is an ordinary
  request that CORS does govern.

  ALL THREE CALLBACKS RUN ON THEIR OWN CONNECTION'S THREAD, the same virtual
  thread that reads its frames. A slow one delays that page and no other, and two
  pages never run a callback concurrently with each other's - but :on-text must
  not wait on something only a later message from the same page can provide."}
  clojure.cljs.websocket
  (:require [clojure.string :as str])
  (:import [clojure.cljs.ws Connection WebSocketConnection WebSocketExchange
            WebSocketHandler WebSocketUpgrade]
           [java.io BufferedInputStream ByteArrayOutputStream InputStream OutputStream]
           [java.net InetAddress ServerSocket Socket]
           [java.nio.charset StandardCharsets]
           [java.security MessageDigest SecureRandom]
           [java.util Base64]
           [java.util.concurrent ConcurrentHashMap]
           [java.util.function Function]))

(set! *warn-on-reflection* true)

;; --- the secret -------------------------------------------------------------

(defn random-token
  "A token to put in the connect URL. 128 bits from SecureRandom, base64url so it
  survives a query string without escaping."
  []
  (let [b (byte-array 16)]
    (.nextBytes (SecureRandom.) b)
    (.encodeToString (Base64/getUrlEncoder) b)))

(defn- token-ok?
  "MessageDigest/isEqual rather than =, which is not because a timing attack over
  loopback is a real threat - it is that comparing a secret in variable time is
  the sort of thing that is free to get right and awkward to explain otherwise."
  [^String expected ^String given]
  (and (some? given)
       (MessageDigest/isEqual (.getBytes expected StandardCharsets/UTF_8)
                              (.getBytes given StandardCharsets/UTF_8))))

;; --- the little HTTP there is ----------------------------------------------

(defn- read-line!
  "One CRLF-terminated line, a byte at a time.

  A BYTE AT A TIME IS THE WHOLE POINT. The bytes after the blank line are the
  first frame, and the exchange reads them from this same buffer - so nothing here
  may read further than the line it was asked for. See the ws package-info."
  ^String [^InputStream in]
  (let [b (ByteArrayOutputStream.)]
    (loop []
      (let [c (.read in)]
        (cond
          (= -1 c) (when (pos? (.size b)) (.toString b "UTF-8"))
          (= 10 c) (.toString b "UTF-8")
          (= 13 c) (recur)
          :else    (do (.write b c) (recur)))))))

(defn- read-request!
  "{:target, :headers} - the request target and the headers lowercased - or nil if
  the peer hung up or sent nothing that looks like a request.

  The method is not kept: a websocket handshake is a GET by definition, and
  WebSocketUpgrade refuses anything without the Upgrade headers anyway."
  [^InputStream in]
  (when-let [request-line (read-line! in)]
    (let [parts (str/split request-line #" ")]
      (when (<= 2 (count parts))
        (loop [headers {}]
          (let [line (read-line! in)]
            ;; THE BLANK LINE ENDS THE HEADERS, and read-line! answers "" for it -
            ;; nil means the peer hung up instead. An empty string is truthy in
            ;; Clojure, so this cannot be an if-let.
            (if (or (nil? line) (str/blank? line))
              {:target (second parts) :headers headers}
              (let [i (.indexOf line ":")]
                (recur (if (pos? i)
                         (assoc headers (str/lower-case (str/trim (subs line 0 i)))
                                (str/trim (subs line (inc i))))
                         headers))))))))))

(defn- query-param [^String target ^String k]
  (let [i (.indexOf target "?")]
    (when (pos? i)
      (some (fn [^String pair]
              (let [j (.indexOf pair "=")]
                (when (and (pos? j) (= k (subs pair 0 j)))
                  (subs pair (inc j)))))
            (str/split (subs target (inc i)) #"&")))))

(defn- refuse!
  "Say no in a way a browser can report. A socket closed without an answer shows up
  in the console as nothing in particular; a status line says which rule was
  broken."
  [^OutputStream out status ^String reason]
  ;; the reason phrase can carry a header value back (the websocket version the
  ;; peer asked for), so anything but printable ASCII is dropped - read-line!
  ;; already makes CR and LF unreachable, and this keeps that true if it changes
  (let [reason (str/replace reason #"[^\x20-\x7e]" " ")]
    (.write out (.getBytes (str "HTTP/1.1 " status " " reason "\r\n"
                                "connection: close\r\n"
                                "content-length: 0\r\n\r\n")
                           StandardCharsets/US_ASCII))
    (.flush out)))

;; --- a connection -----------------------------------------------------------

(def ^:private abnormal
  "RFC 6455 7.4.1: no close frame arrived. The page crashed, slept or was killed."
  1006)

(defn- serve-connection!
  [^Socket socket {:keys [token on-open on-text on-close]} ^ConcurrentHashMap clients]
  (let [code (atom abnormal)
        ctx  (promise)]
    (try
      (with-open [^Socket s socket]
        (let [in  (BufferedInputStream. (.getInputStream s))
              out (.getOutputStream s)
              req (read-request! in)]
          (cond
            (nil? req)
            nil                                   ; nothing was said; nothing to answer

            (and token (not (token-ok? token (query-param (:target req) "token"))))
            (refuse! out 403 "Forbidden")

            :else
            ;; WebSocketUpgrade throws IllegalStateException on a request that is
            ;; not a handshake - someone pointed a browser at this port, or curl.
            ;; Answering 400 rather than dropping the connection is the difference
            ;; between a message and a mystery.
            (let [pmd     (try
                            (WebSocketUpgrade/accept
                             (reify Function (apply [_ k] (get (:headers req) k)))
                             out nil)
                            (catch IllegalStateException e
                              (refuse! out 400 (or (ex-message e) "Bad Request"))
                              ::refused))
                  conn    (reify Connection
                            (getOutputStream [_] (.getOutputStream s))
                            (isActive [_] (not (.isClosed s))))
                  handler (reify WebSocketHandler
                            (start [this c]
                              (deliver ctx c)
                              (.put clients c s)
                              (when on-open (on-open c req))
                              this)
                            (onText [_ text]
                              (when on-text (on-text @ctx text)))
                            (onBinary [_ _])
                            (onPing [_ payload]
                              (.sendPong ^WebSocketConnection @ctx payload))
                            (onPong [_ _])
                            (onClose [_ c _] (reset! code c)))]
              (when-not (= ::refused pmd)
                (.process (WebSocketExchange. conn in handler pmd)))))))
      (catch Throwable _
        ;; the page went away mid-frame, or never spoke the protocol. Either way
        ;; this connection is over and :on-close below is what says so.
        nil)
      (finally
        (when (realized? ctx)
          (.remove clients ^Object @ctx)
          (when on-close (on-close @ctx @code)))))))

;; --- the server -------------------------------------------------------------

(defn websocket-server
  "Listen for websockets and hand each one to the callbacks.

    :port      what to bind, default 0 - an ephemeral port
    :host      default 127.0.0.1, which is the only interface a REPL should be on
    :token     a secret the connect URL must carry as ?token=..., default none.
               random-token makes one. Without it any page on the internet may
               connect - see this namespace's docstring
    :on-open   (fn [conn req])       a page arrived; `req` is what it sent to get
                                     in - {:target, :headers} - which is where a
                                     User-Agent comes from, the handshake being
                                     the only time a page says what it is
    :on-text   (fn [conn text])      it said something
    :on-close  (fn [conn code])      it went away; 1006 means it never said so

  `conn` is a clojure.cljs.ws.WebSocketConnection - (.sendText conn s) writes to
  that page, from any thread, and may be held for as long as the page is there.

  Closeable. (:port srv) is what it bound and (:connections srv) is who is
  connected right now, oldest first being no promise anyone makes.

  Closing says goodbye to every page - 1001, going away - before dropping the
  sockets, so a browser reports a clean close rather than an error."
  ^java.io.Closeable
  [{:keys [port host] :or {port 0 host "127.0.0.1"} :as opts}]
  (let [ss      (ServerSocket. (int port) 0 (InetAddress/getByName host))
        clients (ConcurrentHashMap.)
        threads (-> (Thread/ofVirtual) (.name "cljs-ws-" 0) (.factory))]
    (.start
     ^Thread
     (.newThread threads
                 ^Runnable
                 (fn []
                   (loop []
                     (when-let [s (try (.accept ss) (catch Throwable _ nil))]
                       (.start ^Thread (.newThread threads
                                                   ^Runnable
                                                   #(serve-connection! s opts clients)))
                       (recur))))))
    (reify
      clojure.lang.ILookup
      (valAt [this k] (.valAt ^clojure.lang.ILookup this k nil))
      (valAt [_ k not-found]
        (case k
          :port        (.getLocalPort ss)
          :connections (vec (.keySet clients))
          not-found))
      java.io.Closeable
      (close [_]
        (.close ss)
        (doseq [[^WebSocketConnection c ^Socket s] (into {} clients)]
          (try (.sendClose c 1001) (catch Throwable _ nil))
          (try (.close s) (catch Throwable _ nil)))))))
