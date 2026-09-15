;   Copyright (c) Rich Hickey. All rights reserved.
;   The use and distribution terms for this software are covered by the
;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;   which can be found in the file epl-v10.html at the root of this distribution.
;   By using this software in any fashion, you are agreeing to be bound by
;   the terms of this license.
;   You must not remove this notice, or any other, from this software.

(ns ^{:doc "The RFC 6455 framing in clojure.cljs.ws, exercised end to end.

  THE CLIENT IS THE JDK'S OWN java.net.http.WebSocket, which is the point: this
  framing is only worth anything if something that did not come from the same
  source agrees with it. It masks every frame, it fragments what it is told to,
  and it runs the closing handshake - the three parts of the protocol a server is
  most likely to get wrong and least likely to notice. Nothing here is asserted
  against our own encoder.

  The last two tests do not use it, because a conforming client cannot be made to
  break the protocol and will not offer permessage-deflate.

  No compiler and no cursor: this namespace is Java and sockets."}
  clojure.cljs.ws-test
  (:require [clojure.test :refer [deftest is]])
  (:import [clojure.cljs.ws Connection PerMessageDeflate WebSocketConnection
            WebSocketExchange WebSocketHandler WebSocketUpgrade]
           [java.io BufferedInputStream ByteArrayOutputStream InputStream]
           [java.net InetAddress ServerSocket Socket SocketTimeoutException URI]
           [java.net.http HttpClient WebSocket WebSocket$Listener]
           [java.nio.charset StandardCharsets]
           [java.util.concurrent LinkedBlockingQueue TimeUnit]
           [java.util.function Function]))

(def ^:private ms 10000)

(defn- took [^LinkedBlockingQueue q] (.poll q ms TimeUnit/MILLISECONDS))

;; --- reading the request the handshake needs --------------------------------

(defn- read-line!
  "One CRLF-terminated line, a byte at a time.

  A BYTE AT A TIME BECAUSE OF WHAT COMES AFTER: the bytes past the blank line are
  the first frame, and the exchange has to find them. Here that is safe either way
  since both halves share one buffer - see package-info.java - but the test is
  also the example, so it does it the way a caller must."
  [^InputStream in]
  (let [b (ByteArrayOutputStream.)]
    (loop []
      (let [c (.read in)]
        (cond (or (= -1 c) (= 10 c)) (.toString b "UTF-8")
              (= 13 c)               (recur)
              :else                  (do (.write b c) (recur)))))))

(defn- read-headers!
  "The request's headers, lowercased, the request line dropped."
  [^InputStream in]
  (loop [first? true acc {}]
    (let [line (read-line! in)]
      (cond
        (.isEmpty line) acc
        first?          (recur false acc)
        :else           (let [i (.indexOf line ":")]
                          (recur false
                                 (if (pos? i)
                                   (assoc acc (.toLowerCase (.trim (subs line 0 i)))
                                          (.trim (subs line (inc i))))
                                   acc)))))))

;; --- a server over the slice ------------------------------------------------

(defn- serve!
  "Accept ONE websocket connection on an ephemeral port and echo text back.

  Answers {:port :conn :events :stop!} - :conn a promise of the
  WebSocketConnection the exchange hands its handler, so a test can push from the
  server side, and :events a queue carrying the close code and any failure."
  []
  (let [ss     (ServerSocket. 0 0 (InetAddress/getByName "127.0.0.1"))
        conn   (promise)
        events (LinkedBlockingQueue.)]
    (.start
     (Thread/ofVirtual)
     ^Runnable
     (fn []
       (try
         (with-open [^Socket s (.accept ss)]
           (let [in      (BufferedInputStream. (.getInputStream s))
                 headers (read-headers! in)
                 out     (.getOutputStream s)
                 pmd     (WebSocketUpgrade/accept
                          (reify Function (apply [_ k] (get headers k)))
                          out nil)
                 c       (reify Connection
                           (getOutputStream [_] (.getOutputStream s))
                           (isActive [_] (not (.isClosed s))))
                 handler (reify WebSocketHandler
                           (start [this ctx] (deliver conn ctx) this)
                           (onText [_ payload]
                             (.sendText ^WebSocketConnection @conn (str "echo:" payload)))
                           (onBinary [_ _])
                           (onPing [_ payload] (.sendPong ^WebSocketConnection @conn payload))
                           (onPong [_ _])
                           (onClose [_ code _] (.offer events [:closed code])))]
             (.process (WebSocketExchange. c in handler pmd))))
         (catch Throwable t (.offer events [:error (str (ex-message t))])))))
    {:port (.getLocalPort ss) :conn conn :events events :stop! #(.close ss)}))

(defn- connect!
  "The JDK's websocket client against `port`, and the queue whole messages arrive
  on. Fragments are joined here, so a test sees messages rather than frames."
  [port]
  (let [q   (LinkedBlockingQueue.)
        acc (StringBuilder.)
        l   (reify WebSocket$Listener
              (onText [_ ws data last?]
                (.append acc data)
                (when last?
                  (.offer q (.toString acc))
                  (.setLength acc 0))
                (.request ^WebSocket ws 1)
                nil))]
    [(-> (HttpClient/newHttpClient)
         (.newWebSocketBuilder)
         (.buildAsync (URI/create (str "ws://127.0.0.1:" port "/")) l)
         (.get ms TimeUnit/MILLISECONDS))
     q]))

;; --- the protocol -----------------------------------------------------------

(deftest test-a-text-message-goes-there-and-comes-back
  (let [{:keys [port stop!]} (serve!)
        [^WebSocket ws q]    (connect! port)]
    (try
      (.get (.sendText ws "hello" true) ms TimeUnit/MILLISECONDS)
      (is (= "echo:hello" (took q)))
      (finally (stop!)))))

(deftest test-a-message-split-across-frames-arrives-whole
  ;; continuation frames, which a browser sends without being asked and which a
  ;; decoder that only ever saw whole messages will not have been shown
  (let [{:keys [port stop!]} (serve!)
        [^WebSocket ws q]    (connect! port)]
    (try
      (doseq [[part last?] [["frag-" false] ["mented-" false] ["message" true]]]
        (.get (.sendText ws part last?) ms TimeUnit/MILLISECONDS))
      (is (= "echo:frag-mented-message" (took q)))
      (finally (stop!)))))

(deftest test-a-payload-past-the-16-bit-length-survives
  ;; 70 KB: past 125, past 65535, so both extended length forms are exercised -
  ;; and a compiled cljs.core is bigger than this, which is why it matters
  (let [{:keys [port stop!]} (serve!)
        [^WebSocket ws q]    (connect! port)
        big                  (apply str (repeat 70000 "x"))]
    (try
      (.get (.sendText ws big true) ms TimeUnit/MILLISECONDS)
      (is (= (str "echo:" big) (took q)))
      (finally (stop!)))))

(deftest test-the-server-can-speak-first
  ;; the whole reason for a socket: the JVM writes when it has something to say,
  ;; rather than waiting for a request to answer
  (let [{:keys [port conn stop!]} (serve!)
        [^WebSocket ws q]         (connect! port)]
    (try
      (.sendText ^WebSocketConnection @conn "unsolicited")
      (is (= "unsolicited" (took q)))
      (finally (stop!)))))

(deftest test-a-close-carries-its-code
  ;; a refresh reports itself, which is the machinery a long-poll has to replace
  ;; with silence and a timeout
  (let [{:keys [port events stop!]} (serve!)
        [^WebSocket ws _]           (connect! port)]
    (try
      (.get (.sendClose ws WebSocket/NORMAL_CLOSURE "done") ms TimeUnit/MILLISECONDS)
      (is (= [:closed 1000] (took events)))
      (finally (stop!)))))

;; --- what a conforming client will not do -----------------------------------

(deftest test-an-unmasked-frame-is-refused
  ;; Section 5.1: a server MUST close the connection on a frame that is not
  ;; masked. The JDK client always masks, so this one is spoken by hand.
  (let [{:keys [port stop!]} (serve!)]
    (try
      (with-open [s (Socket. "127.0.0.1" (int port))]
        ;; SO THAT A REGRESSION FAILS RATHER THAN HANGS. Every other test here
        ;; waits on a queue with a timeout; this one waits on a socket, and a
        ;; server that wrongly accepted the frame simply never answers.
        (.setSoTimeout s ms)
        (let [out  (.getOutputStream s)
              in   (.getInputStream s)
              read #(try (.read in) (catch SocketTimeoutException _ ::timed-out))]
          (.write out (.getBytes (str "GET / HTTP/1.1\r\n"
                                      "host: 127.0.0.1\r\n"
                                      "upgrade: websocket\r\n"
                                      "connection: Upgrade\r\n"
                                      "sec-websocket-key: dGhlIHNhbXBsZSBub25jZQ==\r\n"
                                      "sec-websocket-version: 13\r\n\r\n")
                                 StandardCharsets/US_ASCII))
          (.flush out)
          (read-headers! in)
          ;; FIN + text, 2 bytes, and no mask bit
          (.write out (byte-array (map unchecked-byte [0x81 0x02 0x68 0x69])))
          (.flush out)
          (let [b0 (read) b1 (read) hi (read) lo (read)]
            (is (= 0x88 b0) "a close frame")
            (is (= 2 b1) "carrying a status code")
            (is (= 1002 (+ (* 256 hi) lo)) "1002, protocol error"))))
      (finally (stop!)))))

(deftest test-compression-is-negotiated-or-declined
  ;; what Chrome and Firefox actually offer. The JDK client offers nothing, so
  ;; the socket tests above run uncompressed and this covers the other path.
  (let [pmd (PerMessageDeflate/negotiate "permessage-deflate; client_max_window_bits")]
    (is (some? pmd))
    (is (= "permessage-deflate" (.buildResponseHeaderValue pmd)))
    (is (nil? (PerMessageDeflate/negotiate nil))
        "declining is what a null context means, and no caller changes")
    (let [src (.getBytes (str "{:type :result :value \"" (apply str (repeat 3000 "abc")) "\"}")
                         StandardCharsets/UTF_8)]
      (is (= (seq src) (seq (.decompress pmd (.compress pmd src))))))))
