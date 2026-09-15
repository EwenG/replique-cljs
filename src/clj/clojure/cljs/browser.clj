;   Copyright (c) Rich Hickey. All rights reserved.
;   The use and distribution terms for this software are covered by the
;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;   which can be found in the file epl-v10.html at the root of this distribution.
;   By using this software in any fashion, you are agreeing to be bound by
;   the terms of this license.
;   You must not remove this notice, or any other, from this software.


(ns ^{:doc "The browser runtime: an asset server, a websocket, and the same
  IJsRuntime the node transport implements. doc/cljs-repl.md 6.

  A browser cannot be dialled, so it dials out - and what it opens now is a
  socket, where it used to be a request held open. The JVM writes a script into
  that socket and the page writes back the result.

  TWO LISTENERS, WHICH IS NOT A COMPROMISE BUT THE SHAPE OF THE PROBLEM.
  com.sun.net.httpserver frames every response itself and will not hand back a
  connection, and the bytes it has already buffered past the request headers are
  exactly the first websocket frame - so the socket cannot be a handler on it. It
  gets a listener of its own (clojure.cljs.websocket), and the asset server stays
  what it was, because serving a compiled program with an ETag and a 304 has
  nothing to gain from a socket.

  WHAT THE SOCKET DELETED, all of it machinery that existed to imitate one:

    SESSION NUMBERING. A refresh closes the old socket before opening the new one,
    so the two can never be confused and no number has to tell them apart. A
    session is still counted - :session below - but only so that a caller can SEE
    that a page was replaced; nothing on the wire carries it.

    THE SILENCE THRESHOLD, the 5-second :alive ping and the :bye beacon. A closed
    socket reports itself, at once and with a code; a page that dies without
    closing is found by the websocket ping instead of by 20 seconds of quiet.

    THE POLL, its 20-second heartbeat, and the requirement that a request be in
    flight for the JVM to have anywhere to write.

  WHAT IT FIXED. A print and the value of the form that printed it used to be two
  POSTs on two connections, ordered by luck. They are now two frames on one
  socket, delivered to one callback thread in the order they were sent.

  WHAT IS UNCHANGED, because it was never about the transport: evaluations are
  serialised by a permit, each runs on a virtual thread of its own, and ending a
  session interrupts them all so that a blocked caller gets an answer rather than
  a wait.

  Two entry points, mirroring the node pair in clojure.cljs.repl:

    browser-runtime  the servers plus the IJsRuntime over them, Closeable
    browser-repl     that, an output directory, and the loop over both"}
  clojure.cljs.browser
  (:require [clojure.cljs.env :as env]
            [clojure.cljs.output :as output]
            [clojure.cljs.repl :as repl]
            [clojure.cljs.websocket :as websocket]
            [clojure.edn :as edn]
            [clojure.java.io :as io]
            [clojure.string :as str])
  (:import [clojure.cljs.ws WebSocketConnection]
           [com.sun.net.httpserver HttpExchange HttpHandler HttpServer]
           [java.io File Writer]
           [java.net InetSocketAddress URLDecoder]
           [java.nio.charset StandardCharsets]
           [java.nio.file Files LinkOption]
           [java.nio.file.attribute BasicFileAttributes FileAttribute]
           [java.util.concurrent CompletableFuture ConcurrentHashMap
            ExecutionException Executors Semaphore ThreadFactory TimeUnit]))

;; --- what a browser runtime is run beside -----------------------------------

(def ^:private client-name "runtime_browser.js")

(def ^:private client-resource
  "The browser transport, beside runtime.js on the classpath - one host's way of
  being reached, where runtime.js is what every host shares."
  "clojure/cljs/runtime_browser.js")

(defn write-runtime!
  "Write what a browser runtime is served out of: an output root
  (clojure.cljs.output - runtime.js and the package.json) plus the browser
  transport.

  Read from the classpath on each call, so editing the client and reloading the
  page is enough to see the change."
  [dir]
  (let [dir (output/write-prelude! dir)]
    (spit (File. dir client-name) (slurp (io/resource client-resource)))
    dir))

(def ^:private default-page
  "What GET / answers when the output directory has no index.html of its own.

  A page of nothing but the connect call, because the interesting case is the other
  one: a real application serves its own page, imports this module from wherever
  the REPL is listening, and calls connect - which needs no argument, since the
  module knows the URL it was itself served from."
  (str "<!doctype html>\n"
       "<html>\n<head><meta charset=\"utf-8\"><title>ClojureScript REPL</title></head>\n"
       "<body>\n"
       "<p>Connected to a ClojureScript REPL. Evaluate a form on the JVM side;\n"
       "this page is where it runs. Open the console to see what the program prints.</p>\n"
       "<script type=\"module\">\n"
       "import { connect } from \"./" client-name "\";\n"
       "connect();\n"
       "</script>\n"
       "</body>\n</html>\n"))

;; --- serving the output directory -------------------------------------------

(def ^:private mime
  "Enough of a table to serve a compiled program and the page around it. .js is the
  one that has to be right - a browser refuses a module served as anything else -
  and the rest are here so that an application's own assets can sit in the output
  directory beside its namespaces."
  {"js"   "text/javascript"
   "mjs"  "text/javascript"
   "json" "application/json"
   "map"  "application/json"
   "html" "text/html"
   "htm"  "text/html"
   "css"  "text/css"
   "svg"  "image/svg+xml"
   "png"  "image/png"
   "jpg"  "image/jpeg"
   "jpeg" "image/jpeg"
   "gif"  "image/gif"
   "ico"  "image/x-icon"
   "webp" "image/webp"
   "woff" "font/woff"
   "woff2" "font/woff2"
   "ttf"  "font/ttf"
   "txt"  "text/plain"
   "edn"  "application/edn"
   "cljs" "text/x-clojure"
   "cljc" "text/x-clojure"
   "clj"  "text/x-clojure"})

(defn- content-type [^String path]
  (let [i (.lastIndexOf path ".")]
    (or (when (pos? i) (mime (str/lower-case (subs path (inc i)))))
        "application/octet-stream")))

(defn- under
  "The file `path` names inside `root`, or nil if it names anything else.

  Canonicalised before the check rather than scanned for \"..\": a path is only
  inside a directory if the filesystem says so once every link and every dot
  segment has been resolved."
  ^File [^File root ^String path]
  (let [^File root (.getCanonicalFile root)
        f (.getCanonicalFile (File. root (subs path 1)))]
    (when (and (.isFile f)
               (str/starts-with? (str (.toPath f)) (str (.toPath root) File/separator)))
      f)))

;; --- the wire ---------------------------------------------------------------

(def ^:private no-store
  "For the transport. A cached poll response would be a script handed out twice."
  "no-store")

(def ^:private revalidate
  "For the output directory. NOT no-store, and the difference is the whole of the
  caching story here: no-store forbids the browser to keep the bytes at all, so
  every refresh re-downloads the whole program; no-cache lets it keep them and
  requires it to ask before using them. Asking is cheap and the answer is usually
  304, so correctness is identical - a stale module can never be run, because the
  browser never uses one without checking - and what is saved is the body."
  "no-cache")

(defn- send!
  ([ex status ctype body] (send! ex status ctype body no-store))
  ([^HttpExchange ex status ^String ctype ^bytes body ^String cache]
   (doto (.getResponseHeaders ex)
     (.set "Content-Type" ctype)
     (.set "Cache-Control" cache)
     ;; the page may be the application's own, on the application's own origin
     (.set "Access-Control-Allow-Origin" "*")
     (.set "Access-Control-Allow-Methods" "GET, POST, OPTIONS")
     (.set "Access-Control-Allow-Headers" "Content-Type, If-None-Match"))
   (if (or (= 204 status) (= 304 status) (zero? (alength body)))
     (.sendResponseHeaders ex status -1)
     (do (.sendResponseHeaders ex status (alength body))
         (with-open [os (.getResponseBody ex)]
           (.write os body))))
   nil))

(defn- send-text! [^HttpExchange ex status ^String ctype ^String body]
  (send! ex status (str ctype "; charset=utf-8") (.getBytes body StandardCharsets/UTF_8)))

;; --- conditional requests ---------------------------------------------------

(defn- etag
  "A tag for `f` from its modification time and size, computed WITHOUT reading it -
  which is the point, since the whole saving of a 304 is the read and the send.

  SOUND HERE FOR A REASON THAT IS NOT GENERAL. Modification time is a proxy for
  content, and normally a poor one; it is a good one against this output directory
  because clojure.cljs.driver/write-if-changed! does not rewrite a file whose bytes
  did not change. So a compiled namespace's mtime moves when and only when the
  namespace did.

  Nanoseconds rather than File/lastModified's milliseconds, which narrows the one
  window where this could be wrong - a rewrite to the same size within one clock
  tick - to whatever the filesystem's own resolution is.

  The prelude is the harmless other direction: write-runtime! rewrites runtime.js
  on every start whether or not it changed, so it misses the cache once per session
  and is served in full. Costing a fetch is not the same kind of mistake as
  skipping one."
  ^String [^File f]
  (let [a (Files/readAttributes (.toPath f) BasicFileAttributes
                                ^"[Ljava.nio.file.LinkOption;" (into-array LinkOption []))]
    (str "\"" (.to (.lastModifiedTime a) TimeUnit/NANOSECONDS) "-" (.size a) "\"")))

(defn- fresh?
  "Does the request already hold `tag`? If-None-Match is a comma-separated list, and
  a proxy may have weakened what we sent into W/\"...\" on the way."
  [^HttpExchange ex ^String tag]
  (when-let [given (.getFirst (.getRequestHeaders ex) "If-None-Match")]
    (boolean (some #(= tag (str/replace (str/trim %) #"^W/" ""))
                   (str/split given #",")))))

(defn- send-asset!
  "200 with the bytes, or 304 with none - and the ETag either way, since a 304 that
  dropped it would make the next request unconditional again."
  [^HttpExchange ex ^String ctype ^String tag ^bytes body]
  (.set (.getResponseHeaders ex) "ETag" tag)
  (if body
    (send! ex 200 ctype body revalidate)
    (send! ex 304 ctype (byte-array 0) revalidate)))

;; --- where the page is told to dial ----------------------------------------

(def ^:private info-name
  "Written into the output directory, which the asset server serves, so that a
  page can find the socket from the URL it imported the client from. A file rather
  than something interpolated into runtime_browser.js, so that the client stays
  the bytes on the classpath and editing it needs no restart."
  "cljs-repl.json")

(defn- write-connect-info!
  [^File dir ws-port ^String token]
  (spit (File. dir info-name)
        (str "{\"ws\": \"ws://127.0.0.1:" ws-port "/?token=" token "\"}\n")))

;; --- serializing evaluations -----------------------------------------------
;;
;; A VIRTUAL THREAD PER EVALUATION, HOLDING A PERMIT, where Replique has a
;; single-thread executor. The two serialize equally; the difference is what else
;; each one gives you.
;;
;; A single-thread executor says "one at a time" by implication - you have to know
;; that newSingleThreadExecutor means that - and it hides the queue, which is the
;; one thing worth seeing. It also cannot answer the question R3 will ask: has my
;; task started yet? Replique needs that (a completion or a watch must not block on
;; an absent runtime) and pays for it with a mutable submitted? flag on EvalTask and
;; a cancel-then-get dance, because an executor will not say. A permit says it for
;; free: tryAcquire with a timeout either gets in or does not, and nothing was ever
;; queued behind a runtime that is not there.
;;
;; It also collapses two shutdown mechanisms into one. shutdownNow interrupts the
;; RUNNING task and hands back the ones that never started, which Replique then runs
;; itself with a dynamic var bound so each answers its caller instead of waiting -
;; the *stopped-eval-executor?* dance. Here there is no such split: every evaluation
;; is a thread, waiting or working, and interrupting them all is the whole of it.

(def ^:private broken
  "Replique's wording, for Replique's case: the evaluation was interrupted because
  the session ended under it - which now means another page connected."
  {:status :error :value "Connection broken"})

(def ^:private gone
  "The other case, and a different sentence because it is a different fact: the
  page did not lose a race, it left."
  {:status :error
   :value  "The browser is gone - it was closed, reloaded or crashed."})

(defn- end-session!
  "End every evaluation belonging to the session that is finishing, and say why.

  THREE THINGS ARE DONE AND THEY ARE NOT THE SAME. The reason is recorded first, so
  that whatever wakes next reports the right one. The turn in flight is COMPLETED,
  which is how the thread waiting on it returns at once rather than by being
  interrupted out of a wait. And every worker is interrupted, which is for the ones
  parked on the permit that have no future to complete yet - though the guarantee
  for those is really the session re-check each makes on its way in.

  One call where a single-thread executor needed two mechanisms and a dynamic var:
  an evaluation that has not started is a thread parked on acquire, not a Runnable
  in a queue somebody has to run by hand."
  [state reason]
  (swap! state assoc :reason reason)
  (when-let [^CompletableFuture p (:pending @state)]
    (.complete p reason))
  (doseq [^Thread t (:workers @state)]
    (.interrupt t)))

(defn- start-session!
  "A page connected: a new one, or the same page refreshed. Either way whatever was
  running belongs to a session that is over.

  The order matters. The previous session ends first, so that nothing it owned is
  still waiting when its connection is replaced; then the new session is installed
  whole, so no evaluation can see half of it."
  [state conn]
  (end-session! state broken)
  (:session
   (swap! state
          (fn [m]
            (let [n (inc (or (:session m) 0))]
              (assoc m
                     :session n
                     :conn    conn
                     :reason  nil
                     :pending nil
                     :permit  (Semaphore. 1 true)   ; fair, so two callers keep their order
                     :workers (ConcurrentHashMap/newKeySet)
                     ;; named per session and numbered within it, so a stack dump
                     ;; says which page an evaluation belonged to
                     :threads (-> (Thread/ofVirtual)
                                  (.name (str "cljs-eval-" n "-") 0)
                                  (.factory))))))))

(defn- close-session!
  "The page went away. Only the CURRENT one matters: an older connection closing is
  a tab being tidied up, and its session ended when it stopped being current."
  [state conn]
  (when (identical? conn (:conn @state))
    (end-session! state gone)
    (swap! state assoc :conn nil)))

(defn- turn
  "One evaluation, once it holds the permit: write the script into the socket and
  wait for the frame that answers it.

  TWO WAYS OUT WHERE THE LONG-POLL HAD THREE. Answered, which is the ordinary case.
  Ended, because the session finished under it - and that arrives as a completion
  rather than as an interrupt, so it is instant and carries its own reason. The
  third, giving up because the page has said nothing for twenty seconds, is gone
  along with the thing that made it necessary: there is no waiting to find out
  whether anyone is there.

  The wait is not bounded, and deliberately: an evaluation may legitimately take
  minutes, and what ends it is evidence rather than a deadline."
  [state session js]
  (let [pending (CompletableFuture.)
        {:keys [conn]} (swap! state (fn [m]
                                      (if (= session (:session m))
                                        (assoc m :pending pending)
                                        m)))]
    (if-not (= session (:session @state))
      broken
      (do
        (try
          (.sendText ^WebSocketConnection conn js)
          (catch Throwable t
            (.complete pending {:status :error :phase :transport
                                :value  (str "The runtime failed: " (ex-message t))})))
        (.get pending)))))

(defn- evaluate!
  "Run `js` on a virtual thread of its own, one evaluation at a time, and wait for
  the answer.

  The thread is ours rather than the caller's, which is the property that makes
  ending a session safe: a refresh interrupts threads this namespace made, never one
  it was handed. Doing the work on the calling thread would be less machinery and
  would put an interrupt on the REPL loop.

  The session is re-checked AFTER the permit is taken. Waiting for it is exactly
  the window in which a page can be replaced, and a thread that started before the
  refresh must not go on to evaluate for the page that replaced it."
  [state js]
  (let [{:keys [session permit workers threads]} @state
        answer (CompletableFuture.)
        body   (fn []
                 (let [me (Thread/currentThread)]
                   (.add ^java.util.Set workers me)
                   (try
                     (.acquire ^Semaphore permit)
                     (try
                       (.complete answer (if (= session (:session @state))
                                           (turn state session js)
                                           (or (:reason @state) broken)))
                       (finally (.release ^Semaphore permit)))
                     (catch InterruptedException _
                       (.complete answer (or (:reason @state) broken)))
                     (catch Throwable t
                       (.complete answer {:status :error :phase :transport
                                          :value (str "The runtime failed: "
                                                      (ex-message t))}))
                     (finally
                       (.remove ^java.util.Set workers me)
                       ;; a future nobody completed is a caller who never returns
                       (.complete answer broken)))))]
    (.start ^Thread (.newThread ^ThreadFactory threads ^Runnable body))
    (try
      (.get answer)
      (catch InterruptedException _ (.interrupt (Thread/currentThread)) broken)
      (catch ExecutionException e
        {:status :error :phase :transport
         :value  (str "The runtime failed: " (ex-message (or (ex-cause e) e)))}))))

;; --- what the page says -----------------------------------------------------

(defn- on-print!
  [^Writer out content]
  (locking out
    (.write out ^String content)
    (.flush out)))

(defn- on-text!
  "A frame from the page: the result of the script it was given, or something it
  printed.

  BOTH ARRIVE HERE, ON ONE THREAD, IN ORDER, which is the whole of what the socket
  bought: a println inside a form and that form's value used to be two POSTs that
  could land either way round.

  A result is completed into the turn that asked for it, and a result that finds no
  turn is dropped - the evaluation was ended by a refresh between the two halves,
  and a value nobody is waiting for must not be left for the next one to take as
  its own.

  A RESULT IS ONLY TAKEN FROM THE PAGE THE SCRIPT WAS SENT TO; A PRINT IS TAKEN
  FROM ANY OF THEM. The asymmetry is deliberate. A result answers a question this
  JVM asked, and a page that was not asked has no standing to answer it. Output is
  not an answer to anything - it is something that happened - and a tab left open
  from before the refresh is still a page whose console someone may be watching,
  so dropping what it says would lose information rather than prevent a mistake."
  [state ^Writer out conn text]
  (let [{:keys [type content]} (edn/read-string text)]
    (case type
      :result (when (identical? conn (:conn @state))
                (when-let [^CompletableFuture p (:pending @state)]
                  (.complete p (edn/read-string content))))
      :print  (on-print! out content)
      nil)))


;; --- serving the output directory, continued -------------------------------

(defn- handle-get
  [^File dir ^String path ^HttpExchange ex]
  (let [path (URLDecoder/decode path StandardCharsets/UTF_8)
        path (if (= "/" path) "/index.html" path)
        f    (under dir path)]
    (cond
      ;; THE ONE FILE THAT MUST NOT BE REMEMBERED, and the only no-store left on
      ;; this server now that the wire is not on it. It carries the socket's port
      ;; and its token, and both are new every time the REPL starts - a page that
      ;; answered from cache would dial a port nobody is listening on, with a
      ;; secret that is no longer a secret. The client asks no-store too; this is
      ;; the half that does not depend on the client being the one we wrote.
      (and f (= (str "/" info-name) path))
      (send! ex 200 "application/json" (Files/readAllBytes (.toPath ^File f)) no-store)

      f (let [tag (etag f)]
          (send-asset! ex (content-type path) tag
                       (when-not (fresh? ex tag) (Files/readAllBytes (.toPath f)))))
      (= "/index.html" path) (send-text! ex 200 "text/html" default-page)
      :else (send-text! ex 404 "text/plain" (str "No " path " here.")))))

(defn- handler
  "GET and nothing else. The transport used to arrive here as POSTs; it is a socket
  on its own port now, and what is left is the output directory."
  [^File dir]
  (reify HttpHandler
    (handle [_ ex]
      (try
        (let [^HttpExchange ex ex
              method (.getRequestMethod ex)
              path   (.getPath (.getRequestURI ex))]
          (case method
            ;; If-None-Match is not a CORS-safelisted request header, so a page on
            ;; the application's own origin preflights its conditional fetches
            "OPTIONS" (send! ex 204 "text/plain" (byte-array 0))
            "GET"     (handle-get dir path ex)
            (send-text! ex 405 "text/plain" "Method not allowed")))
        (catch Throwable _
          ;; the browser went away mid-response. This connection is over and the
          ;; next request starts a new one.
          nil)
        (finally (.close ^HttpExchange ex))))))


;; --- the runtime ------------------------------------------------------------

(defn- temp-dir ^File []
  (.toFile (Files/createTempDirectory "cljs-browser" (into-array FileAttribute []))))

(defn- delete-tree! [^File f]
  (when (.isDirectory f)
    (run! delete-tree! (.listFiles f)))
  (.delete f))


(defn browser-runtime
  "Serve `dir` over HTTP, listen for a websocket beside it, and evaluate in
  whatever browser connects.

    :dir       the output directory to serve, and the one the driver compiles into -
               a temp directory by default
    :port      what the asset server listens on, default 0, an ephemeral port
    :ws-port   what the socket listens on, default 0. A second port, for the reason
               this namespace's docstring gives
    :out       where the page's console output is written, default *out*

  Closeable, and closing it stops both servers and unblocks any evaluation still
  waiting on the page.

  The returned object answers (:url rt), which is what to open, (:port rt),
  (:ws-port rt), (:dir rt) - which is what the driver has to compile into - and
  (:session rt), which is nil until a page connects and a different number after
  every refresh.

  A TOKEN GUARDS THE SOCKET, and the asset server is how a page learns it: the
  connect info is written into the output directory, so anything served from here
  can read it and anything that was not cannot. A websocket is not subject to the
  same-origin policy - any page anywhere may open one to this machine - and a REPL
  that accepted such a connection would evaluate your forms in a stranger's page.

  Evaluating before a browser has connected is not an error and not a wait: it
  answers with what to do about it. That is Replique's behaviour and it is the
  right one for a REPL you started before you opened the page."
  ([] (browser-runtime nil))
  ([{:keys [dir port ws-port out] :or {port 0 ws-port 0 out *out*}}]
   (let [^File own (when-not dir (temp-dir))
         ^File dir (write-runtime! (or dir own))
         srv       (atom {:session nil})
         token     (websocket/random-token)
         ws        (websocket/websocket-server
                    {:port     ws-port
                     :token    token
                     :on-open  (fn [conn] (start-session! srv conn))
                     :on-text  (fn [conn text] (on-text! srv out conn text))
                     :on-close (fn [conn _] (close-session! srv conn))})
         ;; A VIRTUAL THREAD PER REQUEST. Less load-bearing than it was - the
         ;; twenty-second held poll it was chosen for is gone - but still right for
         ;; a server with no pool: no unbounded growth, no keepalive, and no thread
         ;; reused between requests, so nothing thread-local can survive from one to
         ;; the next, which for Clojure means a dynamic binding left unwound.
         server    (doto (HttpServer/create (InetSocketAddress. "127.0.0.1" (int port)) 0)
                     (.setExecutor (Executors/newVirtualThreadPerTaskExecutor))
                     (.createContext "/" (handler dir))
                     (.start))
         port      (.getPort (.getAddress server))
         url       (str "http://127.0.0.1:" port "/")
         props     {:url url :port port :ws-port (:port ws) :dir dir}]
     (write-connect-info! dir (:port ws) token)
     (reify
       repl/IJsRuntime
       (-evaluate [_ js]
         (if-not (:conn @srv)
           {:status :error
            :value  (str "No browser is connected. Open " url " - or import "
                         client-name " from it in a page of your own - and "
                         "evaluate this again.")}
           (evaluate! srv js)))
       clojure.lang.ILookup
       ;; :session is the one that is not a constant, and the one worth asking for:
       ;; it is nil until a page connects and a different number after a refresh,
       ;; so it is how anything holding this runtime can tell either apart.
       (valAt [this k] (.valAt ^clojure.lang.ILookup this k nil))
       (valAt [_ k not-found]
         (if (= :session k)
           (when (:conn @srv) (:session @srv))
           (get props k not-found)))
       java.io.Closeable
       (close [_]
         (end-session! srv gone)
         (swap! srv assoc :conn nil)
         (.close ws)
         (.stop server 0)
         (when own (delete-tree! own)))))))

(defn browser-repl
  "A ClojureScript REPL in a browser: an output directory, the two servers over it,
  and the loop over all of them. Blocks until the input runs out.

    :dir           the output directory - a temporary one, removed on exit, if none
                   is given
    :port          what the asset server listens on, default 0
    :ws-port       what the socket listens on, default 0
    :source-paths  where .cljs files are found, default the classpath directories
    :ns            the namespace to start in, default cljs.user
    :in :out       as clojure.cljs.repl/repl takes them
    :program-out   where the page's console output goes, default :out

  One call, for the reason node-repl is one call: the driver compiles into a
  directory and the browser fetches out of it, and a require would silently compile
  where nothing looks if the two differed.

  The URL to open is printed before the first prompt. Nothing waits for it - a form
  evaluated before a page connects says so and the REPL goes on, which is what lets
  you start the REPL first and open the page when you get to it."
  ([] (browser-repl nil))
  ([{:keys [dir port ws-port source-paths ns in out program-out]
     :or   {ns 'cljs.user in *in* out *out*}}]
   ;; The cursor is established here, for the reason repl/node-repl says.
   (env/with-current-ns ns
     (let [^File own (when-not dir (temp-dir))
           ^File d   (io/file (or dir own))
           cenv      (env/compile-env {:ns ns})]
       (try
         (with-open [rt (browser-runtime (cond-> {:dir d :out (or program-out out)}
                                           port    (assoc :port port)
                                           ws-port (assoc :ws-port ws-port)))]
           (doto ^Writer out
             (.write (str "Waiting for a browser on " (:url rt) "\n"))
             (.flush))
           (repl/repl cenv rt {:ns ns :in in :out out
                               :out-dir d :source-paths source-paths}))
         (finally (when own (delete-tree! own))))))))

