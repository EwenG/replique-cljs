;   Copyright (c) Rich Hickey. All rights reserved.
;   The use and distribution terms for this software are covered by the
;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;   which can be found in the file epl-v10.html at the root of this distribution.
;   By using this software in any fashion, you are agreeing to be bound by
;   the terms of this license.
;   You must not remove this notice, or any other, from this software.

(ns ^{:doc "The browser runtime: an asset server, a long-poll, and the same
  IJsRuntime the node transport implements. doc/cljs-repl.md R1.

  A browser cannot be dialled, so it dials out and holds a request open; the JVM
  answers that request when it has something to evaluate, and the answer to the
  NEXT request carries the result. That is Replique's transport, kept for the
  reason doc/cljs-repl.md 6 gives - the polling is not the valuable part, the
  failure semantics are:

    SESSION NUMBERING, so a page refresh invalidates the evaluations the previous
    page never answered. A refresh is not a disconnection a socket would notice:
    the old page simply stops polling, and without a number the JVM would wait for
    an answer that no longer has anyone to produce it.

    EVERY EVALUATION ENDED when the session that owns it does, so that a blocked
    caller gets \"Connection broken\" rather than hanging. Replique reaches this
    with shutdown-eval-executor - interrupt the running task, then hand back the
    queued ones and run them yourself with a dynamic var bound. Here an evaluation
    is a virtual thread holding a permit, so waiting and working are the same
    thing and interrupting them all is the whole of it.

  WHAT IS NOT KEPT, and each because §3.1 removed the need rather than because it
  was skipped: goog/base.js, cljs_deps.js and the bootstrap - ES modules are the
  dependency graph; the pending-eval/after-load handshake in Replique's client -
  loading is an expression here (§5), so a turn is one promise; and every
  cljs.closure call, because the driver already wrote the files this serves.

  DEFERRED, and named so that their absence is a decision: source-mapped stacktraces
  belong with R2. Replique's timeout-before-submitted is NOT on that list any more -
  a tooling request that must not block on an absent runtime is tryAcquire with a
  timeout, so R3 gets it for the price of a call rather than of a mechanism.

  Two entry points, mirroring the node pair in clojure.cljs.repl:

    browser-runtime  the server plus the IJsRuntime over it, Closeable
    browser-repl     that, an output directory, and the loop over both"}
  clojure.cljs.browser
  (:require [clojure.cljs.env :as env]
            [clojure.cljs.output :as output]
            [clojure.cljs.repl :as repl]
            [clojure.edn :as edn]
            [clojure.java.io :as io]
            [clojure.string :as str])
  (:import [com.sun.net.httpserver HttpExchange HttpHandler HttpServer]
           [java.io File Writer]
           [java.net InetSocketAddress URLDecoder]
           [java.nio.charset StandardCharsets]
           [java.nio.file Files LinkOption]
           [java.nio.file.attribute BasicFileAttributes FileAttribute]
           [java.util.concurrent CompletableFuture ExecutionException Executors
            Semaphore SynchronousQueue ThreadFactory TimeUnit]
           [java.util.concurrent ConcurrentHashMap]))

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

;; --- how long anything waits ------------------------------------------------

(def ^:private heartbeat-ms
  "How long a poll is held before it is answered with 204 and the browser asks
  again. It exists so that an idle REPL is not one request that has been open for
  an hour: proxies and fetch implementations both have opinions about those, and a
  request that ends on purpose beats one that ends by timing out."
  20000)

(def ^:private liveness-tick-ms
  "How often an evaluation waiting for its answer looks up to see whether the page
  has gone quiet. Not a deadline and not a delay: a result that arrives wakes the
  wait immediately, and this only sets the resolution at which silence-ms below is
  noticed. Coarse on purpose - a second's granularity against a twenty-second
  threshold is as fine as it can matter."
  1000)

(def ^:private offer-ms
  "How long a script waits for a poll to carry it. A live page always has one in
  flight or one arriving - it re-polls the instant it has answered - so nothing but
  an absent runtime waits this long."
  30000)

(def ^:private silence-ms
  "How long the JVM waits to hear ANYTHING from a page that owes it a result before
  deciding the page is gone.

  This is the number that makes a long-poll behave like a socket. A closed socket
  reports itself; a long-poll that has been answered has nothing left open to
  break, and writing a script into a dead connection succeeds - the bytes reach the
  kernel and no error is ever raised. So the page says it is still there every 5
  seconds while it evaluates, and this is the silence that means it is not.

  Comfortably above the client's 5s ping and below the 20s idle heartbeat, because
  the two windows do not overlap: a page that owes a result is not polling."
  20000)

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
  the session ended under it."
  {:status :error :value "Connection broken"})

(def ^:private expired
  "Handed to a held poll to tell it its session is over.

  It travels on js-queue, which otherwise carries only scripts - strings - so a
  keyword there is unambiguous by construction.

  The queue being a SynchronousQueue is what makes this safe as well as useful:
  offer with no timeout succeeds ONLY when a consumer is already waiting, so this
  either reaches a held poll or does nothing at all. It can never be left sitting
  in the queue for the next session's poll to pick up, because a SynchronousQueue
  holds nothing."
  ::expired)

(def ^:private silent
  "The other case, and a different sentence because it is a different fact: nothing
  interrupted anything, the page simply stopped answering."
  {:status :error
   :value  "The browser stopped answering - it was closed, reloaded or crashed."})

(defn- touch!
  "Note that `n`'s page was heard from. Every message does this, which is what makes
  silence mean something."
  [state n]
  (when (= n (:session @state))
    (swap! state assoc :last-seen (System/currentTimeMillis))))

(defn- silent?
  [state n]
  (and (= n (:session @state))
       (< silence-ms (- (System/currentTimeMillis) (or (:last-seen @state) 0)))))

(defn- gone!
  "Mark the session over because the page stopped answering, so that the NEXT
  evaluation says there is no browser instead of waiting to find out again.

  It does not shut the executor down: this runs ON the executor, and a task cannot
  drain the queue it is standing in. The next :ready replaces it whole."
  [state n]
  (swap! state (fn [m] (if (= n (:session m)) (assoc m :state :stopped) m))))

(defn- release-polls!
  "Wake every poll held for the CURRENT session and tell it the session is over.

  Loops because a page could in principle have more than one request in flight, and
  stops the moment an offer fails - which is the moment no one is left waiting."
  [state]
  (when-let [q (:js-queue @state)]
    (loop []
      (when (.offer ^SynchronousQueue q expired)
        (recur)))))

(defn- turn
  "One evaluation, once it holds the permit: hand the script to whichever poll is
  waiting, then wait for the answer the next poll brings.

  THREE WAYS OUT, and the third is the one a socket would not have needed.
  Interrupted, because the session ended under it. Answered, which is the ordinary
  case. Or given up on, because the page has said nothing for silence-ms - and that
  wait is not bounded by a deadline, since an evaluation may legitimately take
  minutes; it is bounded by evidence that no one is evaluating."
  [state session js]
  (let [{:keys [js-queue result-queue]} @state]
    (if-not (.offer ^SynchronousQueue js-queue js offer-ms TimeUnit/MILLISECONDS)
      (do (gone! state session) silent)
      (loop []
        (if-let [r (.poll ^SynchronousQueue result-queue
                          liveness-tick-ms TimeUnit/MILLISECONDS)]
          r
          (if (silent? state session)
            (do (gone! state session) silent)
            (recur)))))))

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
                                           broken))
                       (finally (.release ^Semaphore permit)))
                     (catch InterruptedException _ (.complete answer broken))
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

(defn- stop-evaluations!
  "End every evaluation belonging to the session that is finishing.

  TWO THINGS DO THIS, and they are not the same thing. For the evaluation holding
  the permit the interrupt is the mechanism: it is parked in `turn`, waiting for a
  poll or for an answer, and nothing else would end that. For the ones waiting on
  the permit it is only a shortcut - the guarantee is the session re-check in
  `evaluate!`, which each of them makes on the way in as the permit comes free.
  Interrupting them as well is insurance against a future release path that is not
  instant, and it costs a loop.

  Either way it is one call where a single-thread executor needed two mechanisms,
  and no dynamic var: an evaluation that has not started is a thread parked on
  acquire, not a Runnable in a queue somebody has to run by hand."
  [state]
  (doseq [^Thread t (:workers @state)]
    (.interrupt t)))

;; --- the handlers -----------------------------------------------------------

(defn- on-ready!
  "A runtime announcing itself: a new page, or the same page refreshed. Either way
  the previous session is over.

  The order matters. :state goes to :stopped first, so nothing new is submitted to
  an executor that is about to be shut down; then the previous page's held poll is
  released, so it learns its session is over rather than waiting to notice; then the
  old executor is drained, which is what unblocks anyone waiting on that page; then
  the new session is installed whole."
  [state]
  (let [session (:session @state)
        n (inc (or session 0))]
    (swap! state assoc :state :stopped)
    (release-polls! state)
    (stop-evaluations! state)
    (swap! state assoc
           :state        :started
           :session      n
           :last-seen    (System/currentTimeMillis)
           :permit       (Semaphore. 1 true)   ; fair, so two callers keep their order
           :workers      (ConcurrentHashMap/newKeySet)
           ;; named per session and numbered within it, so a stack dump says which
           ;; page an evaluation belonged to
           :threads      (-> (Thread/ofVirtual) (.name (str "cljs-eval-" n "-") 0) (.factory))
           :js-queue     (SynchronousQueue.)
           :result-queue (SynchronousQueue.))
    n))

(defn- on-poll!
  "A runtime reporting the previous script's result, if it had one, and asking for
  the next.

  Delivering the result and taking the next script are one request because that is
  what a long-poll is: the runtime is never without a request in flight, so the JVM
  is never without somewhere to send a script.

  The result is OFFERED rather than put: the evaluation that asked for it may have
  been interrupted by a refresh between the two halves of this turn, and a result
  nobody is waiting for must be dropped rather than left to be taken by the next
  evaluation as its own answer."
  [state n content ^HttpExchange ex]
  (let [{:keys [session js-queue result-queue]} @state]
    (if (not= n session)
      (send-text! ex 409 "text/plain" "Session expired")
      (do
        (when content
          (.offer ^SynchronousQueue result-queue (edn/read-string content)
                  5000 TimeUnit/MILLISECONDS))
        ;; ONE park, for the whole heartbeat. This used to wake every 250ms to
        ;; re-read the session number - eighty times per idle heartbeat, per page,
        ;; to notice something that happens once - and the answer is to be TOLD
        ;; rather than to look: whatever ends a session hands this queue a
        ;; sentinel, which arrives here as an ordinary wake-up. It is also faster
        ;; where it matters, since a refresh now ends the old page's poll at once
        ;; instead of up to a tick later.
        (let [js (.poll ^SynchronousQueue js-queue heartbeat-ms TimeUnit/MILLISECONDS)]
          (cond
            (nil? js)         (send! ex 204 "text/plain" (byte-array 0))
            (= expired js)    (send-text! ex 409 "text/plain" "Session expired")
            :else
            (try
              (send-text! ex 200 "text/javascript" js)
              (catch Exception e
                ;; the script was taken off the queue and never reached anyone.
                ;; The evaluation waiting for it has to be told, or it waits for
                ;; an answer that cannot come.
                (.offer ^SynchronousQueue result-queue broken
                        5000 TimeUnit/MILLISECONDS)
                (throw e)))))))))

(defn- on-print!
  [^Writer out content]
  (locking out
    (.write out ^String content)
    (.flush out)))

(defn- on-bye!
  "The page said it was leaving - a closed tab, or a navigation away. A refresh says
  it too, and its :bye carries the session the following :ready has already
  replaced, which is why this checks the number before acting on it.

  Worth having even though silence would find the same thing out: closing a tab is
  the common case, and 20 seconds of a REPL that answers nothing is a long time to
  spend rediscovering something the browser was willing to tell us."
  [state n]
  (when (= n (:session @state))
    (swap! state assoc :state :stopped)
    (release-polls! state)
    (stop-evaluations! state)))

(defn- handle-post
  [state ^Writer out ^HttpExchange ex]
  (let [body (slurp (.getRequestBody ex) :encoding "UTF-8")
        {:keys [type session content]} (edn/read-string body)
        _    (touch! state session)
        ack  #(send! ex 200 "text/plain" (byte-array 0))]
    (case type
      :ready  (send-text! ex 200 "application/json"
                          (str "{\"session\": " (on-ready! state) "}"))
      :poll   (on-poll! state session nil ex)
      :result (on-poll! state session content ex)
      :print  (do (when (= session (:session @state)) (on-print! out content))
                  (ack))
      :alive  (ack)                    ; touch! above was the whole of it
      :bye    (do (on-bye! state session) (ack))
      (send-text! ex 400 "text/plain" (str "Unknown message type: " (pr-str type))))))

(defn- handle-get
  [^File dir ^String path ^HttpExchange ex]
  (let [path (URLDecoder/decode path StandardCharsets/UTF_8)
        path (if (= "/" path) "/index.html" path)
        f    (under dir path)]
    (cond
      f (let [tag (etag f)]
          (send-asset! ex (content-type path) tag
                       (when-not (fresh? ex tag) (Files/readAllBytes (.toPath f)))))
      (= "/index.html" path) (send-text! ex 200 "text/html" default-page)
      :else (send-text! ex 404 "text/plain" (str "No " path " here.")))))

(defn- handler
  [state ^File dir out]
  (reify HttpHandler
    (handle [_ ex]
      (try
        (let [^HttpExchange ex ex
              method (.getRequestMethod ex)
              path   (.getPath (.getRequestURI ex))]
          (case method
            "OPTIONS" (send! ex 204 "text/plain" (byte-array 0))
            "POST"    (handle-post state out ex)
            "GET"     (handle-get dir path ex)
            (send-text! ex 405 "text/plain" "Method not allowed")))
        (catch Throwable _
          ;; the browser went away mid-response, or the body was not a message.
          ;; Either way this connection is over and the next poll starts a new one.
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
  "Serve `dir` over HTTP and evaluate in whatever browser connects to it.

    :dir      the output directory to serve, and the one the driver compiles into -
              a temp directory by default
    :port     what to listen on, default 0, which is an ephemeral port
    :out      where the runtime's own output is written, default *out*
    :out      where the page's console output is written, default *out*

  Closeable, and closing it stops the server and unblocks any evaluation still
  waiting on the page.

  The returned object answers (:url rt), which is what to open, (:port rt), (:dir
  rt) - which is what the driver has to compile into - and (:session rt), which is
  nil until a page connects and a different number after every refresh.

  Evaluating before a browser has connected is not an error and not a wait: it
  answers with what to do about it. That is Replique's behaviour and it is the
  right one for a REPL you started before you opened the page."
  ([] (browser-runtime nil))
  ([{:keys [dir port out] :or {port 0 out *out*}}]
   (let [^File own (when-not dir (temp-dir))
         ^File dir (write-runtime! (or dir own))
         srv       (atom {:state :stopped :session 0})
         ;; A VIRTUAL THREAD PER REQUEST, which is what this server is shaped for:
         ;; every held poll is a thread parked for up to 20 seconds doing nothing,
         ;; and that is the case thread-per-request was made cheap for.
         ;;
         ;; Not for speed - measured, it is a wash: virtual threads start ~20x
         ;; cheaper and block ~20% dearer, and a pool was already amortising the
         ;; first away. It is for what stops being true. There is no pool, so no
         ;; unbounded growth and no keepalive to know about (a cached pool's
         ;; threads are non-daemon and linger a minute past the work, which is why
         ;; the eval executor below still asks for daemon ones). And no thread is
         ;; reused between requests, so nothing thread-local can survive from one
         ;; to the next - which for Clojure means a dynamic binding left unwound.
         ;;
         ;; Checked rather than assumed, because a pinned carrier would serialise
         ;; the polls and this server would quietly hold one page at a time: with
         ;; the scheduler cut to a single carrier, two held requests still run
         ;; concurrently, so neither the exchange I/O nor SynchronousQueue pins.
         server    (doto (HttpServer/create (InetSocketAddress. "127.0.0.1" (int port)) 0)
                     (.setExecutor (Executors/newVirtualThreadPerTaskExecutor))
                     (.createContext "/" (handler srv dir out))
                     (.start))
         port      (.getPort (.getAddress server))
         url       (str "http://127.0.0.1:" port "/")
         props     {:url url :port port :dir dir}]
     (reify
       repl/IJsRuntime
       (-evaluate [_ js]
         (if (not= :started (:state @srv))
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
           (let [{:keys [state session]} @srv]
             (if (= :started state) session nil))
           (get props k not-found)))
       java.io.Closeable
       (close [_]
         (swap! srv assoc :state :stopped)
         (stop-evaluations! srv)
         ;; a held poll would otherwise sit out the rest of its heartbeat on a
         ;; server that is already gone
         (release-polls! srv)
         (.stop server 0)
         (when own (delete-tree! own)))))))

(defn browser-repl
  "A ClojureScript REPL in a browser: an output directory, an HTTP server over it,
  and the loop over both. Blocks until the input runs out.

    :dir           the output directory - a temporary one, removed on exit, if none
                   is given
    :port          what to listen on, default 0
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
  ([{:keys [dir port source-paths ns in out program-out]
     :or   {ns 'cljs.user in *in* out *out*}}]
   ;; The cursor is established here, for the reason repl/node-repl says.
   (env/with-current-ns ns
     (let [^File own (when-not dir (temp-dir))
           ^File d   (io/file (or dir own))
           cenv      (env/compile-env {:ns ns})]
       (try
         (with-open [rt (browser-runtime {:dir d :port port :out (or program-out out)})]
           (doto ^Writer out
             (.write (str "Waiting for a browser on " (:url rt) "\n"))
             (.flush))
           (repl/repl cenv rt {:ns ns :in in :out out
                               :out-dir d :source-paths source-paths}))
         (finally (when own (delete-tree! own))))))))
