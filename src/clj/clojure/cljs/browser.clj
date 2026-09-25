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
            ExecutionException Executors Semaphore ThreadFactory TimeoutException
            TimeUnit]))

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

;; --- who is connected ------------------------------------------------------
;;
;; A VECTOR, NEWEST LAST, AND THE LAST OF IT IS WHERE EVALUATION GOES. The
;; long-poll could not have held more than one page: two runtimes polling one REPL
;; would take alternate turns and answer each other's questions, so a page that was
;; replaced had to be told to step aside. Scripts now go to a connection by name,
;; so an older page cannot take a turn it was not offered, and several may stay.
;;
;; WHICH MAKES THE INTERESTING DISTINCTION POSSIBLE, and it is repl/IJsRuntimes':
;; loading is not evaluation. A require is idempotent and answers nil wherever it
;; runs, and what you want from it is that every page you have open picks up the new
;; code - so it goes to all of them. An ordinary form has a value, and a value needs
;; one answer rather than a set of them differing by which page's clock or random
;; seed produced it - so it goes to one.
;;
;; A SECOND TAB BREAKS NOTHING; A REFRESH STILL BREAKS EVERYTHING. The two used to
;; be indistinguishable - both arrived as a :ready - and both had to be treated as a
;; replacement. Over a socket a refresh closes before it opens and a new tab closes
;; nothing, so opening one moves the cursor and leaves what is running alone, while
;; the close that a refresh begins with ends the evaluations the old page owned.

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
;;
;; THE PERMIT BELONGS TO THE REPL AND NOT TO A PAGE. One evaluation at a time is a
;; property of the prompt - you typed one form - and it stays true across a refresh,
;; which is why it is made once with the runtime rather than once per session.

(def ^:private broken
  "Replique's wording, for Replique's case: the evaluation was interrupted because
  the session ended under it."
  {:status :error :value "Connection broken"})

(def ^:private gone
  "The other case, and a different sentence because it is a different fact: the
  page did not lose a race, it left."
  {:status :error
   :value  "The browser is gone - it was closed, reloaded or crashed."})

(def ^:private other-page-ms
  "How long a broadcast waits for a page that is NOT the one evaluation targets.

  The target is waited for without a bound, because an evaluation may legitimately
  take minutes and that is the REPL's semantics. The others cannot have that: a
  backgrounded tab on a sleeping laptop is connected, will answer eventually, and
  must not be able to hold up a require. So they get a generous fixed grace and are
  reported rather than waited for - a load is a few hundred milliseconds of module
  fetching, and ten seconds of it means something is wrong with that page, not with
  this one."
  10000)

(defn- end-turns!
  "End every evaluation in flight, and say why.

  TWO MECHANISMS FOR TWO POPULATIONS. A turn that has been sent is COMPLETED, which
  is how the thread waiting on it returns at once and with the right reason rather
  than by being interrupted out of a wait. An evaluation that has not started is a
  thread parked on the permit with no turn to complete, and for that the interrupt
  is the mechanism.

  One call where a single-thread executor needed two mechanisms and a dynamic var:
  an evaluation that has not started is a thread parked on acquire, not a Runnable
  in a queue somebody has to run by hand."
  [state reason]
  (swap! state assoc :reason reason)
  (doseq [[_ ^CompletableFuture p] (:pending @state)]
    (.complete p reason))
  (doseq [^Thread t (:workers @state)]
    (.interrupt t)))

(def ^:private browsers
  "Enough of a table to say which page is which, in the order it must be tried:
  Edge and Opera both claim to be Chrome, and Chrome claims to be Safari, so the
  specific names come first and Safari - the only one that claims nothing - last."
  [[#"Firefox/(\d+)" "Firefox"]
   [#"Edg/(\d+)"     "Edge"]
   [#"OPR/(\d+)"     "Opera"]
   [#"Chrome/(\d+)"  "Chrome"]
   [#"Version/(\d+).*Safari" "Safari"]
   [#"Safari/(\d+)"  "Safari"]])

(defn- page-name
  "What to call the page that sent `req`, from its User-Agent - which the handshake
  is the only place to get, since a websocket frame carries nothing but its payload.

  A guess, and it says so when it is one: an agent this does not recognise is shown
  truncated rather than labelled wrongly, and a page that sent none at all - which
  is every non-browser client, node included - is \"unknown\"."
  [req]
  (let [ua (get-in req [:headers "user-agent"])]
    (cond
      (str/blank? ua) "unknown"
      :else (or (some (fn [[re nm]]
                        (when-let [m (re-find re ua)]
                          (str nm " " (second m))))
                      browsers)
                (if (< (count ua) 40) ua (str (subs ua 0 37) "..."))))))

(defn- start-session!
  "A page connected. It becomes the one evaluation targets, and NOTHING IS ENDED:
  over a socket this is either a new tab, which has replaced nothing, or the second
  half of a refresh whose first half already ended what the old page owned.

  THE SESSION COUNTER IS ALSO THE PAGE'S NAME. It only ever goes up, so a number
  never means two different pages in one REPL - which matters for (pages n), where
  reusing 2 for a tab opened after the first one closed would be a way to evaluate
  in the wrong place."
  [state conn req]
  (:session
   (swap! state (fn [m]
                  (let [n (inc (or (:session m) 0))]
                    (assoc m
                           :conns   (conj (:conns m) conn)
                           :conn    conn
                           :reason  nil
                           :session n
                           :pages   (assoc (:pages m) conn
                                           {:id n :name (page-name req)})))))))

(defn- close-session!
  "A page went away.

  The turn it owed ends either way - somebody is waiting on an answer that page was
  going to produce. Everything ELSE ends only if it was the page evaluation
  targeted, which is what makes closing a stale tab a non-event and a refresh the
  end of the session."
  [state conn]
  (let [target? (identical? conn (:conn @state))]
    (when-let [^CompletableFuture p (get (:pending @state) conn)]
      (.complete p gone))
    (swap! state (fn [m]
                   (let [conns (vec (remove #(identical? conn %) (:conns m)))]
                     (assoc m
                            :conns conns
                            ;; WHICHEVER IS NEWEST, and only because the page that
                            ;; was chosen has gone. A close is the one thing that
                            ;; moves the target without being asked to.
                            :conn  (last conns)
                            :pages (dissoc (:pages m) conn)))))
    (when target?
      (end-turns! state gone))))

;; --- one evaluation ---------------------------------------------------------

(defn- start-turn!
  "Register a turn for `conn` and write the script into its socket. Answers the
  CompletableFuture the page's result will complete."
  [state conn js]
  (let [pending (CompletableFuture.)]
    (swap! state assoc-in [:pending conn] pending)
    (try
      (.sendText ^WebSocketConnection conn js)
      (catch Throwable t
        (.complete pending {:status :error :phase :transport
                            :value  (str "The runtime failed: " (ex-message t))})))
    pending))

(defn- finish-turn!
  "Forget the turn, so that a result arriving after it ended is dropped rather than
  taken by whatever asks next."
  [state conn]
  (swap! state update :pending dissoc conn))

(defn- note-other-page!
  [^Writer out r]
  (locking out
    (.write out (str ";; another connected page did not load this: " (:value r) "\n"))
    (.flush out)))

(defn- turn
  "One evaluation, once it holds the permit: write the script into the socket - or
  into every socket, when this is a load - and wait for the answers.

  TWO WAYS OUT WHERE THE LONG-POLL HAD THREE. Answered, which is the ordinary case.
  Ended, because the page went away or was replaced - and that arrives as a
  completion rather than an interrupt, so it is instant and carries its own reason.
  The third, giving up because nothing has been heard for twenty seconds, is gone
  along with the thing that made it necessary: there is no waiting to find out
  whether anyone is there.

  Only the target's answer is returned. The others are reported, for the reason
  IJsRuntimes gives: a tab left open from yesterday failing to load something must
  not be why your require says it failed."
  [state ^Writer out js all?]
  (let [{:keys [conns conn]} @state]
    (if (nil? conn)
      gone
      (let [targets (if all? conns [conn])
            turns   (mapv (fn [c] [c (start-turn! state c js)]) targets)]
        (try
          (let [mine (some (fn [[c ^CompletableFuture f]]
                             (when (identical? c conn) (.get f)))
                           turns)]
            (doseq [[c ^CompletableFuture f] turns
                    :when (not (identical? c conn))]
              (let [r (try (.get f other-page-ms TimeUnit/MILLISECONDS)
                           (catch TimeoutException _
                             {:status :error
                              :value  (str "it did not answer within "
                                           other-page-ms "ms")}))]
                (when (= :error (:status r))
                  (note-other-page! out r))))
            mine)
          (finally
            (doseq [[c _] turns] (finish-turn! state c))))))))

(defn- evaluate!
  "Run `js` on a virtual thread of its own, one evaluation at a time, and wait for
  the answer. `all?` sends it to every connected page instead of only the one
  evaluation targets. `ms` bounds the wait, or nil does not bound it.

  The thread is ours rather than the caller's, which is the property that makes
  ending a session safe: a refresh interrupts threads this namespace made, never one
  it was handed. Doing the work on the calling thread would be less machinery and
  would put an interrupt on the REPL loop.

  AND IT IS WHAT MAKES A DEADLINE POSSIBLE AT ALL (repl/IJsDeadline). Giving up is
  interrupting that thread, which does the right thing in both places it can be:
  one still parked on the permit leaves the queue without ever having sent
  anything, and one that has sent its script stops waiting for the page and lets
  the permit go, so the evaluation behind it is not held up by a question nobody is
  listening to the answer to any more. The script itself goes on running in the
  page - nothing can stop JavaScript - and its result is dropped when it arrives,
  because the turn it would have completed was forgotten on the way out (see
  finish-turn!).

  WHICH OF THE TWO IT WAS is worth reporting rather than eliding, so the worker
  says when it has started: a question that never got in front of the browser and
  one the browser is still chewing on are different situations for whoever asked."
  [state ^Writer out js all? ms]
  (let [{:keys [permit workers threads]} @state
        answer  (CompletableFuture.)
        started (volatile! false)
        body    (fn []
                  (let [me (Thread/currentThread)]
                    (.add ^java.util.Set workers me)
                    (try
                      (.acquire ^Semaphore permit)
                      (try
                        (vreset! started true)
                        (.complete answer (turn state out js all?))
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
                        (.complete answer broken)))))
        worker  (.newThread ^ThreadFactory threads ^Runnable body)]
    (.start ^Thread worker)
    (try
      (if ms
        (try
          (.get answer ms TimeUnit/MILLISECONDS)
          (catch TimeoutException _
            (.interrupt ^Thread worker)
            (if @started (repl/timed-out ms) (repl/busy ms))))
        (.get answer))
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
  "A frame from a page: the result of the script it was given, or something it
  printed.

  BOTH ARRIVE HERE, ON THAT PAGE'S OWN THREAD, IN ORDER, which is the whole of what
  the socket bought: a println inside a form and that form's value used to be two
  POSTs that could land either way round.

  A result is completed into the turn THAT PAGE was given, and a result from a page
  with no turn open is dropped - it answered late, or it answered something nobody
  asked. A print is taken from any page at all, with or without a turn: output is
  not an answer to anything, and a tab someone still has open is a console someone
  may still be watching.

  AND AN UNCAUGHT ERROR IS TAKEN ON THE SAME TERMS AS A PRINT, because it is the
  same kind of thing: an exception out of an event handler or a promise nobody
  caught belongs to no turn, so there is nobody to return it to and the only place
  for it is the output. Symbolicated on the way (repl/uncaught-text) - the maps are
  in the directory this server serves, so the frames can be read back as
  ClojureScript exactly as a caught error's are."
  [state ^File dir ^Writer out conn text]
  (let [{:keys [type content]} (edn/read-string text)]
    (case type
      :result   (when-let [^CompletableFuture p (get (:pending @state) conn)]
                  (.complete p (edn/read-string content)))
      :print    (on-print! out content)
      :uncaught (on-print! out (repl/uncaught-text dir content))
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


(defn- pages-of
  "Who is connected, oldest first, as repl/IJsRuntimes wants it: {:id :name
  :target?}. Data rather than a table, because how to show it is the REPL's
  business and who is there is this namespace's."
  [state]
  (let [{:keys [conns conn pages]} @state]
    (mapv (fn [c] (assoc (get pages c) :target? (identical? c conn))) conns)))

(defn- select-page!
  "Point evaluation at the page called `id`. False if there is no such page.

  IT DOES NOT DISTURB ANYTHING IN FLIGHT, and cannot: an evaluation binds to a
  connection when it is sent, not when it is asked for, so a form already running
  in the old page goes on running there and answers its own caller. What moves is
  only where the NEXT one goes."
  [state id]
  (boolean
   (when-let [c (some (fn [c] (when (= id (:id (get (:pages @state) c))) c))
                      (:conns @state))]
     (swap! state assoc :conn c)
     true)))

(defn- nobody-connected
  "The answer when there is no page, which is not an error to recover from and not
  a wait: a REPL you started before you opened the browser is the normal way round,
  and the useful answer is the URL. nil when a page IS connected."
  [url state]
  (when-not (:conn @state)
    {:status :error
     :value  (str "No browser is connected. Open " url " - or import "
                  client-name " from it in a page of your own - and "
                  "evaluate this again.")}))

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
         srv       (atom {:session nil
                          :conns   []
                          :conn    nil
                          :pages   {}
                          :pending {}
                          ;; made once, with the runtime, not once per page - see
                          ;; the note above broken
                          :permit  (Semaphore. 1 true)   ; fair, so two callers keep their order
                          :workers (ConcurrentHashMap/newKeySet)
                          :threads (-> (Thread/ofVirtual)
                                       (.name "cljs-eval-" 0)
                                       (.factory))})
         token     (websocket/random-token)
         ws        (websocket/websocket-server
                    {:port     ws-port
                     :token    token
                     :on-open  (fn [conn req] (start-session! srv conn req))
                     :on-text  (fn [conn text] (on-text! srv dir out conn text))
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
         (or (nobody-connected url srv) (evaluate! srv out js false nil)))
       repl/IJsDeadline
       ;; What tooling asks with, and the reason the permit is a permit: a
       ;; completion or a watch must not wait behind the form you are running, and
       ;; tryAcquire says whether it would have to.
       (-evaluate-within [_ js ms]
         (or (nobody-connected url srv) (evaluate! srv out js false ms)))
       ;; The fourth cell, and the transport had it all along: `evaluate!' takes
       ;; both axes, and until now three of the four combinations were reachable.
       ;; What asks for this is tooling that wants every page rather than one -
       ;; and tooling is the half that cannot wait, which is why the method lives
       ;; in IJsDeadline and not beside -evaluate-all.
       (-evaluate-all-within [_ js ms]
         (or (nobody-connected url srv) (evaluate! srv out js true ms)))
       repl/IJsRuntimes
       ;; the load path. Every page gets the script; the one evaluation targets is
       ;; the one whose answer is the answer. See this namespace's "who is
       ;; connected" note and repl/IJsRuntimes.
       (-evaluate-all [_ js]
         (or (nobody-connected url srv) (evaluate! srv out js true nil)))
       (-pages [_] (pages-of srv))
       (-select-page! [_ id] (select-page! srv id))
       clojure.lang.ILookup
       ;; :session is the one that is not a constant, and the one worth asking for:
       ;; it is nil until a page connects and a different number after a refresh,
       ;; so it is how anything holding this runtime can tell either apart.
       (valAt [this k] (.valAt ^clojure.lang.ILookup this k nil))
       (valAt [_ k not-found]
         (case k
           :session     (when (:conn @srv) (:session @srv))
           ;; every page holding a socket, oldest first - the last of them is the
           ;; one an ordinary evaluation goes to
           :connections (:conns @srv)
           (get props k not-found)))
       java.io.Closeable
       (close [_]
         (end-turns! srv gone)
         (swap! srv assoc :conns [] :conn nil :pages {})
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
    :main          a namespace to require before the first prompt, if any. A page
                   that is not open yet cannot be given it, and says so - the
                   compile happens either way
    :in :out       as clojure.cljs.repl/repl takes them
    :program-out   where the page's console output goes, default :out
    :analysis      as clojure.cljs.repl/repl takes it

  One call, for the reason node-repl is one call: the driver compiles into a
  directory and the browser fetches out of it, and a require would silently compile
  where nothing looks if the two differed.

  The URL to open is printed before the first prompt. Nothing waits for it - a form
  evaluated before a page connects says so and the REPL goes on, which is what lets
  you start the REPL first and open the page when you get to it."
  ([] (browser-repl nil))
  ([{:keys [dir port ws-port source-paths ns main in out program-out analysis]
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
           (repl/repl cenv rt {:ns ns :main main :in in :out out
                               :out-dir d :source-paths source-paths
                               :analysis analysis}))
         (finally (when own (delete-tree! own))))))))

