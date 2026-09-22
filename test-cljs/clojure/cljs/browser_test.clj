;   Copyright (c) Rich Hickey. All rights reserved.
;   The use and distribution terms for this software are covered by the
;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;   which can be found in the file epl-v10.html at the root of this distribution.
;   By using this software in any fashion, you are agreeing to be bound by
;   the terms of this license.
;   You must not remove this notice, or any other, from this software.


(ns ^{:doc "The browser runtime: the asset server, the websocket, and what each
  way of leaving means.

  THE PAGE IS A NODE PROCESS HERE, and the substitution is exact in the half these
  tests are about and inexact in the half they are not. runtime_browser.js is
  loaded and run unmodified - it needs fetch, WebSocket and eval, and nothing else
  a browser has that node lacks - so the wire and the print channel are the real
  ones. What node does differently is where $CLJS.require finds a module: relative
  to runtime.js's own URL, which is a file under node and an HTTP origin in a
  browser. That path is tested from the other end instead, by fetching the same
  files over HTTP and comparing them to what the driver wrote.

  Some tests speak the socket by hand instead, with the JDK's own websocket
  client. Those are the ones about timing - what is held, what is released, what
  answers whom - where a real page's turn-taking would hide the thing under test.

  The framing itself is not re-checked here; it has its own tests in ws-test, and
  who may open a socket at all has its own in websocket-test.

  Skipped when node is not on PATH."}
  clojure.cljs.browser-test
  (:require [clojure.cljs.browser :as browser]
            [clojure.cljs.driver :as driver]
            [clojure.cljs.env :as env]
            [clojure.cljs.output :as output]
            [clojure.cljs.repl :as repl]
            [clojure.cljs.test-harness :as h]
            [clojure.java.io :as io]
            [clojure.string :as str]
            [clojure.test :refer [deftest is use-fixtures]])
  (:import [java.io File StringWriter]
           [java.net HttpURLConnection URI URL]
           [java.net.http HttpClient WebSocket WebSocket$Listener]
           [java.util.concurrent ExecutionException LinkedBlockingQueue TimeUnit]))

(use-fixtures :each h/cursor)

;; --- a page, standing in ----------------------------------------------------

(defn- start-page!
  "A node process running the browser client against `rt`, and a thread copying
  what it says to `log`.

  It is written into the output directory rather than run from a string so that it
  imports the client by the same relative specifier a served page uses. `extra` is
  a line put in front of the connect, for the one test that needs the page itself
  to do something node's way."
  ([rt log] (start-page! rt log ""))
  ([rt ^StringBuffer log ^String extra]
   (let [^File dir (:dir rt)]
     (spit (File. dir "page.js")
           (str "import { connect, reportUncaught } from \"./runtime_browser.js\";\n"
                extra
                "connect(process.argv[2]);\n"))
     (let [p (-> (ProcessBuilder. ["node" "page.js" (:url rt)])
                 (.directory dir)
                 (.redirectErrorStream true)
                 (.start))]
       (doto (Thread. #(with-open [r (io/reader (.getInputStream p))]
                         (loop []
                           (when-let [l (.readLine r)]
                             (.append log (str l "\n"))
                             (recur))))
                      "page-output")
         (.setDaemon true)
         (.start))
       p))))

(defn- wait-for
  "Poll `f` until it is truthy, for up to `ms`. Returns what it saw, or nil."
  ([f] (wait-for f 15000))
  ([f ms]
   (loop [waited 0]
     (or (f)
         (when (< waited ms)
           (Thread/sleep 50)
           (recur (+ waited 50)))))))

(defn- connected!
  "Start a page and wait until the JVM has heard from it, returning [process
  session]. The session number is what says a page connected - and a DIFFERENT
  number is what says a second one took over."
  ([rt log] (connected! rt log nil))
  ([rt log after]
   (let [p (start-page! rt log)
         n (wait-for #(let [n (:session rt)]
                        (when (and n (not= n after)) n)))]
     (is (some? n) "a page connected")
     [p n])))

(defmacro ^:private with-page
  "A browser runtime, a page against it, and both cleaned up. `bindings` is
  [rt-sym out-sym log-sym] - the runtime, where the page's console output goes and
  what the page process itself said."
  [[rt out log & {:keys [dir]}] & body]
  `(let [~out (StringWriter.)
         ~log (StringBuffer.)]
     (with-open [~rt (browser/browser-runtime (cond-> {:out ~out} ~dir (assoc :dir ~dir)))]
       ;; cljs.core into the directory the page fetches from - see with-core!. The
       ;; browser reaches it over the same HTTP server that serves every other
       ;; module, so what makes it work here is only that the file is on disk,
       ;; which is the whole point of the two halves sharing one directory.
       (with-core! ~rt)
       (let [p# (first (connected! ~rt ~log))]
         (try ~@body (finally (.destroy ^Process p#)))))))

(def ^:private connection-broken
  "What an evaluation the session ended under answers with."
  {:status :error :value "Connection broken"})

(defn- with-core!
  "Compile cljs.core into the directory `rt` serves from, and return rt.

  with-page does this for the runtimes it makes; the two tests that build one by
  hand call it themselves. Needed because every script opens with await
  $CLJS.require(\"cljs.core\") since §5.12, and that reads a file off disk."
  [rt]
  (driver/compile-namespace! (env/compile-env {:ns 'cljs.user}) 'cljs.core
                             {:out-dir (:dir rt)})
  rt)

(defn- values
  [rt ns-sym src]
  (mapv :value (repl/eval-src (env/compile-env {:ns ns-sym}) rt src)))


;; --- a page, spoken by hand -------------------------------------------------

(defn- ws-url
  "Where the page is told to dial, read from the file the JVM wrote into the output
  directory - which is how a real page finds it too."
  [rt]
  (second (re-find #"\"ws\": \"([^\"]+)\""
                   (slurp (File. ^File (:dir rt) "cljs-repl.json")))))

(defn- fake-page!
  "A websocket that is not a page: it connects and queues the scripts it is handed
  instead of evaluating them, so a test can answer in its own time - or not at all.

  `ua` is the User-Agent it claims, which is all the JVM ever learns about what a
  page is.

  Answers [ws scripts]."
  ([rt] (fake-page! rt nil))
  ([rt ua]
   (let [scripts (LinkedBlockingQueue.)
         acc     (StringBuilder.)
         l       (reify WebSocket$Listener
                   (onText [_ socket data last?]
                     (.append acc data)
                     (when last?
                       (.offer scripts (.toString acc))
                       (.setLength acc 0))
                     (.request ^WebSocket socket 1)
                     nil))]
     [(-> (HttpClient/newHttpClient)
          (.newWebSocketBuilder)
          (cond-> ua (.header "User-Agent" ua))
          (.buildAsync (URI/create (ws-url rt)) l)
          (.get 10000 TimeUnit/MILLISECONDS))
      scripts])))

(defn- answer!
  "Send `edn` - itself the text of a result map, which is what a page sends: what
  runtime.js printed, JSON.stringify'd."
  [^WebSocket ws edn]
  (.get (.sendText ws (str "{:type :result :content " (pr-str edn) "}") true)
        10000 TimeUnit/MILLISECONDS))

(defn- took [^LinkedBlockingQueue q] (.poll q 10000 TimeUnit/MILLISECONDS))

;; --- the asset server -------------------------------------------------------

(defn- GET
  "[status body] for a GET of `path` on `rt`."
  [rt ^String path]
  (let [^HttpURLConnection c (.openConnection (URL. (str (:url rt) (subs path 1))))
        status (.getResponseCode c)]
    [status (try (slurp (.getInputStream c)) (catch Exception _ nil))]))

(defn- fetch
  "A GET, optionally conditional on `tag`, as {:status :etag :cache :body}."
  ([rt path] (fetch rt path nil))
  ([rt ^String path tag]
   (let [^HttpURLConnection c (.openConnection (URL. (str (:url rt) (subs path 1))))]
     (.setUseCaches c false)                ; the JDK client must not answer for us
     (.setRequestMethod c "GET")
     (when tag (.setRequestProperty c "If-None-Match" tag))
     {:status (.getResponseCode c)
      :etag   (.getHeaderField c "ETag")
      :cache  (.getHeaderField c "Cache-Control")
      :body   (try (slurp (.getInputStream c)) (catch Exception _ nil))})))

(h/deftest-when h/node? test-the-output-directory-is-what-is-served
  ;; The browser fetches modules from the same directory the driver compiles into,
  ;; by the specifiers clojure.cljs.output computes - so the server's whole job is
  ;; to be that directory, and nothing here knows a path the layout did not give it.
  (with-open [rt (browser/browser-runtime {})]
    (is (= [200 (output/prelude-source)] (GET rt "/runtime.js")))
    (is (= 200 (first (GET rt "/package.json"))))
    (is (str/includes? (second (GET rt "/runtime_browser.js")) "export async function connect"))
    ;; a program compiled into it is reachable at the path the layout gives it
    (let [cenv (env/compile-env {:ns 'cljs.user})
          src  (h/write-sources! '{served.core "(ns served.core) (def x 1)"})]
      (try
        (repl/eval-src cenv rt "(require 'served.core)"
                       {:out-dir (:dir rt) :source-paths [src]})
        (let [[status body] (GET rt (str "/" (output/ns->path 'served.core)))]
          (is (= 200 status))
          (is (= (slurp (io/file (:dir rt) (output/ns->path 'served.core))) body)))
        (finally (h/delete-tree! src))))))

(h/deftest-when h/node? test-nothing-outside-the-output-directory-is-served
  ;; Canonicalised before the check rather than scanned for "..", so an encoding
  ;; that spells the same path differently does not get a different answer.
  (with-open [rt (browser/browser-runtime {})]
    (is (= 404 (first (GET rt "/nope.js"))))
    (is (= 404 (first (GET rt "/../../../../etc/passwd"))))
    (is (= 404 (first (GET rt "/%2e%2e/%2e%2e/%2e%2e/etc/passwd"))))))

(h/deftest-when h/node? test-the-page-is-the-application-s-if-it-has-one
  ;; The default page exists so that a REPL with no application still has somewhere
  ;; to connect from. The interesting case is the other one, and it is the reason
  ;; the client takes its URL from import.meta.url: a real page is the
  ;; application's own, and it should not have to be told where the REPL is.
  (with-open [rt (browser/browser-runtime {})]
    (is (str/includes? (second (GET rt "/")) "runtime_browser.js"))
    (spit (File. ^File (:dir rt) "index.html") "<h1>the application</h1>")
    (is (= "<h1>the application</h1>" (second (GET rt "/"))))))

;; --- evaluating -------------------------------------------------------------

(h/deftest-when h/node? test-evaluating-before-a-page-connects-says-what-to-do
  ;; Not an error to recover from and not a wait: a REPL you started before you
  ;; opened the page is the normal way round, and the answer is the URL.
  (with-open [rt (browser/browser-runtime {})]
    (let [r (repl/-evaluate rt "1")]
      (is (= :error (:status r)))
      (is (str/includes? (:value r) (:url rt))))))

(h/deftest-when h/node? test-the-oracle-over-the-browser-transport
  ;; doc/cljs-repl.md 9's R0 oracle, over the other transport. It is the same test
  ;; because the transport is not what makes it work: a var is a property of a
  ;; namespace object in the runtime, and the JVM half above it does not know
  ;; which runtime it is talking to.
  (with-page [rt out log]
    (is (= ["#object[Function browser_oracle$core$f]" "2"
            "#object[Function browser_oracle$core$g]" "3"
            "#object[Function browser_oracle$core$f]" "102"]
           (values rt 'browser-oracle.core
                   "(def f (fn* ([x] (js* \"~{} + 1\" x))))
                    (f 1)
                    (def g (fn* ([x] (f (js* \"~{} + 1\" x)))))
                    (g 1)
                    (def f (fn* ([x] (js* \"~{} + 100\" x))))
                    (g 1)")))))

(h/deftest-when h/node? test-an-error-comes-back-as-one
  (with-page [rt out log]
    (let [r (first (repl/eval-src (env/compile-env {:ns 'browser-err.core}) rt
                                  "(js* \"nope_at_all()\")"))]
      (is (= :error (:status r)))
      (is (str/includes? (:value r) "nope_at_all")))))

(h/deftest-when h/node? test-the-print-channel-carries-the-page-s-console
  ;; A browser has no stdout for the JVM to pump, so unlike node this channel is not
  ;; optional (doc/cljs-repl.md 8). Before M5 there is no *print-fn* to set, so what
  ;; is forwarded is the console - tee'd, because devtools is where a browser user
  ;; looks first.
  (with-page [rt out log]
    (values rt 'browser-out.core "(js* \"console.log('hello from the page'), 1\")")
    (is (wait-for #(str/includes? (str out) "hello from the page")))))


(h/deftest-when h/node? test-a-print-arrives-before-the-value-of-the-form-that-printed-it
  ;; THE BUG THE SOCKET FIXED, and the only one of these tests that could not have
  ;; passed before. A print and the result of the form that printed it used to be
  ;; two POSTs on two connections, ordered by whichever the kernel got to first;
  ;; the REPL could print a form's value above the output that form produced.
  ;;
  ;; They are now two frames on one socket, handed to one callback thread in order,
  ;; and the print is written before the result is completed - so by the time
  ;; -evaluate has returned at all, the output is already there. No waiting, which
  ;; is the point: a wait here would pass under the old transport too.
  (with-page [rt out log]
    (let [v (values rt 'browser-order.core
                    "(js* \"console.log('printed first'), 42\")")]
      (is (= ["42"] v))
      (is (str/includes? (str out) "printed first")
          "already written when the value came back"))))

;; --- loading ----------------------------------------------------------------

(def ^:private two-files
  '{my-lib.core "(ns my-lib.core)
                 (def helper (fn* ([x] (js* \"~{} * 2\" x))))"
    app.core    "(ns app.core (:require [my-lib.core :as lib]))
                 (def use-it (fn* ([] (lib/helper 21))))"})

(h/deftest-when h/node? test-r1-over-the-browser-transport
  ;; The R1 oracle again, and for the same reason as the R0 one above: require,
  ;; :reload and the shipped body are decided on the JVM and answered by the
  ;; runtime, and neither half asks which transport carried the script.
  (let [src (h/write-sources! two-files)
        out (h/temp-dir)]
    (try
      (with-page [rt program-out log :dir out]
        (let [cenv (env/compile-env {:ns 'cljs.user})
              opts {:out-dir out :source-paths [src]}
              run  (fn [s] (mapv :value (repl/eval-src cenv rt s opts)))]
          (is (= ["nil" "42"] (run "(require '[app.core :as a]) (a/use-it)")))
          (h/write-sources! src '{my-lib.core "(ns my-lib.core)
                                               (def helper (fn* ([x] (js* \"~{} * 3\" x))))"})
          (is (= ["nil" "63"] (run "(require 'my-lib.core :reload) (a/use-it)")))))
      (finally (h/delete-tree! src) (h/delete-tree! out)))))

;; --- what a refresh does ----------------------------------------------------

(h/deftest-when h/node? test-a-second-page-leaves-the-first-one-alone
  ;; THE SEMANTICS A SOCKET CHANGED. Over the long-poll a second page arriving was
  ;; indistinguishable from a refresh - both were a :ready - and both had to end
  ;; whatever the previous page owed, because two runtimes polling one REPL would
  ;; answer each other's questions.
  ;;
  ;; A socket tells the two apart: a refresh closes before it opens, a new tab
  ;; closes nothing. So opening one moves where evaluation goes and disturbs
  ;; nothing that is running - and it is the CLOSE, when it comes, that ends what
  ;; the old page owed.
  (let [out (StringWriter.) log (StringBuffer.)]
    (with-open [rt (browser/browser-runtime {:out out})]
      (with-core! rt)
      (let [[a n] (connected! rt log)
            hung  (future (repl/-evaluate
                           rt "(async function () { return new Promise(function () {}); })()"))]
        (is (nil? (deref hung 500 nil)) "waiting on the first page")
        (let [[b _] (connected! rt log n)]
          (is (nil? (deref hung 1000 nil))
              "a new tab is not a refresh: what the first page owes is still owed")
          (is (= 2 (count (:connections rt))) "both are connected")
          ;; and now the close, which is the half a refresh really consists of
          (.destroyForcibly ^Process a)
          (let [r (deref hung 10000 :blocked)]
            (is (= :error (:status r)))
            (is (str/includes? (:value r) "browser is gone")))
          (is (= ["2"] (values rt 'refresh.core "(js* \"1 + 1\")"))
              "and the page that is left has the REPL")
          (.destroy ^Process b))))))

(h/deftest-when h/node? test-a-page-going-away-ends-the-evaluations-that-never-started-either
  ;; The half a single-thread executor needed a second mechanism for. Replique's
  ;; shutdownNow interrupts the RUNNING task and hands back the ones still queued,
  ;; which it then runs itself with a dynamic var bound so each answers its caller
  ;; instead of waiting - two mechanisms, because a queued Runnable is not a thread
  ;; and cannot be interrupted.
  ;;
  ;; A permit collapses that: an evaluation that has not started is a thread parked
  ;; on acquire, and end-turns! interrupts it. This is the test that says so - the
  ;; second evaluation never reached the page at all, and still answered its caller.
  (let [out (StringWriter.) log (StringBuffer.)]
    (with-open [rt (browser/browser-runtime {:out out})]
      (let [[p _]  (connected! rt log)
            running (future (repl/-evaluate
                             rt "(async function () { return new Promise(function () {}); })()"))
            _       (Thread/sleep 500)          ; let it take the permit
            waiting (future (repl/-evaluate rt "(async function () { return 1; })()"))]
        (is (nil? (deref running 200 nil)) "the first holds the permit")
        (is (nil? (deref waiting 200 nil)) "the second is behind it")
        (.destroyForcibly ^Process p)
        (is (str/includes? (:value (deref running 10000 {})) "browser is gone")
            "the one that was running, completed")
        (is (str/includes? (:value (deref waiting 10000 {})) "browser is gone")
            "the one that never started, interrupted")))))

(h/deftest-when h/node? test-a-page-that-is-killed-ends-its-evaluations-at-once
  ;; WHAT THE SOCKET IS FOR. Over the long-poll this was the expensive case: a page
  ;; killed between being handed a script and answering it had nothing open to
  ;; break, and writing into a dead connection SUCCEEDS - the bytes reach the kernel
  ;; and no error is raised - so the JVM could only find out by not being spoken to
  ;; for twenty seconds. It needed a 5-second liveness ping from the page, a
  ;; silence threshold, and a :bye beacon on pagehide to make the common case
  ;; bearable.
  ;;
  ;; All three are gone. The socket closes when the process dies, the JVM is told,
  ;; and the evaluation ends. The assertion is therefore not "it eventually ends"
  ;; but that it ends in well under the twenty seconds it used to take.
  (let [out (StringWriter.) log (StringBuffer.)]
    (with-open [rt (browser/browser-runtime {:out out})]
      (let [[p _]   (connected! rt log)
            hung    (future (repl/-evaluate
                             rt "(async function () { return new Promise(function () {}); })()"))
            _       (is (nil? (deref hung 500 nil)) "waiting on the page")
            t0      (System/currentTimeMillis)
            _       (.destroyForcibly ^Process p)
            _       (.waitFor ^Process p)
            r       (deref hung 20000 :hung)
            elapsed (- (System/currentTimeMillis) t0)]
        (is (= :error (:status r)))
        (is (str/includes? (:value r) "browser is gone"))
        (is (< elapsed 5000) (str "told rather than timed out, took " elapsed "ms"))
        ;; and the session is over, so the next evaluation says so at once rather
        ;; than discovering it again
        (is (nil? (:session rt)))
        (is (str/includes? (:value (repl/-evaluate rt "1")) "No browser is connected"))))))

(deftest test-an-older-page-is-still-heard-even-though-it-is-not-asked
  ;; A REFRESH USED TO EVICT THE PAGE IT REPLACED - it was told 409 and stepped
  ;; aside, because two runtimes polling one REPL would take alternate turns and
  ;; answer each other's questions. A socket makes that restriction unnecessary:
  ;; scripts go to one connection by name, so an older page cannot take a turn that
  ;; was not offered to it, and there is no reason to hang up on it.
  ;;
  ;; What it may still do is print. Output is not an answer to anything, and a tab
  ;; left open is a tab whose console someone may be watching - so it is forwarded,
  ;; where a result from the same page would be ignored.
  (let [out (StringWriter.)]
    (with-open [rt (browser/browser-runtime {:out out})]
      (let [[^WebSocket a _] (fake-page! rt)
            first-session    (wait-for #(:session rt))
            [^WebSocket b _] (fake-page! rt)]
        (is (some? first-session))
        (is (wait-for #(when-let [n (:session rt)] (when (not= n first-session) n)))
            "the second page took the REPL over")
        (.get (.sendText a "{:type :print :content \"from the old page\\n\"}" true)
              10000 TimeUnit/MILLISECONDS)
        (is (wait-for #(str/includes? (str out) "from the old page"))
            "the page that lost the REPL is still heard")
        (.abort a)
        (.abort b)))))


;; --- one script at a time ---------------------------------------------------

(deftest test-two-evaluations-each-get-their-own-answer
  ;; What serializing is FOR, and it is not fairness. Two evaluations in flight at
  ;; once would both write a script into the socket and both wait for a result, and
  ;; nothing says the answer to the first is taken by the thread that asked for it -
  ;; the REPL would print one form's value under another form's prompt.
  ;;
  ;; The page is spoken by hand here, one turn at a time, which is the shape a real
  ;; page has: runtime_browser.js chains its evaluations on one promise.
  (with-open [rt (browser/browser-runtime {})]
    (let [[^WebSocket ws scripts] (fake-page! rt)]
      (is (some? (wait-for #(:session rt))) "connected")
      (let [a   (future (repl/-evaluate rt "SCRIPT-A"))
            b   (future (repl/-evaluate rt "SCRIPT-B"))
            js1 (took scripts)]
        (is (nil? (.poll scripts 500 TimeUnit/MILLISECONDS))
            "the second script is not sent until the first is answered")
        (answer! ws "{:status :success :value \"1\"}")
        (let [js2 (took scripts)]
          (is (= #{"SCRIPT-A" "SCRIPT-B"} #{js1 js2}) "each got exactly one turn"))
        (answer! ws "{:status :success :value \"2\"}")
        (is (= #{"1" "2"} #{(:value (deref a 10000 :never)) (:value (deref b 10000 :never))})
            "and each got its own answer, not the other's")
        (.abort ws)))))

;; --- a load goes everywhere, a value comes from one -------------------------

(deftest test-a-load-reaches-every-page-but-a-value-comes-from-one
  ;; THE DISTINCTION STEP 4 IS ABOUT (doc/cljs-repl.md 6.2, repl/IJsRuntimes). A
  ;; require is idempotent and answers nil wherever it runs, and what you want from
  ;; it is that every page you have open picks up the new code. An ordinary form has
  ;; a value, and a value needs ONE answer rather than a set of them differing by
  ;; which page's clock or random seed produced it.
  ;;
  ;; Both pages are spoken by hand, because what is under test is which sockets the
  ;; script was written into - and a real page would answer before the question
  ;; could be asked.
  (let [src (h/write-sources! two-files)]
    (try
      (with-open [rt (browser/browser-runtime {})]
        (let [[^WebSocket a as] (fake-page! rt)
              n1                (wait-for #(:session rt))
              [^WebSocket b bs] (fake-page! rt)]
          (is (some? n1))
          (is (wait-for #(= 2 (count (:connections rt)))) "both are connected")
          (let [cenv (env/compile-env {:ns 'cljs.user})
                opts {:out-dir (:dir rt) :source-paths [src]}
                done (future (repl/eval-src cenv rt "(require '[app.core :as app])" opts))
                ja   (took as)
                jb   (took bs)]
            (is (str/includes? ja "$CLJS.require") "a load, not a body")
            (is (= ja jb) "and the same one reached both pages")
            (answer! a "{:status :success :value \"nil\"}")
            (answer! b "{:status :success :value \"nil\"}")
            (is (= ["nil"] (mapv :value (deref done 10000 :never))))
            ;; an ordinary form: the newest page only
            (let [v (future (repl/eval-src cenv rt "(app/use-it)" opts))]
              (is (some? (took bs)) "the page evaluation targets got it")
              (is (nil? (.poll ^LinkedBlockingQueue as 1000 TimeUnit/MILLISECONDS))
                  "and the other was not asked")
              (answer! b "{:status :success :value \"42\"}")
              (is (= ["42"] (mapv :value (deref v 10000 :never))))))
          (.abort a)
          (.abort b)))
      (finally (h/delete-tree! src)))))

(deftest test-a-page-that-will-not-load-does-not-fail-the-require
  ;; The grace the other pages get, and why they get one. The page evaluation
  ;; targets is waited for without a bound - an evaluation may legitimately take
  ;; minutes. The others cannot have that: a backgrounded tab on a sleeping laptop
  ;; is connected, will answer eventually, and must not be able to hold up a
  ;; require. So it is reported rather than waited for, and a tab left open from
  ;; yesterday is not the reason your require says it failed.
  (with-redefs [browser/other-page-ms 500]
    (let [src (h/write-sources! two-files)
          out (StringWriter.)]
      (try
        (with-open [rt (browser/browser-runtime {:out out})]
          (let [[^WebSocket a as] (fake-page! rt)
                _                 (wait-for #(:session rt))
                [^WebSocket b bs] (fake-page! rt)]
            (is (wait-for #(= 2 (count (:connections rt)))))
            (let [cenv (env/compile-env {:ns 'cljs.user})
                  opts {:out-dir (:dir rt) :source-paths [src]}
                  done (future (repl/eval-src cenv rt "(require 'app.core)" opts))]
              (took as)
              (took bs)
              (answer! b "{:status :success :value \"nil\"}")   ; only the target answers
              (is (= ["nil"] (mapv :value (deref done 10000 :never)))
                  "the require succeeded on the strength of the page that answered")
              (is (str/includes? (str out) "another connected page")
                  "and the one that did not was reported rather than ignored"))
            (.abort a)
            (.abort b)))
        (finally (h/delete-tree! src))))))

;; --- choosing which page answers --------------------------------------------

(def ^:private chrome-ua
  "What Chrome actually sends, which is four browsers' worth of history: it claims
  to be Mozilla, KHTML, Safari and Chrome, and Edge and Opera claim to be Chrome on
  top of that. The order browsers are matched in is the whole of the parsing."
  (str "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 "
       "(KHTML, like Gecko) Chrome/140.0.0.0 Safari/537.36"))

(def ^:private firefox-ua
  (str "Mozilla/5.0 (Macintosh; Intel Mac OS X 14.7; rv:143.0) Gecko/20100101 "
       "Firefox/143.0"))

(deftest test-pages-says-who-is-connected-and-who-answers
  ;; (pages) is the one REPL special that is not about namespaces. It exists
  ;; because a socket let more than one page connect at once (doc/cljs-repl.md
  ;; 6.3) and evaluation has to go somewhere: without it the target is whichever
  ;; tab you opened last, and the only way back to an earlier one is to close tabs
  ;; until it is newest again.
  (with-open [rt (browser/browser-runtime {})]
    (let [cenv (env/compile-env {:ns 'cljs.user})
          run  #(first (repl/eval-src cenv rt % {:out-dir (:dir rt)}))]
      (is (= "No page is connected." (:value (run "(pages)")))
          "before anyone connects")
      (let [[^WebSocket a as] (fake-page! rt chrome-ua)
            _                 (wait-for #(:session rt))
            [^WebSocket b bs] (fake-page! rt firefox-ua)]
        (is (wait-for #(= 2 (count (:connections rt)))))
        (is (= "  1  Chrome 140\n* 2  Firefox 143" (:value (run "(pages)")))
            "named by what they said they were, newest targeted")
        ;; move it, and the NEXT evaluation goes elsewhere
        (is (= "* 1  Chrome 140\n  2  Firefox 143" (:value (run "(pages 1)"))))
        (let [v (future (repl/eval-src cenv rt "(js* \"1 + 1\")" {:out-dir (:dir rt)}))]
          (is (some? (took as)) "the page that was chosen got the script")
          (is (nil? (.poll ^LinkedBlockingQueue bs 1000 TimeUnit/MILLISECONDS))
              "and the one that was not, did not")
          (answer! a "{:status :success :value \"2\"}")
          (is (= ["2"] (mapv :value (deref v 10000 :never)))))
        (.abort a)
        (.abort b)))))

(deftest test-choosing-a-page-that-is-not-there-says-so
  (with-open [rt (browser/browser-runtime {})]
    (let [cenv (env/compile-env {:ns 'cljs.user})
          run  #(first (repl/eval-src cenv rt % {:out-dir (:dir rt)}))
          [^WebSocket a _] (fake-page! rt chrome-ua)]
      (is (wait-for #(:session rt)))
      (let [r (run "(pages 9)")]
        (is (= :error (:status r)))
        (is (str/includes? (:value r) "There is no page 9")))
      (let [r (run "(pages :chrome)")]
        (is (= :error (:status r)))
        (is (str/includes? (:value r) "a page is named by a number")))
      (is (= "* 1  Chrome 140" (:value (run "(pages)")))
          "and neither mistake moved anything")
      (.abort a))))

(deftest test-a-page-number-is-never-reused
  ;; The session counter names the page, and it only goes up. If a closed tab's
  ;; number were handed to the next one, (pages 2) would be a way to evaluate in a
  ;; page you did not mean - and you would not find out from the number.
  (with-open [rt (browser/browser-runtime {})]
    (let [cenv (env/compile-env {:ns 'cljs.user})
          run  #(first (repl/eval-src cenv rt % {:out-dir (:dir rt)}))
          [^WebSocket a _] (fake-page! rt chrome-ua)]
      (is (wait-for #(:session rt)))
      (.abort a)
      (is (wait-for #(zero? (count (:connections rt)))))
      (let [[^WebSocket b _] (fake-page! rt firefox-ua)]
        (is (wait-for #(= 1 (count (:connections rt)))))
        (is (= "* 2  Firefox 143" (:value (run "(pages)")))
            "the second page is 2, not 1 again")
        (.abort b)))))

(h/deftest-when h/node? test-a-runtime-with-one-page-says-so
  ;; node is one runtime and cannot be more, so it does not implement IJsRuntimes
  ;; and the question has a short answer rather than an error.
  (let [out (StringWriter.)]
    (with-open [rt (repl/node-runtime {:out out})]
      (is (= "This runtime has one page and it is that one."
             (:value (first (repl/eval-src (env/compile-env {:ns 'cljs.user}) rt
                                           "(pages)" {:out-dir (:dir rt)}))))))))

;; --- not sending what the browser already has -------------------------------

(deftest test-an-unchanged-file-is-revalidated-rather-than-resent
  ;; The output directory is served no-cache, NOT no-store, and the difference is
  ;; the whole of it: no-store forbids the browser to keep the bytes, so every
  ;; refresh re-downloads the program; no-cache lets it keep them and makes it ask
  ;; first. Correctness is untouched - a module is never used without asking - and
  ;; what is saved is the body, which is the part that will matter when cljs.core
  ;; is one of the files.
  (with-open [rt (browser/browser-runtime {})]
    (let [first-time (fetch rt "/runtime.js")]
      (is (= 200 (:status first-time)))
      (is (= "no-cache" (:cache first-time)))
      (is (some? (:etag first-time)) "served with a tag to ask about")
      (let [again (fetch rt "/runtime.js" (:etag first-time))]
        (is (= 304 (:status again)) "the browser already has it")
        (is (str/blank? (:body again)) "and it was not sent again")
        (is (= (:etag first-time) (:etag again))
            "the tag comes back, or the next request would be unconditional")))))

(deftest test-a-recompiled-namespace-is-sent-again
  ;; The other half, and the one that would make a caching bug dangerous rather
  ;; than merely wasteful: when the file HAS changed, the tag must change with it.
  ;; It is derived from modification time and size, which is only a sound proxy
  ;; for content because the driver does not rewrite a file whose bytes did not
  ;; change - see the etag docstring.
  (let [src (h/write-sources! '{cached.core "(ns cached.core) (def x 1)"})]
    (try
      (with-open [rt (browser/browser-runtime {})]
        (let [cenv (env/compile-env {:ns 'cljs.user})
              opts {:out-dir (:dir rt) :source-paths [src]}
              path (str "/" (output/ns->path 'cached.core))]
          (repl/eval-src cenv rt "(require 'cached.core)" opts)
          (let [before (fetch rt path)]
            (is (= 200 (:status before)))
            ;; unchanged: asking is answered with 304
            (repl/eval-src cenv rt "(require 'cached.core)" opts)
            (is (= 304 (:status (fetch rt path (:etag before)))))
            ;; changed: the same question gets the new file
            (h/write-sources! src '{cached.core "(ns cached.core) (def x 987654321)"})
            (repl/eval-src (env/compile-env {:ns 'cljs.user}) rt
                           "(require 'cached.core :reload)" opts)
            (let [after (fetch rt path (:etag before))]
              (is (= 200 (:status after)) "the stale tag was not honoured")
              (is (not= (:etag before) (:etag after)))
              (is (str/includes? (:body after) "987654321"))))))
      (finally (h/delete-tree! src)))))


;; --- who may open the socket ------------------------------------------------

(deftest test-the-socket-is-not-open-to-anyone-who-finds-the-port
  ;; A websocket is not subject to the same-origin policy: any page anywhere may
  ;; open one to this machine, with an Origin header it writes itself and no
  ;; preflight to refuse. A REPL that accepted such a connection would evaluate the
  ;; developer's forms in a stranger's page and hand back what they printed.
  ;;
  ;; So the connect info is served out of the output directory - reachable by
  ;; anything this server served, and by nothing else - and the token in it is
  ;; checked before the upgrade. websocket-test covers the check itself; this is
  ;; the wiring, that browser-runtime actually turns it on.
  (with-open [rt (browser/browser-runtime {})]
    (let [url (ws-url rt)]
      (is (str/includes? url "token="))
      (is (thrown? ExecutionException
                   (-> (HttpClient/newHttpClient)
                       (.newWebSocketBuilder)
                       (.buildAsync (URI/create (str/replace url #"token=.*" "token=guess"))
                                    (reify WebSocket$Listener))
                       (.get 10000 TimeUnit/MILLISECONDS)))
          "the port alone is not enough")
      (is (nil? (:session rt)) "and nothing connected"))))

(deftest test-the-connect-info-is-never-cached
  ;; Assets are revalidated; this one file is not cached at all. It carries the
  ;; socket's port and token, both new on every start, and a page that answered
  ;; from cache would dial a port nobody is listening on.
  (with-open [rt (browser/browser-runtime {})]
    (let [r (fetch rt "/cljs-repl.json")]
      (is (= 200 (:status r)))
      (is (= "no-store" (:cache r)))
      (is (nil? (:etag r)) "nothing to revalidate against")
      (is (str/includes? (:body r) "\"ws\": \"ws://")))))



;; --- errors no turn owns ----------------------------------------------------

(deftest test-an-error-nobody-asked-about-reaches-the-output
  ;; An exception out of an event handler, or a promise nobody caught: there is no
  ;; turn to complete, so the only place for it is where the page's console goes.
  ;;
  ;; Spoken by hand, because what is under test is this end - that a third kind of
  ;; message is understood at all, and that its stack is read back as
  ;; ClojureScript on the way. That the CLIENT sends one is the next test.
  (let [out (StringWriter.)]
    (with-open [rt (browser/browser-runtime {:out out})]
      (let [[^WebSocket ws _] (fake-page! rt)]
        (is (some? (wait-for #(:session rt))) "connected")
        (.get (.sendText ws (str "{:type :uncaught :content "
                                 (pr-str (str "{:status :error :value \"Error: out of nowhere\""
                                              " :stacktrace \"Error: out of nowhere\\n"
                                              "    at whatever (ns/nope/core.js:3:1)\"}"))
                                 "}")
                         true)
              10000 TimeUnit/MILLISECONDS)
        (is (wait-for #(str/includes? (str out) ";; uncaught error: Error: out of nowhere"))
            (str out))
        (is (str/includes? (str out) "at whatever") "and the frames came with it")
        (.abort ws)))))

(h/deftest-when h/node? test-the-client-reports-an-error-no-turn-owns
  ;; The other end of the same channel, and the half of it a real browser reaches
  ;; through addEventListener("error"/"unhandledrejection"). Node has no such
  ;; events - it has process.on - so the stand-in page wires its own to the very
  ;; same reportUncaught the events are wired to, which leaves untested only the
  ;; two lines of registration that could not run here at all.
  (let [out (StringWriter.)
        log (StringBuffer.)]
    (with-open [rt (browser/browser-runtime {:out out})]
      (with-core! rt)
      (let [p (start-page! rt log "process.on(\"unhandledRejection\", reportUncaught);\n")]
        (try
          (is (some? (wait-for #(:session rt))) "connected")
          ;; dropped rather than returned: a promise the turn returns is awaited by
          ;; the turn, and so is caught after all
          (values rt 'browser-stray.core
                  "(js* \"(function(){ Promise.reject(new Error('from the page')); return 1; })()\")")
          (is (wait-for #(str/includes? (str out) ";; uncaught error: Error: from the page"))
              (str out))
          (finally (.destroy p)))))))


;; --- a caller that gives up -------------------------------------------------

(deftest test-a-bounded-evaluation-stops-waiting-for-a-page-that-does-not-answer
  ;; The page took the script and said nothing. -evaluate would wait for as long as
  ;; that takes, which is right for a form at a prompt and wrong for a completion.
  (with-open [rt (browser/browser-runtime {})]
    (let [[^WebSocket ws scripts] (fake-page! rt)]
      (is (some? (wait-for #(:session rt))) "connected")
      (let [r (repl/evaluate-within rt "SCRIPT-UNANSWERED" 400)]
        (is (= "SCRIPT-UNANSWERED" (took scripts)) "it was sent")
        (is (= :error (:status r)))
        (is (str/includes? (:value r) "did not answer within 400ms") (:value r)))
      (.abort ws))))

(deftest test-a-bounded-evaluation-that-never-reached-the-page-says-a-different-thing
  ;; Which is the distinction the whole deadline is for: nothing was sent, so there
  ;; is nothing running that this asked for, and whoever asked can say so without
  ;; hedging. The permit is held by an ordinary evaluation that is still waiting -
  ;; a form at a prompt, in life.
  (with-open [rt (browser/browser-runtime {})]
    (let [[^WebSocket ws scripts] (fake-page! rt)]
      (is (some? (wait-for #(:session rt))) "connected")
      (let [held (future (repl/-evaluate rt "SCRIPT-AT-THE-PROMPT"))]
        (is (= "SCRIPT-AT-THE-PROMPT" (took scripts)))
        (let [r (repl/evaluate-within rt "SCRIPT-FOR-TOOLING" 300)]
          (is (= :error (:status r)))
          (is (str/includes? (:value r) "busy for the whole 300ms") (:value r))
          (is (nil? (.poll ^LinkedBlockingQueue scripts 200 TimeUnit/MILLISECONDS))
              "and it never reached the page"))
        (answer! ws "{:status :success :value \"1\"}")
        (is (= "1" (:value @held))))
      (.abort ws))))

(deftest test-giving-up-lets-the-next-evaluation-through
  ;; What makes a deadline more than a timer: the caller's place in the queue goes
  ;; with the wait. A bounded call that gave up must not leave the permit held by a
  ;; thread still listening for an answer nobody wants any more.
  (with-open [rt (browser/browser-runtime {})]
    (let [[^WebSocket ws scripts] (fake-page! rt)]
      (is (some? (wait-for #(:session rt))) "connected")
      (is (= :error (:status (repl/evaluate-within rt "SCRIPT-ABANDONED" 300))))
      (is (= "SCRIPT-ABANDONED" (took scripts)))
      (let [next (future (repl/-evaluate rt "SCRIPT-AFTER"))]
        (is (= "SCRIPT-AFTER" (took scripts)) "the next one got in")
        (answer! ws "{:status :success :value \"7\"}")
        (is (= "7" (:value @next))))
      ;; AND THE ABANDONED ANSWER GOES NOWHERE, arriving late to a turn that was
      ;; forgotten on the way out.
      (.abort ws))))

(deftest test-a-bounded-evaluation-with-no-page-answers-at-once
  ;; Not a wait at all, bounded or otherwise: a REPL started before the browser is
  ;; the normal way round, and the useful answer is the URL.
  (with-open [rt (browser/browser-runtime {})]
    (let [r (repl/evaluate-within rt "ANYTHING" 30000)]
      (is (= :error (:status r)))
      (is (str/includes? (:value r) "No browser is connected") (:value r)))))


;; --- starting on a namespace ------------------------------------------------

(deftest test-a-main-given-before-the-page-is-open-says-what-to-open
  ;; browser-repl passes :main through, and the browser is the transport where
  ;; that can fail for a reason that is not the program's: there is nowhere to
  ;; ship it yet. The answer is the one any form gets there, and it is the useful
  ;; one - it names the url. The namespace COMPILED, which is the half a repl
  ;; start is really for, so requiring it once the page is there costs nothing.
  (let [src (h/write-sources! '{page.main "(ns page.main) (def x 1)"})
        out (StringWriter.)]
    (try
      (browser/browser-repl {:in (java.io.StringReader. "") :out out
                             :main 'page.main :source-paths [src]})
      (is (str/includes? (str out) "Waiting for a browser on"))
      (is (str/includes? (str out) "No browser is connected") (str out))
      (is (str/includes? (str out) "cljs.user=> ") (str out))
      (finally (h/delete-tree! src)))))
