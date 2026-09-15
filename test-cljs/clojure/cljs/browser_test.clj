;   Copyright (c) Rich Hickey. All rights reserved.
;   The use and distribution terms for this software are covered by the
;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;   which can be found in the file epl-v10.html at the root of this distribution.
;   By using this software in any fashion, you are agreeing to be bound by
;   the terms of this license.
;   You must not remove this notice, or any other, from this software.

(ns ^{:doc "The browser runtime: the asset server, the long-poll and its failure
  semantics.

  THE PAGE IS A NODE PROCESS HERE, and the substitution is exact in the half these
  tests are about and inexact in the half they are not. runtime_browser.js is
  loaded and run unmodified - it needs fetch and eval and nothing else a browser
  has that node lacks - so the wire, the session numbering and the print channel
  are the real ones. What node does differently is where $CLJS.require finds a
  module: relative to runtime.js's own URL, which is a file under node and an HTTP
  origin in a browser. That path is tested from the other end instead, by fetching
  the same files over HTTP and comparing them to what the driver wrote.

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
           [java.net HttpURLConnection URL]))

(use-fixtures :each h/cursor)

;; --- a page, standing in ----------------------------------------------------

(defn- start-page!
  "A node process running the browser client against `rt`, and a thread copying
  what it says to `log`.

  It is written into the output directory rather than run from a string so that it
  imports the client by the same relative specifier a served page uses."
  [rt ^StringBuffer log]
  (let [^File dir (:dir rt)]
    (spit (File. dir "page.js")
          "import { connect } from \"./runtime_browser.js\";\nconnect(process.argv[2]);\n")
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
      p)))

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

(h/deftest-when h/node? test-the-oracle-over-the-long-poll
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

(h/deftest-when h/node? test-a-refresh-ends-the-evaluation-the-old-page-never-answered
  ;; The reason session numbering is the valuable half of Replique's transport
  ;; (doc/cljs-repl.md 6). A refresh is not a disconnection a socket would notice -
  ;; the old page just stops polling - so without a number the JVM would wait for
  ;; an answer that has no one left to produce it. With one, the new page's :ready
  ;; drains the eval executor and every blocked caller is told.
  (let [out (StringWriter.) log (StringBuffer.)]
    (with-open [rt (browser/browser-runtime {:out out})]
      (with-core! rt)
      (let [[a n] (connected! rt log)
            ;; a script the page will never finish
            hung (future (repl/-evaluate
                          rt "(async function () { return new Promise(function () {}); })()"))]
        (is (nil? (deref hung 500 nil)) "still waiting on the page")
        (let [[b _] (connected! rt log n)]
          (is (= {:status :error :value "Connection broken"} (deref hung 10000 :blocked)))
          ;; and the new page has the REPL
          (is (= ["2"] (values rt 'refresh.core "(js* \"1 + 1\")")))
          (.destroy ^Process a)
          (.destroy ^Process b))))))

(h/deftest-when h/node? test-the-page-that-lost-the-session-steps-aside
  ;; Two runtimes polling one REPL would take alternate turns and answer each
  ;; other's questions, so the one whose session expired stops - and says how to
  ;; come back, because it is a page someone may still be looking at.
  (let [out (StringWriter.) log (StringBuffer.)]
    (with-open [rt (browser/browser-runtime {:out out})]
      (with-core! rt)
      (let [[a n] (connected! rt log)
            [b _] (connected! rt log n)]
        (is (wait-for #(str/includes? (str log) "session expired")))
        (.destroy ^Process a)
        (.destroy ^Process b)))))

;; --- what a page that just goes away does -----------------------------------

(defn- POST
  "[status body] for a POST of the EDN `msg` on `rt` - a runtime message, sent by
  hand rather than by a page."
  [rt ^String msg]
  (let [^HttpURLConnection c (doto ^HttpURLConnection (.openConnection (URL. (:url rt)))
                              (.setRequestMethod "POST")
                              (.setDoOutput true))]
    (with-open [o (.getOutputStream c)]
      (.write o (.getBytes msg "UTF-8")))
    [(.getResponseCode c) (try (slurp (.getInputStream c)) (catch Exception _ nil))]))

(h/deftest-when h/node? test-a-page-that-stops-answering-does-not-hang-the-repl
  ;; THE ONE THING LONG-POLLING COSTS (doc/cljs-repl.md 6.1). A socket that closes
  ;; reports itself; a long-poll that has already been answered has nothing open to
  ;; break, and writing a script into a dead connection SUCCEEDS - the bytes reach
  ;; the kernel and no error is ever raised. So a page killed between being handed a
  ;; script and answering it used to leave the REPL waiting forever, which is the
  ;; failure this transport must not have.
  ;;
  ;; The two waits are shortened here rather than waited out: what is under test is
  ;; that silence ends the wait, not how long the silence is. With the real numbers
  ;; a page pings every 5s while it evaluates and 20s of nothing means it is gone.
  (with-redefs [browser/silence-ms 1000
                browser/offer-ms   1000]
    (let [out (StringWriter.) log (StringBuffer.)]
      (with-open [rt (browser/browser-runtime {:out out})]
        (let [[p _] (connected! rt log)]
          (is (= "1" (:value (repl/-evaluate rt "(async function () { return 1; })()"))))
          ;; killed outright: no unload handler runs, nothing is sent, and the held
          ;; poll's socket dies without the JVM being able to notice
          (.destroyForcibly ^Process p)
          (.waitFor ^Process p)
          ;; the script is handed to the dead poll and the answer never comes
          (let [r (deref (future (repl/-evaluate rt "(async function () { return 1; })()"))
                         20000 :hung)]
            (is (= :error (:status r)))
            (is (str/includes? (:value r) "stopped answering")))
          ;; and the session is over, so the next one says so at once rather than
          ;; discovering it again
          (let [r (deref (future (repl/-evaluate rt "(async function () { return 1; })()"))
                         20000 :hung)]
            (is (= :error (:status r)))
            (is (str/includes? (:value r) "No browser is connected"))))))))

(h/deftest-when h/node? test-a-page-that-says-goodbye-is-believed-at-once
  ;; Silence finds the same thing out, but closing a tab is the common case and
  ;; twenty seconds of a REPL answering nothing is a long time to spend
  ;; rediscovering something the browser was willing to say. A real page sends this
  ;; from pagehide with sendBeacon, the one request a browser still sends while it
  ;; tears the page down.
  (let [out (StringWriter.) log (StringBuffer.)]
    (with-open [rt (browser/browser-runtime {:out out})]
      (let [[p n] (connected! rt log)]
        (is (= 200 (first (POST rt (str "{:type :bye :session " n "}")))))
        (is (nil? (:session rt)) "the session is over")
        (let [r (repl/-evaluate rt "(async function () { return 1; })()")]
          (is (str/includes? (:value r) "No browser is connected")))
        (.destroyForcibly ^Process p)))))

(h/deftest-when h/node? test-a-goodbye-from-the-page-a-refresh-replaced-is-ignored
  ;; A refresh fires pagehide too, and its beacon can arrive AFTER the new page's
  ;; :ready. It carries the session number the :ready already replaced, which is
  ;; the whole reason this checks the number before acting on it - a late goodbye
  ;; from the previous page must not end the session that succeeded it.
  (let [out (StringWriter.) log (StringBuffer.)]
    (with-open [rt (browser/browser-runtime {:out out})]
      (with-core! rt)
      (let [[a n1] (connected! rt log)
            [b n2] (connected! rt log n1)]
        (POST rt (str "{:type :bye :session " n1 "}"))
        (is (= n2 (:session rt)) "the new session stands")
        (is (= ["2"] (values rt 'late-bye.core "(js* \"1 + 1\")")))
        (.destroyForcibly ^Process a)
        (.destroyForcibly ^Process b)))))

;; --- being told, rather than looking ----------------------------------------

(deftest test-a-held-poll-is-released-the-moment-its-session-ends
  ;; A held poll used to wake every 250ms to re-read the session number - eighty
  ;; times per idle heartbeat, per page, to notice something that happens once.
  ;; Now whatever ends a session hands the queue a sentinel and the poll is simply
  ;; told, so this test is also the proof that it is: nothing else wakes a held
  ;; poll early any more, so a 409 arriving in well under the 20s heartbeat can
  ;; only have come from the sentinel.
  ;;
  ;; No page here at all - the protocol is spoken by hand, which is what makes the
  ;; timing readable.
  (with-open [rt (browser/browser-runtime {})]
    (let [n    (:session (do (POST rt "{:type :ready}") rt))
          held (future (POST rt (str "{:type :poll :session " n "}")))]
      (is (nil? (deref held 1000 nil)) "the poll is held, not answered")
      (let [t0 (System/currentTimeMillis)
            _  (POST rt "{:type :ready}")         ; a refresh: session n+1
            r  (deref held 10000 :never-released)
            ms (- (System/currentTimeMillis) t0)]
        (is (= 409 (first r)) "the held poll was told its session is over")
        (is (< ms 2000) (str "released promptly, took " ms "ms")))
      ;; and the sentinel did not outlive the session that sent it: a poll on the
      ;; NEW session is held like any other rather than being handed a stale one.
      ;; SynchronousQueue makes that true by construction - an offer with no
      ;; timeout stores nothing - and this is the observation of it.
      (let [n2   (:session rt)
            next (future (POST rt (str "{:type :poll :session " n2 "}")))]
        (is (not= n n2) "the refresh moved the session on")
        (is (nil? (deref next 1500 nil)) "the new session's poll is held")))))

(h/deftest-when h/node? test-a-refresh-ends-the-evaluations-that-never-started-either
  ;; The half a single-thread executor needed a second mechanism for. Replique's
  ;; shutdownNow interrupts the RUNNING task and hands back the ones still queued,
  ;; which it then runs itself with a dynamic var bound so each answers its caller
  ;; instead of waiting - two mechanisms, because a queued Runnable is not a thread
  ;; and cannot be interrupted.
  ;;
  ;; A permit collapses that: an evaluation that has not started is a thread parked
  ;; on acquire, and it ends because it re-checks the session on the way in as the
  ;; permit comes free. This is the test that says so - the second evaluation never
  ;; reached the page at all, and still answered its caller.
  ;;
  ;; It does NOT isolate the interrupt in stop-evaluations!, and cannot: the two
  ;; paths overlap by design, and the re-check alone is enough here. See that
  ;; docstring for which of them is the guarantee.
  (let [out (StringWriter.) log (StringBuffer.)]
    (with-open [rt (browser/browser-runtime {:out out})]
      (let [[a n] (connected! rt log)
            running (future (repl/-evaluate
                             rt "(async function () { return new Promise(function () {}); })()"))
            _       (Thread/sleep 500)          ; let it take the permit
            waiting (future (repl/-evaluate rt "(async function () { return 1; })()"))]
        (is (nil? (deref running 200 nil)) "the first holds the permit")
        (is (nil? (deref waiting 200 nil)) "the second is behind it")
        (let [[b _] (connected! rt log n)]
          (is (= connection-broken (deref running 10000 :blocked)) "the one that was running")
          (is (= connection-broken (deref waiting 10000 :blocked)) "the one that never started")
          (.destroy ^Process a)
          (.destroy ^Process b))))))

(defn- result-msg
  "A :result message carrying `edn` - itself the EDN text of a result map, which is
  how a page sends one: JSON.stringify of what runtime.js printed."
  [n edn]
  (str "{:type :result :session " n " :content " (pr-str edn) "}"))

(deftest test-two-evaluations-each-get-their-own-answer
  ;; What serializing is FOR, and it is not fairness. Two evaluations in flight at
  ;; once would both hand a script to the page and both wait on the result queue,
  ;; and nothing says the answer to the first is taken by the thread that asked for
  ;; it - the REPL would print one form's value under another form's prompt.
  ;;
  ;; The page is spoken by hand here, one turn at a time, which is the shape a real
  ;; page has: it never has two requests in flight.
  (with-open [rt (browser/browser-runtime {})]
    (POST rt "{:type :ready}")
    (let [n  (:session rt)
          a  (future (repl/-evaluate rt "SCRIPT-A"))
          b  (future (repl/-evaluate rt "SCRIPT-B"))
          ;; one script at a time: the second is not handed out until the first has
          ;; been answered, which is the permit doing its job
          [_ js1] (POST rt (str "{:type :poll :session " n "}"))
          [_ js2] (POST rt (result-msg n "{:status :success :value \"1\"}"))]
      (is (= #{"SCRIPT-A" "SCRIPT-B"} #{js1 js2}) "each got exactly one turn")
      ;; nothing waits on the answer to the last one
      (future (POST rt (result-msg n "{:status :success :value \"2\"}")))
      (is (= #{"1" "2"} #{(:value (deref a 5000 :never)) (:value (deref b 5000 :never))})
          "and each got its own answer, not the other's"))))

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

(deftest test-the-transport-is-never-cached
  ;; Assets are revalidated; the wire is not cached at all. A poll response held in
  ;; a cache would be a script handed out twice, which is a different kind of wrong
  ;; from a stale file.
  (with-open [rt (browser/browser-runtime {})]
    (let [^HttpURLConnection c (.openConnection (URL. (:url rt)))]
      (.setUseCaches c false)
      (.setRequestMethod c "POST")
      (.setDoOutput c true)
      (with-open [o (.getOutputStream c)]
        (.write o (.getBytes "{:type :ready}" "UTF-8")))
      (is (= 200 (.getResponseCode c)))
      (is (= "no-store" (.getHeaderField c "Cache-Control")))
      (is (nil? (.getHeaderField c "ETag"))))))
