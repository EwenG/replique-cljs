;   Copyright (c) Rich Hickey. All rights reserved.
;   The use and distribution terms for this software are covered by the
;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;   which can be found in the file epl-v10.html at the root of this distribution.
;   By using this software in any fashion, you are agreeing to be bound by
;   the terms of this license.
;   You must not remove this notice, or any other, from this software.

(ns ^{:doc "The compilation driver, and with it M3's oracle: a multi-file program
  compiled to disk and run by node as modules, with no REPL and no socket
  anywhere.

  This is the only test of the COLD path - a <script type=\"module\"> entry point
  whose static imports pull the graph - so it is what says the output layout, the
  relative specifiers, the module prologue and $ns across files all agree."}
  clojure.cljs.driver-test
  (:require [clojure.cljs.driver :as driver]
            [clojure.cljs.env :as env]
            [clojure.cljs.output :as output]
            [clojure.cljs.reader :as reader]
            [clojure.cljs.test-harness :as h]
            [clojure.java.io :as io]
            [clojure.java.shell :as sh]
            [clojure.string :as str]
            [clojure.test :refer [are deftest is testing use-fixtures]])
  (:import [java.io File]))

(use-fixtures :each h/cursor)

(defmacro twice
  "A macro reached through :require-macros, from a real JVM namespace on the
  classpath - which is how the driver resolves one, and why a .clj macro file has
  to be on the classpath rather than merely on the source path."
  [x]
  (list 'js* "(~{} + ~{})" x x))

;; --- a program on disk ------------------------------------------------------

(def ^:private temp-dir h/temp-dir)
(def ^:private delete-tree! h/delete-tree!)
(defn- write-sources! [dir sources] (h/write-sources! dir sources))

(defn- node [^File f]
  (let [{:keys [out err exit]} (sh/sh "node" (.getPath f))]
    (if (zero? exit) (str/trim out) (str "THREW: " (str/trim err)))))

(def ^:private program
  '{deep.util   "(ns deep.util)
                 (def double (fn* ([x] (js* \"~{} * 2\" x))))"

    my-lib.core "(ns my-lib.core (:require [deep.util :as u]))
                 (def helper (fn* ([x] (u/double x))))"

    app.core    "(ns app.core
                   (:require [my-lib.core :as lib :refer [helper]])
                   (:require-macros [clojure.cljs.driver-test :refer [twice]]))
                 (def answer (fn* ([] (twice (lib/helper 10)))))
                 (js* \"console.log(~{})\" (answer))
                 (js* \"console.log(~{})\" (helper 3))"})

;; --- the paths --------------------------------------------------------------

(deftest test-a-source-path-is-munged-where-an-output-path-is-not
  (are [ns-sym src out] (and (= src (driver/ns->source-path ns-sym ".cljs"))
                             (= out (output/ns->path ns-sym)))
    'app.core    "app/core.cljs"     "ns/app/core.js"
    ;; the two rules part company here, and each says why in its own docstring:
    ;; a source file is named by a convention we inherited, an output file by one
    ;; we chose
    'my-lib.core "my_lib/core.cljs"  "ns/my-lib/core.js"
    'a.b.c       "a/b/c.cljs"        "ns/a/b/c.js"))

(deftest test-the-default-source-path-is-the-classpath-directories
  ;; a jar entry is skipped, so what comes back is somewhere a file can be edited
  (let [paths (driver/default-source-paths)]
    (is (seq paths))
    (is (every? #(.isDirectory ^File %) paths))))

(deftest test-a-cljs-file-beats-a-cljc-of-the-same-name
  (let [dir (temp-dir)]
    (try
      (spit (doto (io/file dir "x/y.cljc") (-> .getParentFile .mkdirs)) "")
      (is (str/ends-with? (str (driver/find-source [dir] 'x.y)) "x/y.cljc"))
      (spit (io/file dir "x/y.cljs") "")
      (is (str/ends-with? (str (driver/find-source [dir] 'x.y)) "x/y.cljs"))
      (is (nil? (driver/find-source [dir] 'no.such)))
      (finally (delete-tree! dir)))))

;; --- M3's oracle ------------------------------------------------------------

(h/deftest-when h/node? test-a-multi-file-program-compiles-and-runs
  (let [src (write-sources! (temp-dir) program)
        out (temp-dir)]
    (try
      (let [cenv   (env/compile-env {:ns 'cljs.user})
            result (driver/compile-namespace! cenv 'app.core
                                              {:out-dir out :source-paths [src]})]
        ;; depth first, post-order: a namespace is compiled after everything it
        ;; requires, which is the order the module system will evaluate it in - and
        ;; cljs.core comes first of all, required by every one of them whether or
        ;; not its ns form says so (§5.12)
        (is (= '[cljs.core deep.util my-lib.core app.core] (:compiled result)))
        ;; two files per namespace: the module and the map beside it (§5.43)
        (is (= 8 (count (:written result))))

        ;; the layout, on disk
        (is (.isFile (io/file out "runtime.js")))
        (is (.isFile (io/file out "package.json")))
        (is (.isFile (io/file out "ns/app/core.js")))
        (is (.isFile (io/file out "ns/app/core.js.map")))
        (is (.isFile (io/file out "ns/my-lib/core.js")))
        (is (.isFile (io/file out "ns/my-lib/core.js.map")))

        ;; a module opens with its imports: the prelude by a relative specifier
        ;; that counts the directories it sits in, then one per required namespace
        (let [text (slurp (io/file out "ns/app/core.js"))]
          (is (str/includes? text "from \"../../runtime.js\""))
          (is (str/includes? text "import \"../my-lib/core.js\""))
          (is (str/includes? text "const my_lib$core$ns = $ns(\"my-lib.core\")"))
          ;; a script's await $CLJS.require has no place in a module
          (is (not (str/includes? text "$CLJS.require"))))

        ;; and it runs: node given the entry module pulls the graph through the
        ;; static imports, with nothing computing an order at load time
        (is (= "40\n6" (node (io/file out "ns/app/core.js")))))
      (finally (delete-tree! src) (delete-tree! out)))))

(h/deftest-when h/node? test-a-second-compile-writes-nothing
  ;; A FRESH ENVIRONMENT EVERY TIME, which is what makes this a test of the WRITE
  ;; rather than of the skip: an environment that had already compiled these would
  ;; compile none of them again (test-what-is-already-compiled-is-not-compiled-
  ;; again), and then nothing being rewritten would say nothing at all. Here every
  ;; namespace really is re-analysed and re-emitted, and the module still keeps its
  ;; mtime - which is what editors and watchers care about.
  (let [src (write-sources! (temp-dir) program)
        out (temp-dir)]
    (try
      (let [compile #(driver/compile-namespace! (env/compile-env {:ns 'cljs.user})
                                                'app.core
                                                {:out-dir out :source-paths [src]})]
        (is (= 8 (count (:written (compile)))))
        (is (= '[cljs.core deep.util my-lib.core app.core] (:compiled (compile))))
        ;; NOTHING BUT CLJS.CORE, which is rewritten every time - and that is the
        ;; one exception the driver's docstring names rather than a hole in this
        ;; test. core.cljs uses macros that call gensym, and a gensym mints a new
        ;; name on every expansion, so the file genuinely compiles to different text
        ;; each run (G__2997 one time, G__3984 the next). Pinned here so that making
        ;; gensym deterministic per compilation has to come through this assertion.
        ;;
        ;; ITS MAP IS NOT REWRITTEN, and that is the source map falling out right
        ;; rather than a coincidence: a gensym changes the NAME a line holds and not
        ;; the line it was written on, so the positions are the same positions and
        ;; the map is byte-identical (§5.43).
        (is (= ["ns/cljs/core.js"]
               (mapv #(str/join "/" (take-last 3 (str/split (str %) #"/")))
                     (:written (compile)))))
        ;; edited, and only that file is rewritten - beside cljs.core, and with the
        ;; map of the file whose lines moved
        (spit (io/file src "deep/util.cljs")
              "(ns deep.util) (def double (fn* ([x] (js* \"~{} * 3\" x))))")
        (is (= 3 (count (:written (compile)))))
        (is (= "60\n9" (node (io/file out "ns/app/core.js")))))
      (finally (delete-tree! src) (delete-tree! out)))))

;; --- what is already compiled ------------------------------------------------
;;
;; The environment is what the driver asks about a dependency, and it lives as long
;; as the JVM. These four say what that means at each end: nothing is done twice,
;; a file named is still always compiled, the two flags are how a caller says
;; otherwise, and the output directory is asked as well as the environment.

(deftest test-what-is-already-compiled-is-not-compiled-again
  (let [src  (write-sources! (temp-dir) program)
        out  (temp-dir)
        cenv (env/compile-env {:ns 'cljs.user})
        opts {:out-dir out :source-paths [src]}]
    (try
      (is (= '[cljs.core deep.util my-lib.core app.core]
             (:compiled (driver/compile-namespace! cenv 'app.core opts))))
      ;; THE SECOND ASK IS THE WHOLE POINT. All four are in the environment, with
      ;; their vars, their requires and their aliases, so there is no question left
      ;; for a compile to answer - and a REPL asks this on every form that mentions
      ;; a namespace, which is why doing nothing has to be free rather than fast.
      (let [again (driver/compile-namespace! cenv 'app.core opts)]
        (is (= [] (:compiled again)))
        (is (= [] (:written again)))
        ;; and no bodies, which is what plain require ships nothing of: it ships a
        ;; question to the runtime instead (repl/require-script)
        (is (= [] (:scripts again))))
      ;; A NAMESPACE THE ENVIRONMENT HAS NOT GOT still compiles, and only it: the
      ;; skip is per namespace and not a switch that turns the driver off.
      (spit (io/file src "app/extra.cljs")
            "(ns app.extra (:require [my-lib.core :as lib]))\n(def n (fn* ([] (lib/helper 1))))\n")
      (is (= '[app.extra] (:compiled (driver/compile-namespace! cenv 'app.extra opts))))
      (finally (delete-tree! src) (delete-tree! out)))))

(h/deftest-when h/node? test-load-file-compiles-the-file-and-nothing-under-it
  ;; what a REPL user types, and the reason any of this was noticed: loading one
  ;; source of a program with three hundred namespaces in it used to recompile all
  ;; three hundred, because the run began by forgetting what the environment knew.
  (let [src  (write-sources! (temp-dir) program)
        out  (temp-dir)
        cenv (env/compile-env {:ns 'cljs.user})
        opts {:out-dir out :source-paths [src]}]
    (try
      (driver/compile-namespace! cenv 'app.core opts)
      (spit (io/file src "app/core.cljs")
            (str "(ns app.core (:require [my-lib.core :as lib :refer [helper]]))\n"
                 "(js* \"console.log(~{})\" (helper 5))\n"))
      (let [r (driver/compile-file! cenv (str (io/file src "app/core.cljs")) opts)]
        ;; THE FILE, AND NOT ITS GRAPH. No flag said so: load-file goes straight to
        ;; compile-one! because you named this file, while its requires are
        ;; ordinary requires and the environment has them.
        (is (= '[app.core] (:compiled r)))
        ;; and the edit took, which is the half that would make a skip here a bug
        (is (= "10" (node (io/file out "ns/app/core.js")))))
      (finally (delete-tree! src) (delete-tree! out)))))

(deftest test-reload-names-one-namespace-and-reload-all-names-the-graph
  (let [src  (write-sources! (temp-dir) program)
        out  (temp-dir)
        cenv (env/compile-env {:ns 'cljs.user})
        base {:out-dir out :source-paths [src]}
        compile #(driver/compile-namespace! cenv 'app.core (merge base %))]
    (try
      (is (= '[cljs.core deep.util my-lib.core app.core] (:compiled (compile {}))))
      ;; :reload is the namespace the caller NAMED and nothing under it, which is
      ;; what the flag means in Clojure and what it has to mean here for
      ;; (require 'app.core :reload) to ship app.core's body and no other
      (is (= '[app.core] (:compiled (compile {:reload true}))))
      ;; :reload-all is the graph, and it is the only way to pick up a dependency
      ;; edited outside this process
      (is (= '[cljs.core deep.util my-lib.core app.core]
             (:compiled (compile {:reload-all true}))))
      (finally (delete-tree! src) (delete-tree! out)))))

(deftest test-the-output-directory-is-asked-as-well-as-the-environment
  ;; TWO HALVES ON TWO CLOCKS. The environment holds the analysis and lives as long
  ;; as the JVM; the directory holds the module the runtime imports and is made
  ;; fresh every time a runtime starts. A skip that asked only the first would
  ;; answer a new directory with an empty one.
  (let [src  (write-sources! (temp-dir) program)
        out  (temp-dir)
        out2 (temp-dir)
        cenv (env/compile-env {:ns 'cljs.user})]
    (try
      (driver/compile-namespace! cenv 'app.core {:out-dir out :source-paths [src]})
      ;; one module deleted, and it is compiled again - the environment still holds
      ;; it and the directory no longer does
      (is (.delete (io/file out "ns/app/core.js")))
      (is (= '[app.core]
             (:compiled (driver/compile-namespace! cenv 'app.core
                                                   {:out-dir out :source-paths [src]}))))
      ;; and a directory that has none of it: everything again, into the new one
      (is (= '[cljs.core deep.util my-lib.core app.core]
             (:compiled (driver/compile-namespace! cenv 'app.core
                                                   {:out-dir out2 :source-paths [src]}))))
      (is (.isFile (io/file out2 "ns/app/core.js")))
      (finally (delete-tree! src) (delete-tree! out) (delete-tree! out2)))))

(h/deftest-when h/node? test-a-clojure-name-with-no-file-of-its-own-means-the-cljs-one
  ;; doc/cljs-compiler.md §5.20. Three of ClojureScript's own test namespaces open
  ;; with (:require [clojure.test :refer [deftest is]]) and there is no
  ;; clojure/test.cljs anywhere, here or upstream.
  ;;
  ;; End to end rather than at the ns form, because the rule is decided in two
  ;; places that must agree: the driver knows there is no file (ensure!) and the
  ;; analyzer knows there is no namespace (aliased-clj-ns). Either half alone
  ;; compiles something that does not run.
  (let [src (write-sources!
             (temp-dir)
             '{cljs.only    "(ns cljs.only) (def n 41)"
               clojure.both "(ns clojure.both) (def n 1)"
               cljs.both    "(ns cljs.both) (def n 2)"
               app.core     "(ns app.core
                               (:require [clojure.only :as o :refer [n]]
                                         [clojure.both :as b]))
                             (js* \"console.log(~{})\"
                                  (+ n o/n clojure.only/n b/n))"})
        out (temp-dir)]
    (try
      (let [result (driver/compile-namespace! (env/compile-env {:ns 'cljs.user})
                                              'app.core
                                              {:out-dir out :source-paths [src]})]
        ;; cljs.only was compiled and clojure.only was not, because there is
        ;; nothing to compile under that name
        (is (contains? (set (:compiled result)) 'cljs.only))
        ;; the module imports the TARGET. Nothing is emitted under the name the
        ;; require was written with - an alias is a Clojure-side name only.
        (let [text (slurp (io/file out "ns/app/core.js"))]
          (is (str/includes? text "import \"../cljs/only.js\""))
          (is (not (str/includes? text "clojure/only.js"))))
        ;; 41 + 41 + 41 + 1: the refer, the asked-for alias, the long name, and
        ;; clojure.both, which has a file of its own and is therefore itself. That
        ;; last one is the whole of why clojure.string and clojure.set are not
        ;; swept up by this - the rule fires only where nothing exists.
        (is (= "124" (node (io/file out "ns/app/core.js")))))
      (finally (delete-tree! src) (delete-tree! out)))))

;; --- what it refuses --------------------------------------------------------

(defn- refuses [sources ns-sym]
  (let [src (write-sources! (temp-dir) sources)
        out (temp-dir)]
    (try
      (h/message #(driver/compile-namespace! (env/compile-env {:ns 'cljs.user})
                                             ns-sym
                                             {:out-dir out :source-paths [src]}))
      (finally (delete-tree! src) (delete-tree! out)))))

(deftest test-a-cycle-is-named-rather-than-overflowing-the-stack
  (let [msg (refuses '{a.one "(ns a.one (:require [a.two :as t]))"
                       a.two "(ns a.two (:require [a.one :as o]))"}
                     'a.one)]
    (is (re-find #"Circular dependency: a.one -> a.two -> a.one" msg))))

(deftest test-a-missing-source-says-where-it-looked
  (let [msg (refuses '{a.one "(ns a.one (:require [no.such.thing :as t]))"} 'a.one)]
    (is (re-find #"Could not locate no/such/thing.cljs" msg))
    (is (re-find #"on the source path" msg))))

(deftest test-a-file-has-to-begin-with-the-ns-form-it-declares
  (is (re-find #"must begin with an ns form, not def"
               (refuses '{a.one "(def x 1)"} 'a.one)))
  (is (re-find #"is empty" (refuses '{a.one ""} 'a.one)))
  (is (re-find #"declares a.other but was required as a.one"
               (refuses '{a.one "(ns a.other)"} 'a.one))))

(deftest test-a-namespace-defined-at-the-repl-needs-no-file
  ;; the driver demands a source only for a namespace it has never seen. One
  ;; declared some other way - typed at a REPL - is left alone rather than
  ;; overwritten with an empty one
  (let [src  (write-sources! (temp-dir) '{a.one "(ns a.one (:require [typed.in :as t]))
                                                 (def x (fn* ([] (t/y))))"})
        out  (temp-dir)
        cenv (env/compile-env {:ns 'cljs.user})]
    (try
      (h/analyze cenv '(ns typed.in))
      (h/analyze cenv '(def y 1))
      (is (= '[cljs.core a.one] (:compiled (driver/compile-namespace!
                                            cenv 'a.one
                                            {:out-dir out :source-paths [src]}))))
      (finally (delete-tree! src) (delete-tree! out)))))

(deftest test-a-var-records-the-file-it-was-written-in
  ;; WHERE A DEFINITION WAS WRITTEN, which is what an editor opens when somebody
  ;; asks to be taken to it. The position was always here - the reader read it -
  ;; and the file was not, because nothing in a form says which file it came out
  ;; of; clojure.cljs.analyzer/*source-file* is how it arrives.
  ;;
  ;; THE PATH IS THE ONE UNDER A SOURCE DIRECTORY, not the one this machine
  ;; happens to hold, which is the same rule Clojure follows for a var of its own
  ;; and the only spelling another process's classpath can resolve. It is also
  ;; source-label, so a file has ONE name here and in its source map rather than
  ;; two spellings of itself.
  ;; written with its own newlines rather than as an indented literal, because
  ;; the columns asserted below are columns of THIS text
  (let [src  (write-sources! (temp-dir)
                             {'app.core (str "(ns app.core)\n"
                                             "(def greet (fn* ([x] x)))\n"
                                             "(deftype Box [v])\n")})
        out  (temp-dir)
        cenv (env/compile-env {:ns 'cljs.user})]
    (try
      (driver/compile-namespace! cenv 'app.core {:out-dir out :source-paths [src]})
      (let [written (ns-interns (env/find-cljs-ns cenv 'app.core))
            at      #(select-keys (meta (get written %)) [:file :line :column])]
        (is (= {:file "app/core.cljs" :line 2 :column 6}  (at 'greet)))
        ;; A TYPE IS PLACED BY ITS NAME and not by the form it is defined in.
        ;; deftype* is built by a macro out of syntax-quote, which copies no
        ;; metadata, while the symbol inside it is the one the reader read - so
        ;; taking the form's position would have given every type line 1, which
        ;; reads like a position and is not one. The form begins at column 1 and
        ;; the name at column 10, so the column is what says which one answered.
        (is (= {:file "app/core.cljs" :line 3 :column 10} (at 'Box))))
      ;; AND EACH FILE ANSWERS FOR ITSELF. cljs.core is compiled by this same call,
      ;; underneath it, and what its vars record is cljs.core's file rather than
      ;; the one whose compilation went and fetched it.
      (is (= "cljs/core.cljs"
             (:file (meta (.findInternedVar ^clojure.lang.Namespace
                                            (env/find-cljs-ns cenv 'cljs.core)
                                            'map)))))
      (finally (delete-tree! src) (delete-tree! out)))))

(deftest test-a-var-defined-at-a-repl-records-no-file
  ;; NIL RATHER THAN A NAME THAT NAMES NOTHING. A form typed at a prompt was not
  ;; read from a file, and Clojure's answer there - "NO_SOURCE_PATH" - is a string
  ;; every tool downstream then has to know is a lie. An absent key says the same
  ;; thing and says it once.
  (let [cenv (h/fresh-env 'app.core)]
    (h/analyze cenv '(def typed 1))
    (let [v (get (ns-interns (env/find-cljs-ns cenv 'app.core)) 'typed)]
      (is (some? v))
      (is (nil? (:file (meta v))))
      ;; the position is still there: it is the reader's and it was never the
      ;; driver's to supply
      (is (contains? (meta v) :line)))))

(deftest test-the-same-source-compiles-to-the-same-text
  ;; what write-if-changed! rests on. The name counter restarts per compilation
  ;; unit, every set that reaches the output - the requires, in the imports and in
  ;; the prologue - is sorted on the way there, and no absolute path appears in it.
  ;; The one exception is a macro calling gensym, which mints a name per expansion;
  ;; see clojure.cljs.driver's docstring
  (let [src (write-sources! (temp-dir) program)
        out (temp-dir)]
    (try
      (let [text #(do (driver/compile-namespace! (env/compile-env {:ns 'cljs.user})
                                                 'app.core
                                                 {:out-dir out :source-paths [src]})
                      (slurp (io/file out "ns/app/core.js")))]
        (is (= 1 (count (distinct (repeatedly 5 text))))))
      (finally (delete-tree! src) (delete-tree! out)))))

(h/deftest-when h/node? test-a-deleted-require-leaves-the-module
  ;; the environment outlives the file, so an ns form has to replace what the last
  ;; one left rather than add to it - see env/clear-ns-declaration!. Recompiling in
  ;; a FRESH environment would hide this, which is why this one is reused
  ;;
  ;; :reload IS WHAT MAKES THE SECOND COMPILE HAPPEN, and it has to be said here
  ;; for the same reason a user has to say it: the environment already holds
  ;; app.core, so the plain form of this call now compiles nothing and the edit
  ;; would never be read. That is the trade `ensure!' documents - an environment is
  ;; asked, not a disk - and saying the flag is how a caller opts out of it.
  (let [src  (write-sources! (temp-dir) program)
        out  (temp-dir)
        cenv (env/compile-env {:ns 'cljs.user})]
    (try
      (let [compile #(driver/compile-namespace! cenv 'app.core
                                                {:out-dir out :source-paths [src]
                                                 :reload true})
            text    #(slurp (io/file out "ns/app/core.js"))]
        (compile)
        (is (str/includes? (text) "import \"../my-lib/core.js\""))
        (spit (io/file src "app/core.cljs")
              "(ns app.core)\n(js* \"console.log(~{})\" 7)\n")
        (compile)
        (is (not (str/includes? (text) "my-lib")))
        (is (= "7" (node (io/file out "ns/app/core.js")))))
      (finally (delete-tree! src) (delete-tree! out)))))

;; --- the implicit require, loaded ---------------------------------------------
;;
;; doc/cljs-compiler.md §5.12. A namespace requires cljs.core whether or not it says
;; so, which the compiler had NAMED (§5.9) and REFERRED without anything loading it.
;; These are the three consequences of closing that: a module imports it, the driver
;; compiles it first, and the program that comes out is real ClojureScript.

(h/deftest-when h/node? test-a-program-that-requires-nothing-still-gets-cljs-core
  (let [src (write-sources!
             (temp-dir)
             '{demo.core "(ns demo.core)
                          (def xs [1 2 3])
                          (defn total [] (reduce + xs))
                          (js/console.log (pr-str {:xs xs :total (total)}))"})
        out (temp-dir)]
    (try
      (let [result (driver/compile-namespace! (env/compile-env {:ns 'cljs.user})
                                              'demo.core
                                              {:out-dir out :source-paths [src]})]
        ;; compiled FIRST, because everything requires it
        (is (= '[cljs.core demo.core] (:compiled result)))
        ;; and imported, which is the line that makes the require a load
        (is (str/includes? (slurp (io/file out "ns/demo/core.js"))
                           "import \"../cljs/core.js\";"))
        ;; the whole point: real vectors, real keywords, real printing, from a file
        ;; whose ns form names nothing at all
        (is (= "{:xs [1 2 3], :total 6}" (node (io/file out "ns/demo/core.js")))))
      (finally (delete-tree! src) (delete-tree! out)))))

(h/deftest-when h/node? test-a-data-reader-namespace-is-compiled-by-the-run
  ;; §5.30. A data reader is a dependency of the PROGRAM, not of the namespace that
  ;; uses the tag: cljs.reader's tag table holds a call to every registered reader,
  ;; so those namespaces have to be loaded before its module body runs - and here
  ;; that means an import, which means compiled. Nothing in an ns form can say so,
  ;; because which namespaces they are is whatever the classpath registered. So the
  ;; run compiles them, exactly as it compiles cljs.core whether or not an ns form
  ;; says so.
  (let [src (write-sources!
             (temp-dir)
             '{demo.core "(ns demo.core) (js/console.log \"ok\")"})
        out (temp-dir)]
    (try
      (with-redefs [reader/user-data-readers
                    (constantly {'my/up (with-meta identity
                                          {:sym 'clojure.string/upper-case})})]
        (let [result (driver/compile-namespace! (env/compile-env {:ns 'cljs.user})
                                                'demo.core
                                                {:out-dir out :source-paths [src]})]
          ;; before demo.core, and before cljs.core is pulled in on its behalf
          (is (= '[cljs.core clojure.string demo.core] (:compiled result)))))
      (finally (delete-tree! src) (delete-tree! out))))

  ;; a reader whose namespace has no ClojureScript source is SKIPPED rather than
  ;; refused: it may be a JVM reader used only while compiling, and the tag still
  ;; reads there
  (let [src (write-sources!
             (temp-dir)
             '{demo.core "(ns demo.core) (js/console.log \"ok\")"})
        out (temp-dir)]
    (try
      (with-redefs [reader/user-data-readers
                    (constantly {'my/x (with-meta identity
                                         {:sym 'no.such.namespace/read-it})})]
        (is (= '[cljs.core demo.core]
               (:compiled (driver/compile-namespace! (env/compile-env {:ns 'cljs.user})
                                                     'demo.core
                                                     {:out-dir out
                                                      :source-paths [src]})))))
      (finally (delete-tree! src) (delete-tree! out)))))

(deftest test-cljs-core-is-found-off-the-classpath
  ;; not on the caller's source paths, and it must not have to be: cljs.core ships
  ;; with this compiler the way cljs/core.cljs ships inside the ClojureScript jar,
  ;; and a caller passing :source-paths is replacing its own tree, not ours
  (let [dir (temp-dir)]
    (try
      (is (some? (driver/find-source [dir] 'cljs.core)))
      (is (nil? (driver/find-source [dir] 'no.such.namespace)))
      (finally (delete-tree! dir)))))

(h/deftest-when h/node? test-the-env-a-macro-sees-follows-the-file
  ;; &env carries {:ns {:name ...}} as a VALUE, read by defprotocol and defmulti
  ;; among others - so it has to be built per form, after the ns form has moved the
  ;; cursor. Built once per file it named whatever namespace the driver was in when
  ;; it opened the file: cljs.user for the first, and the PREVIOUS FILE for every
  ;; one after it. Two namespaces, so the second is compiled after the first.
  (let [src (write-sources!
             (temp-dir)
             '{one.core "(ns one.core)
                         (defprotocol IOne (-one [this]))"
               two.core "(ns two.core (:require [one.core]))
                         (defprotocol ITwo (-two [this]))
                         (deftype T [] ITwo (-two [this] 42))
                         (js/console.log (-two (T.)))"})
        out (temp-dir)]
    (try
      (driver/compile-namespace! (env/compile-env {:ns 'cljs.user}) 'two.core
                                 {:out-dir out :source-paths [src]})
      (let [js (slurp (io/file out "ns/two/core.js"))]
        ;; two$core$$ITwo$_two$arity$1, not one$core$ or cljs$user$
        (is (str/includes? js "two$core$$ITwo$_two$arity$1") js)
        (is (not (str/includes? js "one$core$$ITwo")) js))
      (is (= "42" (node (io/file out "ns/two/core.js"))))
      (finally (delete-tree! src) (delete-tree! out)))))

;; --- the //# sourceURL of a reloaded body -----------------------------------

(deftest test-a-reloaded-body-sits-where-the-module-does
  ;; doc/cljs-output-layout.md §4's first rule is that a script reloading a
  ;; namespace body carries the MODULE's URL, so that a browser treats it as a new
  ;; version of a file it already has rather than as an anonymous program. That
  ;; claim is worth nothing if the two disagree about line numbers, and they very
  ;; nearly did: before emitter/script put the prelude bindings on its opening line,
  ;; the script was exactly one line longer than the module, every time.
  ;;
  ;; Exactly one, and not by luck. The module is one runtime import, one import per
  ;; require, one const per alias, and two registry lines; the script is one opener,
  ;; one await per require, one const per alias, a fetch guard and one registry
  ;; line. The counts match only with the opener and the globals sharing a line.
  ;;
  ;; This is checked against a program with requires rather than one without,
  ;; because a prologue with nothing in it would agree by accident.
  (let [src (write-sources! (temp-dir) program)
        out (temp-dir)]
    (try
      (let [cenv   (env/compile-env {:ns 'cljs.user})
            r      (driver/compile-namespace! cenv 'app.core
                                              {:out-dir out :source-paths [src]})
            module (str/split-lines (slurp (io/file out "ns/app/core.js")))
            script (str/split-lines (second (first (filter #(= 'app.core (first %))
                                                           (:scripts r)))))
            ;; the first line of the body: the first line of either that is not
            ;; prologue. `answer` is the program's first def and appears once.
            at     (fn [ls] (first (keep-indexed #(when (str/includes? %2 "answer =") %1) ls)))]
        (is (some? (at module)))
        (is (= (at module) (at script))
            (str "module body at " (at module) ", script body at " (at script)))
        (testing "and the script says so, on its last line"
          (is (str/ends-with? (second (first (filter #(= 'app.core (first %)) (:scripts r))))
                              "\n//# sourceURL=ns/app/core.js"))))
      (finally (delete-tree! src) (delete-tree! out)))))

;; --- the source map beside the module ---------------------------------------

(def ^:private mapped-program
  "One namespace whose line numbers are the point, so they are written out here:

     1  (ns map.demo)
     2
     3  (defn add
     4    [a b]
     5    (let [s (+ a b)]
     6      (* s 2)))
     7
     8  (defn go
     9    []
    10    (add 1 2))"
  {'map.demo (str "(ns map.demo)\n"
                  "\n"
                  "(defn add\n"
                  "  [a b]\n"
                  "  (let [s (+ a b)]\n"
                  "    (* s 2)))\n"
                  "\n"
                  "(defn go\n"
                  "  []\n"
                  "  (add 1 2))\n")})

(defn- compiled-with-map
  "Compile mapped-program into `out` and hand back what a consumer of the map sees:
  the module's lines, the decoded map, and the reload script."
  [out src]
  (let [cenv (env/compile-env {:ns 'cljs.user})
        r    (driver/compile-namespace! cenv 'map.demo {:out-dir out :source-paths [src]})
        json (slurp (io/file out "ns/map/demo.js.map"))]
    {:lines     (str/split-lines (slurp (io/file out "ns/map/demo.js")))
     :json      json
     :positions (h/map-positions json)
     :script    (second (first (filter #(= 'map.demo (first %)) (:scripts r))))}))

(defn- line-mapping
  "Where the one generated line containing `needle` came from, as
  [source line column] - and nil if it is unmapped. Fails loudly if `needle` does
  not name exactly one line, so a test cannot quietly assert about nothing."
  [{:keys [lines positions]} needle]
  (let [hits (keep-indexed #(when (str/includes? %2 needle) %1) lines)]
    (assert (= 1 (count hits)) (str needle " matched " (count hits) " lines"))
    (nth positions (first hits))))

(h/deftest-when h/node? test-a-module-is-mapped-back-to-its-source
  (let [src (write-sources! (temp-dir) mapped-program)
        out (temp-dir)]
    (try
      (let [c (compiled-with-map out src)]
        (testing "the module names the map beside it, by a bare name"
          ;; bare, so it resolves against whatever the module itself was loaded as
          ;; - a file: URL under node, an http: one in a browser - with neither
          ;; side being told where the output root is
          (is (= "//# sourceMappingURL=demo.js.map" (last (:lines c))))
          (is (.isFile (io/file out "ns/map/demo.js.map"))))

        (testing "the source is named as it would be found, and travels with it"
          (is (= ["map/demo.cljs"] (h/map-sources (:json c))))
          (is (= (get mapped-program 'map.demo)
                 (h/map-content (:json c) "map/demo.cljs"))))

        (testing "every line of the body is placed, and placed where it was written"
          ;; §5.43. The columns are inside the form rather than at its opening
          ;; paren, because the first thing a line emits is the first SUBFORM the
          ;; reader gave a position to - which is a position in the right form on
          ;; the right line, and that is what a stack frame needs.
          (is (= 3 (second (line-mapping c "demo$add"))))
          (is (= 5 (second (line-mapping c "let s__"))))
          (is (= 6 (second (line-mapping c "s__3 * "))))
          (is (= 8 (second (line-mapping c "demo$go"))))
          (is (= 10 (second (line-mapping c "demo$ns.add.call"))))
          ;; the (ns ...) form, which is the one line of the body that is not a defn
          (is (= 1 (second (line-mapping c "$CLJS.loaded.add")))))

        (testing "the module's own scaffolding is mapped to nothing"
          ;; an import and a $ns binding came from no ClojureScript at all, and
          ;; saying so is better than pointing them at the ns form
          (is (nil? (line-mapping c "from \"../../runtime.js\"")))
          (is (nil? (line-mapping c "const map$demo$ns")))
          (is (nil? (line-mapping c "$CLJS.fetched.add")))
          (is (nil? (line-mapping c "sourceMappingURL"))))

        (testing "and there are no holes in between"
          ;; from the first placed line to the last, every line is placed: a line
          ;; the emitter produced and nothing claimed would be a line a debugger
          ;; steps into and falls out of the source for
          (let [ps    (:positions c)
                first' (first (keep-indexed #(when %2 %1) ps))
                last'  (last (keep-indexed #(when %2 %1) ps))]
            (is (some? first'))
            (is (every? some? (subvec (vec ps) first' (inc last'))))
            (is (every? #(<= 1 (second %) 10) (filter some? ps)))))

        (testing "the reload script borrows the module's map, and can"
          ;; the script carries the module's URL (§4's first rule) and names the
          ;; same map, which is only correct because the two agree line for line -
          ;; what test-a-reloaded-body-sits-where-the-module-does pins. Checked
          ;; here as well, against the placed lines rather than one landmark: every
          ;; line the map places must hold the same code in both.
          (is (str/includes? (:script c) "\n//# sourceMappingURL=demo.js.map\n"))
          (let [script (str/split-lines (:script c))]
            (doseq [[i p] (map-indexed vector (:positions c))
                    :when (and p (< i (count script)))]
              (is (= (str/trim (nth (:lines c) i)) (str/trim (nth script i)))
                  (str "line " (inc i) " differs: module " (pr-str (nth (:lines c) i))
                       ", script " (pr-str (nth script i))))))))
      (finally (delete-tree! src) (delete-tree! out)))))
