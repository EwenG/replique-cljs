;   Copyright (c) Rich Hickey. All rights reserved.
;   The use and distribution terms for this software are covered by the
;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;   which can be found in the file epl-v10.html at the root of this distribution.
;   By using this software in any fashion, you are agreeing to be bound by
;   the terms of this license.
;   You must not remove this notice, or any other, from this software.

(ns ^{:doc "npm/: the tree the compiler names, and now the one it schedules.

  doc/cljs-npm.md §6 wrote this boundary down as a mapping and a list: the
  specifier names the file (clojure.cljs.output/js->path), a compile's result
  carries :js-requires and :js-missing, and `report-missing-js!` says once per
  directory and specifier what is not there yet. That left the SCHEDULING to a
  person - compile, read the warning, go and run a bundler, come back - and this
  namespace is what takes it back.

  WHAT CHANGED IS NOT THE POLICY, IT IS THE AXIS. `mandatory` and `automatic` are
  different things and the original decision ran them together. What
  doc/cljs-advanced.md §3 is really protecting is that a project which does not
  need npm never notices one; making the build AUTOMATIC serves that better than
  making it EXTERNAL did, because the build step nobody has to run is more absent
  than the build step everybody has to run by hand. So:

    no string require  ->  nothing here runs, nothing is located, no node process
    a bundler is found ->  npm/ is built, and there is no build step
    none is found      ->  §6's report, word for word, which is where we were

  LOCATE, THEN ACQUIRE, THEN REPORT, and the three steps are in that order because
  they cost that much. Locating is a handful of `.isFile` calls. Acquiring is one
  `npm install` into a cache under the user's home, paid once ever. Reporting is
  what is left when there is no node, no node_modules, or no network - and it is
  not a degraded mode so much as the mode this compiler shipped in until now.

  THE BINARY IS NOT VENDORED. esbuild ships as one Go executable per platform, and
  putting eight of those inside a Clojure artifact is a real cost carried by every
  project, most of which never make a string require. Acquiring on demand is the
  better trade, and the marginal requirement is small: node and a populated
  node_modules are already hard requirements the moment a string require appears,
  because that is where the package is.

  WHY ESBUILD AND NOT OURS. A bundler here needs npm resolution with conditional
  `exports`, CommonJS-to-ESM per file, and `process.env.NODE_ENV` dead-code
  elimination - React's CommonJS build is wrapped in exactly that conditional, so
  without the last one a program ships the development build and nothing says so.
  It also needs a JavaScript parser on the JVM, where the only credible one is
  Closure's, which doc/cljs-advanced.md §2 priced out and declined. Writing it in
  JavaScript on node instead is writing esbuild badly.

  Everything node-side is in build_npm.mjs beside this file. It runs node, but it
  never LOADS a package: esbuild resolves each specifier, reports its format and
  bundles it, so a package that touches `document` the moment it is loaded costs
  nothing here. What the script has to find out about a specifier is one bit -
  CommonJS or ES module - because that is what decides which object the emitted
  import binds (doc/cljs-npm.md §2.1), and esbuild answers it from the same
  resolution it is about to do anyway."}
  clojure.cljs.npm
  (:require [clojure.cljs.output :as output]
            [clojure.edn :as edn]
            [clojure.java.io :as io]
            [clojure.string :as str])
  (:import [java.io File]))

(def esbuild-version
  "The esbuild acquired when the project has none of its own.

  PINNED, and low-ceremony about it: a version that is known to have built the
  91-specifier tree doc/cljs-npm.md §8 measures is worth more than the newest one,
  and nothing here tracks a range. A project that wants another version installs
  it, and `locate-esbuild` prefers the project's over this one - which is the
  whole of how a user overrides it."
  "0.28.2")

(def script-resource
  "Where build_npm.mjs lives on the classpath. Beside runtime.js and for the same
  reason: src/clj is an unfiltered resource root, so the file ships in the jar
  verbatim (clojure.cljs.output/prelude-resource)."
  "clojure/cljs/build_npm.mjs")

;; --- the project, and the cache ----------------------------------------------

(defn project-root
  "The nearest directory at or above `start` that has a node_modules, or nil.

  NODE'S OWN RULE, not one invented here, and that matters more than it looks:
  esbuild resolves a bare specifier by walking up from the importing file exactly
  this way, so a root found by any other rule would be a root esbuild disagrees
  with. The entries it bundles are written under this directory for the same
  reason (build_npm.mjs).

  NIL IS AN ANSWER AND NOT A FAILURE. No node_modules means no package to resolve,
  so there is nothing a bundler could have built and the honest reply is §6's
  report. It is also what keeps this out of the way of every test and every
  project that has no JavaScript in it at all."
  ([] (project-root (System/getProperty "user.dir")))
  ([start]
   (loop [^File d (.getAbsoluteFile (io/file start))]
     (when d
       (if (.isDirectory (File. d "node_modules"))
         d
         (recur (.getParentFile d)))))))

(defn- cache-dir
  "Where an acquired esbuild is kept: $XDG_CACHE_HOME/replique-cljs, or
  ~/.cache/replique-cljs.

  UNDER THE USER AND NOT UNDER THE PROJECT, because the point of acquiring is to
  pay for it once rather than once a project, and because node_modules is the
  project's to manage - writing a package into it that its package.json does not
  name is the kind of thing that survives until someone's `npm ci` deletes it."
  ^File []
  (File. (io/file (or (not-empty (System/getenv "XDG_CACHE_HOME"))
                      (str (System/getProperty "user.home") File/separator ".cache")))
         "replique-cljs"))

(defn- work-dir
  "The scratch directory under `root` that a build uses: the script, and the
  generated entry modules.

  INSIDE node_modules/.cache, which is where a JavaScript tool is expected to put
  exactly this and is already ignored by every version control setup that ignores
  node_modules. It has to be under the project at all because esbuild resolves a
  bare specifier upwards from the importing file, so entries written anywhere else
  resolve nothing."
  ^File [^File root]
  (File. root (str "node_modules" File/separator ".cache" File/separator "replique-cljs")))

;; --- locating a bundler -------------------------------------------------------

(defn- esbuild-at
  "esbuild as a package directory: {:module <lib/main.js> :version \"0.28.2\"}, or
  nil when `pkg-dir` is not one.

  The version is read with a regular expression rather than a JSON parser, and the
  only thing it is used for is the cache key below and the line a report prints.
  Nothing branches on it: a version too old to have the JavaScript API fails the
  build with esbuild's own message, which says more than a comparison here would."
  [^File pkg-dir]
  (let [pj   (File. pkg-dir "package.json")
        main (File. pkg-dir (str "lib" File/separator "main.js"))]
    (when (and (.isFile pj) (.isFile main))
      {:module  (.getAbsolutePath main)
       :version (or (second (re-find #"(?m)^\s*\"version\"\s*:\s*\"([^\"]+)\"" (slurp pj)))
                    "unknown")})))

(defn- given-esbuild
  "The :esbuild option, which may name the package directory or lib/main.js itself."
  [given]
  (let [^File f (io/file given)]
    (cond
      (.isDirectory f) (some-> (esbuild-at f) (assoc :how :given))
      (.isFile f)      {:module (.getAbsolutePath f) :version "given" :how :given}
      :else            nil)))

(defn locate-esbuild
  "An esbuild this build may use, without installing anything. Nil when there is
  none.

    {:module \"/…/esbuild/lib/main.js\" :version \"0.28.2\" :how :project}

  Three places, in the order a project would want them asked:

    :given    the :esbuild option, for a project that keeps one somewhere of its
              own or wants a specific build under test. AUTHORITATIVE: a path that
              names no esbuild is nil and not a reason to go looking, because
              quietly using a different bundler than the one asked for is how a
              measurement stops being about what it says it is about;
    :project  <root>/node_modules/esbuild - THEIRS, version and all. A project
              that already bundles has an esbuild with a version its lockfile
              pins, and using a second one behind its back is how two tools end
              up disagreeing about what a package exports;
    :cache    the one `acquire-esbuild!` put under the user's home, shared by
              every project that has none of its own."
  [{:keys [esbuild root]}]
  (if esbuild
    (given-esbuild esbuild)
    (or (when root
          (some-> (esbuild-at (File. (io/file root) (str "node_modules" File/separator "esbuild")))
                  (assoc :how :project)))
        (some-> (esbuild-at (File. (cache-dir) (str "esbuild" File/separator esbuild-version
                                                    File/separator "node_modules"
                                                    File/separator "esbuild")))
                (assoc :how :cache)))))

(defn- exec
  "Run `cmd` in `dir`. {:exit n :out s}, with stderr merged into stdout because
  every caller here wants the whole of what a failing tool said.

  A TOOL THAT IS NOT INSTALLED IS AN EXIT CODE HERE AND NOT AN EXCEPTION. No node
  on PATH is exactly the case this whole namespace is supposed to degrade for, and
  ProcessBuilder answers it by throwing out of a compile - which would turn the
  absence of an optional tool into a failure to compile ClojureScript."
  [cmd ^File dir]
  (try
    (let [pb (ProcessBuilder. ^java.util.List (vec cmd))]
      (.redirectErrorStream pb true)
      (when dir (.directory pb dir))
      (let [p   (.start pb)
            out (slurp (.getInputStream p))]
        {:exit (.waitFor p) :out out}))
    (catch Exception e
      {:exit -1 :out (str (first cmd) ": " (.getMessage e))})))

(defn acquire-esbuild!
  "Install esbuild into the cache under the user's home, and return what
  `locate-esbuild` would then find. Nil if it could not.

  ONE npm install, PAID ONCE EVER, and announced while it happens because a
  compile that silently pauses to talk to a network is worse than one that says
  it is doing so. It is reached only when a project has a node_modules and no
  esbuild in it - nosco-gamma is exactly that case: 740 packages, built with
  shadow-cljs and Closure, no esbuild anywhere.

  --prefix is what keeps it out of the project: npm writes <prefix>/node_modules
  and nothing else, and the prefix is a directory of this version's own so a later
  pin does not have to uninstall anything."
  []
  (let [prefix (File. (cache-dir) (str "esbuild" File/separator esbuild-version))]
    (.mkdirs prefix)
    (binding [*out* *err*]
      (println (str "Installing esbuild " esbuild-version " into " prefix
                    " - once, for the npm/ tree (doc/cljs-npm.md §6).")))
    (let [{:keys [exit out]} (exec ["npm" "install" "--no-audit" "--no-fund"
                                    "--loglevel" "error" "--prefix" (.getPath prefix)
                                    (str "esbuild@" esbuild-version)]
                                   prefix)]
      (if (zero? exit)
        (some-> (esbuild-at (File. prefix (str "node_modules" File/separator "esbuild")))
                (assoc :how :cache))
        (binding [*out* *err*]
          (println (str "WARNING: could not install esbuild (" exit "): " (str/trim out)))
          nil)))))

;; --- what a build was made of -------------------------------------------------

(defn- installed-stamp
  "What `root` has installed, as cheaply as the question can be asked:
  {name [modified length]} over the files that change when it does.

  node_modules/.package-lock.json is npm's own record of the tree it wrote, so it
  moves on every install and on nothing else; the other four are here because a
  project may use a different package manager and because one of them is usually
  what a person edits. THIS IS A CACHE KEY AND NOT A PROOF - someone who edits a
  file inside node_modules by hand gets a stale bundle, and the answer to that is
  to delete npm/, which is also the answer to every other kind of stale output
  directory (doc/cljs-output-layout.md §0)."
  [^File root]
  (into (sorted-map)
        (for [n    ["node_modules/.package-lock.json" "package-lock.json"
                    "yarn.lock" "pnpm-lock.yaml" "package.json"]
              :let [f (File. root ^String (str/replace n "/" File/separator))]
              :when (.isFile f)]
          [n [(.lastModified f) (.length f)]])))

(defn- build-key
  "Everything a build's output depends on, in one comparable value.

  The specifier list and the NODE_ENV the tree was built for, because those are
  the inputs; the esbuild, because two versions do not emit the same bytes; and
  the installed stamp, because the packages are the rest of the input and are not
  ours to read."
  [^File root esbuild specifiers dev]
  {:specifiers (vec specifiers)
   :dev        (boolean dev)
   :esbuild    (select-keys esbuild [:version :module])
   :installed  (installed-stamp root)})

(defn- manifest-file
  "Where a build records what it did, so the next one can decline to repeat it.

  INSIDE npm/, which is the tree it describes: deleting that tree is how a person
  says `build it again`, and a manifest that outlived it would answer `already
  did`. Nothing else in an output directory records anything durable
  (doc/cljs-output-layout.md §0) and this does not either - it is about the
  bundler's tree, not about the layout."
  ^File [dir]
  (File. (io/file dir) (str output/js-dir File/separator ".build.edn")))

(defn- read-manifest
  [dir]
  (let [f (manifest-file dir)]
    (when (.isFile f)
      (try (edn/read-string (slurp f)) (catch Exception _ nil)))))

(defn- prune!
  "Delete what the LAST build wrote and this one did not.

  Only those files, and that restriction is the whole safety of it: a chunk's name
  holds a hash of its contents, so a changed dependency leaves the old chunk
  behind for ever, and a specifier dropped from an ns form leaves its module.
  Anything under npm/ that no manifest claims was put there by someone else - a
  hand-written stand-in, the tests' bundler - and is left alone."
  [dir old new]
  (let [gone (remove (set new) old)]
    (doseq [^String p gone]
      (.delete (File. (io/file dir) ^String (str/replace p "/" File/separator))))
    (count gone)))

;; --- the build ----------------------------------------------------------------

(defn- write-script!
  "Put build_npm.mjs where the node process can run it, and return the file.

  Read from the classpath on every build rather than cached, for
  clojure.cljs.output/prelude-source's reason: it is a file on disk while this is
  being worked on, and a REPL session that changes it should not have to restart."
  ^File [^File work]
  (.mkdirs work)
  (let [f (File. work "build_npm.mjs")]
    (spit f (slurp (io/resource script-resource)))
    f))

(defn build!
  "Build the npm/ tree under `dir` for `specifiers`, with `esbuild`, rooted at the
  project `root`. Returns the node script's own report.

    {:ok true :modules 91 :chunks 50 :bytes 8853408 :probes 1 :rounds 1
     :outputs [\"npm/react.js\" …] :kinds {\"react\" :cjs \"@visx/scale\" :esm …}
     :failed []}

  or {:ok false :error :build :detail \"…\"}.

  :kinds IS THE ANSWER TO THE ONE QUESTION THE SCRIPT HAS TO ASK, which is whether
  a package is CommonJS: an ES module's alias binds its namespace object and a
  CommonJS package's binds module.exports, and only esbuild can say which a
  specifier resolves to. It is in the report and in the manifest because it is the
  fact that decides what the emitted import means - doc/cljs-npm.md §2.1 - and
  because a person looking at a package that behaves oddly wants to see it.

  THE REPORT IS THE SCRIPT'S, read from a file rather than from its stdout: esbuild
  writes to stdout too, and a report that has to be found among build noise is a
  parser waiting to be written. It is EDN because the JVM half has no JSON reader
  and does not want one for eight fields."
  [dir root esbuild specifiers dev]
  (let [^File work (work-dir root)
        script     (write-script! work)
        list-file  (File. work "specifiers.txt")
        report     (File. work "report.edn")]
    (.delete report)
    (spit list-file (str/join "\n" specifiers))
    (let [{:keys [exit out]}
          (exec (cond-> ["node" (.getPath script)
                         (str "--esbuild=" (:module esbuild))
                         (str "--entries=" (.getPath (File. work "entries")))
                         (str "--report=" (.getPath report))]
                  dev (conj "--dev")
                  :always (conj (.getAbsolutePath (io/file dir)) (.getPath list-file)))
                root)
          r (when (.isFile report)
              (try (edn/read-string (slurp report)) (catch Exception _ nil)))]
      (or r {:ok false :error :node
             :detail (str "node exited " exit (when (seq out) (str ": " (str/trim out))))}))))

;; --- the seam -----------------------------------------------------------------

(def ^:private failures
  "Builds that did not work, as {dir key}.

  clojure.cljs.output/reported's shape and its reason, one step further along: the
  check runs on every compile and a REPL evaluating form after form must not
  re-run a failing build once a form. A build is retried when anything it depends
  on changes, which is exactly what the key says."
  (atom {}))

(defn- build-needed?
  "Is there a build to do? `missing` is what output/missing-js already answered.

  TWO REASONS AND NO OTHERS. Something we named is not on disk and no build of
  ours has been made from these inputs yet - the plain case, and the one a first
  compile into a fresh directory always hits. Or a build of ours IS recorded there
  and its key has moved, which is how a changed lockfile or a dropped specifier
  gets rebuilt while the files are all still present.

  A MISSING MODULE IS NOT BY ITSELF A REASON, and that is the half worth spelling
  out. A specifier no bundler can resolve - a typo, a package nobody installed -
  is missing before the build and missing after it, and esbuild has already said
  everything it has to say about it. Rebuilding on the strength of that would run
  a node process once a compile, and once a REPL FORM, for ever. The key is the
  whole of the question: same inputs, same answer, however unsatisfying the answer
  was.

  WHAT IS ALSO NOT A REASON: a full npm/ with no manifest beside it. That is
  somebody else's tree - a hand-written stand-in, another bundler's output,
  doc/cljs-npm.md §8's fixtures - and building over it would be this compiler
  taking ownership of a directory it was told it does not own."
  [missing manifest k]
  (if manifest
    (not= k (:key manifest))
    (boolean (seq missing))))

(def ^:private locks
  "One lock object per output directory, so that two REPL threads compiling into
  the same one do not run two esbuilds over one npm/ tree. Keyed by the path
  rather than by the File, which does not compare the way a key has to."
  (atom {}))

(defn- lock-for
  [dir]
  (let [k (str (io/file dir))]
    (or (get @locks k) (get (swap! locks update k #(or % (Object.))) k))))

(def ^:private told
  "Which output directories have already been told why nothing was built, as
  #{[dir why]}. output/reported's rule one level up: a REPL evaluating form after
  form must hear it once."
  (atom #{}))

(defn- say-why!
  "One line naming the one thing a person can do about it, before the list of what
  is owed. Said only when something is actually missing - a build that did not run
  because there was nothing to build is not news - and only for the case that has
  an action attached to it: no esbuild. :no-root is a project with no node_modules
  at all, where the report's own last paragraph already says everything true."
  [dir why]
  (when (and (= :no-bundler why) (not (contains? @told [(str dir) why])))
    (swap! told conj [(str dir) why])
    (binding [*out* *err*]
      (println (str "WARNING: no esbuild, so " (File. (io/file dir) output/js-dir)
                    " was not built. Add esbuild to the project, or let this"
                    " install one under " (cache-dir) " (:npm {:acquire true}).")))))

(defn- build-into!
  "Run the build and file what it did: prune what the last one left, write the
  manifest, or remember the failure so a REPL does not retry it once a form."
  [dir root esbuild specifiers manifest k dev]
  (let [r (build! dir root esbuild specifiers dev)]
    (if (:ok r)
      (do (prune! dir (get-in manifest [:report :outputs]) (:outputs r))
          (swap! failures dissoc (str dir))
          (spit (manifest-file dir) (pr-str {:key k :report (dissoc r :ok)}))
          (assoc r :how (:how esbuild) :esbuild (:version esbuild)))
      (do (swap! failures assoc (str dir) k)
          (binding [*out* *err*]
            (println (str "WARNING: could not build "
                          (File. (io/file dir) output/js-dir)
                          " (" (name (or (:error r) :build)) "): "
                          (some-> (:detail r) str/trim))))
          (assoc r :how (:how esbuild))))))

(defn ensure-js!
  "Make sure the modules `specifiers` name are under `dir`, then say which of them
  still are not.

  THE ONE SEAM, and all three callers go through it: a compile
  (clojure.cljs.driver/run!*), a REPL form whose namespace made a string require,
  and (require '[\"react\" :as R]) typed at a REPL - which compiles nothing, so the
  driver never runs for it (doc/cljs-npm.md §6).

  Returns {:missing [\"…\"] :build {…}}, where :build is nil when nothing was built
  and carries :why when that was a decision rather than a no-op:

    :disabled         :npm {:build false}
    :no-root          no node_modules at or above the project, so no package to
                      resolve and nothing a bundler could have built
    :no-bundler       no esbuild found, and either acquiring it was declined or
                      it did not work
    :already-failed   this exact build failed once already in this process

  A nil :build with no :why is the ordinary case and covers two of them: nothing
  was missing and no manifest of ours was out of date, which includes an npm/ tree
  somebody else wrote and which is left alone (build-needed?).

  Options, under :npm in the compiler's option map:

    :build    false turns all of this off and leaves doc/cljs-npm.md §6's report
    :acquire  false declines the npm install, leaving locate-then-report
    :root     the project directory, default: the nearest node_modules at or
              above (System/getProperty \"user.dir\")
    :esbuild  a path to use instead of looking
    :dev      build the packages with NODE_ENV=development. Default false, and
              the default is that way round on purpose: shipping React's
              development build by accident is silent and costs 5.9x, while
              getting its terser production errors in a REPL session is merely
              annoying and is one option away.

  LOCKED ON THE DIRECTORY, because two REPL threads compiling into one output
  directory would otherwise run two esbuilds over one npm/ tree."
  [dir specifiers opts]
  (let [npm (:npm opts)]
    (if (or (empty? specifiers) (false? (:build npm)))
      {:missing (output/report-missing-js! dir specifiers)
       :build   (when (seq specifiers) {:ok false :why :disabled})}
      (locking (lock-for dir)
        (let [missing  (output/missing-js dir specifiers)
              manifest (read-manifest dir)
              ;; A ROOT IS A DIRECTORY WITH A node_modules IN IT, whether it was
              ;; found or given. `project-root` answers nil rather than guessing,
              ;; and an explicit :root is held to the same rule: a project whose
              ;; packages are not installed has nothing for a bundler to resolve,
              ;; and saying so is better than running esbuild against an empty
              ;; tree and reporting its complaint.
              root     (some-> (or (:root npm) (project-root)) io/file project-root)
              esbuild  (when root
                         (or (locate-esbuild (assoc npm :root root))
                             ;; ACQUIRING IS FOR BUILDING SOMETHING THAT IS NOT
                             ;; THERE. A tree that is complete does not get a
                             ;; network install to confirm it.
                             (when (and (seq missing) (not (false? (:acquire npm))))
                               (acquire-esbuild!))))
              k        (when esbuild (build-key root esbuild specifiers (:dev npm)))
              build
              (cond
                (not (build-needed? missing manifest k))   nil
                (nil? root)                                {:ok false :why :no-root}
                (nil? esbuild)                             {:ok false :why :no-bundler}
                (= k (get @failures (str dir)))            {:ok false :why :already-failed}
                :else (build-into! dir root esbuild specifiers manifest k (:dev npm)))]
          (when-let [why (:why build)] (say-why! dir why))
          {:missing (output/report-missing-js! dir specifiers)
           :build   build})))))
