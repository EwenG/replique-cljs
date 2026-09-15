# replique-cljs

A ClojureScript compiler and REPL built on [replique-clj](../replique-clj), a
vendored Clojure 1.12.5 whose reader and namespace registry know about a second
world.

Not a fork of ClojureScript. The analyzer, emitter, driver, source maps, stack
symbolication and both REPL transports are written here; what is vendored from
ClojureScript is the part that has to be — `cljs/core.cljc`, `cljs/core.cljs` and
the handful of namespaces around them, plus a nine-file subset of the Closure
Library — and `core-test` checks that vendoring line by line against the jar.

## Build and test

It depends on the fork, which is not on Maven Central, so install that first:

```
cd ../replique-clj && mvn -o install -DskipTests
cd ../replique-cljs && mvn -o test
```

`mvn -o test` runs the whole suite (`test-cljs/`). Two things it wants are
optional and each one missing skips only the tests that need it: **node** on
`PATH` for anything that runs JavaScript, and the ClojureScript jar for the
`cljs.analyzer` AST oracle.

## Why the Java stayed behind

Three pieces of `clojure.lang` make this possible and all three live in
replique-clj: `NamespaceWorld` (a registry indirection, so a ClojureScript
namespace and a JVM namespace of the same name are different objects),
`LispReader`'s `:cljs` platform feature, and the Compiler's position recording.
They are changes to *Clojure*, and the oracle for them is Clojure's own test
suite — 783 tests, 20,448 assertions, which that project keeps green. Nothing in
this repo is Java.

## Documentation

`doc/` is where the reasoning lives, and it is the point of entry:

| | |
|---|---|
| [`cljs-compiler.md`](doc/cljs-compiler.md) | the compiler: milestones M0–M6, and §5 on every decision that needed one |
| [`cljs-repl.md`](doc/cljs-repl.md) | the REPL: the namespace registry, both transports, R0–R4 |
| [`cljs-output-layout.md`](doc/cljs-output-layout.md) | where emitted files go, and what that settles |
| [`cljs-advanced.md`](doc/cljs-advanced.md) | what `:advanced` is worth, and the O-ladder that would buy it |
| [`cljs-lazy-loading.md`](doc/cljs-lazy-loading.md) | `:require-lazy`, code splitting, and the part we refuse to do |
