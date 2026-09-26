// The npm/ tree: built here, named by the compiler.
//
//   node build_npm.mjs --esbuild=<path> --entries=<dir> --report=<file> \
//                      [--dev] <out-dir> <specifier-list-file>
//
// clojure.cljs.npm schedules this; doc/cljs-npm.md §6 is why it exists at all and
// doc/cljs-output-layout.md is where the paths come from. Everything this writes
// lands at `<out-dir>/npm/<specifier>.js`, which is output/js->path's answer
// stated a second time - by --outbase and --outdir rather than by a table, so
// there is no mapping here to drift out of step with that one.
//
// EVERY OUTPUT EXPORTS ONE NAME, `$module`, AND IT IS THE MODULE'S VALUE: the
// namespace object of an ES module, and `module.exports` itself of a CommonJS one.
// That single rule is the whole of the interop, and it is what the ns form's four
// options are then read off - doc/cljs-npm.md §2. The two halves of it are the two
// entry shapes below, and which one a specifier gets is the only thing this script
// has to find out about it.
//
// NOTHING IS EXECUTED HERE. esbuild resolves, esbuild reports the format, esbuild
// bundles; no package is ever loaded into this process. That is not a nicety -
// lottie-light-react touches `document` the moment it loads, so a script that
// enumerated a package by importing it would fail on a machine with no DOM, which
// is every machine this runs on.
//
// IT REPORTS IN EDN, written to --report. The JVM half of this has no JSON reader
// and does not want one for eight fields; EDN it can read with clojure.edn, which
// is in core. The file is written whether the build worked or not, so a failure is
// a sentence rather than an exit code.
import { writeFileSync, mkdirSync, rmSync, readFileSync, realpathSync } from "node:fs";
import { dirname, join, relative, resolve } from "node:path";
import { pathToFileURL } from "node:url";

const argv = process.argv.slice(2);
const flag = (name) => {
  const p = argv.find((a) => a.startsWith("--" + name + "="));
  return p ? p.slice(name.length + 3) : null;
};
const dev = argv.includes("--dev");
const esbuildPath = flag("esbuild");
const entryDir = flag("entries");
const reportPath = flag("report");
const [outDir, listFile] = argv.filter((a) => !a.startsWith("--"));

// --- the report --------------------------------------------------------------

// A KEYWORD IS NOT A STRING, and the difference is the whole reason for this
// class: `:cjs` says what shape a package has, `"cjs"` would be a package of that
// name. Everything else EDN needs is JavaScript's own - a JSON string is a valid
// EDN string, escapes included.
class Kw {
  constructor(name) { this.name = name; }
}
const kw = (name) => new Kw(name);

function edn(x) {
  if (x === null || x === undefined) return "nil";
  if (x instanceof Kw) return ":" + x.name;
  if (typeof x === "boolean") return x ? "true" : "false";
  if (typeof x === "number") return Number.isFinite(x) ? String(x) : "nil";
  if (typeof x === "string") return JSON.stringify(x);
  if (Array.isArray(x)) return "[" + x.map(edn).join(" ") + "]";
  if (x instanceof Map) {
    return "{" + [...x].map(([k, v]) => edn(k) + " " + edn(v)).join(" ") + "}";
  }
  return "{" + Object.entries(x)
    .filter(([, v]) => v !== undefined)
    .map(([k, v]) => ":" + k + " " + edn(v)).join(" ") + "}";
}

// WRITTEN ON THE WAY OUT AND ONLY ONCE. The caller reads this file rather than
// this process's stdout, because esbuild writes to stdout too and a report that
// has to be found among build noise is a parser waiting to be written.
let reported = false;
function report(m, code) {
  if (!reported && reportPath) {
    reported = true;
    writeFileSync(reportPath, edn(m) + "\n");
  }
  process.exit(code);
}

function die(why, detail) {
  report({ ok: false, error: why, detail: detail ? String(detail).slice(0, 2000) : null }, 1);
}

if (!outDir || !listFile || !entryDir || !esbuildPath) {
  die("usage", "build_npm.mjs --esbuild= --entries= --report= <out-dir> <list-file>");
}

let esbuild;
try {
  esbuild = await import(pathToFileURL(esbuildPath).href);
} catch (e) {
  die("no-esbuild", e && e.message);
}

let specs;
try {
  specs = readFileSync(listFile, "utf8").split("\n").map((s) => s.trim()).filter(Boolean);
} catch (e) {
  die("no-list", e && e.message);
}

// --- the two entry shapes ------------------------------------------------------

// BESIDE THE PROJECT'S node_modules, not under the output directory, and that is
// not a tidiness choice: esbuild resolves a bare specifier from the importing
// file's own directory upwards, so an entry written into an output tree that
// happens to sit outside the project finds no node_modules and nothing resolves
// at all. The caller puts this under <project>/node_modules/.cache for that
// reason.
function entryPath(spec) { return join(entryDir, spec + ".js"); }

// `require` IS THE RESOLUTION AS WELL AS THE VALUE, and this is the entry every
// specifier gets unless it cannot have one.
//
// THE VALUE. `module.exports` is what an alias must end up holding, and only
// `require` yields it. `import * as` and `import x from` both go through esbuild's
// interop, which wraps the exports in a fresh namespace object and - when the
// package sets `__esModule` - unwraps `.default` on the way. Either is the wrong
// object: `module.exports` may BE the function the package is
// (`module.exports = debounce`), and it carries properties no static view of the
// file can see. `require` returns the object the package assigned, untouched. For a
// package that is really an ES module, `require` of it gives the namespace object,
// which is what an ES module's `module.exports` would be - so the one call answers
// both halves of §2.1's table without being told which it is looking at.
//
// THE RESOLUTION, which is the half that took a bug to find. A package shipping
// BOTH builds - `exports: {import, require}`, or `module` beside `main` - has two
// files saying the same thing, and which one a bundler loads is a CONDITION rather
// than a fact about the package:
//
//     orderedmap    exports.require -> dist/index.cjs   module.exports = OrderedMap
//                   exports.import  -> dist/index.js    export default OrderedMap
//
// Asked with `import * as`, esbuild takes the `import` condition and the alias
// becomes {default: OrderedMap} - so `OrderedMap/from`, which is what the package
// is FOR, reads a named export the ES build has not got. Asked with `require` it
// takes the other one and the alias is OrderedMap, which is what shadow-cljs binds
// and what the project's source was written against. Both toolchains ask the same
// way for the same reason, and ClojureScript's own :bundle target emits a require()
// call for its bundler to resolve.
//
// A package with no `exports` map is unaffected: `mainFields` decides, esbuild's
// browser default is ["browser", "module", "main"], and that is shadow's order too -
// date-fns/sub resolves to its ESM build under both, and `$default` reads the
// `default` off the namespace `require` gives back.
const CJS = (spec) =>
  `export const $module = require(${JSON.stringify(spec)});\n`;

// THE FALLBACK, FOR A PACKAGE `require` CANNOT REACH. Two shapes cannot be
// required: one whose `exports` map offers an `import` condition and no `require`
// one, and one whose ES module has a top-level await - `require` of that is refused
// because there is nothing synchronous to return. Both are ES modules by the only
// route they have left, so `import * as` is what is left to ask with, and the
// namespace object it binds is what §2.1's first row says `$module` is anyway.
const ESM = (spec) =>
  `import * as $module from ${JSON.stringify(spec)};\nexport { $module };\n`;

const form = new Map(specs.map((s) => [s, CJS]));
// What each specifier's resolved file turned out to BE, which is not the same
// question as which entry shape reached it: `require` of an ES module is a legal
// thing to do and what comes back is that module's namespace. Reported as `kinds`,
// because it is what decides which object an alias binds - §2.1.
const formats = new Map();
let live = new Set(specs);
const failed = [];

// The directory the entries are in, as THIS process spells it. --entries may name
// it through a symbolic link - every temporary directory on macOS does, /var being
// a link to /private/var - and esbuild answers in paths resolved against
// process.cwd(), which is not. Comparing the two spellings without this finds no
// entry for any error and no entry in any metafile, so a probe learns nothing and
// a failure has nobody to blame.
let entryRoot = entryDir;

function writeEntries() {
  rmSync(entryDir, { recursive: true, force: true });
  mkdirSync(entryDir, { recursive: true });
  entryRoot = realpathSync(entryDir);
  return [...live].map((spec) => {
    const p = entryPath(spec);
    mkdirSync(dirname(p), { recursive: true });
    writeFileSync(p, form.get(spec)(spec));
    return p;
  });
}

// esbuild spells a path in an error location and in a metafile key relative to
// THIS process's directory; the entries are keyed by specifier. One function, so
// the two ways in agree.
function specOf(file) {
  if (!file) return null;
  const spec = relative(entryRoot, resolve(process.cwd(), file)).replace(/\.js$/, "");
  return live.has(spec) ? spec : null;
}

// The options are shared between the probe and the build ON PURPOSE: resolution
// depends on platform and on conditions, so a probe that asked anything else
// would be answering about a different file than the one that gets bundled.
const options = (extra) => ({
  entryPoints: writeEntries(),
  outbase: entryDir,
  bundle: true, format: "esm", splitting: true, platform: "browser",
  // SHADOW-CLJS'S ORDER, SAID OUT LOUD. shadow's default is
  // `:entry-keys ["browser" "main" "module"]' (shadow.build.npm), and a project
  // whose `ns' forms were written against it has to get the same file here or the
  // same form means something else - which is §2's whole promise.
  //
  // `main' BEFORE `module', which is not esbuild's browser default for an import
  // statement and IS its default for a `require' call, the call this makes. The
  // difference is the package's CommonJS build against its ES one, and for a
  // package that ships both with no `exports' map to choose between them the
  // CommonJS build is the one whose `module.exports' an alias can BE:
  //
  //   linkify-html   main: dist/linkify-html.cjs   module.exports = linkifyHtml
  //                  module: dist/linkify-html.mjs export { linkifyHtml as default }
  //
  // `(:require ["linkify-html" :as linkify-html])' and then calling it is what the
  // package is for, and it works on the first and not on the second, where the
  // alias is {default: linkifyHtml}. Measured the same way on turndown,
  // form-data-entries and scroll-into-view-if-needed: four packages of one project,
  // each of them an alias that is called and each of them an object under `module'.
  //
  // WHAT THE OTHER ORDER WAS FOR does not need it. date-fns/sub was the example -
  // `["date-fns/sub$default" :as sub]' wants a `default' to read, and its CommonJS
  // build ends `module.exports = exports.default' and has none - but
  // date-fns/sub/package.json declares `module' and no `main' at all, so `main'
  // first finds nothing there and falls through to the ES build regardless. Both
  // orders resolve it to esm/sub/index.js.
  //
  // An `exports' map still wins over this, which is what leaves §2.2's other half
  // alone - orderedmap keeps going through its `require' condition.
  mainFields: ["browser", "main", "module"],
  // NOT optional: without it esbuild defaults NODE_ENV to "development" for the
  // browser platform and silently bundles React's development build - 83KB
  // against 14KB, and no error either way.
  define: { "process.env.NODE_ENV": dev ? '"development"' : '"production"' },
  logLevel: "silent", metafile: true,
  ...extra,
});

// --- the probe: which specifiers are CommonJS ----------------------------------

// ASKED OF esbuild AND OF NOTHING ELSE. A build with `write: false` costs one pass
// over the same graph the real build walks, and its metafile records each input's
// `format` - so the answer comes from the resolver that is going to do the work,
// under the same conditions, rather than from a heuristic about package.json.
//
// It is asked with EVERY entry in the shape it will really be built in, which is
// the only way the answer is about the right FILE: a dual package resolves to one
// file under `require` and another under `import`, so a probe that asked the other
// way would report the format of a file the build is not going to read.
let probes = 0, meta = null;
for (;;) {
  probes++;
  try {
    meta = (await esbuild.build(options({ write: false, outdir: join(entryDir, ".probe") }))).metafile;
    break;
  } catch (e) {
    if (!e.errors || probes > 6) die("resolve", (e.errors || []).map((x) => x.text).join("\n") || (e && e.message));
    let progress = 0;
    for (const err of e.errors) {
      const spec = specOf(err.location && err.location.file);
      if (!spec) continue;
      // A package whose "exports" map offers an `import` condition and no `require`
      // one: unreachable by require, and an ES module by the only route it has left.
      if (form.get(spec) === CJS) { form.set(spec, ESM); progress++; }
      else { live.delete(spec); failed.push([spec, err.text.slice(0, 200)]); progress++; }
    }
    if (!progress) die("resolve", e.errors.map((x) => x.text).join("\n"));
  }
}

// The entry reaches exactly one file - the package - so the one import it has is the
// one whose format is the package's. The KIND of that import is whichever shape the
// entry has, which is why both are looked for; what is being read is the target.
//
// NOTHING IS DECIDED HERE ANY MORE. The shape is `require` unless require could not
// reach the package at all, and that was settled by the loop above. This records
// what was reached, for the report.
for (const [input, o] of Object.entries(meta.inputs)) {
  const spec = specOf(input);
  if (!spec) continue;
  const imported = (o.imports || [])
        .find((i) => i.kind === "import-statement" || i.kind === "require-call");
  const target = imported && meta.inputs[imported.path];
  if (target && target.format) formats.set(spec, target.format);
}

// --- the build -----------------------------------------------------------------

// WHAT THE PROBE CANNOT ANSWER, THE BUILD COMPLAINS ABOUT. `require` of an ES
// module is refused when that module has a top-level await - there is nothing
// synchronous to hand back - and the probe writes nothing, so it never got that
// far. Put such a specifier in its ES shape and build again: that shape needs no
// proving, being the one every ES module resolves under.
let rounds = 0;
for (;;) {
  rounds++;
  try {
    const result = await esbuild.build(options({ outdir: join(outDir, "npm") }));
    const outs = Object.entries(result.metafile.outputs);
    const chunk = (p) => /chunk-[A-Z0-9]+\.js$/.test(p);
    // WHAT THE PACKAGE IS, not which entry reached it. A dual package required
    // through its `require` condition is a CommonJS file and says so; an ES module
    // that `require` reached all the same is an ES module.
    const kinds = new Map([...live].sort()
                          .map((s) => [s, kw(formats.get(s) === "cjs" ? "cjs" : "esm")]));
    rmSync(entryDir, { recursive: true, force: true });
    report({
      ok: true,
      // relative to the output root, which is the spelling js->path uses and the
      // one the caller prunes a later build against
      outputs: outs.map(([p]) => relative(outDir, p).split("\\").join("/")).sort(),
      modules: outs.filter(([p]) => !chunk(p)).length,
      chunks: outs.filter(([p]) => chunk(p)).length,
      bytes: outs.reduce((n, [, o]) => n + o.bytes, 0),
      probes: probes,
      rounds: rounds,
      dev: dev,
      kinds: kinds,
      failed: failed,
      // EXIT 0 EVEN WITH FAILURES IN IT. The bundle was written; a specifier that
      // could not be resolved is a sentence in the report, and the caller is going
      // to ask output/missing-js which files are actually there anyway. A non-zero
      // exit here means only that there is nothing worth reading.
    }, 0);
  } catch (e) {
    if (!e.errors || rounds > 6) {
      die("build", (e.errors || []).map((x) => x.text).join("\n") || (e && e.message));
    }
    let progress = 0;
    for (const err of e.errors) {
      const spec = specOf(err.location && err.location.file);
      if (!spec) continue;
      if (form.get(spec) === CJS) { form.set(spec, ESM); progress++; }
      else { live.delete(spec); failed.push([spec, err.text.slice(0, 200)]); progress++; }
    }
    // NO PROGRESS IS THE END OF IT. Looping on an error the rule above cannot act
    // on would spin six times and say the same thing, so say it now.
    if (!progress) die("build", e.errors.map((x) => x.text).join("\n"));
  }
}
