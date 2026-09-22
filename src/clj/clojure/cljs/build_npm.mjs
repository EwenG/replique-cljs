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

// AN ES MODULE STANDS FOR ITS NAMESPACE OBJECT, which is what `import * as` binds
// and what `:as` must therefore end up holding. Nothing is copied and nothing is
// wrapped, so esbuild can still see which of its exports are used and drop the
// rest.
const ESM = (spec) =>
  `import * as $module from ${JSON.stringify(spec)};\nexport { $module };\n`;

// A CommonJS MODULE STANDS FOR `module.exports`, AND ONLY `require` YIELDS IT.
// `import * as` and `import x from` both go through esbuild's interop, which wraps
// the exports in a fresh namespace object and - when the package sets
// `__esModule` - unwraps `.default` on the way. Either is the wrong object:
// `module.exports` may BE the function the package is (`module.exports = debounce`),
// and it carries properties no static view of the file can see. `require` returns
// the object the package assigned, untouched.
//
// This is the whole of what doc/cljs-npm.md §2.1 calls the CommonJS rule, and it
// is shadow-cljs's semantics: an alias on a CommonJS package names its exports
// object, so `$default` and `:default` read `.default` OFF it rather than being it.
const CJS = (spec) =>
  `export const $module = require(${JSON.stringify(spec)});\n`;

const form = new Map(specs.map((s) => [s, ESM]));
// A specifier only `require` could resolve at all: it never goes back to ESM,
// because ESM is what already failed for it.
const forced = new Set();
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
// It is asked with EVERY entry in its ES shape, because that shape resolves both
// kinds: esbuild will happily `import * as` a CommonJS file, it just gives the
// wrong object. The probe wants the format, not the object.
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
      // A package whose "exports" map offers a `require` condition and no `import`
      // one: unreachable as ESM, and CommonJS by the only route it has left.
      if (form.get(spec) === ESM) { form.set(spec, CJS); forced.add(spec); progress++; }
      else { live.delete(spec); failed.push([spec, err.text.slice(0, 200)]); progress++; }
    }
    if (!progress) die("resolve", e.errors.map((x) => x.text).join("\n"));
  }
}

// The entry imports exactly one file - the package - so the first import it has is
// the one whose format decides the shape.
for (const [input, o] of Object.entries(meta.inputs)) {
  const spec = specOf(input);
  if (!spec || forced.has(spec)) continue;
  const imported = (o.imports || []).find((i) => i.kind === "import-statement");
  const target = imported && meta.inputs[imported.path];
  if (target && target.format === "cjs") form.set(spec, CJS);
}

// --- the build -----------------------------------------------------------------

// WHAT THE PROBE CANNOT ANSWER, THE BUILD COMPLAINS ABOUT. `require` of an ES
// module is refused when that module has a top-level await, and the probe never
// tried it, so the one specifier this can be wrong about is a CommonJS-shaped
// answer the real build will not take. Put it back in its ES shape and build
// again - the probe already proved that shape resolves.
let rounds = 0;
for (;;) {
  rounds++;
  try {
    const result = await esbuild.build(options({ outdir: join(outDir, "npm") }));
    const outs = Object.entries(result.metafile.outputs);
    const chunk = (p) => /chunk-[A-Z0-9]+\.js$/.test(p);
    const kinds = new Map([...live].sort()
                          .map((s) => [s, kw(form.get(s) === CJS ? "cjs" : "esm")]));
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
      if (form.get(spec) === CJS && !forced.has(spec)) { form.set(spec, ESM); progress++; }
      else { live.delete(spec); failed.push([spec, err.text.slice(0, 200)]); progress++; }
    }
    // NO PROGRESS IS THE END OF IT. Looping on an error the rule above cannot act
    // on would spin six times and say the same thing, so say it now.
    if (!progress) die("build", e.errors.map((x) => x.text).join("\n"));
  }
}
