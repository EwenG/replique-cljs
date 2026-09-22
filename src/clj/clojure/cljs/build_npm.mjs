// The npm/ tree: built here, named by the compiler.
//
//   node build_npm.mjs --esbuild=<path> --entries=<dir> --report=<file> \
//                      [--dev] <out-dir> <specifier-list-file>
//
// clojure.cljs.npm schedules this; doc/cljs-npm.md 6 is why it exists at all and
// doc/cljs-output-layout.md is where the paths come from. Everything this writes
// lands at `<out-dir>/npm/<specifier>.js`, which is output/js->path's answer
// stated a second time - by --outbase and --outdir rather than by a table, so
// there is no mapping here to drift out of step with that one.
//
// ONE node PROCESS, and that is a finding rather than a preference: only node's
// loader knows what names a CommonJS package exports - esbuild cannot see them,
// and `export * from "react"` bundles to a module with no exports at all,
// silently. So enumeration has to happen on node, and since esbuild has a
// JavaScript API the bundling may as well happen beside it. The alternative was a
// pipeline the compiler orchestrates, which is two processes and a wire format
// for no gain.
//
// IT REPORTS IN EDN, written to --report. The JVM half of this has no JSON reader
// and does not want one for six fields; EDN it can read with clojure.edn, which is
// in core. The file is written whether the build worked or not, so a failure is a
// sentence rather than an exit code.
import { writeFileSync, mkdirSync, rmSync, readFileSync } from "node:fs";
import { dirname, join, relative } from "node:path";
import { createRequire } from "node:module";
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
// class: `:esbuild` says how a package was enumerated, `"esbuild"` would be a
// package of that name. Everything else EDN needs is JavaScript's own - a JSON
// string is a valid EDN string, escapes included.
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

// --- enumerating what a package exports ---------------------------------------

const req = createRequire(join(entryDir, "anchor.js"));

const IDENT = /^[A-Za-z_$][A-Za-z0-9_$]*$/;
const RESERVED = new Set(["default","import","export","class","function","var","let","const","new","delete","typeof","in","of","do","if","else","return","this","null","true","false","await","yield","super","case","catch","try","throw","void","with","while","for","switch","break","continue","debugger","enum","extends","instanceof"]);
// esbuild's own CommonJS interop marker. require() reports it as an export
// because it IS a property of module.exports; it is never a real name, and a
// dual package's ESM half does not have it.
const INTEROP = new Set(["__esModule"]);

function usable(keys) {
  return keys.filter((k) => IDENT.test(k) && !RESERVED.has(k) && !INTEROP.has(k));
}

// ASKED OF ESBUILD FIRST, AND WITHOUT RUNNING ANYTHING. `export * from "x"`
// re-exports an ES module's named exports, and esbuild's metafile then lists what
// the output ended up exporting - which is the same resolver and the same
// conditions the real build will use, so there is nothing to reconcile
// afterwards. It also never EXECUTES the package: lottie-light-react touches
// `document` the moment it is loaded, so enumerating it by importing it fails on
// a machine that has no DOM, which is every machine this runs on.
//
// It says nothing about a CommonJS package - `export *` from one yields no names
// at all, silently - so node answers for those, and node executing them is a cost
// only they pay. That order is the correction Stage 1 made to Stage 0's plan:
// esbuild is the authority and node is the fallback, not the other way round.
const probeDir = join(entryDir, ".probe");

async function esbuildExports(specs) {
  rmSync(probeDir, { recursive: true, force: true });
  const byEntry = new Map();
  for (const spec of specs) {
    const p = join(probeDir, spec + ".js");
    mkdirSync(dirname(p), { recursive: true });
    writeFileSync(p, `export * from ${JSON.stringify(spec)};\n`);
    byEntry.set(p, spec);
  }
  const out = new Map();
  // ONE AT A TIME: a probe that cannot resolve must not take the other ninety
  // with it. This is the slow half of the run and it is the price of finding out
  // which specifier is the broken one.
  for (const [p, spec] of byEntry) {
    try {
      const r = await esbuild.build({
        entryPoints: [p], outbase: probeDir, outdir: join(probeDir, "out"),
        bundle: true, format: "esm", platform: "browser", write: false,
        define: { "process.env.NODE_ENV": '"production"' },
        logLevel: "silent", metafile: true,
      });
      const o = Object.values(r.metafile.outputs)[0];
      out.set(spec, usable(o && o.exports ? o.exports : []));
    } catch (_) {
      out.set(spec, null);   // null = esbuild could not even resolve it
    }
  }
  rmSync(probeDir, { recursive: true, force: true });
  return out;
}

async function describe(spec, fromEsbuild) {
  if (fromEsbuild && fromEsbuild.length) {
    return { how: "esbuild", named: fromEsbuild, hasDefault: true };
  }
  try {
    const ns = await import(spec);
    return { how: "import", named: usable(Object.keys(ns)), hasDefault: true };
  } catch (e1) {
    try {
      const m = req(spec);
      const keys = (m && typeof m === "object") ? Object.keys(m) : [];
      return { how: "require", named: usable(keys), hasDefault: true };
    } catch (e2) {
      if (fromEsbuild === null) {
        return { how: "FAILED", err: `unresolvable: ${e2.code || String(e2.message).slice(0, 80)}` };
      }
      // esbuild resolves it and it has no named exports: a CommonJS module whose
      // whole API is its default, or one node will not load. Either way the
      // default alone is a true answer.
      return { how: "default-only", named: [], hasDefault: true };
    }
  }
}

// --- the entries -------------------------------------------------------------

// BESIDE THE PROJECT'S node_modules, not under the output directory, and that is
// not a tidiness choice: esbuild resolves a bare specifier from the importing
// file's own directory upwards, so an entry written into an output tree that
// happens to sit outside the project finds no node_modules and nothing resolves
// at all. The caller puts this under <project>/node_modules/.cache for that
// reason.
function entryPath(spec) { return join(entryDir, spec + ".js"); }

function writeEntry(spec, d) {
  const lines = [];
  if (d.named.length) lines.push(`export { ${d.named.join(", ")} } from ${JSON.stringify(spec)};`);
  if (d.hasDefault)   lines.push(`export { default } from ${JSON.stringify(spec)};`);
  const p = entryPath(spec);
  mkdirSync(dirname(p), { recursive: true });
  writeFileSync(p, lines.join("\n") + "\n");
  return p;
}

let specs;
try {
  specs = readFileSync(listFile, "utf8").split("\n").map((s) => s.trim()).filter(Boolean);
} catch (e) {
  die("no-list", e && e.message);
}

rmSync(entryDir, { recursive: true, force: true });
mkdirSync(entryDir, { recursive: true });

const probed = await esbuildExports(specs);
const desc = new Map(), failed = [], kinds = new Map();
for (const spec of specs) {
  const d = await describe(spec, probed.get(spec));
  if (d.how === "FAILED") { failed.push([spec, d.err]); continue; }
  kinds.set(spec, kw(d.how));
  desc.set(spec, d);
  writeEntry(spec, d);
}

// --- the build ---------------------------------------------------------------

// ESBUILD IS THE AUTHORITY, and this loop is how it gets asked. node's require()
// reports a DUAL package's CommonJS half while esbuild resolves its ESM half, so
// the two disagree about which names exist and about whether there is a default.
// Rather than model the difference, build and read the complaint: every error is
// of the form `No matching export in "..." for import "NAME"`, and it names the
// entry it came from. Drop exactly those names and build again. Over 91 real
// specifiers it converges in two rounds and drops ninety-nine names, which is
// better than modelling it - esbuild's complaint is by definition its own view,
// so there is nothing left to be wrong about.
const MATCH = /No matching export in .* for import "([^"]+)"/;
let round = 0, dropped = 0;
for (;;) {
  round++;
  try {
    const result = await esbuild.build({
      entryPoints: [...desc.keys()].map(entryPath),
      outbase: entryDir, outdir: join(outDir, "npm"),
      bundle: true, format: "esm", splitting: true, platform: "browser",
      // NOT optional: without it esbuild defaults NODE_ENV to "development" for
      // the browser platform and silently bundles React's development build -
      // 83KB against 14KB, and no error either way.
      define: { "process.env.NODE_ENV": dev ? '"development"' : '"production"' },
      logLevel: "silent", metafile: true,
    });
    const outs = Object.entries(result.metafile.outputs);
    const chunk = (p) => /chunk-[A-Z0-9]+\.js$/.test(p);
    rmSync(entryDir, { recursive: true, force: true });
    report({
      ok: true,
      // relative to the output root, which is the spelling js->path uses and the
      // one the caller prunes a later build against
      outputs: outs.map(([p]) => relative(outDir, p).split("\\").join("/")).sort(),
      modules: outs.filter(([p]) => !chunk(p)).length,
      chunks: outs.filter(([p]) => chunk(p)).length,
      bytes: outs.reduce((n, [, o]) => n + o.bytes, 0),
      rounds: round,
      dropped: dropped,
      dev: dev,
      kinds: kinds,
      failed: failed,
      // EXIT 0 EVEN WITH FAILURES IN IT. The bundle was written; a specifier that
      // could not be enumerated is a sentence in the report, and the caller is
      // going to ask output/missing-js which files are actually there anyway. A
      // non-zero exit here means only that there is nothing worth reading.
    }, 0);
  } catch (e) {
    if (!e.errors || round > 6) {
      die("build", (e.errors || []).map((x) => x.text).join("\n") || (e && e.message));
    }
    let progress = 0;
    for (const err of e.errors) {
      const m = MATCH.exec(err.text);
      if (!m || !err.location) continue;
      const spec = relative(entryDir, join(process.cwd(), err.location.file)).replace(/\.js$/, "");
      const d = desc.get(spec);
      if (!d) continue;
      if (m[1] === "default") {
        if (d.hasDefault) { d.hasDefault = false; progress++; dropped++; }
      } else {
        const i = d.named.indexOf(m[1]);
        if (i >= 0) { d.named.splice(i, 1); progress++; dropped++; }
      }
      writeEntry(spec, d);
    }
    // NO PROGRESS IS THE END OF IT. Looping on an error the rule above cannot
    // act on would spin six times and say the same thing, so say it now.
    if (!progress) die("build", e.errors.map((x) => x.text).join("\n"));
  }
}
