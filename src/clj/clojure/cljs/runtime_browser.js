// The browser half of the REPL transport. doc/cljs-repl.md §6: a websocket, which
// the JVM writes to when it has something to evaluate and this answers on.
//
// It is a separate file from runtime.js on purpose, and the same separation node
// makes: runtime.js is the prelude and the evaluator, which every host shares;
// this is one host's way of being reached.
//
// The wire:
//
//   here -> JVM   an EDN map, {:type :result/:print/:uncaught :content "..."}
//   JVM -> here   the script to evaluate, as the frame's text, and nothing else
//
// Neither side parses its own hard format: the JVM reads EDN with clojure.edn and
// this writes it with JSON.stringify, whose string escapes EDN understands. The
// rule node's transport follows, in the other direction.
//
// WHAT A SOCKET REMOVED, all of it machinery that existed to imitate one:
//
//   the poll, the 204 heartbeat and the request that had to be in flight for the
//   JVM to have somewhere to write;
//
//   the session number, because the connection is the session - a refresh closes
//   this socket before it opens the next one, so the two can never be confused;
//
//   the 5-second :alive ping and the :bye beacon, because a socket that closes
//   says so, and one that dies without closing is found by the JVM's ping.
//
// WHAT IT FIXED. A print and the result of the form that printed it used to be two
// POSTs on two connections, in no particular order; they are now two messages on
// one socket, in the order they happened.
//
// WHY THIS IS SO MUCH SMALLER THAN REPLIQUE'S CLIENT. Replique needs a
// pending-eval/after-load-hook handshake because a goog.require injects a <script>
// and finishes later, with no promise to await. Here loading is an expression
// (§5): evaluate() returns a promise that is already the whole turn, imports and
// all, so awaiting it is the entire mechanism.

import { errorEdn, evaluate, munge } from "./runtime.js";

// --- the connection ---------------------------------------------------------

let base = null;
let socket = null;
let stopped = false;

// JSON.stringify of a string is a valid EDN string literal - the escapes EDN knows
// are a superset of the ones V8 emits - which is what lets a result travel inside
// an EDN map without a second escaping scheme.
function message(type, content) {
  return "{:type :" + type +
    (content === undefined ? "" : " :content " + JSON.stringify(content)) + "}";
}

function send(s) {
  // A socket that closed between the print and this is not an error worth
  // raising: the REPL will have been told by the close itself.
  try {
    if (socket && socket.readyState === 1) socket.send(s);
  } catch (e) { /* gone */ }
}

function sleep(ms) {
  return new Promise((resolve) => setTimeout(resolve, ms));
}

// --- printing ---------------------------------------------------------------
//
// A browser has no stdout for the JVM to pump, so the :print channel is not
// optional here the way it is under node (§8). What fills it is cljs.core's
// *print-fn*, which is the channel's own name for itself: a println is a program
// saying something to whoever reads its output, and under a REPL that is the REPL.
//
// IT USED TO BE THE CONSOLE, TEE'd, because before cljs.core was vendored there was
// no *print-fn* to set and the console was the only thing there was to forward.
// That made ONE WIRE OUT OF TWO DIFFERENT THINGS. A console.log is a program
// talking to the BROWSER: devtools shows it against the line that produced it, with
// the object itself rather than a printed copy of it, expandable - and a page's own
// logging is not something a REPL asked for. On an application of any size it is
// most of what there is, so a REPL that forwarded it was a REPL whose output buffer
// was mostly somebody else's. It stays in the console now, where it was going
// anyway, and only what a program prints deliberately travels.
//
// No queue any more. Two POSTs needed one, because they were two connections that
// could arrive in either order; two frames on one socket cannot.

export function sendPrint(s) {
  send(message("print", s));
}

// The three vars, under the names a property lookup needs. munge is the compiler's
// own, imported rather than spelt, so these cannot drift from what the emitter
// wrote: `*print-fn*' is a property of the cljs.core namespace object like any
// other var (doc/cljs-repl.md §3.1), and dynamic changes nothing about that.
const PRINT_FN = munge("*print-fn*");
const PRINT_ERR_FN = munge("*print-err-fn*");
const PRINT_NEWLINE = munge("*print-newline*");

// What cljs.core hands a *print-fn* is the pieces of one print, already strings.
function printToRepl(...args) {
  sendPrint(args.join(""));
}

// *print-newline* goes back to true with them, and that is not a detail:
// `enable-console-print!' turns it off because console.log ends a line by itself,
// and a socket does not. Without this every println arrives glued to the next one.
function setPrint() {
  const core = globalThis.$CLJS.namespaces.get("cljs.core");
  // The namespace OBJECT exists from the prelude on - runtime.js publishes
  // globalThis.cljs = { core: ns("cljs.core") } before anything is loaded - so what
  // says cljs.core has RUN is one of its vars being there.
  if (!core || !(PRINT_FN in core) || core[PRINT_FN] === printToRepl) return;
  core[PRINT_FN] = printToRepl;
  core[PRINT_ERR_FN] = printToRepl;
  core[PRINT_NEWLINE] = true;
}

// REQUIRED here rather than waited for. cljs.core installs the console on ITSELF as
// it loads - `maybe-enable-print!' calls `enable-console-print!' wherever there is a
// js/console, which is every browser - so this has to happen after cljs.core has
// run, and something has to make sure it does. Waiting for a namespace to go past
// would lose exactly one println: the first, because the script carrying the first
// form somebody types opens by requiring cljs.core (§5.12) and prints in the same
// breath.
//
// Idempotent, and cheap when it is not the first: require_ answers a namespace
// already loaded with null rather than fetching it again.
//
// A failure is not one. A page may connect before anything has been compiled into
// the directory it would fetch from, and the two ends of every turn try again.
async function installPrint() {
  try { await globalThis.$CLJS.require("cljs.core"); }
  catch (e) { /* not there yet; the next turn is another chance */ }
  setPrint();
}

// --- what no turn owns -------------------------------------------------------
//
// An exception out of a setTimeout callback, an error in an event handler, a
// promise nobody caught: none of them belongs to an evaluation, because the form
// that scheduled the work answered long ago. A browser reports these through its
// own error-reporting path and NOT by calling console.error, so the tee above does
// not see them - which is why they need a hook of their own.
//
// Whatever is sent is the same error result a form that throws produces, built by
// the same errorEdn, and that is deliberate: an error nobody was waiting for should
// read the way one that was reads, down to leaving what was thrown in *e.
//
// EXPORTED, and not only for symmetry with connect: the host is what decides where
// these arrive from, and a page that already has an error reporter of its own can
// hand this what it caught instead of letting the events do it.

export function reportUncaught(e) {
  send(message("uncaught", errorEdn(e)));
}

// NOTHING IS PREVENTED, and this is the one place a page's own reporting is still
// listened to. An uncaught error is not console output - a browser reports one
// through its own path and NOT by calling console.error - so taking the console out
// of the print channel does not take this with it, and it should not: an exception
// out of an event handler, in a tab with no devtools open, is the thing a developer
// is least able to see for themselves. Listened to rather than intercepted: the
// browser's own report of it is the better of the two, and it is left alone.
function watchUncaught() {
  if (globalThis.__cljsUncaught__) return;   // connect() may be called more than once
  // A host that has no events to listen to is not a browser - node, under the
  // tests, which reaches this file for the wire and not for this - and there is
  // nothing here it could be given.
  if (typeof addEventListener !== "function") return;
  globalThis.__cljsUncaught__ = true;
  // ev.error is null for an error thrown by a cross-origin script, where all the
  // browser will say is "Script error."; that string is better than silence.
  addEventListener("error", (ev) => reportUncaught(ev.error || ev.message));
  addEventListener("unhandledrejection", (ev) => reportUncaught(ev.reason));
}

// --- the loop ---------------------------------------------------------------

// One script at a time, and the chain is what guarantees it: the JVM serialises
// evaluations at its end, so nothing should overlap here either - but a socket
// will happily deliver a second frame while the first is still being awaited, and
// two evaluations interleaved would answer each other's turns.
let turn = Promise.resolve();

function onScript(js) {
  turn = turn.then(async () => {
    // Both ends of the turn, because either can be the one that made it possible:
    // cljs.core may have been loaded by the page between two forms, or by this form
    // itself - and a form that loads it is a form that may print through it.
    setPrint();
    let content;
    try {
      content = await evaluate(js);
    } catch (e) {
      // evaluate() answers errors rather than throwing them, so reaching here
      // means the transport itself broke. Say so rather than leaving the JVM to
      // wait for an answer that is not coming.
      content = '{:status :error :value "' + String(e && e.message) + '"}';
    }
    setPrint();
    send(message("result", content));
  });
}

// Where to dial. The output directory is served by the asset server and this file
// came from it, so the module's own URL locates a small file the JVM wrote there
// with the socket's port and the token that gets past it.
async function wsUrl() {
  const res = await fetch(new URL("cljs-repl.json", base).href, { cache: "no-store" });
  if (!res.ok) throw new Error("no REPL info at " + base);
  return (await res.json()).ws;
}

function open(url) {
  socket = new WebSocket(url);
  socket.onmessage = (e) => onScript(e.data);
  socket.onclose = () => {
    socket = null;
    // RECONNECTING IS SAFE HERE IN A WAY IT WAS NOT OVER THE LONG-POLL, where a
    // request that failed on the way back might already have been delivered and
    // re-sending would have answered the next evaluation with this one's value.
    // A close loses nothing: the JVM ends every evaluation the connection owned.
    if (!stopped) sleep(1000).then(() => { if (!stopped) connect(base); });
  };
}

// The URL defaults to the directory this module was served from, which is the
// output root and therefore the REPL server - so a page that imports it over the
// network needs no configuration at all, and a page on the application's own
// origin needs no more than the import.
export async function connect(u) {
  base = u || new URL(".", import.meta.url).href;
  stopped = false;
  await installPrint();
  watchUncaught();
  for (;;) {
    try {
      open(await wsUrl());
      return base;
    } catch (e) { /* the JVM is not listening yet */ }
    await sleep(1000);
  }
}

export function disconnect() {
  stopped = true;
  if (socket) socket.close(1000, "disconnect");
  socket = null;
}

globalThis.$CLJS.connect = connect;
