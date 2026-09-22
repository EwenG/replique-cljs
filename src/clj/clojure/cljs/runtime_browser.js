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

import { errorEdn, evaluate, print as printValue } from "./runtime.js";

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
// optional here the way it is under node (§8). Before M5 there is no *print-fn* to
// set, so what there is to forward is the console - and it is TEE'd rather than
// replaced, because the devtools console is where a browser user looks first and
// taking it away to feed a REPL would be a poor trade.
//
// No queue any more. Two POSTs needed one, because they were two connections that
// could arrive in either order; two frames on one socket cannot.

export function sendPrint(s) {
  send(message("print", s));
}

function teeConsole() {
  if (console.__cljsTee__) return;      // connect() may be called more than once
  console.__cljsTee__ = true;
  for (const name of ["log", "info", "warn", "error"]) {
    const original = console[name].bind(console);
    console[name] = function (...args) {
      original(...args);
      try {
        sendPrint(args.map((x) => typeof x === "string" ? x : printValue(x))
                      .join(" ") + "\n");
      } catch (e) { /* a REPL that is not there is not a reason to lose the log */ }
    };
  }
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

// NOTHING IS PREVENTED, which is teeConsole's trade again: the devtools console is
// where a browser user looks first, and a REPL that swallowed an uncaught error to
// report it elsewhere would be taking away the better of the two reports.
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
    let content;
    try {
      content = await evaluate(js);
    } catch (e) {
      // evaluate() answers errors rather than throwing them, so reaching here
      // means the transport itself broke. Say so rather than leaving the JVM to
      // wait for an answer that is not coming.
      content = '{:status :error :value "' + String(e && e.message) + '"}';
    }
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
  teeConsole();
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
