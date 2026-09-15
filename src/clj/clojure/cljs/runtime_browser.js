// The browser half of the REPL transport. doc/cljs-repl.md §6: the runtime cannot
// be dialled, so it dials out and holds the request open - the JVM answers it when
// it has something to evaluate, and the answer to the NEXT request carries the
// result. One request in flight is one REPL turn.
//
// It is a separate file from runtime.js on purpose, and the same separation node
// makes: runtime.js is the prelude and the evaluator, which every host shares;
// this is one host's way of being reached.
//
// The wire, adapted from Replique's and keeping its message shape:
//
//   here -> JVM   an EDN map, {:type :ready/:poll/:result/:print/:alive/:bye
//                 :session n :content "..."}, as the POST body
//   JVM -> here   the script to evaluate, as the response body - or JSON, for the
//                 one response that is not a script (:ready, which assigns the
//                 session number)
//
// Neither side parses its own hard format: the JVM reads EDN with clojure.edn and
// this reads JSON with JSON.parse. The rule node's transport follows, in the other
// direction.
//
// WHY THIS IS SO MUCH SMALLER THAN REPLIQUE'S CLIENT. Replique needs a
// pending-eval/after-load-hook handshake because a goog.require injects a <script>
// and finishes later, with no promise to await. Here loading is an expression
// (§5): evaluate() returns a promise that is already the whole turn, imports and
// all, so awaiting it is the entire mechanism.

import { evaluate, print as printValue } from "./runtime.js";

// --- the connection ---------------------------------------------------------

let url = null;
let session = null;
let stopped = false;

// JSON.stringify of a string is a valid EDN string literal - the escapes EDN knows
// are a superset of the ones V8 emits - which is what lets a result travel inside
// an EDN map without a second escaping scheme.
function message(type, content) {
  return "{:type :" + type +
    (session === null ? "" : " :session " + session) +
    (content === undefined ? "" : " :content " + JSON.stringify(content)) + "}";
}

// text/plain rather than application/edn, so that this stays a CORS "simple
// request" and a page served from the application's own origin can talk to the
// REPL without a preflight round trip on every turn.
function post(body) {
  return fetch(url, {
    method: "POST",
    headers: { "Content-Type": "text/plain" },
    body: body,
  });
}

function sleep(ms) {
  return new Promise((resolve) => setTimeout(resolve, ms));
}

// --- saying we are still here -----------------------------------------------
//
// THE ONE THING LONG-POLLING COSTS. A socket that closes tells the other end so;
// a long-poll has nothing open to break. Between the moment this page is handed a
// script and the moment it posts the result there is no request in flight at all,
// so a page that is closed, crashed or navigated away during an evaluation leaves
// the JVM waiting for an answer that has no one left to produce it - and waiting
// is exactly what it should do otherwise, because an evaluation may legitimately
// take minutes.
//
// So the liveness a socket would have given for free is sent by hand, and only in
// that window, where nothing else is being sent anyway.

const ALIVE_MS = 5000;

async function evaluateAlive(js) {
  const ping = setInterval(() => { post(message("alive")).catch(() => {}); },
                           ALIVE_MS);
  try {
    return await evaluate(js);
  } finally {
    clearInterval(ping);
  }
}

// And the clean case says so at once rather than being noticed by silence.
// sendBeacon is the one request a browser will still send while tearing the page
// down; a refresh fires this too, and the :bye that arrives late carries the old
// session number, which the JVM has already replaced and therefore ignores.
function sayGoodbye() {
  try {
    if (typeof navigator !== "undefined" && navigator.sendBeacon) {
      navigator.sendBeacon(url, message("bye"));
    }
  } catch (e) { /* leaving is not a thing that can fail */ }
}

// --- printing ---------------------------------------------------------------
//
// A browser has no stdout for the JVM to pump, so the :print channel is not
// optional here the way it is under node (§8). Before M5 there is no *print-fn* to
// set, so what there is to forward is the console - and it is TEE'd rather than
// replaced, because the devtools console is where a browser user looks first and
// taking it away to feed a REPL would be a poor trade.
//
// Queued and sent one at a time: printing must not interleave two POSTs onto one
// connection, and it must never be awaited by the turn that caused it.

const printQueue = [];
let flushing = false;

function flushPrints() {
  const s = printQueue.shift();
  if (s === undefined) { flushing = false; return; }
  post(message("print", s)).catch(() => {}).then(flushPrints);
}

export function sendPrint(s) {
  printQueue.push(s);
  if (!flushing) { flushing = true; flushPrints(); }
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

// --- the loop ---------------------------------------------------------------

// A dropped request ends the session rather than being retried, and that is a
// decision rather than laziness: the JVM offers the result to a waiting evaluation
// the moment the POST arrives, so a request that failed on the way back has
// already been delivered - re-sending it would answer the NEXT evaluation with the
// previous one's value, and the REPL would print every answer one turn late
// forever. Reconnecting says the honest thing instead: this session is over, and
// the JVM unblocks whoever was waiting with "Connection broken".
async function reconnect() {
  if (stopped) return;
  await sleep(1000);
  if (!stopped) connect(url);
}

async function run(mySession) {
  let content;                  // undefined on the first turn: nothing to report
  while (!stopped && session === mySession) {
    let res;
    try {
      res = await post(message(content === undefined ? "poll" : "result", content));
    } catch (e) {
      return reconnect();
    }
    content = undefined;
    if (res.status === 409) {
      // another page took the session over. Retrying would be two runtimes
      // fighting over one REPL, so this one steps aside and says how to come back.
      stopped = true;
      console.log("ClojureScript REPL: this page's session expired. To reconnect:"
                  + '\n  (await import("' + url + 'runtime_browser.js")).connect()');
      return;
    }
    if (res.status === 204) continue;   // the idle heartbeat: no work yet
    if (!res.ok) return reconnect();
    content = await evaluateAlive(await res.text());
  }
}

// The URL defaults to the directory this module was served from, which is the
// output root and therefore the REPL server - so a page that imports it over the
// network needs no configuration at all, and a page on the application's own
// origin needs no more than the import.
export async function connect(u) {
  url = u || new URL(".", import.meta.url).href;
  stopped = false;
  session = null;
  teeConsole();
  if (!globalThis.__cljsGoodbye__ && typeof addEventListener === "function") {
    globalThis.__cljsGoodbye__ = true;
    addEventListener("pagehide", sayGoodbye);
  }
  for (;;) {
    try {
      const res = await post(message("ready"));
      if (res.ok) {
        session = (await res.json()).session;
        run(session);
        return url;
      }
    } catch (e) { /* the JVM is not listening yet */ }
    await sleep(1000);
  }
}

export function disconnect() {
  stopped = true;
}

globalThis.$CLJS.connect = connect;
