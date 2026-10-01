// The Node half of the REPL transport. doc/cljs-repl.md §6: node has native ESM
// and import() straight off the filesystem, so there is no asset server and no
// long-poll here - it dials the JVM on a socket and the whole transport is a
// reader and a writer.
//
// It is a separate file from runtime.js on purpose. runtime.js is the prelude and
// the evaluator, which every host shares; this is one host's way of being reached.
// The browser reuses the other file unchanged and replaces only this one.
//
// The wire, one line each way:
//
//   JVM -> here   a JSON string literal holding the script to evaluate
//   here -> JVM   an EDN map, {:type :result/:print/:uncaught/:notify :content "..."}
//
// Neither side parses its own hard format. The JVM writes JSON, which node reads
// with JSON.parse; node writes EDN, which the JVM reads with clojure.edn. Both
// formats escape newlines inside strings, so a line is a whole message.
//
// THE ENVELOPE IS THE BROWSER'S, and so is the reason for it: a print and the
// value of the form that printed it have to arrive in the order they happened,
// and they only can if they travel on one channel. They used to be two - the
// socket for the value, the process's stdout for the print, pumped by a thread of
// the JVM's - and which of them the JVM saw first was a race it lost often enough
// to notice.

import net from "node:net";
import { errorEdn, evaluate, print as printValue } from "./runtime.js";

// JSON.stringify of a string is a valid EDN string literal - the escapes EDN
// knows are a superset of the ones V8 emits - which is what lets a result travel
// inside an EDN map without a second escaping scheme.
function message(type, content) {
  return "{:type :" + type +
    (content === undefined ? "" : " :content " + JSON.stringify(content)) + "}";
}

const port = Number(process.argv[2]);
if (!Number.isInteger(port) || port <= 0) {
  console.error("usage: node runtime_node.js <port>");
  process.exit(2);
}

const socket = net.connect(port, "127.0.0.1");
socket.setEncoding("utf8");
socket.on("connect", () => {
  captureConsole();
  socket.write("{:type :ready}\n");
});

function send(s) {
  // A socket that closed between the print and this is not an error worth
  // raising: the REPL will have been told by the close itself.
  try {
    if (!socket.writable) return false;
    socket.write(s + "\n");
    return true;
  } catch (e) {
    return false;
  }
}

// What the program says unasked - see runtime_browser.js, which says the same.
globalThis.$CLJS.sendNotify = (content) => send(message("notify", String(content)));

// --- printing ---------------------------------------------------------------
//
// REPLACED, where the browser TEES. There the console has a second reader - the
// devtools panel, which is where a browser user looks first - so taking it away
// to feed a REPL would be a poor trade. Here the second reader is this process's
// stdout, which the JVM pumps into the very same place the :print channel goes:
// teeing would show every line twice.
//
// The originals are kept and used whenever the socket cannot take it, which is
// everything said before the connection and everything said after it broke -
// including the two messages below, which are the only reasons this file prints
// anything of its own.
function captureConsole() {
  if (console.__cljsCaptured__) return;
  console.__cljsCaptured__ = true;
  for (const name of ["log", "info", "warn", "error"]) {
    const original = console[name].bind(console);
    console[name] = function (...args) {
      let text;
      try {
        text = args.map((x) => typeof x === "string" ? x : printValue(x))
                   .join(" ") + "\n";
      } catch (e) {
        // a value whose printer threw is still a line the user asked for
        original(...args);
        return;
      }
      if (!send(message("print", text))) original(...args);
    };
  }
}

// --- what no turn owns -------------------------------------------------------
//
// An exception thrown out of a setTimeout callback, or a promise nobody caught,
// belongs to no evaluation: the form that scheduled the work answered long ago.
// Node's default for the first is to print it and EXIT, which under a REPL is the
// worst of both - the runtime disappears, and the next form you type reports a
// broken connection rather than the mistake that broke it.
//
// So both are taken and sent on the :uncaught channel. It is the same error result
// a form that throws produces, built by the same errorEdn, and that is deliberate:
// an error nobody was waiting for should read the way one that was reads, down to
// leaving what was thrown in *e.
//
// TAKING uncaughtException IS ALSO WHAT KEEPS THE PROCESS ALIVE, and that is a
// departure from node's default made on purpose. The browser is the argument: a
// page that throws in an event handler stays open, and a REPL whose two hosts
// disagree about whether a stray exception ends the session would be a REPL you
// could not reason about. Node's warning that state may be inconsistent after an
// uncaught exception is true and the answer to it is to restart the REPL - which
// is a choice you can only make if you are still there to make it.
function reportUncaught(e) {
  // console.error rather than nothing when the socket cannot take it: captureConsole
  // falls back to the original, so this lands on the process's stdout, which is the
  // channel the JVM pumps and the only one left before the connection or after it
  // broke.
  if (!send(message("uncaught", errorEdn(e)))) console.error(e);
}

process.on("uncaughtException", reportUncaught);
// BELT AND BRACES, and knowingly: node's default is --unhandled-rejections=throw,
// which raises the rejection's reason as an uncaught exception, so the handler
// above already takes it and a test that removes only this line sees no change.
// What this line buys is independence from that flag - under `warn` or `none` a
// dropped rejection would otherwise never reach the REPL at all - and the cost of
// it is one line.
process.on("unhandledRejection", reportUncaught);

// One turn at a time. Evaluation is async, so two lines arriving in one chunk
// would otherwise be evaluated concurrently and answered out of order - and the
// JVM matches answers to questions by position, having asked only one.
let turn = Promise.resolve();
let buf = "";

socket.on("data", (chunk) => {
  buf += chunk;
  let i;
  while ((i = buf.indexOf("\n")) >= 0) {
    const line = buf.slice(0, i);
    buf = buf.slice(i + 1);
    turn = turn
      .then(async () => send(message("result", await evaluate(JSON.parse(line)))))
      // evaluate does not throw, so this is about the line itself - a truncated
      // or unparseable one. Answering keeps the conversation in step; going quiet
      // would leave the JVM blocked on a read forever.
      .catch((e) => send(message(
        "result",
        '{:status :error :phase :transport :value ' +
          JSON.stringify(String((e && e.message) || e)) + "}")));
  }
});

// The JVM closing the socket is how the session ends; there is nothing else for
// this process to be doing.
socket.on("close", () => process.exit(0));
socket.on("error", (e) => {
  console.error("cljs runtime: " + e.message);
  process.exit(1);
});
