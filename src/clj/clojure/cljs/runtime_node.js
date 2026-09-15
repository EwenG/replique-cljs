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
//   here -> JVM   the EDN map runtime.js/evaluate returns
//
// Neither side parses its own hard format. The JVM writes JSON, which node reads
// with JSON.parse; node writes EDN, which the JVM reads with clojure.edn. Both
// formats escape newlines inside strings, so a line is a whole message.

import net from "node:net";
import { evaluate } from "./runtime.js";

const port = Number(process.argv[2]);
if (!Number.isInteger(port) || port <= 0) {
  console.error("usage: node runtime_node.js <port>");
  process.exit(2);
}

const socket = net.connect(port, "127.0.0.1");
socket.setEncoding("utf8");
socket.on("connect", () => socket.write("{:type :ready}\n"));

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
      .then(async () => socket.write((await evaluate(JSON.parse(line))) + "\n"))
      // evaluate does not throw, so this is about the line itself - a truncated
      // or unparseable one. Answering keeps the conversation in step; going quiet
      // would leave the JVM blocked on a read forever.
      .catch((e) => socket.write(
        '{:status :error :phase :transport :value ' +
          JSON.stringify(String((e && e.message) || e)) + "}\n"));
  }
});

// The JVM closing the socket is how the session ends; there is nothing else for
// this process to be doing.
socket.on("close", () => process.exit(0));
socket.on("error", (e) => {
  console.error("cljs runtime: " + e.message);
  process.exit(1);
});
