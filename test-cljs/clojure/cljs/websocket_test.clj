;   Copyright (c) Rich Hickey. All rights reserved.
;   The use and distribution terms for this software are covered by the
;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;   which can be found in the file epl-v10.html at the root of this distribution.
;   By using this software in any fashion, you are agreeing to be bound by
;   the terms of this license.
;   You must not remove this notice, or any other, from this software.

(ns ^{:doc "The listener in clojure.cljs.websocket: who may connect, what the
  callbacks see, and what closing means.

  The framing underneath has its own tests in ws-test and is not re-checked here.
  What this namespace is about is the part that is ours - the token, the refusals,
  the three callbacks, and the two ways a page can leave.

  The client is again the JDK's own, so a browser's half of the handshake is a
  real one rather than one written to match."}
  clojure.cljs.websocket-test
  (:require [clojure.cljs.websocket :as ws]
            [clojure.test :refer [deftest is]])
  (:import [clojure.cljs.ws WebSocketConnection]
           [java.io ByteArrayOutputStream InputStream]
           [java.net Socket URI]
           [java.net.http HttpClient WebSocket WebSocket$Listener]
           [java.nio.charset StandardCharsets]
           [java.util.concurrent ExecutionException LinkedBlockingQueue TimeUnit]))

(def ^:private ms 10000)

(defn- took [^LinkedBlockingQueue q] (.poll q ms TimeUnit/MILLISECONDS))

(defn- client!
  "Connect to `port`, carrying `token` when there is one. Answers [ws messages
  closes] - two queues, one for whole text messages and one for the close code."
  ([port] (client! port nil))
  ([port token]
   (let [msgs   (LinkedBlockingQueue.)
         closes (LinkedBlockingQueue.)
         acc    (StringBuilder.)
         l      (reify WebSocket$Listener
                  (onText [_ socket data last?]
                    (.append acc data)
                    (when last?
                      (.offer msgs (.toString acc))
                      (.setLength acc 0))
                    (.request ^WebSocket socket 1)
                    nil)
                  (onClose [_ _ status _]
                    (.offer closes status)
                    nil))]
     [(-> (HttpClient/newHttpClient)
          (.newWebSocketBuilder)
          (.buildAsync (URI/create (str "ws://127.0.0.1:" port "/"
                                        (when token (str "?token=" token))))
                       l)
          (.get ms TimeUnit/MILLISECONDS))
      msgs closes])))

(defn- status-line
  "Speak `request` at `port` by hand and read back the first line of the answer."
  [port ^String request]
  (with-open [s (Socket. "127.0.0.1" (int port))]
    (.setSoTimeout s ms)
    (.write (.getOutputStream s) (.getBytes request StandardCharsets/US_ASCII))
    (.flush (.getOutputStream s))
    (let [^InputStream in (.getInputStream s)
          b (ByteArrayOutputStream.)]
      (loop []
        (let [c (.read in)]
          (cond (or (= -1 c) (= 10 c)) (.trim (.toString b "UTF-8"))
                :else                  (do (.write b c) (recur))))))))

;; --- the callbacks ----------------------------------------------------------

(deftest test-a-page-is-heard-and-can-be-spoken-to
  (let [heard (LinkedBlockingQueue.)]
    (with-open [srv (ws/websocket-server
                     {:on-text (fn [conn text]
                                 (.offer heard text)
                                 (.sendText ^WebSocketConnection conn (str "re:" text)))})]
      (let [[^WebSocket c msgs] (client! (:port srv))]
        (.get (.sendText c "hello" true) ms TimeUnit/MILLISECONDS)
        (is (= "hello" (took heard)) "what the page said reached :on-text")
        (is (= "re:hello" (took msgs)) "and the answer reached the page")))))

(deftest test-open-and-close-are-both-reported
  (let [events (LinkedBlockingQueue.)]
    (with-open [srv (ws/websocket-server
                     {:on-open  (fn [_] (.offer events :open))
                      :on-close (fn [_ code] (.offer events [:close code]))})]
      (let [[^WebSocket c] (client! (:port srv))]
        (is (= :open (took events)))
        (.get (.sendClose c WebSocket/NORMAL_CLOSURE "bye") ms TimeUnit/MILLISECONDS)
        (is (= [:close 1000] (took events)) "a page that says goodbye is 1000")))))

(deftest test-a-page-that-vanishes-is-abnormal
  ;; THE CASE A LONG-POLL CANNOT SEE, and the reason for all the silence-and-
  ;; timeout machinery it needs instead: here the socket reports itself.
  (let [events (LinkedBlockingQueue.)]
    (with-open [srv (ws/websocket-server {:on-close (fn [_ code] (.offer events code))})]
      (let [[^WebSocket c] (client! (:port srv))]
        (.abort c)                              ; no close frame, just gone
        (is (= 1006 (took events)))))))

(deftest test-the-server-knows-who-is-connected
  (with-open [srv (ws/websocket-server {})]
    (is (= [] (:connections srv)))
    (let [[^WebSocket a] (client! (:port srv))
          [^WebSocket b] (client! (:port srv))]
      ;; both handshakes are done, but :on-open runs on each connection's own
      ;; thread, so wait for the registration rather than assume it
      (loop [n 0]
        (when (and (< (count (:connections srv)) 2) (< n 100))
          (Thread/sleep 50)
          (recur (inc n))))
      (is (= 2 (count (:connections srv))))
      (.abort a)
      (.abort b))))

(deftest test-two-pages-are-independent
  (with-open [srv (ws/websocket-server
                   {:on-text (fn [conn text]
                               (.sendText ^WebSocketConnection conn (str "re:" text)))})]
    (let [[^WebSocket a msgs-a] (client! (:port srv))
          [^WebSocket b msgs-b] (client! (:port srv))]
      (.get (.sendText a "from-a" true) ms TimeUnit/MILLISECONDS)
      (.get (.sendText b "from-b" true) ms TimeUnit/MILLISECONDS)
      (is (= "re:from-a" (took msgs-a)))
      (is (= "re:from-b" (took msgs-b)) "neither answer went to the other page"))))

(deftest test-closing-the-server-says-goodbye
  ;; 1001, going away - so a page reports a clean close rather than an error, and
  ;; can tell "the REPL stopped" from "the network broke"
  (let [srv (ws/websocket-server {})
        [_ _ closes] (client! (:port srv))]
    (.close srv)
    (is (= 1001 (took closes)))))

;; --- who may connect --------------------------------------------------------

(deftest test-without-the-token-a-connection-is-refused
  (with-open [srv (ws/websocket-server {:token (ws/random-token)})]
    (is (thrown? ExecutionException (client! (:port srv)))
        "no token at all")
    (is (thrown? ExecutionException (client! (:port srv) "not-the-token"))
        "a wrong one")
    (is (= "HTTP/1.1 403 Forbidden" (status-line (:port srv)
                                                 (str "GET /?token=wrong HTTP/1.1\r\n"
                                                      "host: 127.0.0.1\r\n"
                                                      "upgrade: websocket\r\n"
                                                      "connection: Upgrade\r\n"
                                                      "sec-websocket-key: dGhlIHNhbXBsZSBub25jZQ==\r\n"
                                                      "sec-websocket-version: 13\r\n\r\n")))
        "and it is refused before the upgrade, not after")))

(deftest test-with-the-token-a-connection-is-let-through
  (let [token (ws/random-token)]
    (with-open [srv (ws/websocket-server {:token token})]
      (let [[^WebSocket c] (client! (:port srv) token)]
        (is (some? c))
        (.abort c)))))

(deftest test-a-request-that-is-not-a-handshake-is-answered
  ;; someone pointed a browser at the socket port. A dropped connection would be a
  ;; mystery in the console; a status line is not.
  (with-open [srv (ws/websocket-server {})]
    (is (= "HTTP/1.1 400 Missing or invalid Upgrade header"
           (status-line (:port srv) "GET / HTTP/1.1\r\nhost: 127.0.0.1\r\n\r\n")))))
