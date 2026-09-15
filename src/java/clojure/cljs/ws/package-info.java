/**
 *   Copyright (c) Thomas Heller. All rights reserved.
 *   The use and distribution terms for this software are covered by the
 *   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
 *   which can be found in the file epl-v10.html at the root of this distribution.
 *   By using this software in any fashion, you are agreeing to be bound by
 * 	 the terms of this license.
 *   You must not remove this notice, or any other, from this software.
 **/

/**
 * RFC 6455 server framing, so the browser transport can be a socket rather than a
 * long-poll. doc/cljs-repl.md 6.
 *
 * <h2>Where this came from</h2>
 *
 * shadow-http 0.1.8 ({@code com.thheller/shadow-http}), the HTTP server Thomas
 * Heller wrote to get Undertow out of shadow-cljs and which shadow-cljs 3.4.x runs
 * its REPL relay over. Taken as source rather than as a dependency because the
 * dependency is a whole HTTP server - it would bring a second asset-serving path
 * beside {@code com.sun.net.httpserver}, which this fork already uses and whose
 * ETag/304 handling is not a transport concern - and because the part that is hard
 * to write is small enough to carry.
 *
 * EPL 1.0, the same licence as this fork. The upstream files carry no per-file
 * notice; the headers here were added.
 *
 * <h2>What was changed, and how to take a newer version</h2>
 *
 * EIGHT OF THE NINE LIFTED FILES ARE BYTE-IDENTICAL TO UPSTREAM apart from the
 * {@code package} line and the notice above, which is the property worth keeping:
 * re-syncing is a diff, not a merge. Before editing one of them, consider whether
 * the change belongs upstream instead.
 *
 * Two files are ours:
 *
 * <ul>
 * <li>{@link clojure.cljs.ws.Connection} is narrowed to the two methods
 *     {@link clojure.cljs.ws.WebSocketExchange} actually calls - it wants somewhere
 *     to write and a way to ask whether the socket is still there. Upstream's also
 *     declares {@code getServer}, {@code isSecure}, {@code getRemoteAddress},
 *     {@code getInputStream} and {@code upgrade(Exchange)}, and those five were the
 *     whole of the coupling to the rest of that server.
 * <li>{@link clojure.cljs.ws.WebSocketUpgrade} is upstream's
 *     {@code HttpRequest.upgradeToWebSocket} taken out of the request object and
 *     given a header lookup instead, so that whoever read the request line off the
 *     socket supplies it.
 * </ul>
 *
 * Nothing else is referenced. The package compiles against an empty classpath, and
 * uses only {@code java.io}, {@code java.lang}, {@code java.nio.charset},
 * {@code java.security}, {@code java.util}, {@code java.util.concurrent.locks},
 * {@code java.util.function} and {@code java.util.zip} - base module throughout, no
 * NIO channels, no Unsafe, no JNA.
 *
 * <h2>Two things that will bite</h2>
 *
 * THE HANDSHAKE AND THE FIRST FRAME SHARE A BUFFER. Whoever reads the request
 * headers must hand {@link clojure.cljs.ws.WebSocketExchange} the same
 * {@code InputStream} it read them with: a buffered reader will already have pulled
 * bytes past the blank line, and those bytes are the first frame. This is also why
 * {@code com.sun.net.httpserver} cannot be upgraded in place - it owns that buffer
 * and will not give it up - and why the socket needs a listener of its own.
 *
 * {@code WebSocketExchange.MAX_FRAME_SIZE} IS NOT A CAP. It is the outgoing
 * fragmentation threshold: a message above it is split into continuation frames
 * automatically, so shipping a multi-megabyte script is fine. The incoming limit is
 * {@code WebSocketInput.MAX_PAYLOAD_LENGTH}, 16 MB, and it is per frame; an
 * assembled fragmented message is not bounded, which is acceptable only because
 * this listens on the loopback interface and the peer is the developer's own page.
 *
 * <h2>Compression</h2>
 *
 * {@link clojure.cljs.ws.PerMessageDeflate} negotiates what Chrome and Firefox
 * actually offer. It is optional in the sense that matters: pass a null context and
 * the extension is simply declined, which is what {@code negotiate(null)} already
 * answers, and no caller changes.
 */
package clojure.cljs.ws;
