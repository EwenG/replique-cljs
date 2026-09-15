/**
 *   Copyright (c) Thomas Heller. All rights reserved.
 *   The use and distribution terms for this software are covered by the
 *   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
 *   which can be found in the file epl-v10.html at the root of this distribution.
 *   By using this software in any fashion, you are agreeing to be bound by
 * 	 the terms of this license.
 *   You must not remove this notice, or any other, from this software.
 *
 *   Extracted from shadow-http 0.1.8's HttpRequest.upgradeToWebSocket, so
 *   that the handshake depends on a header lookup rather than on that
 *   server's request object. See package-info.java.
 **/

package clojure.cljs.ws;

import java.io.IOException;
import java.io.OutputStream;
import java.nio.charset.StandardCharsets;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.Base64;
import java.util.function.Function;

/**
 * The RFC 6455 opening handshake, lifted out of shadow-http's HttpRequest so that
 * it depends on a header lookup rather than on that server's request object.
 *
 * `headers` answers a LOWERCASED field name with its value, or null. Whoever read
 * the request line and headers off the socket supplies it.
 */
public class WebSocketUpgrade {

    public static final String WEBSOCKET_GUID = "258EAFA5-E914-47DA-95CA-C5AB0DC85B11";

    public static String computeAcceptKey(String wsKey) throws NoSuchAlgorithmException {
        MessageDigest sha1 = MessageDigest.getInstance("SHA-1");
        byte[] hash = sha1.digest((wsKey + WEBSOCKET_GUID).getBytes(StandardCharsets.US_ASCII));
        return Base64.getEncoder().encodeToString(hash);
    }

    /**
     * Validate the request, write the 101, and answer the negotiated
     * permessage-deflate context - or null, which is the ordinary case.
     *
     * The caller must not have consumed anything past the blank line ending the
     * request headers, and must hand WebSocketExchange the SAME InputStream it
     * read them with: a buffered reader will have pulled bytes past the headers,
     * and those bytes are the first frame.
     */
    public static PerMessageDeflate accept(Function<String, String> headers,
                                           OutputStream out,
                                           String subProtocol) throws IOException {
        String upgrade = headers.apply("upgrade");
        if (upgrade == null || !upgrade.equalsIgnoreCase("websocket")) {
            throw new IllegalStateException("Missing or invalid Upgrade header");
        }

        String connection = headers.apply("connection");
        if (connection == null || !connection.toLowerCase().contains("upgrade")) {
            throw new IllegalStateException("Missing or invalid Connection header");
        }

        String wsKey = headers.apply("sec-websocket-key");
        if (wsKey == null || wsKey.isEmpty()) {
            throw new IllegalStateException("Missing Sec-WebSocket-Key header");
        }

        String wsVersion = headers.apply("sec-websocket-version");
        if (!"13".equals(wsVersion)) {
            throw new IllegalStateException("Unsupported WebSocket version: " + wsVersion);
        }

        try {
            String acceptKey = computeAcceptKey(wsKey);
            PerMessageDeflate pmd = PerMessageDeflate.negotiate(headers.apply("sec-websocket-extensions"));

            StringBuilder sb = new StringBuilder();
            sb.append("HTTP/1.1 101 Switching Protocols\r\n");
            sb.append("connection: Upgrade\r\n");
            sb.append("upgrade: websocket\r\n");
            sb.append("sec-websocket-accept: ").append(acceptKey).append("\r\n");
            if (pmd != null) {
                sb.append("sec-websocket-extensions: ").append(pmd.buildResponseHeaderValue()).append("\r\n");
            }
            if (subProtocol != null && !subProtocol.isEmpty()) {
                sb.append("sec-websocket-protocol: ").append(subProtocol).append("\r\n");
            }
            sb.append("\r\n");

            out.write(sb.toString().getBytes(StandardCharsets.US_ASCII));
            out.flush();
            return pmd;
        } catch (NoSuchAlgorithmException e) {
            throw new IOException("SHA-1 not available", e);
        }
    }
}
