/**
 *   Copyright (c) Thomas Heller. All rights reserved.
 *   The use and distribution terms for this software are covered by the
 *   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
 *   which can be found in the file epl-v10.html at the root of this distribution.
 *   By using this software in any fashion, you are agreeing to be bound by
 * 	 the terms of this license.
 *   You must not remove this notice, or any other, from this software.
 *
 *   From shadow-http 0.1.8. Unmodified but for the package line -
 *   see package-info.java before editing.
 **/

package clojure.cljs.ws;

import java.io.IOException;

public interface WebSocketConnection {

    boolean isOpen();

    void sendText(String text) throws IOException;

    void sendBinary(byte[] bytes, int offset, int length) throws IOException;

    default void sendBinary(byte[] bytes) throws IOException {
        sendBinary(bytes, 0, bytes.length);
    }

    /*
    void sendBinary(ByteBuffer buf) throws IOException;

    void sendBinary(InputStream in) throws IOException;
     */

    void sendPing(byte[] payload) throws IOException;

    default void sendPing() throws IOException {
        sendPing(new byte[0]);
    }

    void sendPong(byte[] payload) throws IOException;

    default void sendPong() throws IOException {
        sendPong(new byte[0]);
    }

    void sendClose(int statusCode) throws IOException;
}
