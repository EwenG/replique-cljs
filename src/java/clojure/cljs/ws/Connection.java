/**
 *   Copyright (c) Thomas Heller. All rights reserved.
 *   The use and distribution terms for this software are covered by the
 *   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
 *   which can be found in the file epl-v10.html at the root of this distribution.
 *   By using this software in any fashion, you are agreeing to be bound by
 * 	 the terms of this license.
 *   You must not remove this notice, or any other, from this software.
 *
 *   Narrowed from shadow-http 0.1.8's Connection, which also declares
 *   getServer, isSecure, getRemoteAddress, getInputStream and upgrade -
 *   the five that tie it to the rest of that server. See package-info.java.
 **/

package clojure.cljs.ws;

import java.io.IOException;
import java.io.OutputStream;

/**
 * What a WebSocketExchange needs from the connection underneath it, and nothing
 * more: somewhere to write frames, and a way to ask whether the socket is still
 * there.
 *
 * NARROWED FROM shadow-http's Connection, which also carries getServer(),
 * isSecure(), getRemoteAddress(), getInputStream() and upgrade(Exchange) - the
 * five that tie it to the rest of that server. WebSocketExchange never calls any
 * of them; it touches this object in exactly two places.
 */
public interface Connection {

    OutputStream getOutputStream() throws IOException;

    boolean isActive();
}
