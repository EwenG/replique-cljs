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

/**
 * Protocol exception carrying a WebSocket close status code (Section 7.4).
 */
public class WebSocketProtocolException extends IOException {
    private final int statusCode;

    public WebSocketProtocolException(int statusCode, String message) {
        super(message);
        this.statusCode = statusCode;
    }

    /**
     * The appropriate WebSocket close status code (Section 7.4.1) for this error.
     */
    public int getStatusCode() {
        return statusCode;
    }
}
