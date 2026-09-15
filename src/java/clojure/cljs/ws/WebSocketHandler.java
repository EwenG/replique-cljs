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

public interface WebSocketHandler {

    default WebSocketHandler start(WebSocketConnection ctx) {
        return this;
    }
    default void onText(String payload) throws IOException {
    }

    default void onBinary(byte[] payload) throws IOException {
    }

    void onPing(byte[] payload) throws IOException;

    default void onPong(byte[] payload) throws IOException {
    }

    default void onClose(int statusCode, String reason) {
    }

    class Base implements WebSocketHandler {
        protected WebSocketConnection context;

        public Base() {
        }

        @Override
        public WebSocketHandler start(WebSocketConnection ctx) {
            this.context = ctx;
            return this;
        }

        @Override
        public void onText(String payload) throws IOException {
        }

        @Override
        public void onBinary(byte[] payload) throws IOException {
        }

        @Override
        public void onPing(byte[] payload) throws IOException {
            context.sendPong(payload);
        }

        @Override
        public void onPong(byte[] payload) throws IOException {
        }

        @Override
        public void onClose(int statusCode, String reason) {
        }
    }
}
