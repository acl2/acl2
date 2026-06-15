; JSON-RPC Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Quan Luu (quan.luu@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JSONRPC")

; include-raw is a macro defined in tools/include-raw, not a built-in.
(include-book "tools/include-raw" :dir :system)

; Load usocket transitively via hunchentoot (same pattern as centaur/bridge).
(include-book "quicklisp/hunchentoot" :dir :system)

(include-book "process-rpc")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc run-jsonrpc-server
  :parents (jsonrpc)
  :short "Start a TCP socket server that handles JSON-RPC 2.0 requests."
  :long "<p>@('run-jsonrpc-server') opens a TCP server socket on the given
  port and enters an accept loop.  For each incoming connection it reads
  JSON-RPC messages, dispatches them through the same pipeline as
  @(see process-json-rpc-file), and writes the responses back on the same
  connection.  A single connection may carry multiple request/response
  exchanges; the connection is closed when the client
  disconnects.</p>

  <p>Usage:</p>

  @({
    (run-jsonrpc-server 7070 state)
  })

  <p>Messages must be delimited by a newline character.</p>

  <p>This function does not return under normal operation.  It can be
  interrupted with a SIGINT (Ctrl-C).</p>")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Logical stub — the real definition is installed by socket-raw.lsp below.

(defun run-jsonrpc-server (port state)
  (declare (xargs :guard (natp port)
                  :mode :program
                  :stobjs state))
  (declare (ignore port))
  (prog2$ (er hard? 'run-jsonrpc-server
              "Raw Lisp definition of run-jsonrpc-server not installed.")
          (mv nil state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defttag :jsonrpc-socket)

; (depends-on "socket-raw.lsp")
(include-raw "socket-raw.lsp" :host-readtable t)
