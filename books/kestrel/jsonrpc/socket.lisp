; JSON-RPC Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Quan Luu (quan.luu@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JSONRPC")

(include-book "tools/include-raw" :dir :system)
(include-book "quicklisp/usocket" :dir :system)

(include-book "process-rpc")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc run-jsonrpc-server
  :parents (jsonrpc)
  :short "Start a TCP socket server that handles JSON-RPC 2.0 requests."
  :long "<p>@('run-jsonrpc-server') opens a TCP server socket on the given
  port and accepts connections sequentially.  For each connection it enters
  a loop reading JSON-RPC messages, dispatching them through the same
  pipeline as @(see process-json-rpc-file), and writing the responses back.
  When a client disconnects (EOF), the server waits for the next connection.
  The function only returns on error.</p>

  <p>The @('interface') argument controls which network interface the server
  binds to.  Pass @('nil') (or @('\"127.0.0.1\"')) to accept connections only
  from the local machine.  Pass @('\"0.0.0.0\"') to accept connections from
  any host on the network &mdash; use this only in trusted environments.</p>

  <p>The @('allowed-methods') argument restricts which methods may be called.
  Pass a list of symbols naming the permitted methods, e.g. @('(subtract add)').
  Pass @(':any') to allow any method in the @('JSONRPC') package (unrestricted).
  Requests for methods not in the list are rejected with a method-not-found
  error.</p>

  <p>Usage (localhost, subtract only):</p>

  @({
    (run-jsonrpc-server 7070 nil '(subtract) state)
  })

  <p>Usage (all interfaces, unrestricted):</p>

  @({
    (run-jsonrpc-server 7070 \"0.0.0.0\" :any state)
  })

  <p>Messages must be delimited by a newline character.</p>")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Logical stub -- the real definition is installed by socket-raw.lsp below.

(defun run-jsonrpc-server (port interface allowed-methods state)
  (declare (xargs :guard (and (natp port)
                              (or (null interface) (stringp interface)))
                  :mode :program
                  :stobjs state))
  (declare (ignore port interface allowed-methods))
  (prog2$ (er hard? 'run-jsonrpc-server
              "Raw Lisp definition of run-jsonrpc-server not installed.")
          (mv nil nil state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defttag :jsonrpc-socket)

; (depends-on "socket-raw.lsp")
(include-raw "socket-raw.lsp" :host-readtable t)
