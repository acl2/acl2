; JSON-RPC Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Quan Luu (quan.luu@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JSONRPC")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun read-json-line (stream)
  "Read one newline-delimited JSON message from STREAM.
   Returns the message as a string (without the newline), or NIL on EOF."
  (let ((line (read-line stream nil nil)))
    (if (or (null line)
            (zerop (length (string-trim '(#\Space #\Tab #\Return) line))))
        nil
      line)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun handle-connection (stream allowed-methods state)
  "Handle a connection: loop reading newline-delimited JSON messages,
   processing each through the ACL2 JSON-RPC pipeline, and writing
   responses back.  Returns (mv nil \"Connection closed\" state) on EOF."
  (loop
    (let ((json-string (read-json-line stream)))
      (when (null json-string)
        (return (mv nil "Connection closed" state)))
      (mv-let (batchp alist)
        (parse-json-rpc json-string)
        (mv-let (erp responses state)
          (process-all alist allowed-methods 'run-jsonrpc-server state)
          (let* ((response-val
                  (cond ((endp responses) nil)
                        (batchp (value-array responses))
                        (t (car responses))))
                 (response-str
                  (if response-val
                      (value-to-json-string response-val)
                    nil)))
            (format t "~a~%" response-str)
            (force-output)
            (when (and (not erp) response-str)
              (write-string response-str stream)
              (write-char #\Newline stream)
              (force-output stream))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun run-jsonrpc-server (port interface allowed-methods state)
  "Start a TCP JSON-RPC 2.0 server listening on PORT.
   INTERFACE is the bind address string (e.g. \"127.0.0.1\" or \"0.0.0.0\");
   NIL defaults to \"127.0.0.1\".
   ALLOWED-METHODS is either :any or a list of permitted method symbols.
   Accepts connections sequentially; after one client disconnects, waits
   for the next.  Returns (mv erp msg state) on error."
  (let* ((host (or interface "127.0.0.1"))
         (server-socket
          (usocket:socket-listen host port
                                 :reuse-address t
                                 :element-type 'character)))
    (format t "JSON-RPC server listening on port ~a~%" port)
    (force-output)
    (unwind-protect
        (loop
          (handler-case
              (let* ((client-socket
                      (usocket:socket-accept server-socket
                                             :element-type 'character))
                     (stream (usocket:socket-stream client-socket)))
                (unwind-protect
                    (mv-let (erp msg new-state)
                      (handle-connection stream allowed-methods state)
                      (declare (ignore msg))
                      (setq state new-state)
                      (when erp
                        (return (mv erp nil state))))
                  (usocket:socket-close client-socket)))
            (error (c)
              (format t "JSON-RPC server error: ~a~%" c)
              (force-output)
              (return (mv t (format nil "Error: ~a" c) state)))))
      (usocket:socket-close server-socket))))
