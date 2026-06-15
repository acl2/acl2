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

(defun handle-connection (stream state)
  "Handle a connection: loop reading newline-delimited JSON messages,
   processing each through the ACL2 JSON-RPC pipeline, and writing
   responses back.  Returns when the client disconnects (EOF)."
  (loop
    (let ((json-string (read-json-line stream)))
      (when (null json-string)
        (return state))
      (mv-let (batchp alist)
        (parse-json-rpc json-string)
        (mv-let (responses state)
          (process-all alist 'run-jsonrpc-server state)
          (let* ((response-val
                  (cond ((endp responses) nil)
                        (batchp (value-array responses))
                        (t (car responses))))
                 (response-str
                  (if response-val
                      (value-to-json-string response-val)
                    nil)))
            (when response-str
              (write-string response-str stream)
              (write-char #\Newline stream)
              (force-output stream))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun run-jsonrpc-server (port state)
  "Start a TCP JSON-RPC 2.0 server listening on PORT.
   Accepts one connection, handles all its newline-delimited messages,
   then returns."
  (let ((server-socket
         (usocket:socket-listen "0.0.0.0" port
                                :reuse-address t
                                :element-type 'character)))
    (format t "JSON-RPC server listening on port ~a~%" port)
    (force-output)
    (unwind-protect
        (handler-case
            (let* ((client-socket
                    (usocket:socket-accept server-socket
                                           :element-type 'character))
                   (stream (usocket:socket-stream client-socket)))
              (unwind-protect
                  (handle-connection stream state)
                (usocket:socket-close client-socket)))
          (error (c)
            (format t "JSON-RPC server: error handling connection: ~a~%" c)
            (force-output)
            state))
      (usocket:socket-close server-socket)))
  (mv nil state))
