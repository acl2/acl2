; JSON-RPC Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Quan Luu (quan.luu@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Raw Lisp implementation of the JSON-RPC TCP socket server.
; Loaded by socket.lisp via include-raw with :host-readtable t.
;
; usocket is available here because socket.lisp includes
; quicklisp/hunchentoot, which loads usocket transitively.
;
; Messages are newline-delimited: the client sends a compact JSON value
; followed by a newline character.  The server reads until the newline,
; processes the message, and writes the response followed by a newline.
; Multiple requests may be sent over a single connection.

(in-package "JSONRPC")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun read-json-line (stream)
  "Read one newline-delimited JSON message from STREAM.
   Returns the message as a string (without the newline), or NIL on EOF."
  (let ((line (read-line stream nil nil)))
    (if (or (null line) (zerop (length (string-trim '(#\Space #\Tab #\Return) line))))
        nil
      line)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun handle-connection (stream acl2-state)
  "Handle a connection: loop reading newline-delimited JSON messages,
   processing each through the ACL2 JSON-RPC pipeline, and writing
   responses back.  Returns when the client disconnects (EOF)."
  (loop
    (let ((json-string (read-json-line stream)))
      (when (null json-string)
        (return acl2-state))

      (multiple-value-bind (batchp alist)
          (parse-json-rpc json-string)
        (multiple-value-bind (responses new-state)
            (process-all alist 'run-jsonrpc-server acl2-state)
          (setf acl2-state new-state)

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

(defun run-jsonrpc-server (port acl2-state)
  "Start a TCP JSON-RPC 2.0 server listening on PORT.
   Messages are newline-delimited.  Single-threaded; does not return
   under normal operation."
  (let ((server-socket
         (usocket:socket-listen "0.0.0.0" port
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
                    (setf acl2-state
                          (handle-connection stream acl2-state))
                  (usocket:socket-close client-socket)))
            (error (c)
              (format t "JSON-RPC server: error handling connection: ~a~%" c)
              (force-output))))
      (usocket:socket-close server-socket)))
  (mv nil acl2-state))
