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
; Each connection carries exactly one request (or one batch).  The client
; sends the JSON, closes its writing side, and the server reads until EOF,
; processes the message, sends the response, and closes the connection.

(in-package "JSONRPC")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun read-stream-to-string (stream)
  "Read all characters from STREAM until EOF and return them as a string.
   Returns NIL if the stream is immediately at EOF (client connected but
   sent nothing)."
  (let ((acc (make-array 256
                         :element-type 'character
                         :adjustable t
                         :fill-pointer 0)))
    (loop
      (let ((ch (read-char stream nil nil)))
        (when (null ch)
          (return (if (zerop (fill-pointer acc))
                      nil
                    (coerce acc 'string))))
        (vector-push-extend ch acc)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun handle-connection (stream acl2-state)
  "Handle a single connection: read the full request until EOF, process it
   through the ACL2 JSON-RPC pipeline, and write the response back."
  (let ((json-string (read-stream-to-string stream)))
    ;; NIL means the client connected and immediately closed with no content.
    (when (null json-string)
      (return-from handle-connection acl2-state))

    ;; Run the JSON-RPC pipeline.
    (multiple-value-bind (batchp alist)
        (parse-json-rpc json-string)
      (multiple-value-bind (responses new-state)
          (process-all alist 'run-jsonrpc-server acl2-state)

        ;; Build and send the response.
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
            (force-output stream)))

        new-state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun run-jsonrpc-server (port acl2-state)
  "Start a TCP JSON-RPC 2.0 server listening on PORT.
   Each connection carries exactly one request or batch: the client sends
   JSON, closes its writing side (EOF), the server processes and responds,
   then closes the connection.  Single-threaded; does not return under
   normal operation."
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
