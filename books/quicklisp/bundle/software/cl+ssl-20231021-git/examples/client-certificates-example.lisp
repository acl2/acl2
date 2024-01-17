;;;; The code contained in this file implements a trivial server and a
;;;; client  that connects  to the  former and  provide a  self signed
;;;; certificate.  The server  is  able to  implement  a procedure  to
;;;; reject or  accept the  client connection,  based on  the client's
;;;; certificate, and using some  form of authentication.  For example
;;;; matching  the   certificate  fingerprint   with  a   database  of
;;;; certificates stored on disk, for example.

;;;; Also,   if  the   certificates   are  used   just  for   univocal
;;;; identification of the client, the  hash of the certificate can be
;;;; saved  by  the server  the  first  time  the client  connect  and
;;;; recalled  the  other  times  with a  mechanism  similar  to  HTTP
;;;; cookies.

;; To generate both the keys and certificates, a command line like the
;; one below could be used:

;; openssl req -new -nodes -x509 -days 365 -subj / -keyout private-key -outform PEM -out certificate

;; The key points here are:

;; For the server
;; - create a context using :verify-mode cl+ssl:+ssl-verify-peer+

;; Optional only if you plan to use self signed client certificates

;; - write  a CFFI callback that  always return 1 (one)  to bypass the
;; certificate authentication against  a certification authority; pass
;; the  symbol  of  this  callback   to  key  parameter  :verify  when
;; generating the context

;; For the client

;; - pass  certificate and key when  generating the stream as  you did
;; for the server

(ql:quickload "cl+ssl")

(ql:quickload "bordeaux-threads")

(ql:quickload "trivial-sockets")

(cffi:defcallback no-verify :int ((preverify-ok :int) (x509-store-ctx :pointer))
  (declare (ignore preverify-ok x509-store-ctx))
  1)

(defun hash-array->string (array)
  (let ((res ""))
    (loop for i across array do
      (setf res
            (concatenate 'string
                         res
                         (format nil "~2,'0x" i))))
    res))

(defun start-trivial-server (port certificate key)
  "Start a  trivial server listening  on `PORT' using  the certificate
and  key   stored  in  the   file  pointed  by  the   filesystem  path
`CERTIFICATE' and `KEY' respectively"
  (format t "~&SSL server listening on port ~d~%" port)
  (bt:make-thread
   (lambda ()
     (trivial-sockets:with-server (server (:port port))
       (let* ((socket (trivial-sockets:accept-connection server
                                                         :element-type '(unsigned-byte 8)))
              (ctx (cl+ssl:make-context :verify-mode cl+ssl:+ssl-verify-peer+
                                        :verify-callback 'no-verify)))

         (cl+ssl:with-global-context (ctx :auto-free-p t)
           (let* ((client-stream (cl+ssl:make-ssl-server-stream socket
                                                                :external-format nil
                                                                :certificate     certificate
                                                                :key             key))
                  (client-certificate      (cl+ssl:ssl-stream-x509-certificate client-stream))
                  (client-cert-fingerprint (cl+ssl:certificate-fingerprint client-certificate
                                                                           :sha256)))
             (let ((data (make-list 2)))
               (read-sequence data client-stream)
               (format t
                       "Server got from client (identified by ~s): ~s~%"
                       (hash-array->string client-cert-fingerprint)
                       (coerce (mapcar #'code-char data)
                               'string))
               (cl+ssl:x509-free client-certificate)
               (close socket)))))))))

(defun start-trivial-client (host port data certificate key)
  "Start a  client to connect with  the server as specified  by `HOST'
and  `PORT', sending  the first  two  characters of  the data  string:
`DATA' and using the certificate and key stored in the file pointed by
the filesystem path `CERTIFICATE' and `KEY' respectively"
  (let ((ctx (cl+ssl:make-context :verify-mode cl+ssl:+ssl-verify-none+)))
    (cl+ssl:with-global-context (ctx :auto-free-p t)
      (let* ((stream       (trivial-sockets:open-stream host port))
             (ssl-stream   (cl+ssl:make-ssl-client-stream stream
                                                          :certificate certificate
                                                          :key         key
                                                          :external-format nil
                                                          :unwrap-stream-p t
                                                          :verify          nil
                                                          :hostname        host)))
        (format t "sending ~a~%" data)
        (write-sequence (map 'vector #'char-code data) ssl-stream)
        (finish-output ssl-stream)
        (close stream)))))
