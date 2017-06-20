;;; Copyright (C) 2001, 2003  Eric Marsden
;;; Copyright (C) 2005  David Lichteblau
;;; Copyright (C) 2007  Pixel // pinterface
;;; "the conditions and ENSURE-SSL-FUNCALL are by Jochen Schmidt."
;;;
;;; See LICENSE for details.

#+xcvb
(module
 (:depends-on ("package" "conditions" "ffi"
                         (:cond ((:featurep :clisp) "ffi-buffer-clisp")
                                (t "ffi-buffer"))
                         "ffi-buffer-all")))

(eval-when (:compile-toplevel)
  (declaim
   (optimize (speed 3) (space 1) (safety 1) (debug 0) (compilation-speed 0))))

(in-package :cl+ssl)

;; Default Cipher List
(defvar *default-cipher-list* "ALL")

(defclass ssl-stream
    (trivial-gray-stream-mixin
     fundamental-binary-input-stream
     fundamental-binary-output-stream)
  ((ssl-stream-socket
    :initarg :socket
    :accessor ssl-stream-socket)
   (close-callback
    :initarg :close-callback
    :accessor ssl-close-callback)
   (handle
    :initform nil
    :accessor ssl-stream-handle)
   (deadline
    :initform nil
    :initarg :deadline
    :accessor ssl-stream-deadline)
   (output-buffer
    :initform (make-buffer +initial-buffer-size+)
    :accessor ssl-stream-output-buffer)
   (output-pointer
    :initform 0
    :accessor ssl-stream-output-pointer)
   (input-buffer
    :initform (make-buffer +initial-buffer-size+)
    :accessor ssl-stream-input-buffer)
   (peeked-byte
    :initform nil
    :accessor ssl-stream-peeked-byte)))

(defmethod print-object ((object ssl-stream) stream)
  (print-unreadable-object (object stream :type t)
    (format stream "for ~A" (ssl-stream-socket object))))

(defclass ssl-server-stream (ssl-stream) 
  ((certificate
    :initarg :certificate
    :accessor ssl-stream-certificate)
   (key
    :initarg :key
    :accessor ssl-stream-key)))

(defmethod stream-element-type ((stream ssl-stream))
  '(unsigned-byte 8))

(defmethod close ((stream ssl-stream) &key abort)
  (cond
    ((ssl-stream-handle stream)
     (unless abort
       (force-output stream))
     (ssl-free (ssl-stream-handle stream))
     (setf (ssl-stream-handle stream) nil)
     (when (streamp (ssl-stream-socket stream))
       (close (ssl-stream-socket stream)))
     (when (ssl-close-callback stream)
       (funcall (ssl-close-callback stream)))
     t)
    (t
     nil)))

(defmethod open-stream-p ((stream ssl-stream))
  (and (ssl-stream-handle stream) t))

(defmethod stream-listen ((stream ssl-stream))
  (or (ssl-stream-peeked-byte stream)
      (setf (ssl-stream-peeked-byte stream)
            (let* ((buf (ssl-stream-input-buffer stream))
                   (handle (ssl-stream-handle stream))
                   (*blockp* nil) ;; for the Lisp-BIO
                   (n (with-pointer-to-vector-data (ptr buf)
                        (nonblocking-ssl-funcall
                         stream handle #'ssl-read handle ptr 1))))
              (and (> n 0) (buffer-elt buf 0))))))

(defmethod stream-read-byte ((stream ssl-stream))
  (or (prog1
         (ssl-stream-peeked-byte stream)
       (setf (ssl-stream-peeked-byte stream) nil))
      (handler-case
          (let ((buf (ssl-stream-input-buffer stream))
                (handle (ssl-stream-handle stream)))
            (with-pointer-to-vector-data (ptr buf)
              (ensure-ssl-funcall
               stream handle #'ssl-read handle ptr 1))
            (buffer-elt buf 0))
        (ssl-error-zero-return ()     ;SSL_read returns 0 on end-of-file
          :eof))))

(defmethod stream-read-sequence ((stream ssl-stream) seq start end &key)
  (when (and (< start end) (ssl-stream-peeked-byte stream))
    (setf (elt seq start) (ssl-stream-peeked-byte stream))
    (setf (ssl-stream-peeked-byte stream) nil)
    (incf start))
  (let ((buf (ssl-stream-input-buffer stream))
        (handle (ssl-stream-handle stream)))
    (loop
        for length = (min (- end start) (buffer-length buf))
        while (plusp length)
        do
          (handler-case
              (let ((read-bytes
                      (with-pointer-to-vector-data (ptr buf)
                        (ensure-ssl-funcall
                         stream handle #'ssl-read handle ptr length))))
                (s/b-replace seq buf :start1 start :end1 (+ start read-bytes))
                (incf start read-bytes))
            (ssl-error-zero-return ()   ;SSL_read returns 0 on end-of-file
              (return))))
    ;; fixme: kein out-of-file wenn (zerop start)?
    start))

(defmethod stream-write-byte ((stream ssl-stream) b)
  (let ((buf (ssl-stream-output-buffer stream)))
    (when (eql (buffer-length buf) (ssl-stream-output-pointer stream))
      (force-output stream))
    (setf (buffer-elt buf (ssl-stream-output-pointer stream)) b)
    (incf (ssl-stream-output-pointer stream)))
  b)

(defmethod stream-write-sequence ((stream ssl-stream) seq start end &key)
  (let ((buf (ssl-stream-output-buffer stream)))
    (when (> (+ (- end start) (ssl-stream-output-pointer stream)) (buffer-length buf))
      ;; not enough space left?  flush buffer.
      (force-output stream)
      ;; still doesn't fit?
      (while (> (- end start) (buffer-length buf))
        (b/s-replace buf seq :start2 start)
        (incf start (buffer-length buf))
        (setf (ssl-stream-output-pointer stream) (buffer-length buf))
        (force-output stream)))
    (b/s-replace buf seq
                 :start1 (ssl-stream-output-pointer stream)
                 :start2 start
                 :end2 end)
    (incf (ssl-stream-output-pointer stream) (- end start)))
  seq)

(defmethod stream-finish-output ((stream ssl-stream))
  (stream-force-output stream))

(defmethod stream-force-output ((stream ssl-stream))
  (let ((buf (ssl-stream-output-buffer stream))
        (fill-ptr (ssl-stream-output-pointer stream))
        (handle (ssl-stream-handle stream)))
    (when (plusp fill-ptr)
      (unless handle
  (error "output operation on closed SSL stream"))
      (with-pointer-to-vector-data (ptr buf)
        (ensure-ssl-funcall stream handle #'ssl-write handle ptr fill-ptr))
      (setf (ssl-stream-output-pointer stream) 0))))

#+(and clozure-common-lisp (not windows))
(defun install-nonblock-flag (fd)
  (ccl::fd-set-flags fd (logior (ccl::fd-get-flags fd) 
                     #.(read-from-string "#$O_NONBLOCK"))))
                     ;; read-from-string is necessary because
                     ;; CLISP and perhaps other Lisps are confused
                     ;; by #$, signaling"undefined dispatch character $", 
                     ;; even though the defun in conditionalized by 
                     ;; #+clozure-common-lisp
                    
#+(and sbcl (not win32))
(defun install-nonblock-flag (fd)
  (sb-posix:fcntl fd
      sb-posix::f-setfl
      (logior (sb-posix:fcntl fd sb-posix::f-getfl)
        sb-posix::o-nonblock)))

#-(or (and clozure-common-lisp (not windows)) sbcl)
(defun install-nonblock-flag (fd)
  (declare (ignore fd)))

#+(and sbcl win32)
(defun install-nonblock-flag (fd)
  (when (boundp 'sockint::fionbio)
    (sockint::ioctl fd sockint::fionbio 1)))

;;; interface functions
;;;

(defun install-handle-and-bio (stream handle socket unwrap-stream-p)
  (setf (ssl-stream-handle stream) handle)
  (when unwrap-stream-p
    (let ((fd (stream-fd socket)))
      (when fd
  (setf socket fd))))
  (etypecase socket
    (integer
     (install-nonblock-flag socket)
     (ssl-set-fd handle socket))
    (stream
     (ssl-set-bio handle (bio-new-lisp) (bio-new-lisp))))
  (ssl-ctx-ctrl handle
    +SSL_CTRL_MODE+
    +SSL_MODE_ACCEPT_MOVING_WRITE_BUFFER+
    (cffi:null-pointer))
  socket)

(defun install-key-and-cert (handle key certificate)
  (when key
    (unless (eql 1 (ssl-use-rsa-privatekey-file handle
            key
            +ssl-filetype-pem+))
      (error 'ssl-error-initialize :reason (format nil "Can't load RSA private key file ~A" key))))
  (when certificate
    (unless (eql 1 (ssl-use-certificate-file handle
               certificate
               +ssl-filetype-pem+))
      (error 'ssl-error-initialize
       :reason (format nil "Can't load certificate ~A" certificate)))))

(defun x509-certificate-names (x509-certificate)
  (unless (cffi:null-pointer-p x509-certificate)
    (cffi:with-foreign-pointer (buf 1024)
      (let ((issuer-name (x509-get-issuer-name x509-certificate))
            (subject-name (x509-get-subject-name x509-certificate)))
        (values
         (unless (cffi:null-pointer-p issuer-name)
           (x509-name-oneline issuer-name buf 1024)
           (cffi:foreign-string-to-lisp buf))
         (unless (cffi:null-pointer-p subject-name)
           (x509-name-oneline subject-name buf 1024)
           (cffi:foreign-string-to-lisp buf)))))))

(defmethod ssl-stream-handle ((stream flexi-streams:flexi-stream))
  (ssl-stream-handle (flexi-streams:flexi-stream-stream stream)))

(defun ssl-stream-x509-certificate (ssl-stream)
  (ssl-get-peer-certificate (ssl-stream-handle ssl-stream)))

(defun ssl-load-global-verify-locations (&rest pathnames)
  "PATHNAMES is a list of pathnames to PEM files containing server and CA certificates.
Install these certificates to use for verifying on all SSL connections.
After RELOAD, you need to call this again."
  (ensure-initialized)
  (dolist (path pathnames)
    (let ((namestring (namestring (truename path))))
      (cffi:with-foreign-strings ((cafile namestring))
        (unless (eql 1 (ssl-ctx-load-verify-locations
                        *ssl-global-context*
                        cafile
                        (cffi:null-pointer)))
          (error "ssl-ctx-load-verify-locations failed."))))))

(defun ssl-set-global-default-verify-paths ()
  "Load the system default verification certificates.
After RELOAD, you need to call this again."
  (ensure-initialized)
  (unless (eql 1 (ssl-ctx-set-default-verify-paths *ssl-global-context*))
    (error "ssl-ctx-set-default-verify-paths failed.")))

(defun ssl-check-verify-p ()
  "Return true if SSL connections will error if the certificate doesn't verify."
  (and *ssl-check-verify-p* (not (eq *ssl-check-verify-p* :unspecified))))

(defun (setf ssl-check-verify-p) (check-verify-p)
  "If CHECK-VERIFY-P is true, signal connection errors if the server certificate doesn't verify."
  (setf *ssl-check-verify-p* (not (null check-verify-p))))

(defun ssl-verify-init (&key
                        (verify-depth nil)
                        (verify-locations nil))
  (check-type verify-depth (or null integer))
  (ensure-initialized)
  (when verify-depth
    (ssl-ctx-set-verify-depth *ssl-global-context* verify-depth))
  (when verify-locations
    (apply #'ssl-load-global-verify-locations verify-locations)
    ;; This makes (setf (ssl-check-verify) nil) persistent
    (unless (null *ssl-check-verify-p*)
      (setf (ssl-check-verify-p) t))
    t))

(defun ssl-stream-check-verify (ssl-stream)
  (let* ((handle (ssl-stream-handle ssl-stream))
         (err (ssl-get-verify-result handle)))
    (unless (eql err 0)
      (error 'ssl-error-verify :stream ssl-stream :error-code err))))

(defun handle-external-format (stream ef)
  (if ef
      (flexi-streams:make-flexi-stream stream :external-format ef)
      stream))

(defmacro with-new-ssl ((var) &body body)
  (alexandria:with-gensyms (ssl)
    `(let* ((,ssl (ssl-new *ssl-global-context*))
            (,var ,ssl))
       (when (cffi:null-pointer-p ,ssl)
         (error 'ssl-error-call :message "Unable to create SSL structure" :queue (read-ssl-error-queue)))
       (handler-bind ((error (lambda (_)
                               (declare (ignore _))
                               (ssl-free ,ssl))))
         ,@body))))

;; fixme: free the context when errors happen in this function
(defun make-ssl-client-stream
    (socket &key certificate key password (method 'ssl-v23-method) external-format
                 close-callback (unwrap-stream-p t)
     (cipher-list *default-cipher-list*)
                 hostname)
  "Returns an SSL stream for the client socket descriptor SOCKET.
CERTIFICATE is the path to a file containing the PEM-encoded certificate for
 your client. KEY is the path to the PEM-encoded key for the client, which
may be associated with the passphrase PASSWORD.
HOSTNAME if specified, will be sent by client during TLS negotiation,
according to the Server Name Indication (SNI) extension to the TLS.
When server handles several domain names, this extension enables the server
to choose certificate for right domain."
  (ensure-initialized :method method)
  (let ((stream (make-instance 'ssl-stream
                               :socket socket
                               :close-callback close-callback)))
    (with-new-ssl (handle)
      (if hostname
          (cffi:with-foreign-string (chostname hostname)
            (ssl-set-tlsext-host-name handle chostname)))
      (setf socket (install-handle-and-bio stream handle socket unwrap-stream-p))
      (ssl-set-connect-state handle)
      (when (zerop (ssl-set-cipher-list handle cipher-list))
        (error 'ssl-error-initialize :reason "Can't set SSL cipher list"))
      (with-pem-password (password)
        (install-key-and-cert handle key certificate))
      (ensure-ssl-funcall stream handle #'ssl-connect handle)
      (when (ssl-check-verify-p)
        (ssl-stream-check-verify stream))
      (handle-external-format stream external-format))))

;; fixme: free the context when errors happen in this function
(defun make-ssl-server-stream
    (socket &key certificate key password (method 'ssl-v23-method) external-format
                 close-callback (unwrap-stream-p t)
                 (cipher-list *default-cipher-list*))
  "Returns an SSL stream for the server socket descriptor SOCKET.
CERTIFICATE is the path to a file containing the PEM-encoded certificate for
 your server. KEY is the path to the PEM-encoded key for the server, which
may be associated with the passphrase PASSWORD."
  (ensure-initialized :method method)
  (let ((stream (make-instance 'ssl-server-stream
                               :socket socket
                               :close-callback close-callback
                               :certificate certificate
                               :key key)))
    (with-new-ssl (handle)
      (setf socket (install-handle-and-bio stream handle socket unwrap-stream-p))
      (ssl-set-accept-state handle)
      (when (zerop (ssl-set-cipher-list handle cipher-list))
        (error 'ssl-error-initialize :reason "Can't set SSL cipher list"))
      (with-pem-password (password)
        (install-key-and-cert handle key certificate))
      (ensure-ssl-funcall stream handle #'ssl-accept handle)
      (handle-external-format stream external-format))))

#+openmcl
(defmethod stream-deadline ((stream ccl::basic-stream))
  (ccl::ioblock-deadline (ccl::stream-ioblock stream t)))
#+openmcl
(defmethod stream-deadline ((stream t))
  nil)


(defgeneric stream-fd (stream))
(defmethod stream-fd (stream) stream)

#+sbcl
(defmethod stream-fd ((stream sb-sys:fd-stream))
  (sb-sys:fd-stream-fd stream))

#+cmu
(defmethod stream-fd ((stream system:fd-stream))
  (system:fd-stream-fd stream))

#+openmcl
(defmethod stream-fd ((stream ccl::basic-stream))
  (ccl::ioblock-device (ccl::stream-ioblock stream t)))

#+clisp
(defmethod stream-fd ((stream stream))
  ;; sockets appear to be direct instances of STREAM
  (ext:stream-handles stream))

#+ecl
(defmethod stream-fd ((stream two-way-stream))
  (si:file-stream-fd (two-way-stream-input-stream stream)))
