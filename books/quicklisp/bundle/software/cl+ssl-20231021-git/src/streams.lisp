;;;; -*- Mode: LISP; Syntax: COMMON-LISP; indent-tabs-mode: nil; coding: utf-8; show-trailing-whitespace: t -*-
;;;
;;; Copyright (C) 2001, 2003  Eric Marsden
;;; Copyright (C) 2005  David Lichteblau
;;; Copyright (C) 2007  Pixel // pinterface
;;; "the conditions and ENSURE-SSL-FUNCALL are by Jochen Schmidt."
;;; Copyright (C) contributors as per cl+ssl git history
;;;
;;; See LICENSE for details.

(eval-when (:compile-toplevel)
  (declaim
   (optimize (speed 3) (space 1) (safety 1) (debug 0) (compilation-speed 0))))

(in-package :cl+ssl)

;; Default Cipher List
(defvar *default-cipher-list* nil)

(defparameter *default-buffer-size* 2048
  "The default size for input and output buffers of SSL-STREAM objects")

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
    :accessor ssl-stream-output-buffer)
   (output-pointer
    :initform 0
    :accessor ssl-stream-output-pointer)
   (input-buffer
    :accessor ssl-stream-input-buffer)
   (peeked-byte
    :initform nil
    :accessor ssl-stream-peeked-byte)))

(defmethod initialize-instance :after ((stream ssl-stream)
                                       &key
                                       (buffer-size *default-buffer-size*)
                                       (input-buffer-size buffer-size)
                                       (output-buffer-size buffer-size)
                                       &allow-other-keys)
  (setf (ssl-stream-output-buffer stream)
        (make-buffer output-buffer-size))
  (setf (ssl-stream-input-buffer stream)
        (make-buffer input-buffer-size)))

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
       (force-output stream)
       (ensure-ssl-funcall stream
                           (complement #'minusp)
                           #'ssl-shutdown
                           (ssl-stream-handle stream)))
     (ssl-free (ssl-stream-handle stream))
     (setf (ssl-stream-handle stream) nil)
     (when (streamp (ssl-stream-socket stream))
       (close (ssl-stream-socket stream) :abort abort))
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
                   (*bio-blockp* nil) ;; for the Lisp-BIO
                   (n (with-pointer-to-vector-data (ptr buf)
                        (nonblocking-ssl-funcall
                         stream #'plusp #'ssl-read handle ptr 1))))
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
               stream #'plusp #'ssl-read handle ptr 1))
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
                       stream #'plusp #'ssl-read handle ptr length))))
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

(defmacro while (cond &body body)
  `(do () ((not ,cond)) ,@body))

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
        (ensure-ssl-funcall stream #'plusp #'ssl-write handle ptr fill-ptr))
      (setf (ssl-stream-output-pointer stream) 0))))

#+(and clozure-common-lisp (not windows))
(defun install-nonblock-flag (fd)
  (ccl::fd-set-flags fd (logior (ccl::fd-get-flags fd)
                                ;; read-from-string is necessary because
                                ;; CLISP and perhaps other Lisps are confused
                                ;; by #$, signaling
                                ;; "undefined dispatch character $",
                                ;; even though the defun in conditionalized by
                                ;; #+clozure-common-lisp
                                #.(read-from-string "#$O_NONBLOCK"))))

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

(defvar *default-unwrap-stream-p* t
  "Default value for UNWRAP-STREAM-P function parameter.

If true (the default), cl+ssl will try to extract file descriptor
from the given TCP Lisp stream and tell OpenSSL to use a socket BIO
based on that file descriptor;
otherwise use a Lisp BIO wrapping the TCP Lisp stream.")

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

  ;; The below call setting +SSL_MODE_ACCEPT_MOVING_WRITE_BUFFER+ mode
  ;; existed since commit 5bd5225.
  ;; It is implemented wrong - ssl-ctx-ctrl expects
  ;; a context as the first parameter, not handle.
  ;; It was lucky to not crush on Linux and Windows,
  ;; untill crash was detedcted on OpenBSD + LibreSSL.
  ;; See https://github.com/cl-plus-ssl/cl-plus-ssl/pull/42.
  ;; We keep this code commented but not removed because
  ;; we don't know what David Lichteblau meant when
  ;; added this - maybe he has some idea?
  ;; (Although modifying global context is a bad
  ;; thing to do for install-handle-and-bio function,
  ;; also we don't see a need for movable buffer -
  ;; we don't repeat calls to ssl functions with
  ;; moved buffer).
  ;;
  ;; (ssl-ctx-ctrl handle
  ;;   +SSL_CTRL_MODE+
  ;;   +SSL_MODE_ACCEPT_MOVING_WRITE_BUFFER+
  ;;   (cffi:null-pointer))

  socket)

(defun install-key-and-cert (handle key certificate)
  (when certificate
    (unless (eql 1 (ssl-use-certificate-file handle
                                             certificate
                                             +ssl-filetype-pem+))
      (error 'ssl-error-initialize
             :reason (format nil "Can't load certificate ~A" certificate))))
  (when key
    (unless (eql 1 (ssl-use-privatekey-file handle
                                            key
                                            +ssl-filetype-pem+))
      (error 'ssl-error-initialize :reason (format nil "Can't load private key file ~A" key)))))

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
  (compat-ssl-get1-peer-certificate (ssl-stream-handle ssl-stream)))

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
  "DEPRECATED. Use the (MAKE-SSL-CLIENT-STREAM .. :VERIFY ?) to enable/disable verification.
Also, MAKE-CONTEXT has :VERIFY-MODE option.

Return true if SSL connections will error if the certificate doesn't verify."
  (and *ssl-check-verify-p* (not (eq *ssl-check-verify-p* :unspecified))))

(defun (setf ssl-check-verify-p) (check-verify-p)
  "DEPRECATED. Use the (MAKE-SSL-CLIENT-STREAM .. :VERIFY ?) to enable/disable verification.
Also, MAKE-CONTEXT has :VERIFY-MODE option.

If CHECK-VERIFY-P is true, signal connection errors if the server certificate doesn't verify."
  (setf *ssl-check-verify-p* (not (null check-verify-p))))

(defun ssl-verify-init (&key
                        (verify-depth nil)
                        (verify-locations nil))
  "DEPRECATED.
Use the (MAKE-SSL-CLIENT-STREAM .. :VERIFY ?) to enable/disable verification.
Use (MAKE-CONTEXT ... :VERIFY-LOCATION ? :VERIFY-DEPTH ?) to control the verification depth and locations.
MAKE-CONTEXT also allows to enab/disable verification."
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

(defun maybe-verify-client-stream (ssl-stream verify-mode hostname)
  ;; VERIFY-MODE is one of NIL, :OPTIONAL, :REQUIRED
  ;; HOSTNAME is either NIL or a string.
  (when verify-mode
    (let* ((handle (ssl-stream-handle ssl-stream))
           (srv-cert (compat-ssl-get1-peer-certificate handle)))
      (unwind-protect
           (progn
             (when (and (eq :required verify-mode)
                        (cffi:null-pointer-p srv-cert))
               (error 'server-certificate-missing
                      :format-control "The server didn't present a certificate."))
             (let ((err (ssl-get-verify-result handle)))
               (unless (eql err +x509-v-ok+)
                 (error 'ssl-error-verify :stream ssl-stream :error-code err)))
             (when (and hostname
                        (not (cffi:null-pointer-p srv-cert)))
               (or (verify-hostname srv-cert hostname)
                   ;; verify-hostname must either return true
                   ;; or signal an error
                   (error "Unexpected NIL returned by CL+SSL:VERIFY-HOSTNAME for ~A"
                          hostname))))
        (unless (cffi:null-pointer-p srv-cert)
          (x509-free srv-cert))))))

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

(defvar *make-ssl-client-stream-verify-default*
  (if (member :windows *features*) ; by trivial-features
      ;; On Windows we can't yet initizlise context with
      ;; trusted certifying authorities from system configuration.
      ;; ssl-ctx-set-default-verify-paths only helps
      ;; on Unix-like platforms.
      ;; See https://github.com/cl-plus-ssl/cl-plus-ssl/issues/54.
      nil
      :required)
  "Helps to mitigate the change in default behaviour of
MAKE-SSL-CLIENT-STREAM - previously it worked as if :VERIFY NIL
but then :VERIFY :REQUIRED became the default on non-Windows platforms.
Change this variable if you want the previous behaviour.")

(defun make-alpn-proto-string (protocols)
  "Convert list of protocol names to the wire-format byte string."
  (with-output-to-string (s)
    (dolist (proto protocols)
      (check-type proto string)
      (write-char (code-char (length proto)) s)
      (write-string proto s))))

;; fixme: free the context when errors happen in this function
(defun make-ssl-client-stream (socket
                               &key
                                 (unwrap-stream-p *default-unwrap-stream-p*)
                                 hostname
                                 close-callback
                                 external-format
                                 (verify (if (ssl-check-verify-p)
                                             :optional
                                             *make-ssl-client-stream-verify-default*))
                                 alpn-protocols
                                 certificate key password
                                 (cipher-list *default-cipher-list*)
                                 method
                                 (buffer-size *default-buffer-size*)
                                 (input-buffer-size buffer-size)
                                 (output-buffer-size buffer-size))
  "Performs TLS/SSL handshake over the specified SOCKET using
the SSL_connect OpenSSL function and returns a Lisp stream that
uses OpenSSL library to encrypt the output data when sending
it to the socket and to decrypt the input received.

Uses a global SSL_CTX instance, which can be overriden
by WITH-GLOBAL-CONTEXT. (The global SSL_CTX is
passed as a parameter to an internall call of SSL_new.)

    SOCKET - represents the socket to be wrapped into an SSL stream.
        Can be either a Lisp stream (of an implementation-dependent type) for that
        socket, or an integer file descriptor of that socket. If that's a
        stream, it will be closed automatically when the SSL stream
        is closed. Also, on CCL, (CCL:STREAM-DEADLINE SOCKET) will be used
        as a deadline for 'socket BIO' mode.
        See README.md / Usage / Timeouts and Deadlines for more information.
        If that's a file descriptor, it is not closed automatically
        (you can use CLOSE-CALLBACK to arrange for that).

    UNWRAP-STREAM-P - if true, (STREAM-FD SOCKET) will be attempted
        to extract the file descriptor. Otherwise the SOCKET
        is left as is. Anyway, if in result we end up with an integer
        file descriptor, a socket BIO is used; if we end up with a
        stream - Lisp BIO is used. This parameter defaults to
        *DEFAULT-UNWRAP-STREAM-P* which is initalized to true.
        See README.md / Usage for more information on BIO types.

    HOSTNAME if specified, will be sent by client during TLS negotiation,
        according to the Server Name Indication (SNI) extension to the TLS.
        If we connect to a server handling multiple domain names,
        this extension enables such server to choose certificate for the
        right domain. Also the HOSTNAME is used for hostname verification
        (if verification is enabled by VERIFY).

    CLOSE-CALLBACK - a function to be called when the created
        ssl stream is CL:CLOSE'ed. The only argument is this ssl stream.

    EXTERNAL-FORMAT - if NIL (the default), a plain (UNSIGNED-BYTE 8)
        ssl stream is returned. With a non-NIL external-format, a flexi-stream
        capable of character I/O will be returned instead, with the specified
        value as its initial external format.

    VERIFY can be specified either as NIL if no check should be performed,
        :OPTIONAL to verify the server's certificate if server presents one or
        :REQUIRED to verify the server's certificate and fail if an invalid
        or no certificate was presented. Defaults to
        *MAKE-SSL-CLIENT-STREAM-VERIFY-DEFAULT* which is initialized
        to :REQUIRED

        The verification includes verifying the HOSTNAME against the server
        ceritificate, using the VERIFY-HOSTNAME function.

        An error is signalled in case of the certificate or hostname
        verification failure.

        Note, the VERIFY logic expects that the global
        SSL_CTX object does not have the SSL_VERIFY_PEER
        flag enabled - the default for the cl+ssl's global SSL_CTX.
        If the current global SSL_CTX object has SSL_VERIFY_PEER enabled,
        the SSL_Connect will perform certificate (but not hostname)
        verification on its own, and an error will be signalled for a
        bad certificate even with :VERIFY NIL.

    ALPN-PROTOCOLS, if specified, should be a list of alpn protocol names,
        such as \"h2\", that will be offered to the server. The protocol
        selected by the server can be retrieved with
        GET-SELECTED-ALPN-PROTOCOL.

    CERTIFICATE is the path to a file containing a PEM-encoded certificate.
        Note, if one certificate will be used for multiple TLS connections,
        it's better to load it into a common SSL_CTX (context) object rather
        than reading it for every new connection.

    KEY is the path to a PEM-encoded private key file of that certificate.

    PASSWORD the password to use for decryptipon of the KEY (if encrypted).

    CIPHER-LIST - If not NIL, must be a string to pass to SSL_set_cipher_list.
        An ERROR is signalled if SSL_CTX_set_cipher_list fails.
        Defaults to *DEFAULT-CIPHER-LIST* which is initialized to NIL.

    METHOD - usually you want to leave the default value. It is used
        to compute the parameter for OpenSSL function SSL_CTX_new when
        creating the global SSL_CTX object for cl+ssl. This parameter only has
        effect on the first call, when the global SSL_CTX is not yet created.
        The default value is TLS_method on OpenSSL > 1.1.0 and SSLv23_method
        for older OpenSSL versions.

    BUFFER-SIZE - default value for both the INPUT-BUFFER-SIZE and
        OUTPUT-BUFFER-SIZE parameters. In turn defaults to the
        *DEFAULT-BUFFER-SIZE* special variable.

    INPUT-BUFFER-SIZE - size of the input buffer of the ssl stream.
        Defaults to the BUFFER-SIZE parameter.

    OUTPUT-BUFFER-SIZE - size of the output buffer of the ssl stream.
        Defaults to the BUFFER-SIZE parameter.
"
  (ensure-initialized :method method)
  (let ((stream (make-instance 'ssl-stream
                               :socket socket
                               :close-callback close-callback
                               :input-buffer-size input-buffer-size
                               :output-buffer-size output-buffer-size)))
    (with-new-ssl (handle)
      (if hostname
          (cffi:with-foreign-string (chostname hostname)
            (ssl-set-tlsext-host-name handle chostname)))
      (if alpn-protocols
          (cffi:with-foreign-string ((string len) (make-alpn-proto-string alpn-protocols))
            (ssl-set-alpn-protos handle string (1- len))))
      (setf socket (install-handle-and-bio stream handle socket unwrap-stream-p))
      (ssl-set-connect-state handle)
      (when (and cipher-list
                 (zerop (ssl-set-cipher-list handle cipher-list)))
        (error 'ssl-error-initialize
               :reason
               "Can't set SSL cipher list: SSL_set_cipher_list returned 0"))
      (with-pem-password (password)
        (install-key-and-cert handle key certificate))
      (collecting-verify-error (handle)
        (ensure-ssl-funcall stream #'plusp #'ssl-connect handle))
      (maybe-verify-client-stream stream verify hostname)
      (handle-external-format stream external-format))))

;; fixme: free the context when errors happen in this function
(defun make-ssl-server-stream (socket
                               &key
                                 (unwrap-stream-p *default-unwrap-stream-p*)
                                 close-callback
                                 external-format
                                 certificate key password
                                 (cipher-list *default-cipher-list*)
                                 method
                                 (buffer-size *default-buffer-size*)
                                 (input-buffer-size buffer-size)
                                 (output-buffer-size buffer-size))
  "Performs server-side TLS handshake over the specified SOCKET using
the SSL_accept OpenSSL function and returns a Lisp stream that
uses OpenSSL library to encrypt the output data when sending
it to the socket and to decrypt the input received.

Uses a global SSL_CTX instance, which can be overriden
by WITH-GLOBAL-CONTEXT. (The global SSL_CTX is
passed as a parameter to an internall call of SSL_new.)

All parameters have the same meaning as documented
for MAKE-SSL-CLIENT-STREAM.
"
  (ensure-initialized :method method)
  (let ((stream (make-instance 'ssl-server-stream
                               :socket socket
                               :close-callback close-callback
                               :certificate certificate
                               :key key
                               :input-buffer-size input-buffer-size
                               :output-buffer-size output-buffer-size)))
    (with-new-ssl (handle)
      (setf socket (install-handle-and-bio stream handle socket unwrap-stream-p))
      (ssl-set-accept-state handle)
      (when (and cipher-list
                 (zerop (ssl-set-cipher-list handle cipher-list)))
        (error 'ssl-error-initialize
               :reason
               "Can't set SSL cipher list: SSL_set_cipher_list returned 0"))
      (with-pem-password (password)
        (install-key-and-cert handle key certificate))
      (collecting-verify-error (handle)
        (ensure-ssl-funcall stream #'plusp #'ssl-accept handle))
      (handle-external-format stream external-format))))

(defun get-selected-alpn-protocol (ssl-stream)
  "A wrapper around SSL_get0_alpn_selected.
Returns the ALPN protocol selected by server, or NIL if none was selected.

SSL-STREAM is the client ssl stream returned by make-ssl-client-stream. "
  (cffi:with-foreign-objects ((ptr :pointer) (len :pointer))
    (ssl-get0-alpn-selected (ssl-stream-handle ssl-stream) ptr len)
    (cffi:foreign-string-to-lisp (cffi:mem-ref ptr :pointer)
                                 :count (cffi:mem-ref len :int))))

(defgeneric stream-fd (stream)
  (:documentation "The STREAM's file descriptor as an integer,
if known / implemented for the current lisp.
Otherwise the STREAM itself. The result of this function can be
passed to MAKE-SSL-CLIENT-STREAM and MAKE-SSL-SERVER-STREAM."))
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

#+allegro
(defmethod stream-fd ((stream stream))
  (socket:socket-os-fd stream))

#+lispworks
(defmethod stream-fd ((stream comm::socket-stream))
  (comm:socket-stream-socket stream))

#+abcl
(progn
  (require :abcl-contrib)
  (require :jss)

  ;;; N.b. Getting the file descriptor from a socket is not supported
  ;;; by any published JVM API, so every JVM implementation may behave
  ;;; somewhat differently.  By using the ability of
  ;;; jss:get-java-fields to access private fields, it is usually
  ;;; possible to "find" an access path to read the underlying integer
  ;;; value of the file decriptor, which is all we need to pass to
  ;;; SSL.
  (defmethod stream-fd ((stream system::socket-stream))
    (let ((errors))
      (macrolet ((saving-error (&body body)
                   `(handler-case
                        ,@body
                      (serious-condition (c)
                        (push c errors)
                        nil))))
        (flet ((get-java-fields (object fields) ;; Thanks to Cyrus Harmon
                 (reduce (lambda (x y)
                           (jss:get-java-field x y t))
                         fields
                         :initial-value object))
               (jvm-version ()
                 (read
                  (make-string-input-stream
                   (java:jstatic "getProperty"
                                 "java.lang.System"
                                 "java.specification.version")))))
          (let ((input-stream (java:jcall "getWrappedInputStream"  ;; TODO: define this as a constant
                                          (two-way-stream-input-stream stream))))
            (or ;; starting from openjdk 14, according to Mark Evenson
                ;; in https://github.com/cl-plus-ssl/cl-plus-ssl/pull/103
                (saving-error (get-java-fields input-stream
                                               '("in" "this$0" "sc" "fd" "fd")))
                ;; This seen to work for the following Java:
                ;; - On my local Linux machine
                ;;   $ java -version
                ;;   openjdk version "1.8.0_292"
                ;;   OpenJDK Runtime Environment (Zulu 8.54.0.21-CA-linux64) (build 1.8.0_292-b10)
                ;;   OpenJDK 64-Bit Server VM (Zulu 8.54.0.21-CA-linux64) (build 25.292-b10, mixed mode)
                ;; - Java 11.0.14 Debian
                ;;   OpenJDK 64-Bit Server VM
                ;;   (Printed by ABCL startup in GitHub Actions Linux VM
                ;;   running Docker image clfoundation/cl-devel:2022-02-09)
                (saving-error (get-java-fields input-stream
                                               '("in" "impl" "fd" "fd")))
                (saving-error (get-java-fields input-stream
                                               '("in" "ch" "fdVal")))
                (warn "cl+ssl:stream-fd: all approaches failed. stream: ~A, jvm-version: ~S, internal input-stream: ~A, errors:~%~{~A~^~%~}"
                      stream
                      (ignore-errors (jvm-version))
                      input-stream
                      (nreverse errors)))))))))
