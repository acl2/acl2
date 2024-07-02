;;;; -*- Mode: LISP; Syntax: COMMON-LISP; indent-tabs-mode: nil; coding: utf-8; show-trailing-whitespace: t -*-
;;;
;;; Copyright (C) 2001, 2003  Eric Marsden
;;; Copyright (C) 2005  David Lichteblau
;;; "the conditions and ENSURE-SSL-FUNCALL are by Jochen Schmidt."
;;; Copyright (C) contributors as per cl+ssl git history
;;;
;;; See LICENSE for details.

(in-package :cl+ssl)

(eval-when (:compile-toplevel :load-toplevel :execute)
  (defconstant +ssl-error-none+ 0)
  (defconstant +ssl-error-ssl+ 1)
  (defconstant +ssl-error-want-read+ 2)
  (defconstant +ssl-error-want-write+ 3)
  (defconstant +ssl-error-want-x509-lookup+ 4)
  (defconstant +ssl-error-syscall+ 5)
  (defconstant +ssl-error-zero-return+ 6)
  (defconstant +ssl-error-want-connect+ 7))


;;; Condition hierarchy
;;;

(defun read-ssl-error-queue ()
  (loop
     :for error-code = (err-get-error)
     :until (zerop error-code)
     :collect error-code))

(defun format-ssl-error-queue (stream-designator queue-designator)
  "STREAM-DESIGNATOR is the same as CL:FORMAT accepts: T, NIL, or a stream.
QUEUE-DESIGNATOR is either a list of error codes (as returned
by READ-SSL-ERROR-QUEUE) or an SSL-ERROR condition."
  (flet ((body (stream)

           ;; If printed-queue is present, just use it
           (when (and (typep queue-designator 'ssl-error)
                      (printed-queue queue-designator))
             (format stream "ERR_print_errors(): ~A"
                     (printed-queue queue-designator))
             (return-from body))

           (let ((queue (etypecase queue-designator
                          (ssl-error (ssl-error-queue queue-designator))
                          (list queue-designator))))
             (format stream "SSL error queue")
             (if queue
                 (progn
                   (format stream ":~%")
                   (loop
                      :for error-code :in queue
                      :do (format stream "~a~%" (err-error-string error-code (cffi:null-pointer)))))
                 (format stream " is empty.")))))
    (case stream-designator
      ((t) (body *standard-output*))
      ((nil) (let ((s (make-string-output-stream :element-type 'character)))
               (unwind-protect
                    (body s)
                 (close s))
               (get-output-stream-string s)))
      (otherwise (body stream-designator)))))

(define-condition cl+ssl-error (error)
  ())

(define-condition ssl-error (cl+ssl-error)
  (
   ;; Stores list of error codes
   ;; (as returned by the READ-SSL-ERROR-QUEUE function)
   (queue :initform nil :initarg :queue :reader ssl-error-queue)

   ;; The queue formatted using ERR_print_errors.
   ;; If this value is present, ignore the QUEUE field (which will
   ;; be empty, most likely, because ERR_print_errors cleans the queue).
   ;;
   ;; That's the preferred way, becuase it includes more info
   ;; than the printing we implemented in Lisp. In particualr, in includes
   ;; the optional string added by ERR_add_error_data, which
   ;; we use to provide error details of unexpected lisp errors
   ;; in Lisp BIO. Consider migrating all the code to PRINTED-QUEUE,
   ;; for example, when working on
   ;; https://github.com/cl-plus-ssl/cl-plus-ssl/issues/75.
   (printed-queue :initform nil
                  :initarg :printed-queue
                  :reader printed-queue)))

(define-condition ssl-error/handle (ssl-error)
  (;; Misnamed, better to be called CODE :READER SSL-ERROR-CODE
   ;; becuase OpenSSL docs use the term RET for return
   ;; values of IO calls like SSL_Read, etc, while
   ;; here we store explanation of such failures
   ;; as returned by SSL_get_error called
   ;; after the failure.
   ;; Unfortunately, SSL-ERROR-CODE is already used
   ;; by SSL-ERROR-VERIFY condition class below
   ;; for return values of SSL_get_verify_result,
   ;; and that's already exported from cl+ssl package.
   ;; Using the same generic function for two different
   ;; types of error codes is not the best approach.
   ;; Keeping it as is for now.
   ;; Or maybe the intention was for SSL-SIGNAL-ERROR
   ;; to really pass RET here (the IO call return value)?
   ;; Unlikely, RET is not very useful.
   (ret :initarg :ret
        :reader ssl-error-ret
        :documentation "The error code returned by SSL_get_error. " )
   (handle :initarg :handle
           :reader ssl-error-handle))
  (:documentation "Base condition for lisp wrappers of SSL_get_error return values.")
  (:report (lambda (condition stream)
             (format stream "Unspecified error ~A on handle ~A. "
                     (ssl-error-ret condition)
                     (ssl-error-handle condition))
             (format-ssl-error-queue stream condition))))

(define-condition ssl-error-initialize (ssl-error)
  ((reason  :initarg :reason
            :reader ssl-error-reason))
  (:report (lambda (condition stream)
             (format stream "SSL initialization error: ~A. "
                     (ssl-error-reason condition))
             (format-ssl-error-queue stream condition))))


(define-condition ssl-error-want-something (ssl-error/handle)
  ())

;;;SSL_ERROR_NONE
(define-condition ssl-error-none (ssl-error/handle)
  ()
  (:documentation
   "The TLS/SSL I/O operation completed. This result code is returned if and
    only if ret > 0.")
  (:report (lambda (condition stream)
             (format stream "The TLS/SSL operation on handle ~A completed (SSL_get_error: ~A). "
                     (ssl-error-handle condition)
                     (ssl-error-ret condition))
             (format-ssl-error-queue stream condition))))

;; SSL_ERROR_ZERO_RETURN
(define-condition ssl-error-zero-return (ssl-error/handle)
  ()
  (:documentation
   "The TLS/SSL connection has been closed. If the protocol version is SSL 3.0
    or TLS 1.0, this result code is returned only if a closure alert has
    occurred in the protocol, i.e. if the connection has been closed cleanly.
    Note that in this case SSL_ERROR_ZERO_RETURN
    does not necessarily indicate that the underlying transport has been
    closed.")
  (:report (lambda (condition stream)
             (format stream "The TLS/SSL connection on handle ~A has been closed (SSL_get_error: ~A). "
                     (ssl-error-handle condition)
                     (ssl-error-ret condition))
             (format-ssl-error-queue stream condition))))

;; SSL_ERROR_WANT_READ
(define-condition ssl-error-want-read (ssl-error-want-something)
  ()
  (:documentation
   "The operation did not complete; the same TLS/SSL I/O function should be
    called again later. If, by then, the underlying BIO has data available for
    reading (if the result code is SSL_ERROR_WANT_READ) or allows writing data
    (SSL_ERROR_WANT_WRITE), then some TLS/SSL protocol progress will take place,
    i.e. at least part of an TLS/SSL record will be read or written. Note that
    the retry may again lead to a SSL_ERROR_WANT_READ or SSL_ERROR_WANT_WRITE
    condition. There is no fixed upper limit for the number of iterations that
    may be necessary until progress becomes visible at application protocol
    level.")
  (:report (lambda (condition stream)
             (format stream "The TLS/SSL operation on handle ~A did not complete: It wants a READ (SSL_get_error: ~A). "
                     (ssl-error-handle condition)
                     (ssl-error-ret condition))
             (format-ssl-error-queue stream condition))))

;; SSL_ERROR_WANT_WRITE
(define-condition ssl-error-want-write (ssl-error-want-something)
  ()
  (:documentation
   "The operation did not complete; the same TLS/SSL I/O function should be
    called again later. If, by then, the underlying BIO has data available for
    reading (if the result code is SSL_ERROR_WANT_READ) or allows writing data
    (SSL_ERROR_WANT_WRITE), then some TLS/SSL protocol progress will take place,
    i.e. at least part of an TLS/SSL record will be read or written. Note that
    the retry may again lead to a SSL_ERROR_WANT_READ or SSL_ERROR_WANT_WRITE
    condition. There is no fixed upper limit for the number of iterations that
    may be necessary until progress becomes visible at application protocol
    level.")
  (:report (lambda (condition stream)
             (format stream "The TLS/SSL operation on handle ~A did not complete: It wants a WRITE (SSL_get_error: ~A). "
                     (ssl-error-handle condition)
                     (ssl-error-ret condition))
             (format-ssl-error-queue stream condition))))

;; SSL_ERROR_WANT_CONNECT
(define-condition ssl-error-want-connect (ssl-error-want-something)
  ()
  (:documentation
   "The operation did not complete; the same TLS/SSL I/O function should be
    called again later. The underlying BIO was not connected yet to the peer
    and the call would block in connect()/accept(). The SSL
    function should be called again when the connection is established. These
    messages can only appear with a BIO_s_connect() or
    BIO_s_accept() BIO, respectively. In order to find out, when
    the connection has been successfully established, on many platforms
    select() or poll() for writing on the socket file
    descriptor can be used.")
  (:report (lambda (condition stream)
             (format stream "The TLS/SSL operation on handle ~A did not complete: It wants a connect first (SSL_get_error: ~A). "
                     (ssl-error-handle condition)
                     (ssl-error-ret condition))
             (format-ssl-error-queue stream condition))))

;; SSL_ERROR_WANT_X509_LOOKUP
(define-condition ssl-error-want-x509-lookup (ssl-error-want-something)
  ()
  (:documentation
   "The operation did not complete because an application callback set by
    SSL_CTX_set_client_cert_cb() has asked to be called again. The
    TLS/SSL I/O function should be called again later. Details depend on the
    application.")
  (:report (lambda (condition stream)
             (format stream "The TLS/SSL operation on handle ~A did not complete: An application callback wants to be called again (SSL_get_error: ~A). "
                     (ssl-error-handle condition)
                     (ssl-error-ret condition))
             (format-ssl-error-queue stream condition))))

;; SSL_ERROR_SYSCALL
(define-condition ssl-error-syscall (ssl-error/handle)
  ((syscall :initarg :syscall))
  (:documentation
   "Some I/O error occurred. The OpenSSL error queue may contain more
    information on the error. If the error queue is empty (i.e. ERR_get_error() returns 0),
    ret can be used to find out more about the error: If ret == 0, an EOF was observed that
    violates the protocol. If ret == -1, the underlying BIO reported an I/O error (for socket
    I/O on Unix systems, consult errno for details).")
  (:report (lambda (condition stream)
             (if (zerop (length (ssl-error-queue condition)))
                 (case (ssl-error-ret condition)
                   (0 (format stream "An I/O error occurred: An unexpected EOF was observed on handle ~A (SSL_get_error: ~A). "
                              (ssl-error-handle condition)
                              (ssl-error-ret condition)))
                   (-1 (format stream "An I/O error occurred in the underlying BIO (SSL_get_error: ~A). "
                               (ssl-error-ret condition)))
                   (otherwise (format stream "An I/O error occurred: undocumented reason (SSL_get_error: ~A). "
                                      (ssl-error-ret condition))))
                 (format stream "An UNKNOWN I/O error occurred in the underlying BIO (SSL_get_error: ~A). "
                         (ssl-error-ret condition)))
             (format-ssl-error-queue stream condition))))

;; SSL_ERROR_SSL
(define-condition ssl-error-ssl (ssl-error/handle)
  ((;; When SSL_Connect or SSL_Accept fail due to
    ;; the SSL_VERIFY_PEER flag and bad peer certificate,
    ;; the error queue simply says "certificate verify failed"
    ;; and the user needs to call SSL_get_verify_result
    ;; to find our the exact verification error (expired cert,
    ;; can't get issuer cert locally, etc).
    ;;
    ;; To facilitate debugging and logging, we
    ;; automaticall store the SSL_get_verify_result
    ;; in this slot and use it in the printed
    ;; representation of the condition.
    ;;
    ;; Ideally, we should only collect the verification
    ;; error if the error queue includes reason code
    ;; SSL_R_CERTIFICATE_VERIFY_FAILED for library
    ;; code ERR_LIB_SSL, but this would require
    ;; us to implement the logic of OpenSSL macros
    ;; ERR_raise, ERR_PACK, taking OpenSSL version into
    ;; account - those macros produce different number
    ;; for that reason code in different OpenSSL versions.
    ;; Here are snippets of printed error queues, starting
    ;; with error code:
    ;;   openssl-0.9.8zh
    ;;     14090086:SSL routines:SSL3_GET_SERVER_CERTIFICATE:certificate verify failed:s3_clnt.c:973:
    ;;   openssl-1.1.1p
    ;;     1416F086:SSL routines:tls_process_server_certificate:certificate verify failed:ssl/statem/statem_clnt.c:1919:
    ;;   openssl-3.0.4
    ;;     0A000086:SSL routines:tls_post_process_server_certificate:certificate verify failed:ssl/statem/statem_clnt.c:1887:
    ;; Therefore we simply collect the verification
    ;; error if it is present at the time of SSL_Connect
    ;; or SSL_Accept failure - see how the
    ;; collecting-verify-error macro is used.
    ;; This approach, however, will not collect verification
    ;; error if it happens not on the initial handshake,
    ;; but during session renegotiation.
    verify-error :type (or null string)
                 :initform nil
                 :accessor ssl-error-ssl-verify-error))
  (:documentation
   "A failure in the SSL library occurred, usually a protocol error. The
    OpenSSL error queue contains more information on the error.")
  (:report (lambda (condition stream)
             (format stream
                     "A failure in the SSL library occurred on handle ~A (SSL_get_error: ~A). "
                     (ssl-error-handle condition)
                     (ssl-error-ret condition))
             (format-ssl-error-queue stream condition)
             (when (ssl-error-ssl-verify-error condition)
               (format stream
                       "~A"
                       (ssl-error-ssl-verify-error condition))))))

(defun collect-verify-error (ssl-error-ssl-condition handle)
  (let ((code (ssl-get-verify-result handle)))
    (unless (eql code +x509-v-ok+)
      (setf (ssl-error-ssl-verify-error ssl-error-ssl-condition)
            (format nil "SSL_get_verify_result: ~d~@[ ~a~]"
                    code (ssl-verify-error-keyword code))))))

(defun collecting-verify-error-impl (handle body-fn)
  (handler-bind ((ssl-error-ssl (lambda (c)
                                  (collect-verify-error c handle))))
    (funcall body-fn)))

(defmacro collecting-verify-error ((handle) &body body)
  `(collecting-verify-error-impl ,handle (lambda () ,@body)))

(defun err-print-errors-to-string ()
  (with-bio-output-to-string (bio)
    (err-print-errors bio)))

(defun ssl-signal-error (handle syscall error-code ret)
  "RET is return value of the failed SYSCALL (like SSL_read, SSL_connect,
SSL_shutdown, etc - most of them designate failure by returning
RET <= 0, althought SSL_shutdow fails with RET < 0.

ERROR-CODE is return value of SSL_get_error - an explanation of the failure.
"
  (let ((printed-queue (err-print-errors-to-string))
        ;; FixMe: the error queue is emptied by (err-print-errors-to-string)
        ;;        above so the QUEUE becomes an empty list.
        (queue (read-ssl-error-queue)))
    ;; BAD: The IF below is responsible to represent the "Unexpected EOF"
    ;; situation, which is when the remote peer closes
    ;; TCP connection without sending TLS close_notify alert,
    ;; as a situation of normal close_notify alert received.
    ;;
    ;; OpenSSL before version 3.0 signals the Unexpected EOF
    ;; as error-code = SSL_ERROR_SYSCALL and ret = 0.
    ;; Normal termination is signalled by error-code = SSL_ERROR_ZERO_RETURN.
    ;;
    ;; As you see below, the IF turns the former into the latter.
    ;;
    ;; We should not suppress the Unexpected EOF error, because
    ;; some protocols on top of TLS may be attacked with TLS truncation
    ;; attack. For example HTTP 0.9, where response size is not specified
    ;; by the server but instead end of message is indicated by server closing
    ;; the connection.
    ;;
    ;; In such protocols a malicious middle-man can insert an unencrypted
    ;; TCP FIN packet, thus giving the client a partial response. OpenSSL treats
    ;; this as an Unexpected EOF error, but cl+ssl turns it into
    ;; the ssl-error-zero-return condition, which is then internally
    ;; converted simply to an end of ssl-stream. Thus the user will treat
    ;; the truncated response as authoritative and complete.
    ;;
    ;; Since OpenSSL 3.0 the suppression does not happen
    ;; and cl+ssl user receives an error condition, because
    ;; the Unexpected EOF is reported as error-code = SSL_ERROR_SSL.
    ;;
    ;; The only reason we currently keep this not fixed for older OpenSSL
    ;; is potential backwards compatibility problems with existing
    ;; Common Lisp libraries and applications and the fact
    ;; that protocols where message sizes are usually
    ;; explicitly indicated (like HTTP 1.1 where Content-Length or
    ;; chunked encoding are used) truncation can be detected
    ;; without relying to TLS and thus some servers close TCP
    ;; connections without sending TLS close_notify alert.
    ;; Some libraries or applications may be relying onto
    ;; silent end of stream after full message is received
    ;; according to the size indicated by the protocol.
    ;;
    ;; See one example of this, discussion and links in
    ;; https://github.com/cl-plus-ssl/cl-plus-ssl/issues/166
    (if (and (eql error-code #.+ssl-error-syscall+)
             (not (zerop ret)))
        (error 'ssl-error-syscall
               :handle handle
               :ret error-code
               :printed-queue printed-queue
               :queue queue
               :syscall syscall)
        (error (case error-code
                 (#.+ssl-error-none+ 'ssl-error-none)
                 (#.+ssl-error-ssl+ 'ssl-error-ssl)
                 (#.+ssl-error-want-read+ 'ssl-error-want-read)
                 (#.+ssl-error-want-write+ 'ssl-error-want-write)
                 (#.+ssl-error-want-x509-lookup+ 'ssl-error-want-x509-lookup)
                 (#.+ssl-error-zero-return+ 'ssl-error-zero-return)
                 (#.+ssl-error-want-connect+ 'ssl-error-want-connect)
                 (#.+ssl-error-syscall+ 'ssl-error-zero-return) ; this is intentional here. we got an EOF from the syscall (ret is 0)
                 (t 'ssl-error/handle))
               :handle handle
               :ret error-code
               :printed-queue printed-queue
               :queue queue))))

(defparameter *ssl-verify-error-alist*
  '((0 :X509_V_OK)
    (2 :X509_V_ERR_UNABLE_TO_GET_ISSUER_CERT)
    (3 :X509_V_ERR_UNABLE_TO_GET_CRL)
    (4 :X509_V_ERR_UNABLE_TO_DECRYPT_CERT_SIGNATURE)
    (5 :X509_V_ERR_UNABLE_TO_DECRYPT_CRL_SIGNATURE)
    (6 :X509_V_ERR_UNABLE_TO_DECODE_ISSUER_PUBLIC_KEY)
    (7 :X509_V_ERR_CERT_SIGNATURE_FAILURE)
    (8 :X509_V_ERR_CRL_SIGNATURE_FAILURE)
    (9 :X509_V_ERR_CERT_NOT_YET_VALID)
    (10 :X509_V_ERR_CERT_HAS_EXPIRED)
    (11 :X509_V_ERR_CRL_NOT_YET_VALID)
    (12 :X509_V_ERR_CRL_HAS_EXPIRED)
    (13 :X509_V_ERR_ERROR_IN_CERT_NOT_BEFORE_FIELD)
    (14 :X509_V_ERR_ERROR_IN_CERT_NOT_AFTER_FIELD)
    (15 :X509_V_ERR_ERROR_IN_CRL_LAST_UPDATE_FIELD)
    (16 :X509_V_ERR_ERROR_IN_CRL_NEXT_UPDATE_FIELD)
    (17 :X509_V_ERR_OUT_OF_MEM)
    (18 :X509_V_ERR_DEPTH_ZERO_SELF_SIGNED_CERT)
    (19 :X509_V_ERR_SELF_SIGNED_CERT_IN_CHAIN)
    (20 :X509_V_ERR_UNABLE_TO_GET_ISSUER_CERT_LOCALLY)
    (21 :X509_V_ERR_UNABLE_TO_VERIFY_LEAF_SIGNATURE)
    (22 :X509_V_ERR_CERT_CHAIN_TOO_LONG)
    (23 :X509_V_ERR_CERT_REVOKED)
    (24 :X509_V_ERR_INVALID_CA)
    (25 :X509_V_ERR_PATH_LENGTH_EXCEEDED)
    (26 :X509_V_ERR_INVALID_PURPOSE)
    (27 :X509_V_ERR_CERT_UNTRUSTED)
    (28 :X509_V_ERR_CERT_REJECTED)
    (29 :X509_V_ERR_SUBJECT_ISSUER_MISMATCH)
    (30 :X509_V_ERR_AKID_SKID_MISMATCH)
    (31 :X509_V_ERR_AKID_ISSUER_SERIAL_MISMATCH)
    (32 :X509_V_ERR_KEYUSAGE_NO_CERTSIGN)
    (50 :X509_V_ERR_APPLICATION_VERIFICATION)))

(defun ssl-verify-error-keyword (code)
  (cadr (assoc code *ssl-verify-error-alist*)))

(defun ssl-verify-error-code (keyword)
  (caar (member keyword *ssl-verify-error-alist* :key #'cadr)))

(define-condition ssl-error-verify (ssl-error)
  ((stream :initarg :stream
           :reader ssl-error-stream
           :documentation "The SSL stream whose peer certificate didn't verify.")
   (error-code :initarg :error-code
               :reader ssl-error-code
               :documentation "The peer certificate verification error code
(as returned by functions like SSL_get_verify_result or X509_STORE_CTX_get_error)."))
  (:report (lambda (condition stream)
             (let ((code (ssl-error-code condition)))
               (format stream "SSL verify error: ~d~@[ ~a~]"
                       code (ssl-verify-error-keyword code)))))
  (:documentation "This condition is signalled on SSL connection when a peer certificate doesn't verify."))

(define-condition ssl-error-call (ssl-error)
  ((message :initarg :message))
  (:documentation
   "A failure in the SSL library occurred..")
  (:report (lambda (condition stream)
             (format stream "A failure in OpenSSL library occurred~@[: ~A~]. "
                     (slot-value condition 'message))
             (format-ssl-error-queue stream condition))))

(define-condition asn1-error (cl+ssl-error)
  ()
  (:documentation "Asn1 syntax error"))

(define-condition invalid-asn1-string (cl+ssl-error)
  ((type :initarg :type :initform nil))
  (:documentation "ASN.1 string parsing/validation error")
  (:report (lambda (condition stream)
             (format stream "ASN.1 syntax error: invalid asn1 string (expected type ~a)" (slot-value condition 'type))))) ;; TODO: when moved to grovel use enum symbol here

(define-condition server-certificate-missing (cl+ssl-error simple-error)
  ()
  (:documentation "SSL server didn't present a certificate"))
