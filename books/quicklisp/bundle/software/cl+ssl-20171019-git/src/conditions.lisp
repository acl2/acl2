;;;; -*- Mode: LISP; Syntax: COMMON-LISP; indent-tabs-mode: nil; coding: utf-8; show-trailing-whitespace: t -*-
;;;
;;; Copyright (C) 2001, 2003  Eric Marsden
;;; Copyright (C) 2005  David Lichteblau
;;; "the conditions and ENSURE-SSL-FUNCALL are by Jochen Schmidt."
;;;
;;; See LICENSE for details.

#+xcvb (module (:depends-on ("package")))

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
   (queue :initform nil :initarg :queue :reader ssl-error-queue)))

(define-condition ssl-error/handle (ssl-error)
  ((ret :initarg :ret
        :reader ssl-error-ret)
   (handle :initarg :handle
           :reader ssl-error-handle))
  (:report (lambda (condition stream)
             (format stream "Unspecified error ~A on handle ~A~%"
                     (ssl-error-ret condition)
                     (ssl-error-handle condition))
       (format-ssl-error-queue stream condition))))

(define-condition ssl-error-initialize (ssl-error)
  ((reason  :initarg :reason
            :reader ssl-error-reason))
  (:report (lambda (condition stream)
             (format stream "SSL initialization error: ~A~%"
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
             (format stream "The TLS/SSL operation on handle ~A completed (return code: ~A).~%"
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
             (format stream "The TLS/SSL connection on handle ~A has been closed (return code: ~A).~%"
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
             (format stream "The TLS/SSL operation on handle ~A did not complete: It wants a READ (return code: ~A).~%"
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
             (format stream "The TLS/SSL operation on handle ~A did not complete: It wants a WRITE (return code: ~A).~%"
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
            (format stream "The TLS/SSL operation on handle ~A did not complete: It wants a connect first (return code: ~A).~%"
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
             (format stream "The TLS/SSL operation on handle ~A did not complete: An application callback wants to be called again (return code: ~A).~%"
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
                   (0 (format stream "An I/O error occurred: An unexpected EOF was observed on handle ~A (return code: ~A).~%"
                              (ssl-error-handle condition)
                              (ssl-error-ret condition)))
                   (-1 (format stream "An I/O error occurred in the underlying BIO (return code: ~A).~%"
                               (ssl-error-ret condition)))
                   (otherwise (format stream "An I/O error occurred: undocumented reason (return code: ~A).~%"
                                      (ssl-error-ret condition))))
                 (format stream "An UNKNOWN I/O error occurred in the underlying BIO (return code: ~A).~%"
                         (ssl-error-ret condition)))
       (format-ssl-error-queue stream condition))))

;; SSL_ERROR_SSL
(define-condition ssl-error-ssl (ssl-error/handle)
  ()
  (:documentation
   "A failure in the SSL library occurred, usually a protocol error. The
    OpenSSL error queue contains more information on the error.")
  (:report (lambda (condition stream)
             (format stream
         "A failure in the SSL library occurred on handle ~A (return code: ~A).~%"
                     (ssl-error-handle condition)
                     (ssl-error-ret condition))
       (format-ssl-error-queue stream condition))))

(defun ssl-signal-error (handle syscall error-code original-error)
  (let ((queue (read-ssl-error-queue)))
    (if (and (eql error-code #.+ssl-error-syscall+)
       (not (zerop original-error)))
  (error 'ssl-error-syscall
         :handle handle
         :ret error-code
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
               :documentation "The peer certificate verification error code."))
  (:report (lambda (condition stream)
             (let ((code (ssl-error-code condition)))
               (format stream "SSL verify error: ~d~@[ ~a~]"
                       code (ssl-verify-error-keyword code)))))
  (:documentation "This condition is signalled on SSL connection when a peer certificate doesn't verify."))

(define-condition ssl-error-call (cl+ssl::ssl-error)
  ((message :initarg :message))
  (:documentation
   "A failure in the SSL library occurred..")
  (:report (lambda (condition stream)
             (format stream "A failure in OpenSSL library occurred~@[: ~A~].~%" (slot-value condition 'message)) (cl+ssl::format-ssl-error-queue stream (cl+ssl::ssl-error-queue condition)))))

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
