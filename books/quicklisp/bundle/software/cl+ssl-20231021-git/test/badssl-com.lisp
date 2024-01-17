;;;; -*- Mode: LISP; Syntax: COMMON-LISP; indent-tabs-mode: nil; coding: utf-8; show-trailing-whitespace: t -*-
;;;
;;; Copyright (C) contributors as per cl+ssl git history
;;;
;;; See LICENSE for details.

(in-package :cl+ssl.test)

(def-suite :cl+ssl.badssl-com :in :cl+ssl
  :description "Tests using badssl.com")

(in-suite :cl+ssl.badssl-com)


(defun test-connect (host &key (verify :required))
  (let ((sock (usocket:socket-connect host 443
                                      :element-type '(unsigned-byte 8))))
    (unwind-protect
         (cl+ssl:make-ssl-client-stream (usocket:socket-stream sock)
                                        :hostname host
                                        :verify verify)
      (usocket:socket-close sock))))

(defmacro modal-test (name &body body)
  "Defines two tests, with equal body, but first executed using file descriptor BIO,
and the other executed with Lisp BIO."
  `(progn
     (test ,(read-from-string (format nil "~A.file-descriptor-bio" name))
       (let ((cl+ssl::*default-unwrap-stream-p* t))
         ,@body))
     (test ,(read-from-string (format nil "~A.lisp-bio" name))
       (let ((cl+ssl::*default-unwrap-stream-p* nil))
         ,@body))))

(modal-test wrong.host
  (signals error
    (test-connect "wrong.host.badssl.com"))
  (signals error
    (test-connect "wrong.host.badssl.com" :verify :optional))
  (finishes
    (test-connect "wrong.host.badssl.com" :verify nil)))

(modal-test expired
  (signals error
    (test-connect "expired.badssl.com"))
  (signals error
    (test-connect "expired.badssl.com" :verify :optional))
  (finishes
    (test-connect "expired.badssl.com" :verify nil)))

(modal-test self-signed
  (signals error
    (test-connect "self-signed.badssl.com")))

(modal-test untrusted-root
  (signals error
    (test-connect "untrusted-root.badssl.com")))

(modal-test verify-error-details
  ;; When SSL_Connect fails due to certificatie
  ;; verification enabled by the SSL_VERIFY_PEER,
  ;; the error condition should include the
  ;; return value of SSL_get_verify_result.
  (let* ((ctx (cl+ssl:make-context :verify-callback nil
                                   :verify-mode cl+ssl::+ssl-verify-peer+))
         (condition (handler-case
                        (cl+ssl:with-global-context (ctx :auto-free-p t)
                          (test-connect "expired.badssl.com" :verify nil))
                      (cl+ssl::ssl-error-ssl (c) c))))
    (is (search "SSL_get_verify_result:"
                (format nil "~A" condition)))))
