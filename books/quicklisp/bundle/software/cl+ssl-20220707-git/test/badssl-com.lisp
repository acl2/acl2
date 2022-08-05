;;;; -*- Mode: LISP; Syntax: COMMON-LISP; indent-tabs-mode: nil; coding: utf-8; show-trailing-whitespace: t -*-

(in-package :cl+ssl.test)

(def-suite :cl+ssl.badssl-com :in :cl+ssl
  :description "Tests using badssl.com")

(in-suite :cl+ssl.badssl-com)


(defun test-connect (host &key (verify :required))
  (usocket:with-client-socket (socket stream host 443
                                      :element-type '(unsigned-byte 8))
    (cl+ssl:make-ssl-client-stream stream
                                   :hostname host
                                   :verify verify)))

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
