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

(test wrong.host
  (signals error
    (test-connect "wrong.host.badssl.com"))
  (signals error
    (test-connect "wrong.host.badssl.com" :verify :optional))
  (finishes
    (test-connect "wrong.host.badssl.com" :verify nil)))

(test expired
  (signals error
    (test-connect "expired.badssl.com"))
  (signals error
    (test-connect "expired.badssl.com" :verify :optional))
  (finishes
    (test-connect "expired.badssl.com" :verify nil)))

(test self-signed
  (signals error
    (test-connect "self-signed.badssl.com")))

(test untrusted-root
  (signals error
    (test-connect "untrusted-root.badssl.com")))
