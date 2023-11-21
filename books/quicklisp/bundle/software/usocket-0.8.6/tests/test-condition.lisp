;;;; -*- Mode: LISP; Base: 10; Syntax: ANSI-Common-lisp; Package: USOCKET-TEST -*-
;;;; See LICENSE for licensing information.

(in-package :usocket-test)

(deftest ns-host-not-found-error.1
  (with-caught-conditions (usocket:ns-host-not-found-error nil)
    (usocket:socket-connect "xxx" 123)
    t)
  nil)


;;; This test does not work, if timeout is ignored by the implementation
;;; Will get a connection-refused-error instead
 #-(or ecl clasp)
(deftest timeout-error.1
  (with-caught-conditions (usocket:timeout-error nil)
    (usocket:socket-connect "common-lisp.net" 81 :timeout 0)
    t)
  nil)

(deftest connection-refused-error.1
  (with-caught-conditions (usocket:connection-refused-error nil)
    (usocket:socket-connect "common-lisp.net" 81)
    t)
  nil)

(deftest operation-not-permitted-error.1
  (with-caught-conditions (usocket:operation-not-permitted-error nil)
    (usocket:socket-listen "127.0.0.1" 81)
    t)
  nil)
