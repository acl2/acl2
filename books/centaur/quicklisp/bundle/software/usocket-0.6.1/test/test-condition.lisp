;;;; $Id: test-condition.lisp 614 2011-03-30 08:16:10Z ctian $
;;;; $URL: svn://common-lisp.net/project/usocket/svn/usocket/tags/0.6.1/test/test-condition.lisp $

(in-package :usocket-test)

(deftest ns-host-not-found-error.1
  (with-caught-conditions (usocket:ns-host-not-found-error nil)
    (usocket:socket-connect "xxx" 123)
    t)
  nil)

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
    (usocket:socket-listen "0.0.0.0" 81)
    t)
  nil)
