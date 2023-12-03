;;;; -*- Mode: Lisp -*-

;;;; See the LICENSE file for licensing information.

(defsystem usocket-test
    :name "usocket test"
    :author "Erik Enge"
    :maintainer "Chun Tian (binghe)"
    :version (:read-file-form "version.sexp")
    :licence "MIT"
    :description "Tests for usocket"
    :depends-on (:usocket-server :rt)
    :components ((:module "tests"
                  :serial t
                  :components ((:file "package")
                               (:file "test-usocket")
                               (:file "test-condition")
                               (:file "test-datagram")
                               (:file "test-timeout")
                               (:file "wait-for-input"))))
    :perform (test-op (o c) (symbol-call :usocket-test :do-tests)))
