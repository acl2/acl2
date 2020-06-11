;;;; -*- Mode: Lisp -*-

;;;; See the LICENSE file for licensing information.

(defsystem usocket-test
    :name "usocket test"
    :author "Erik Enge"
    :maintainer "Chun Tian (binghe)"
    :version (:read-file-form "version.sexp")
    :licence "MIT"
    :description "Tests for usocket"
    :depends-on (:usocket-server
		 :rt)
    :components ((:module "test"
		  :serial t
		  :components ((:file "package")
			       (:file "test-usocket")
			       (:file "test-condition")
			       (:file "test-datagram")
			       (:file "wait-for-input")))))

(defmethod perform ((op test-op) (c (eql (find-system :usocket-test))))
  (funcall (intern "DO-TESTS" "USOCKET-TEST")))
