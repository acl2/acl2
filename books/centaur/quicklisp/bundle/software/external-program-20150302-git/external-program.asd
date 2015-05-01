;;; Copyright 2006-2008 Greg Pfeil
;;; Distributed under the LLGPL (see LICENSE file)

(defpackage external-program-system
  (:use #:cl #:asdf))

(in-package :external-program-system)

(defsystem external-program
  :author "Greg Pfeil <greg@technomadic.org>"
  :licence "LLGPL"
  :version "0.0.6"
  :pathname "src/"
  :components ((:file "external-program")
               (:file "utilities" :depends-on ("external-program"))
               (:file #+allegro "allegro"
                      #+armedbear "armedbear"
                      #+clisp "clisp"
                      #+cmu "cmucl"
                      #+ecl "ecl"
                      ;; #+gcl "gcl"
                      ;; #+liquid "liquid"
                      #+lispworks "lispworks"
                      ;; #+lucid "lucid"
                      #+openmcl "openmcl"
                      #+sbcl "sbcl"
                      ;; #+scl "scieneer"
                      #-(or allegro armedbear clisp cmu ecl lispworks openmcl
                            sbcl)
                      "unsupported"
                      :depends-on ("utilities")))
  :in-order-to ((test-op (load-op external-program-test)))
  :perform (test-op :after (op c)
                    (funcall (intern "RUN!" :external-program-tests)
                             (intern "TESTS" :external-program-tests))))

(defmethod operation-done-p
    ((op test-op) (c (eql (find-system :external-program))))
  (values nil))

(defsystem external-program-test
  :depends-on (external-program fiveam)
  :pathname "tests/"
  :components ((:file "tests")))
