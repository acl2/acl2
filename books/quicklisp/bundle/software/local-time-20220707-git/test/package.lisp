(cl:in-package :cl-user)

(defpackage :local-time.test
  (:use :alexandria
        :common-lisp
        :hu.dwim.stefil
        :local-time))

(in-package :local-time.test)

(defsuite* (test :in root-suite) ()
  (local-time::reread-timezone-repository)
  (run-child-tests))
