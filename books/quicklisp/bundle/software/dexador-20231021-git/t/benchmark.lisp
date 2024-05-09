(in-package :cl-user)
(defpackage dexador-test.benchmark
  (:use :cl))
(in-package :dexador-test.benchmark)

(defun run-benchmark ()
  (clack:clackup
   (lambda (env)
     (declare (ignore env))
     (list 200 ()))))
