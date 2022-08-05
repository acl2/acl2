(in-package :common-lisp-user)

(defpackage :cl-fad-test
  (:use :cl :cl-fad :unit-test)
  (:shadowing-import-from :cl-fad :pathname-directory-equal)
  (:export :test))
