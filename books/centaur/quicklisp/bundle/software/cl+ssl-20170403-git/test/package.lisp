(in-package :cl-user)

(defpackage :cl+ssl.test
  (:use :cl
        :alexandria   
        :5am))

(in-package :cl+ssl.test)

(def-suite :cl+ssl
  :description "Main test suite for CL+SSL")
