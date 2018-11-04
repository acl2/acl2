;;; -*- mode: lisp -*-
;;;
;;; Copyright (C) 2015 Ilya Khaprov <ilya.khaprov@publitechs.com>
;;;
;;; See LICENSE for details.

(defpackage :cl+ssl.test-system
  (:use :cl :asdf))

(in-package :cl+ssl.test-system)

(asdf:defsystem :cl+ssl.test
  :version "0.1"
  :description "CL+SSL test suite"
  :maintainer "Ilya Khaprov <ilya.khaprov@publitechs.com>"
  :author "Ilya Khaprov <ilya.khaprov@publitechs.com>"
  :licence "MIT"
  :depends-on (:fiveam
               (:feature (:or :sbcl :ccl) :cl-coveralls)
               :cl+ssl
               :openssl-1.1.0 ;; for now the dependency is only included to test how the system is loaded
               :usocket)
  :serial t
  :components ((:module "test"
                :serial t
                :components
                ((:file "package")
                 (:file "dummy")
                 (:file "sni")
                 (:file "verify-hostname")
                 (:file "badssl-com")))))
