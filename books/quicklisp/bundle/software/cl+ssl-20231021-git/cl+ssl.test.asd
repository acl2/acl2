;;;; -*- Mode: LISP; Syntax: COMMON-LISP; indent-tabs-mode: nil; coding: utf-8; show-trailing-whitespace: t -*-
;;;
;;; Copyright (C) 2015 Ilya Khaprov <ilya.khaprov@publitechs.com>
;;;
;;; See LICENSE for details.

(defsystem :cl+ssl.test
  :version "0.1"
  :description "CL+SSL test suite"
  :maintainer "Ilya Khaprov <ilya.khaprov@publitechs.com>"
  :author "Ilya Khaprov <ilya.khaprov@publitechs.com>"
  :licence "MIT"
  :depends-on (:cl+ssl
               :fiveam
               :usocket
               :trivial-sockets ; for client-server.lisp
               :bordeaux-threads ; for client-server.lisp
               (:feature (:or :sbcl :ccl) :cl-coveralls))
  :serial t
  :components ((:module "test"
                :serial t
                :components
                ((:file "package")
                 (:file "dummy")
                 (:file "version")
                 (:file "sni")
                 (:file "cert-utilities")
                 (:file "validity-dates")
                 (:file "fingerprint")
                 (:file "verify-hostname")
                 (:file "badssl-com")
                 (:file "bio")
                 (:file "alpn")
                 (:file "client-server")))))
