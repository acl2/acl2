;;;; -*- Mode: LISP; Syntax: ANSI-Common-Lisp; Base: 10 -*-
;;;; *************************************************************************
;;;; FILE IDENTIFICATION
;;;;
;;;; Name:          cl-base64.asd
;;;; Purpose:       ASDF definition file for Cl-Base64
;;;; Programmer:    Kevin M. Rosenberg
;;;; Date Started:  Dec 2002
;;;; *************************************************************************

(in-package #:cl-user)
(defpackage #:cl-base64-system (:use #:asdf #:cl))
(in-package #:cl-base64-system)

(defsystem cl-base64
  :name "cl-base64"
  :author "Kevin M. Rosenberg based on initial code by Juri Pakaste"
  :version "3.4"
  :maintainer "Kevin M. Rosenberg <kmr@debian.org>"
  :licence "BSD-style"
  :description "Base64 encoding and decoding with URI support."
  :components
  ((:file "package")
   (:file "encode" :depends-on ("package"))
   (:file "decode" :depends-on ("package")))
  :in-order-to ((test-op (test-op "cl-base64/test"))))

(defsystem cl-base64/test
    :depends-on (cl-base64 ptester kmrcl)
    :components
    ((:file "tests"))
    :perform (test-op (o s)
                      (or (funcall (intern (symbol-name '#:do-tests)
                                           (find-package '#:cl-base64/test)))
                          (error "test-op failed"))))
