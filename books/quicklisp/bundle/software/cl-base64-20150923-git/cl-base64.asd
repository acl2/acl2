;;;; -*- Mode: LISP; Syntax: ANSI-Common-Lisp; Base: 10 -*-
;;;; *************************************************************************
;;;; FILE IDENTIFICATION
;;;;
;;;; Name:          cl-base64.asd
;;;; Purpose:       ASDF definition file for Cl-Base64
;;;; Programmer:    Kevin M. Rosenberg
;;;; Date Started:  Dec 2002
;;;;
;;;; $Id$
;;;; *************************************************************************

(in-package #:cl-user)
(defpackage #:cl-base64-system (:use #:asdf #:cl))
(in-package #:cl-base64-system)


(defsystem cl-base64
  :name "cl-base64"
  :author "Kevin M. Rosenberg based on initial code by Juri Pakaste"
  :version "3.1"
  :maintainer "Kevin M. Rosenberg <kmr@debian.org>"
  :licence "BSD-style"
  :description "Base64 encoding and decoding with URI support."
  :components
  ((:file "package")
   (:file "encode" :depends-on ("package"))
   (:file "decode" :depends-on ("package"))
   ))

(defmethod perform ((o test-op) (c (eql (find-system 'cl-base64))))
  (operate 'load-op 'cl-base64-tests)
  (operate 'test-op 'cl-base64-tests :force t))

(defsystem cl-base64-tests
    :depends-on (cl-base64 ptester kmrcl)
    :components
    ((:file "tests")))

(defmethod perform ((o test-op) (c (eql (find-system 'cl-base64-tests))))
  (operate 'load-op 'cl-base64-tests)
  (or (funcall (intern (symbol-name '#:do-tests)
		       (find-package '#:cl-base64-tests)))
      (error "test-op failed")))
