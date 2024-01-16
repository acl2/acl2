;;;; -*- Mode: LISP; Base: 10; Syntax: ANSI-Common-lisp; Package: CL-USER -*-
;;;; See the LICENSE file for licensing information.

(in-package :cl-user)

(defpackage :usocket-test
  (:use :common-lisp
	:usocket
	:regression-test)
  (:export #:do-tests
	   #:run-usocket-tests))
