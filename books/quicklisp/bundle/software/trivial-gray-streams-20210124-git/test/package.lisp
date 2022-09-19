;;;; -*- Mode: LISP; Base: 10; Syntax: ANSI-Common-lisp; Package: CL-USER -*-

(defpackage trivial-gray-streams-test 
  (:use :cl #:trivial-gray-streams)
  (:shadow #:method)
  (:export #:run-tests
           #:failed-test-names))

