;;; Copyright (c) 2014 James M. Lawrence
;;; 
;;; Permission is hereby granted, free of charge, to any person
;;; obtaining a copy of this software and associated documentation
;;; files (the "Software"), to deal in the Software without
;;; restriction, including without limitation the rights to use, copy,
;;; modify, merge, publish, distribute, sublicense, and/or sell copies
;;; of the Software, and to permit persons to whom the Software is
;;; furnished to do so, subject to the following conditions:
;;; 
;;; The above copyright notice and this permission notice shall be
;;; included in all copies or substantial portions of the Software.
;;; 
;;; THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
;;; EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
;;; MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
;;; NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
;;; HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
;;; WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
;;; OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;;; DEALINGS IN THE SOFTWARE.

(defpackage #:global-vars-test
  (:use :cl :global-vars)
  (:export #:run))

(in-package #:global-vars-test)

(eval-when (:compile-toplevel :load-toplevel :execute)
  (defvar *a-call-count* 0)
  (defun a ()
    (incf *a-call-count*)
    :a))

(define-global-var -a- (a) "a")
(define-global-var -a- 99)

(eval-when (:compile-toplevel :load-toplevel :execute)
  (defvar *b-call-count* 0)
  (defun b ()
    (incf *b-call-count*)
    :b))

(define-global-parameter -b- (b) "b")
(define-global-parameter -b- 99)

(defparameter *c-call-count* 0)
(defun c ()
  (incf *c-call-count*)
  :c)

(define-global-var* -c- (c) "c")
(define-global-var* -c- 99)

(defparameter *d-call-count* 0)
(defun d ()
  (incf *d-call-count*)
  :d)

(define-global-parameter* -d- (d) "d")
(define-global-parameter* -d- 99)

(define-global-var -e- 99)

(defun run ()
  (assert (eq :a -a-))
  (assert (= 1 *a-call-count*))
  (assert (string= (documentation '-a- 'variable) "a"))
  (assert (eq 99 -b-))
  (assert (= 1 *b-call-count*))
  (assert (string= (documentation '-b- 'variable) "b"))
  (assert (eq :c -c-))
  (assert (= 1 *c-call-count*))
  (assert (string= (documentation '-c- 'variable) "c"))
  (assert (eq 99 -d-))
  (assert (= 1 *d-call-count*))
  (assert (string= (documentation '-d- 'variable) "d"))
  (assert (null (documentation '-e- 'variable)))
  (assert (eq '-w- (define-global-parameter -w- 0)))
  (assert (eq '-x- (define-global-parameter* -x- 0)))
  (assert (eq '-y- (define-global-var -y- 0)))
  (assert (eq '-z- (define-global-var* -z- 0)))
  (format t "~&global-vars tests passed.~%")
  (values))
