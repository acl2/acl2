; Copyright (C) 2013, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This variant of assert.lisp runs assertions at all times, rather than
; skipping them during include-book and the second pass of encapsulate.  The
; comment below "Specific to this file", below, describes the interesting
; difference between this file and assert.lisp.

(in-package "ACL2")

(defun assert!!-body (assertion form)
  `(let ((assertion ,assertion))
     (er-progn
      (if assertion
          (value nil)
        (er soft 'assertion
            "Assertion failed:~%~x0"
            '(assert!! ,assertion ,@(and form (list form)))))
      (value ',(or form '(value-triple nil))))))

(defmacro assert!! (&whole whole-form
                           assertion &optional form)
  (list 'make-event (assert!!-body assertion form)
        :check-expansion t
        :on-behalf-of whole-form))

(assert!! (equal 3 3)
          (defun assert-test1 (x) x))

; Check that above defun was evaluated.
(value-triple (or (equal (assert-test1 3) 3)
                  (er hard 'top-level
                      "Failed to evaluate (assert-test1 3) to 3.")))

(include-book "eval-check")

(must-fail
 (assert!! (equal 3 4)
           (defun assert-test2 (x) x)))

; Check that above defun was not evaluated.
(defun assert-test2 (x)
  (cons x x))

; Simple test with no second argument:
(assert!! (equal (append '(a b c) '(d e f))
                 '(a b c d e f)))

; Check failure of assertion when condition is false:
(must-fail
 (assert!! (equal (append '(a b c) '(d e f))
                  '(a b))))

(deflabel completed-successes)

; Specific to this file:

; The following requires that this book be certified in the initial
; certification world.  It should fail at include-book time if we include the
; book after executing another command, because assert!! uses make-event with
; :check-expansion t.  See assert-check-include.lisp for a successful
; include-book and assert-check-include-1.lisp (and
; assert-check-include-1.acl2) for a failed include-book.

(assert!! (equal (access-command-tuple-form
                  (cddr (car (scan-to-command (w state)))))
                 '(exit-boot-strap-mode)))

; Make sure we get to the end when we include this book under
; assert-check-include.lisp but not under under assert-check-include-1.lisp.
(defun assert-check-end (x)
  x)
