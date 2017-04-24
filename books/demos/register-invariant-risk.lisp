; Copyright (C) 2017, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; In this book we show that execution of (set-register-invariant-risk nil) has
; removed invariant-risk checking for functions defined in
; register-invariant-risk-support.lisp.  See also :doc invariant-risk.

(in-package "ACL2")

(include-book "register-invariant-risk-support")

(defmacro test-rir (form &key (check ':error))
  `(make-event (er-progn (set-check-invariant-risk ,check)
                         (trans-eval ',form 'test-rir state nil)
                         (value '(value-triple :success)))))


(test-rir (foo-program-wrapper 3 st))

; The following may be run in the ACL2 loop after including this book.
; Some cause errors, as mentioned in comments below.

#||

; Works OK (no surprise at all, since 3 satisfies the guard):
(test-rir (update-fld 3 st))

; Not OK (ordinary guard violation):
(test-rir (update-fld nil st))

(set-guard-checking :none)

; Still a guard violation (because a live stobj is involved):
(test-rir (update-fld nil st))

; Back to normal:
(set-guard-checking t)

; Next, we define analogues of foo and foo-program-wrapper (from
; register-invariant-risk-support.lisp) and see that this time we get
; invariant-risk checking, which supports the claim that the alleged
; defeat of invariant-risk checking for foo really did work.

(defun foo2 (n st)
  (declare (xargs :stobjs st :verify-guards nil))
  (update-fld n st))

(defun foo2-program-wrapper (n st)
  (declare (xargs :stobjs st :mode :program))
  (if (integerp n) ; avoid invariant-risk possibility ;
      (foo2 n st)
    (prog2$ (cw "No change due to bad argument: ~x0"
                n)
            (foo2 n st))))

(test-rir (foo2-program-wrapper 3 st))

||#
