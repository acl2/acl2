; Matt Kaufmann
; Copyright (C) 2019, Regents of the University of Texas
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.
; Contributing Author: Alessandro Coglio (coglio@kestrel.edu)

(in-package "ACL2")

(include-book "misc/eval" :dir :system)

;;; Check various combinations of :guard, :verify-guards, and
;;; verify-guards-eagerness.

;;; First, default-verify-guards-eagerness = 1 (default).

(defun-sk fn{g+}{vg-t}{e1} (x)
  (declare (xargs :guard t :verify-guards t))
  (exists y (equal y (cons x x))))

(assert-event (equal (symbol-class 'fn{g+}{vg-t}{e1} (w state))
                     :COMMON-LISP-COMPLIANT))

(defun-sk fn{g+}{vg-nil}{e1} (x)
  (declare (xargs :guard t :verify-guards nil))
  (exists y (equal y (cons x x))))

(assert-event (equal (symbol-class 'fn{g+}{vg-nil}{e1} (w state))
                     :IDEAL))

(defun-sk fn{g-}{vg-t}{e1} (x)
  (declare (xargs :verify-guards t))
  (exists y (equal y (cons x x))))

(assert-event (equal (symbol-class 'fn{g+}{vg-t}{e1} (w state))
                     :COMMON-LISP-COMPLIANT))

(defun-sk fn{g-}{vg-nil}{e1} (x)
  (declare (xargs :verify-guards nil))
  (exists y (equal y (cons x x))))

(assert-event (equal (symbol-class 'fn{g+}{vg-nil}{e1} (w state))
                     :IDEAL))

(defun-sk fn{g+}{vg-}{e1} (x)
  (declare (xargs :guard t))
  (exists y (equal y (cons x x))))

(assert-event (equal (symbol-class 'fn{g+}{vg-}{e1} (w state))
                     :COMMON-LISP-COMPLIANT))

(defun-sk fn{g-}{vg-}{e1} (x)
  (exists y (equal y (cons x x))))

(assert-event (equal (symbol-class 'fn{g-}{vg-}{e1} (w state))
                     :IDEAL))

;;; Next, default-verify-guards-eagerness = 0.

(set-verify-guards-eagerness 0)

(defun-sk fn{g+}{vg-t}{e0} (x)
  (declare (xargs :guard t :verify-guards t))
  (exists y (equal y (cons x x))))

(assert-event (equal (symbol-class 'fn{g+}{vg-t}{e0} (w state))
                     :COMMON-LISP-COMPLIANT))

(defun-sk fn{g+}{vg-nil}{e0} (x)
  (declare (xargs :guard t :verify-guards nil))
  (exists y (equal y (cons x x))))

(assert-event (equal (symbol-class 'fn{g+}{vg-nil}{e0} (w state))
                     :IDEAL))

(defun-sk fn{g-}{vg-t}{e0} (x)
  (declare (xargs :verify-guards t))
  (exists y (equal y (cons x x))))

(assert-event (equal (symbol-class 'fn{g+}{vg-t}{e0} (w state))
                     :COMMON-LISP-COMPLIANT))

(defun-sk fn{g-}{vg-nil}{e0} (x)
  (declare (xargs :verify-guards nil))
  (exists y (equal y (cons x x))))

(assert-event (equal (symbol-class 'fn{g+}{vg-nil}{e0} (w state))
                     :IDEAL))

(defun-sk fn{g+}{vg-}{e0} (x)
  (declare (xargs :guard t))
  (exists y (equal y (cons x x))))

(assert-event (equal (symbol-class 'fn{g+}{vg-}{e0} (w state))
                     :IDEAL))

(defun-sk fn{g-}{vg-}{e0} (x)
  (exists y (equal y (cons x x))))

(assert-event (equal (symbol-class 'fn{g-}{vg-}{e0} (w state))
                     :IDEAL))

;;; Next, default-verify-guards-eagerness = 2.

(set-verify-guards-eagerness 2)

(defun-sk fn{g+}{vg-t}{e2} (x)
  (declare (xargs :guard t :verify-guards t))
  (exists y (equal y (cons x x))))

(assert-event (equal (symbol-class 'fn{g+}{vg-t}{e2} (w state))
                     :COMMON-LISP-COMPLIANT))

(defun-sk fn{g+}{vg-nil}{e2} (x)
  (declare (xargs :guard t :verify-guards nil))
  (exists y (equal y (cons x x))))

(assert-event (equal (symbol-class 'fn{g+}{vg-nil}{e2} (w state))
                     :IDEAL))

(defun-sk fn{g-}{vg-t}{e2} (x)
  (declare (xargs :verify-guards t))
  (exists y (equal y (cons x x))))

(assert-event (equal (symbol-class 'fn{g+}{vg-t}{e2} (w state))
                     :COMMON-LISP-COMPLIANT))

(defun-sk fn{g-}{vg-nil}{e2} (x)
  (declare (xargs :verify-guards nil))
  (exists y (equal y (cons x x))))

(assert-event (equal (symbol-class 'fn{g+}{vg-nil}{e2} (w state))
                     :IDEAL))

(defun-sk fn{g+}{vg-}{e2} (x)
  (declare (xargs :guard t))
  (exists y (equal y (cons x x))))

(assert-event (equal (symbol-class 'fn{g+}{vg-}{e2} (w state))
                     :COMMON-LISP-COMPLIANT))

(defun-sk fn{g-}{vg-}{e2} (x)
  (exists y (equal y (cons x x))))

(assert-event (equal (symbol-class 'fn{g-}{vg-}{e2} (w state))
                     :COMMON-LISP-COMPLIANT))

;;; Check :constrain t.  In particular, the :constrain keyword is ignored for
;;; purposes of guard verification, in that guards are always verified for the
;;; constrained function.

(defun-sk f-constrained (x)
  (declare (xargs :verify-guards nil))
  (exists y (equal y (car x)))
  :constrain t)

(assert-event (equal (symbol-class 'f-constrained (w state))
                     :COMMON-LISP-COMPLIANT))

;;; No guard verification is performed when :constrain is t (even for the local
;;; function).

(defun-sk f-constrained-2 (x)
  (declare (xargs :verify-guards t))
  (exists y (equal y (car x)))
  :constrain t)

(assert-event (equal (symbol-class 'f-constrained (w state))
                     :COMMON-LISP-COMPLIANT))

(defun constant-t-function-arity-1 (x)
  (declare (xargs :mode :logic :guard t)
           (ignore x))
  t)

(defun safe-car (x)
  (declare (xargs :guard t))
  (and (consp x)
       (car x)))

(defattach
  (f-constrained constant-t-function-arity-1)
  (f-constrained-witness safe-car))

;;; Better error messages for duplicate xargs keywords:

(must-fail
 (defun-sk f (x)
   (declare (xargs :verify-guards nil :verify-guards t))
   (exists y (equal y (car x)))))

(must-fail
 (defun-sk f (x)
   (declare (xargs :non-executable nil :non-executable t))
   (exists y (equal y (car x)))))

(must-fail
 (defun-sk f (x)
   (declare (xargs :guard-hints (("Goal" :use nth))
                   :guard-hints (("Goal" :use nth))))
   (exists y (equal y (car x)))))

;;; Test the use of defun-nx vs. defun.

(defun-sk f-non-exec (x)
  (exists y (equal y (car (mv x x)))))

(defun-sk f-non-exec-2 (x)
  (declare (xargs :non-executable t))
  (exists y (equal y (car (mv x x)))))

(must-fail
 (defun-sk f (x)
   (declare (xargs :non-executable nil))
   (exists y (equal y (car (mv x x))))))

(defun-sk f-exec (x)
  (declare (xargs :non-executable nil))
  (exists y (equal y (cons x x))))

;;; Test the correct generation of the :hints keyword in the generated
;;; verify-guards or verify-guards? events.

(defun-sk fa-guard-hints (x)
  (declare (xargs :guard t
                  :verify-guards t
                  :guard-hints (("Goal" :in-theory (enable len)))))
  (forall y (equal y x)))

(defun-sk ex-guard-hints (x)
  (declare (xargs :guard t
                  :verify-guards t
                  :guard-hints (("Goal" :in-theory (enable len)))))
  (exists y (equal y x)))
