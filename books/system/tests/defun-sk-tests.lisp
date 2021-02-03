; Matt Kaufmann
; Copyright (C) 2019, Regents of the University of Texas
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.
; Contributing Author: Alessandro Coglio (coglio@kestrel.edu)

(in-package "ACL2")

(include-book "std/testing/must-fail" :dir :system)

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

(assert-event (equal (f-constrained '(a b)) t))
(assert-event (equal (f-constrained-witness '(a b)) 'a))

;;; No guard verification is performed when :constrain is t (even for the local
;;; function).

(defun-sk f-constrained-2 (x)
  (declare (xargs :verify-guards t))
  (exists y (equal y (car x)))
  :constrain t)

(assert-event (equal (symbol-class 'f-constrained (w state))
                     :COMMON-LISP-COMPLIANT))

;;; Specified :guard is honored even in the case of :constrain t.

(defun-sk f-constrained-3 (x)
  (declare (xargs :guard (and (consp x)
                              (equal (len x) 3))))
  (exists y (equal y (car x)))
  :constrain t)

(assert-event ; failed through 8/24/2020 (guard was 'T)
 (equal (guard 'f-constrained-3 nil (w state))
        '(IF (CONSP X) (EQUAL (LEN X) '3) 'NIL)))

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

;;; Test with stobjs

(defstobj st fld)
(defstub p0 (* * st) => *)
(defstub q0 (* * st) => *)

(defun-sk exists-x-p0-and-q0 (y st)
  (declare (type integer y)
           (xargs :stobjs st
                  :guard (< 3 y)))
  (exists x
    (and (p0 x y st)
         (q0 x y st))))

(assert-event (equal (guard 'exists-x-p0-and-q0 nil (w state))
                     '(IF (STP ST)
                          (IF (INTEGERP Y) (< '3 Y) 'NIL)
                          'NIL)))

(assert-event (equal (guard 'exists-x-p0-and-q0 t (w state))
                     '(IF (INTEGERP Y) (< '3 Y) 'NIL)))

; failed through 8/24/2020:
(defun-sk exists-x-p0-and-q0-constrained (y st)
  (declare (xargs :guard (equal (len y) 3))
           (xargs :stobjs st))
  (exists x
    (and (p0 x y st)
         (q0 x y st)))
  :constrain t)

(assert-event (equal (guard 'exists-x-p0-and-q0-constrained nil (w state))
                     '(IF (STP ST) (EQUAL (LEN Y) '3) 'NIL)))

(assert-event (equal (guard 'exists-x-p0-and-q0-constrained t (w state))
                     '(EQUAL (LEN Y) '3)))

;;; Test with state

(set-state-ok t)

(defstub p1 (* * state) => *)
(defstub q1 (* * state) => *)

; failed through 8/24/2020:
(defun-sk exists-x-p1-and-q1 (y state)
  (declare (xargs :guard (equal (len y) 3)))
  (exists x
    (and (p1 x y state)
         (q1 x y state))))

(assert-event (equal (guard 'exists-x-p1-and-q1 nil (w state))
                     '(IF (STATE-P STATE) (EQUAL (LEN Y) '3) 'NIL)))

(assert-event (equal (guard 'exists-x-p1-and-q1 t (w state))
                     '(EQUAL (LEN Y) '3)))

; failed through 8/24/2020:
(defun-sk exists-x-p1-and-q1-constrained (y state)
  (declare (xargs :guard (equal (len y) 3))
           (xargs :stobjs state))
  (exists x
    (and (p1 x y state)
         (q1 x y state)))
  :constrain t)

(assert-event (equal (guard 'exists-x-p1-and-q1-constrained nil (w state))
                     '(IF (STATE-P STATE) (EQUAL (LEN Y) '3) 'NIL)))

;;; Test (sufficient) redundancy of "downgrade" from guard-verified to not

(defun-sk g1 (x)
  (declare (xargs :guard t))
  (forall y (equal x y)))

;;; failed through 8/24/2020:
(defun-sk g1 (x)
  (forall y (equal x y)))

(defun-sk g2 (x st)
  (declare (xargs :stobjs st :guard t))
  (forall y (equal x (cons y (fld st)))))

;;; failed through 8/24/2020:
(defun-sk g2 (x st)
  (declare (xargs :stobjs st))
  (forall y (equal x (cons y (fld st)))))

(defun-sk g2 (x st)
  (declare (xargs :guard t :stobjs st))
  (forall y (equal x (cons y (fld st)))))

;;; failed through 8/24/2020
(defun-sk g3 (x a b)
  (declare (ignorable a)
           (xargs :guard t)
           (ignorable b))
  (forall y (equal x y)))

;;; Test ignorable declarations

;;; failed through 8/24/2020
(defun-sk g3 (x a b)
  (declare (ignorable a)
           (ignorable b))
  (forall y (equal x y)))
