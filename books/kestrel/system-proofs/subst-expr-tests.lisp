; Tests and examples for subst-expr.lisp
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

; cert_param: (non-acl2r)

;; Counterexamples and examples for the theorems in subst-expr.lisp.  This
;; book is not included by top.lisp.

(include-book "subst-expr")
(include-book "std/testing/must-fail" :dir :system)

;; Without the normal-form hypothesis, OLD can remain: here CONS-TERM
;; evaluates (binary-+ '1 '2), making the result equal to OLD.
(defthm subst-expr1-can-leave-old
  (equal (subst-expr1 'v '(f '3) '(f (binary-+ '1 '2)))
         '(f '3))
  :rule-classes nil)

;; This seldom matters in practice, because the terms that reach subst-expr
;; are usually already in the normal form that cons-term produces: the prover
;; normalizes clauses (even inside HIDE), and remove-guard-holders normalizes
;; rule conclusions, except inside HIDE.  So it can show up for a
;; :type-prescription rule whose :typed-term is a HIDE call:

(defun h (x) (nfix x))

(defthm h-type (natp (h x)) :rule-classes :type-prescription)

(in-theory (disable h (:e h)))

;; The formula is a theorem:
(defthm tp-formula
  (natp (hide (h (+ 1 2))))
  :hints (("Goal" :expand ((:free (x) (hide x)))))
  :rule-classes nil)

;; But this event is rejected ("its conclusion is not a disjunction of type
;; restrictions about the :TYPED-TERM (HIDE (H '3))"), because
;; (subst-expr new-var '(hide (h '3)) '(natp (hide (h (binary-+ '1 '2))))) is
;; (natp (hide (h '3))):
(must-fail
 (defthm tp
   (natp (hide (h (+ 1 2))))
   :hints (("Goal" :expand ((:free (x) (hide x)))))
   :rule-classes ((:type-prescription :typed-term (hide (h 3))))))

;; The event is accepted if the :typed-term is written (hide (h (+ 1 2))):
(defthm tp
  (natp (hide (h (+ 1 2))))
  :hints (("Goal" :expand ((:free (x) (hide x)))))
  :rule-classes ((:type-prescription :typed-term (hide (h (+ 1 2))))))
