; Correctness of the ACL2 system function implicate
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; IMPLICATE (in tau.lisp) makes a term equivalent to (implies t1 t2), with
;; some simplification (using dumb-negate-lit when T2 is 'NIL).  It is used
;; to turn type-prescription rules into terms (see
;; convert-type-prescription-to-term in tau.lisp), which is done for tau and,
;; in defuns.lisp, when combining type-prescriptions
;; (conjoin-type-prescriptions) and using those stored in certificates.

;; We state its correctness using an evaluator that knows IMPLIES plus the
;; functions that dumb-negate-lit depends on (as in flatten-ands-in-lit.lisp).

(include-book "kestrel/evaluators/defevaluator-plus" :dir :system)

(include-book "kestrel/terms-light/lambdas-closed-in-termp" :dir :system)
(include-book "kestrel/terms-light/no-duplicate-lambda-formals-in-termp" :dir :system)
(local (include-book "flatten-ands-in-lit")) ; for properties of dumb-negate-lit
(local (include-book "cons-term-helpers"))
(local (include-book "kestrel/terms-light/termp" :dir :system))

(defevaluator+ implicate-eval if equal eql eq not implies)

;; Cons-term does not evaluate calls of IMPLIES, which is not a primitive.
(local
 (defthm cons-term-of-implies
   (equal (cons-term 'implies args)
          (cons 'implies args))
   :hints (("Goal" :in-theory (enable cons-term cons-term1)))))

(local
 (defthm implicate-eval-of-dumb-negate-lit
   (implies (pseudo-termp term)
            (iff (implicate-eval (dumb-negate-lit term) a)
                 (not (implicate-eval term a))))
   :hints (("Goal" :in-theory (enable dumb-negate-lit)))))

;; The result is true exactly when T1 implies T2.
(defthm implicate-correct
  (implies (and (pseudo-termp t1)
                (pseudo-termp t2))
           (iff (implicate-eval (implicate t1 t2) a)
                (implies (implicate-eval t1 a)
                         (implicate-eval t2 a))))
  :hints (("Goal" :in-theory (enable implicate))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Properties of terms that IMPLICATE preserves.  For termp, IMPLIES, NOT, and
;; EQUAL must have their usual arities.

(defthm pseudo-termp-of-implicate
  (implies (and (pseudo-termp t1)
                (pseudo-termp t2))
           (pseudo-termp (implicate t1 t2)))
  :hints (("Goal" :in-theory (enable implicate))))

(defthm termp-of-implicate
  (implies (and (termp t1 w)
                (termp t2 w)
                (equal (arity 'implies w) 2)
                (equal (arity 'not w) 1)
                (equal (arity 'equal w) 2))
           (termp (implicate t1 t2) w))
  :hints (("Goal" :in-theory (enable implicate termp))))

(defthm lambdas-closed-in-termp-of-implicate
  (implies (and (lambdas-closed-in-termp t1)
                (lambdas-closed-in-termp t2))
           (lambdas-closed-in-termp (implicate t1 t2)))
  :hints (("Goal" :in-theory (enable implicate lambdas-closed-in-termp))))

(defthm no-duplicate-lambda-formals-in-termp-of-implicate
  (implies (and (no-duplicate-lambda-formals-in-termp t1)
                (no-duplicate-lambda-formals-in-termp t2))
           (no-duplicate-lambda-formals-in-termp (implicate t1 t2)))
  :hints (("Goal" :in-theory (enable implicate no-duplicate-lambda-formals-in-termp))))
