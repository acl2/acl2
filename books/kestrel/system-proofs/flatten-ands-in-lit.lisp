; Correctness of the ACL2 system functions flatten-ands-in-lit and dumb-negate-lit
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; FLATTEN-ANDS-IN-LIT (in translate.lisp) splits a term into a list of
;; conjuncts.  It is used, for example, by unprettyify (tau.lisp) to split the
;; hypotheses of theorems when rules are created, and by
;; destructure-forward-chaining-term.  DUMB-NEGATE-LIT (in basis-b.lisp)
;; negates a term, with some simplification; it is also used by unprettyify,
;; and very widely elsewhere.

;; These functions do not use CONS-TERM, so we state their correctness using
;; EQUALITY-EVAL, which knows only IF, EQUAL, EQL, EQ, and NOT.

(include-book "kestrel/evaluators/equality-eval" :dir :system)
(include-book "kestrel/terms-light/no-nils-in-termp" :dir :system)
(include-book "kestrel/terms-light/lambdas-closed-in-termp" :dir :system)
(include-book "kestrel/terms-light/no-duplicate-lambda-formals-in-termp" :dir :system)
(local (include-book "kestrel/terms-light/termp" :dir :system))
(local (include-book "helpers"))
(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/member-equal" :dir :system))

(defthm equality-eval-of-dumb-negate-lit
  (implies (pseudo-termp term)
           (iff (equality-eval (dumb-negate-lit term) a)
                (not (equality-eval term a)))))

;; The conjuncts all evaluate to true exactly when TERM does.
(defthm all-eval-to-true-with-equality-eval-of-flatten-ands-in-lit
  (implies (pseudo-termp term)
           (iff (all-eval-to-true-with-equality-eval (flatten-ands-in-lit term) a)
                (equality-eval term a))))

(defthm all-eval-to-true-with-equality-eval-of-flatten-ands-in-lit-lst
  (implies (pseudo-term-listp x)
           (iff (all-eval-to-true-with-equality-eval (flatten-ands-in-lit-lst x) a)
                (all-eval-to-true-with-equality-eval x a)))
  :hints (("Goal" :in-theory (enable flatten-ands-in-lit-lst all-eval-to-true-with-equality-eval))))

;; Conjoining the conjuncts gives back something equivalent to TERM.
(defthm equality-eval-of-conjoin-of-flatten-ands-in-lit
  (implies (pseudo-termp term)
           (iff (equality-eval (conjoin (flatten-ands-in-lit term)) a)
                (equality-eval term a))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Properties of terms that DUMB-NEGATE-LIT preserves.  For termp, NOT and
;; EQUAL must have their usual arities.

(defthm termp-of-dumb-negate-lit
  (implies (and (termp term w)
                (equal (arity 'not w) 1)
                (equal (arity 'equal w) 2))
           (termp (dumb-negate-lit term) w))
  :hints (("Goal" :expand ((termp term w))
           :in-theory (enable dumb-negate-lit termp))))

;; No-nils-in-termp is not preserved for malformed terms (see
;; dumb-negate-lit-can-introduce-nil in flatten-ands-in-lit-tests.lisp), but it
;; is implied by termp.

(defthm lambdas-closed-in-termp-of-dumb-negate-lit
  (implies (lambdas-closed-in-termp term)
           (lambdas-closed-in-termp (dumb-negate-lit term)))
  :hints (("Goal" :in-theory (enable dumb-negate-lit lambdas-closed-in-termp))))

(defthm no-duplicate-lambda-formals-in-termp-of-dumb-negate-lit
  (implies (no-duplicate-lambda-formals-in-termp term)
           (no-duplicate-lambda-formals-in-termp (dumb-negate-lit term)))
  :hints (("Goal" :in-theory (enable dumb-negate-lit no-duplicate-lambda-formals-in-termp))))

;; Properties of terms that FLATTEN-ANDS-IN-LIT preserves: every conjunct has
;; them.  (As for dumb-negate-lit, no-nils-in-termp is preserved only for
;; well-formed terms; it is implied by termp.)  (That it preserves pseudo-termp follows from its guard
;; verification.)  For termp, NOT and EQUAL must have their usual arities, as
;; for dumb-negate-lit.

(defthm term-listp-of-flatten-ands-in-lit
  (implies (and (termp term w)
                (equal (arity 'not w) 1)
                (equal (arity 'equal w) 2))
           (term-listp (flatten-ands-in-lit term) w))
  :hints (("Goal" :in-theory (enable flatten-ands-in-lit termp))))

(defthm lambdas-closed-in-termsp-of-flatten-ands-in-lit
  (implies (lambdas-closed-in-termp term)
           (lambdas-closed-in-termsp (flatten-ands-in-lit term)))
  :hints (("Goal" :in-theory (enable flatten-ands-in-lit lambdas-closed-in-termp))))

(defthm no-duplicate-lambda-formals-in-termsp-of-flatten-ands-in-lit
  (implies (no-duplicate-lambda-formals-in-termp term)
           (no-duplicate-lambda-formals-in-termsp (flatten-ands-in-lit term)))
  :hints (("Goal" :in-theory (enable flatten-ands-in-lit no-duplicate-lambda-formals-in-termp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; What FLATTEN-ANDS-IN-LIT is for: no conjunct is 'T or is itself a
;; conjunction, i.e., a call (if t1 t2 t3) where t2 or t3 is 'NIL.

(defun conjunction-term-p (term)
  (declare (xargs :guard t))
  (and (consp term)
       (eq (car term) 'if)
       (true-listp term)
       (equal (len term) 4)
       (or (equal (caddr term) *nil*)
           (equal (cadddr term) *nil*))))

(defthm not-member-equal-of-quote-t-and-flatten-ands-in-lit
  (not (member-equal *t* (flatten-ands-in-lit term)))
  :hints (("Goal" :in-theory (enable flatten-ands-in-lit))))

(defthm not-conjunction-term-p-when-member-equal-of-flatten-ands-in-lit
  (implies (member-equal x (flatten-ands-in-lit term))
           (not (conjunction-term-p x)))
  :hints (("Goal" :in-theory (enable flatten-ands-in-lit))))
