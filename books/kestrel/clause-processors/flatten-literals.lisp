; A clause processor to flatten literals
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/conjuncts-and-disjuncts" :dir :system) ; todo: include something simpler!!
(include-book "kestrel/utilities/conjuncts-and-disjuncts-proof" :dir :system)
(include-book "kestrel/terms-light/negate-terms" :dir :system)
(local (include-book "kestrel/terms-light/logic-termp" :dir :system))
(local (include-book "kestrel/utilities/arities-okp" :dir :system))
(local (include-book "kestrel/typed-lists-light/pseudo-term-listp" :dir :system))
(local (include-book "kestrel/lists-light/union-equal" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))

;; Handles a disjunct of the form (not (and x1 ... xn)) by turning it into the
;; set of new top-level literals (not x1) ... (not xn).

(defthm all-eval-to-false-with-con-and-dis-eval-of-union-equal
  (iff (all-eval-to-false-with-con-and-dis-eval (union-equal x y) a)
       (and (all-eval-to-false-with-con-and-dis-eval x a)
            (all-eval-to-false-with-con-and-dis-eval y a)))
  :hints (("Goal" :in-theory (enable all-eval-to-false-with-con-and-dis-eval
                                     union-equal))))

(defthm con-and-dis-eval-of-negate-term
  (iff (con-and-dis-eval (negate-term term) a)
       (not (con-and-dis-eval term a)))
  :hints (("Goal" :in-theory (enable negate-term))))

(defthm all-eval-to-false-with-con-and-dis-eval-when-not-consp
  (implies (not (consp terms))
           (all-eval-to-false-with-con-and-dis-eval terms a))
  :hints (("Goal" :in-theory (enable all-eval-to-false-with-con-and-dis-eval))))

(defthm all-eval-to-false-with-con-and-dis-eval-of-negate-terms
  (iff (all-eval-to-false-with-con-and-dis-eval (negate-terms terms) a)
       (all-eval-to-true-with-con-and-dis-eval terms a))
  :hints (("Goal" :in-theory (enable negate-terms))))

(defund flatten-disjuncts (clause)
  (declare (xargs :guard (pseudo-term-listp clause)
                  :verify-guards nil ; done below
                  ))
  (if (endp clause)
      nil
    (let ((lit (first clause)))
      (if (and (call-of 'not lit)
               (= 1 (len (fargs lit))))
          (let* ((negated-lit (farg1 lit))
                 (negated-disjuncts (get-conjuncts-of-term negated-lit))) ; todo: this can push NOTs into IFs (bad here?)
            (if (< 1 (len negated-disjuncts))
                (union-equal (negate-terms negated-disjuncts) (flatten-disjuncts (rest clause)))
              (cons lit (flatten-disjuncts (rest clause)))))
        (cons lit (flatten-disjuncts (rest clause))) ; todo: should we extract disjuncts in this case?
        ))))

(defthm true-listp-of-flatten-disjuncts
  (true-listp (flatten-disjuncts clause))
  :hints (("Goal" :in-theory (enable flatten-disjuncts))))

(verify-guards flatten-disjuncts)

(defthm pseudo-term-listp-of-flatten-disjuncts
  (implies (pseudo-term-listp clause)
           (pseudo-term-listp (flatten-disjuncts clause)))
  :hints (("Goal" :in-theory (enable flatten-disjuncts))))

(defthm logic-term-listp-of-flatten-disjuncts
  (implies (and (logic-term-listp clause w)
                (arities-okp '((not . 1)
                               (if . 3)
                               (boolif . 3)
                               (booland . 2)
                               (boolor . 2)
                               (myif . 3))
                             w))
           (logic-term-listp (flatten-disjuncts clause)
                             w))
  :hints (("Goal" :in-theory (enable flatten-disjuncts))))

(defthm all-eval-to-false-with-con-and-dis-eval-when-equal-of-disjoin-and-false
  (implies (equal (disjoin clause) ''nil)
           (all-eval-to-false-with-con-and-dis-eval clause a))
  :hints (("Goal" :in-theory (enable disjoin all-eval-to-false-with-con-and-dis-eval))))

(defthm-flag-get-conjuncts-of-term
  (defthm all-eval-to-true-with-con-and-dis-eval-of-get-conjuncts-of-term
    (iff (all-eval-to-true-with-con-and-dis-eval (get-conjuncts-of-term term) a)
         (con-and-dis-eval term a))
    :flag get-conjuncts-of-term)
  (defthm all-eval-to-false-with-con-and-dis-eval-of-get-disjuncts-of-term
    (iff (all-eval-to-false-with-con-and-dis-eval (get-disjuncts-of-term term) a)
         (not (con-and-dis-eval term a)))
    :flag get-disjuncts-of-term)
  :hints (("Goal" :in-theory (enable get-disjuncts-of-term get-conjuncts-of-term))))

(defthm con-and-dis-eval-of-disjoin-of-flatten-disjuncts
  (iff (con-and-dis-eval (disjoin (flatten-disjuncts clause)) a)
       (con-and-dis-eval (disjoin clause) a))
  :hints (("Goal" :in-theory (enable flatten-disjuncts))))

(defund flatten-literals-clause-processor (clause)
  (declare (xargs :guard (pseudo-term-listp clause)))
  (list (flatten-disjuncts clause)))

(defthm logic-term-list-listp-of-flatten-literals-clause-processor
  (implies (and (logic-term-listp clause w)
                (arities-okp '((not . 1)
                               (if . 3)
                               (boolif . 3)
                               (booland . 2)
                               (boolor . 2)
                               (myif . 3))
                             w))
           (logic-term-list-listp (flatten-literals-clause-processor clause) w))
  :hints (("Goal" :in-theory (enable flatten-literals-clause-processor))))

(defthm pseudo-term-list-listp-of-flatten-literals-clause-processor
  (implies (pseudo-term-listp clause)
           (pseudo-term-list-listp (flatten-literals-clause-processor clause)))
  :hints (("Goal" :in-theory (enable flatten-literals-clause-processor))))

;todo: add :well-formedness proof
(defthm flatten-literals-clause-processor-correct
  (implies (and (pseudo-term-listp clause)
                (alistp a)
                (con-and-dis-eval (conjoin-clauses (flatten-literals-clause-processor clause)) a))
           (con-and-dis-eval (disjoin clause) a))
  :rule-classes ((:clause-processor
                  :well-formedness-guarantee logic-term-list-listp-of-flatten-literals-clause-processor))
  :hints (("Goal" :in-theory (enable flatten-literals-clause-processor))))
