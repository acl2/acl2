; A clause processor to flatten literals
;
; Copyright (C) 2021-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/conjuncts-and-disjuncts2" :dir :system) ; todo: include something simpler!!  use a version that doesn't know about booland, etc.
(include-book "kestrel/utilities/conjuncts-and-disjuncts2-proof" :dir :system) ; todo: make local? but gives us ALL-EVAL-TO-FALSE-WITH-CON-AND-DIS-EVAL
(include-book "kestrel/terms-light/negate-terms" :dir :system)
(local (include-book "kestrel/terms-light/logic-termp" :dir :system))
(local (include-book "kestrel/utilities/arities-okp" :dir :system))
(local (include-book "kestrel/typed-lists-light/pseudo-term-listp" :dir :system))
(local (include-book "kestrel/lists-light/union-equal" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))

;; Handles a disjunct of the form (not (and x1 ... xn)) by turning it into the
;; set of new top-level literals (not x1) ... (not xn).

;; Note that a goal may print the same before and after flattening.
;; For example, the clause:
;; ((not (and x y z)) w)
;; and the clause:
;; ((not x) (not y) (not z) w)
;; both print as:
;; (implies (and x y z) w).

;; TODO: Move some of this stuff:

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

(defthm all-eval-to-false-with-con-and-dis-eval-when-equal-of-disjoin-and-false
  (implies (equal (disjoin clause) ''nil)
           (all-eval-to-false-with-con-and-dis-eval clause a))
  :hints (("Goal" :in-theory (enable disjoin all-eval-to-false-with-con-and-dis-eval))))

(defthm-flag-get-conjuncts-of-term2
  (defthm all-eval-to-true-with-con-and-dis-eval-of-get-conjuncts-of-term2
    (iff (all-eval-to-true-with-con-and-dis-eval (get-conjuncts-of-term2 term) a)
         (con-and-dis-eval term a))
    :flag get-conjuncts-of-term2)
  (defthm all-eval-to-false-with-con-and-dis-eval-of-get-disjuncts-of-term2
    (iff (all-eval-to-false-with-con-and-dis-eval (get-disjuncts-of-term2 term) a)
         (not (con-and-dis-eval term a)))
    :flag get-disjuncts-of-term2)
  :hints (("Goal" :in-theory (enable get-disjuncts-of-term2 get-conjuncts-of-term2 myif))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
                 (negated-disjuncts (get-conjuncts-of-term2 negated-lit))) ; todo: this can push NOTs into IFs (bad here?)
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

(defthm con-and-dis-eval-of-disjoin-of-flatten-disjuncts
  (iff (con-and-dis-eval (disjoin (flatten-disjuncts clause)) a)
       (con-and-dis-eval (disjoin clause) a))
  :hints (("Goal" :in-theory (enable flatten-disjuncts))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

(defthm flatten-literals-clause-processor-correct
  (implies (and (pseudo-term-listp clause)
                (alistp a)
                (con-and-dis-eval (conjoin-clauses (flatten-literals-clause-processor clause)) a))
           (con-and-dis-eval (disjoin clause) a))
  :rule-classes ((:clause-processor
                  :well-formedness-guarantee logic-term-list-listp-of-flatten-literals-clause-processor))
  :hints (("Goal" :in-theory (enable flatten-literals-clause-processor))))
