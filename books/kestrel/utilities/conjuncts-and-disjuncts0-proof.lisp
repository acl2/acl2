; Proof of correctness of conjuncts-and-disjuncts functions
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "conjuncts-and-disjuncts0")
(include-book "kestrel/evaluators/if-and-not-eval" :dir :system)
(local (include-book "kestrel/terms-light/negate-term-proof" :dir :system))


;; just changes the evaluator
(defthm if-and-not-eval-of-negate-term
  (iff (if-and-not-eval (negate-term term) a)
       (not (if-and-not-eval term a)))
  :hints (("Goal" :use (:functional-instance negate-term-correct
                                             (not-eval if-and-not-eval)
                                             (not-eval-list if-and-not-eval-list))
           ;; todo: improve defevaluator+ to handle this:
           :in-theory (enable if-and-not-eval-of-fncall-args))))

(defund all-eval-to-false-with-if-and-not-eval (terms a)
  (declare (xargs :guard (and (pseudo-term-listp terms)
                              (alistp a))))
  (if (endp terms)
      t
    (and (not (if-and-not-eval (first terms) a))
         (all-eval-to-false-with-if-and-not-eval (rest terms) a))))

(defthm all-eval-to-false-with-if-and-not-eval-of-cons
  (equal (all-eval-to-false-with-if-and-not-eval (cons term terms) a)
         (and (not (if-and-not-eval term a))
              (all-eval-to-false-with-if-and-not-eval terms a)))
  :hints (("Goal" :in-theory (enable all-eval-to-false-with-if-and-not-eval))))

(defund all-eval-to-true-with-if-and-not-eval (terms a)
  (declare (xargs :guard (and (pseudo-term-listp terms)
                              (alistp a))))
  (if (endp terms)
      t
    (and (if-and-not-eval (first terms) a)
         (all-eval-to-true-with-if-and-not-eval (rest terms) a))))

(defthm all-eval-to-true-with-if-and-not-eval-when-not-consp
  (implies (not (consp terms))
           (all-eval-to-true-with-if-and-not-eval terms a))
  :hints (("Goal" :in-theory (enable all-eval-to-true-with-if-and-not-eval))))

(defthm all-eval-to-true-with-if-and-not-eval-of-cons
  (equal (all-eval-to-true-with-if-and-not-eval (cons term terms) a)
         (and (if-and-not-eval term a)
              (all-eval-to-true-with-if-and-not-eval terms a)))
  :hints (("Goal" :in-theory (enable all-eval-to-true-with-if-and-not-eval))))

;todo: build in to defevaluator+?
(defthm if-and-not-eval-of-disjoin
  (iff (if-and-not-eval (disjoin terms) a)
       (not (all-eval-to-false-with-if-and-not-eval terms a)))
  :hints (("Goal" :in-theory (enable ALL-EVAL-TO-FALSE-WITH-IF-AND-NOT-EVAL))))

(defthm if-and-not-eval-of-conjoin
  (iff (if-and-not-eval (conjoin terms) a)
       (all-eval-to-true-with-if-and-not-eval terms a))
  :hints (("Goal" :in-theory (enable ALL-EVAL-TO-true-WITH-IF-AND-NOT-EVAL))))

;todo: nested induction
(defthm all-eval-to-false-with-if-and-not-eval-of-combine-disjuncts
  (iff (all-eval-to-false-with-if-and-not-eval (combine-disjuncts disjuncts1 disjuncts2) a)
       (and (all-eval-to-false-with-if-and-not-eval disjuncts1 a)
            (all-eval-to-false-with-if-and-not-eval disjuncts2 a)))
  :hints (("Goal" :in-theory (enable combine-disjuncts
                                     all-eval-to-false-with-if-and-not-eval))))

(defthm all-eval-to-true-with-if-and-not-eval-of-combine-conjuncts
  (iff (all-eval-to-true-with-if-and-not-eval (combine-conjuncts conjuncts1 conjuncts2) a)
       (and (all-eval-to-true-with-if-and-not-eval conjuncts1 a)
            (all-eval-to-true-with-if-and-not-eval conjuncts2 a)))
  :hints (("Goal" :in-theory (enable combine-conjuncts
                                     all-eval-to-true-with-if-and-not-eval))))

(defthm ALL-EVAL-TO-FALSE-WITH-IF-AND-NOT-EVAL-of-negate-terms
  (iff (ALL-EVAL-TO-FALSE-WITH-IF-AND-NOT-EVAL (NEGATE-terms conjuncts) A)
       (ALL-EVAL-TO-true-WITH-IF-AND-NOT-EVAL conjuncts A))
  :hints (("Goal" :in-theory (enable NEGATE-terms
                                     ALL-EVAL-TO-FALSE-WITH-IF-AND-NOT-EVAL
                                     ALL-EVAL-TO-true-WITH-IF-AND-NOT-EVAL))))

(defthm ALL-EVAL-TO-true-WITH-IF-AND-NOT-EVAL-of-negate-terms2
  (iff (ALL-EVAL-TO-true-WITH-IF-AND-NOT-EVAL (NEGATE-terms conjuncts) A)
       (ALL-EVAL-TO-false-WITH-IF-AND-NOT-EVAL conjuncts A))
  :hints (("Goal" :in-theory (enable NEGATE-terms
                                     ALL-EVAL-TO-FALSE-WITH-IF-AND-NOT-EVAL
                                     ALL-EVAL-TO-true-WITH-IF-AND-NOT-EVAL))))

(defthm ALL-EVAL-TO-FALSE-WITH-IF-AND-NOT-EVAL-of-negate-conjunct-list
  (iff (ALL-EVAL-TO-FALSE-WITH-IF-AND-NOT-EVAL (NEGATE-CONJUNCT-LIST conjuncts) A)
       (ALL-EVAL-TO-true-WITH-IF-AND-NOT-EVAL conjuncts A))
  :hints (("Goal" :in-theory (enable NEGATE-CONJUNCT-LIST
                                     ALL-EVAL-TO-FALSE-WITH-IF-AND-NOT-EVAL
                                     ALL-EVAL-TO-true-WITH-IF-AND-NOT-EVAL))))

(defthm ALL-EVAL-TO-TRUE-WITH-IF-AND-NOT-EVAL-of-negate-disjunct-list
  (iff (ALL-EVAL-TO-TRUE-WITH-IF-AND-NOT-EVAL (NEGATE-DISJUNCT-LIST disjuncts) A)
       (ALL-EVAL-TO-false-WITH-IF-AND-NOT-EVAL disjuncts A))
  :hints (("Goal" :in-theory (enable NEGATE-DISJUNCT-LIST
                                     ALL-EVAL-TO-TRUE-WITH-IF-AND-NOT-EVAL
                                     ALL-EVAL-TO-false-WITH-IF-AND-NOT-EVAL))))

;; The main theorem in this book
(defthm-flag-get-conjuncts-of-term
  (defthm get-conjuncts-of-term-correct
    (iff (if-and-not-eval (conjoin (get-conjuncts-of-term term)) a)
         (if-and-not-eval term a))
    :flag get-conjuncts-of-term)
  (defthm get-disjuncts-of-term-correct
    (iff (if-and-not-eval (disjoin (get-disjuncts-of-term term)) a)
         (if-and-not-eval term a))
    :flag get-disjuncts-of-term)
  :hints (("Goal" :in-theory (enable get-disjuncts-of-term get-conjuncts-of-term))))
