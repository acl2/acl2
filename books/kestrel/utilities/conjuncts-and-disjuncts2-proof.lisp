; Proof of correctness of conjuncts-and-disjuncts functions
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "conjuncts-and-disjuncts2")
(include-book "kestrel/evaluators/defevaluator-plus" :dir :system)

(defevaluator+ con-and-dis-eval if not booland boolor boolif myif)

(defund all-eval-to-false-with-con-and-dis-eval (terms a)
  (declare (xargs :guard (and (pseudo-term-listp terms)
                              (alistp a))))
  (if (endp terms)
      t
    (and (not (con-and-dis-eval (first terms) a))
         (all-eval-to-false-with-con-and-dis-eval (rest terms) a))))

(defthm all-eval-to-false-with-con-and-dis-eval-of-cons
  (equal (all-eval-to-false-with-con-and-dis-eval (cons term terms) a)
         (and (not (con-and-dis-eval term a))
              (all-eval-to-false-with-con-and-dis-eval terms a)))
  :hints (("Goal" :in-theory (enable all-eval-to-false-with-con-and-dis-eval))))

(defund all-eval-to-true-with-con-and-dis-eval (terms a)
  (declare (xargs :guard (and (pseudo-term-listp terms)
                              (alistp a))))
  (if (endp terms)
      t
    (and (con-and-dis-eval (first terms) a)
         (all-eval-to-true-with-con-and-dis-eval (rest terms) a))))

(defthm all-eval-to-true-with-con-and-dis-eval-when-not-consp
  (implies (not (consp terms))
           (all-eval-to-true-with-con-and-dis-eval terms a))
  :hints (("Goal" :in-theory (enable all-eval-to-true-with-con-and-dis-eval))))

(defthm all-eval-to-true-with-con-and-dis-eval-of-cons
  (equal (all-eval-to-true-with-con-and-dis-eval (cons term terms) a)
         (and (con-and-dis-eval term a)
              (all-eval-to-true-with-con-and-dis-eval terms a)))
  :hints (("Goal" :in-theory (enable all-eval-to-true-with-con-and-dis-eval))))

;todo: build in to defevaluator+?
(defthm con-and-dis-eval-of-disjoin
  (iff (con-and-dis-eval (disjoin terms) a)
       (not (all-eval-to-false-with-con-and-dis-eval terms a)))
  :hints (("Goal" :in-theory (enable ALL-EVAL-TO-FALSE-WITH-CON-AND-DIS-EVAL))))

(defthm con-and-dis-eval-of-conjoin
  (iff (con-and-dis-eval (conjoin terms) a)
       (all-eval-to-true-with-con-and-dis-eval terms a))
  :hints (("Goal" :in-theory (enable ALL-EVAL-TO-true-WITH-CON-AND-DIS-EVAL))))

;todo: nested induction
(defthm all-eval-to-false-with-con-and-dis-eval-of-combine-disjuncts
  (iff (all-eval-to-false-with-con-and-dis-eval (combine-disjuncts disjuncts1 disjuncts2) a)
       (and (all-eval-to-false-with-con-and-dis-eval disjuncts1 a)
            (all-eval-to-false-with-con-and-dis-eval disjuncts2 a)))
  :hints (("Goal" :in-theory (enable combine-disjuncts
                                     all-eval-to-false-with-con-and-dis-eval))))

(defthm all-eval-to-true-with-con-and-dis-eval-of-combine-conjuncts
  (iff (all-eval-to-true-with-con-and-dis-eval (combine-conjuncts conjuncts1 conjuncts2) a)
       (and (all-eval-to-true-with-con-and-dis-eval conjuncts1 a)
            (all-eval-to-true-with-con-and-dis-eval conjuncts2 a)))
  :hints (("Goal" :in-theory (enable combine-conjuncts
                                     all-eval-to-true-with-con-and-dis-eval))))

(defthm negate-term2-correct
  (iff (CON-AND-DIS-EVAL (negate-term2 term) a)
       (not (CON-AND-DIS-EVAL term a)))
  :hints (("Goal" :in-theory (enable negate-term2 myif))))

(defthm ALL-EVAL-TO-FALSE-WITH-CON-AND-DIS-EVAL-of-negate-terms2
  (iff (ALL-EVAL-TO-FALSE-WITH-CON-AND-DIS-EVAL (NEGATE-terms2 conjuncts) A)
       (ALL-EVAL-TO-true-WITH-CON-AND-DIS-EVAL conjuncts A))
  :hints (("Goal" :in-theory (enable NEGATE-terms2
                                     ALL-EVAL-TO-FALSE-WITH-CON-AND-DIS-EVAL
                                     ALL-EVAL-TO-true-WITH-CON-AND-DIS-EVAL))))

(defthm ALL-EVAL-TO-true-WITH-CON-AND-DIS-EVAL-of-negate-terms2
  (iff (ALL-EVAL-TO-true-WITH-CON-AND-DIS-EVAL (NEGATE-terms2 conjuncts) A)
       (ALL-EVAL-TO-false-WITH-CON-AND-DIS-EVAL conjuncts A))
  :hints (("Goal" :in-theory (enable NEGATE-terms2
                                     ALL-EVAL-TO-FALSE-WITH-CON-AND-DIS-EVAL
                                     ALL-EVAL-TO-true-WITH-CON-AND-DIS-EVAL))))

(defthm ALL-EVAL-TO-FALSE-WITH-CON-AND-DIS-EVAL-of-negate-conjuncts
  (iff (ALL-EVAL-TO-FALSE-WITH-CON-AND-DIS-EVAL (NEGATE-CONJUNCTS conjuncts) A)
       (ALL-EVAL-TO-true-WITH-CON-AND-DIS-EVAL conjuncts A))
  :hints (("Goal" :in-theory (enable NEGATE-CONJUNCTS
                                     ALL-EVAL-TO-FALSE-WITH-CON-AND-DIS-EVAL
                                     ALL-EVAL-TO-true-WITH-CON-AND-DIS-EVAL))))

(defthm ALL-EVAL-TO-TRUE-WITH-CON-AND-DIS-EVAL-of-negate-disjuncts
  (iff (ALL-EVAL-TO-TRUE-WITH-CON-AND-DIS-EVAL (NEGATE-DISJUNCTS disjuncts) A)
       (ALL-EVAL-TO-false-WITH-CON-AND-DIS-EVAL disjuncts A))
  :hints (("Goal" :in-theory (enable NEGATE-DISJUNCTS
                                     ALL-EVAL-TO-TRUE-WITH-CON-AND-DIS-EVAL
                                     ALL-EVAL-TO-false-WITH-CON-AND-DIS-EVAL))))

;; The main theorem in this book
(defthm-flag-get-conjuncts-of-term2
  (defthm get-conjuncts-of-term2-correct
    (iff (con-and-dis-eval (conjoin (get-conjuncts-of-term2 term)) a)
         (con-and-dis-eval term a))
    :flag get-conjuncts-of-term2)
  (defthm get-disjuncts-of-term-correct
    (iff (con-and-dis-eval (disjoin (get-disjuncts-of-term2 term)) a)
         (con-and-dis-eval term a))
    :flag get-disjuncts-of-term2)
  :hints (("Goal" :in-theory (enable get-disjuncts-of-term2 get-conjuncts-of-term2))))
