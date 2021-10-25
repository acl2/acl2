; An evaluator that knows about IF and NOT
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/evaluators/defevaluator-plus" :dir :system)

(defevaluator+ if-and-not-eval if not)

;; todo: build some of this in to defevaluator+?

;;;
;;; all-eval-to-true-with-if-and-not-eval
;;;

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

(defthm all-eval-to-true-with-if-and-not-eval-of-append
  (equal (all-eval-to-true-with-if-and-not-eval (append terms1 terms2) a)
         (and (all-eval-to-true-with-if-and-not-eval terms1 a)
              (all-eval-to-true-with-if-and-not-eval terms2 a)))
  :hints (("Goal" :in-theory (enable all-eval-to-true-with-if-and-not-eval))))

(defthm if-and-not-eval-of-conjoin
  (iff (if-and-not-eval (conjoin terms) a)
       (all-eval-to-true-with-if-and-not-eval terms a))
  :hints (("Goal" :in-theory (enable ALL-EVAL-TO-true-WITH-IF-AND-NOT-EVAL))))



;;;
;;; all-eval-to-false-with-if-and-not-eval
;;;

(defund all-eval-to-false-with-if-and-not-eval (terms a)
  (declare (xargs :guard (and (pseudo-term-listp terms)
                              (alistp a))))
  (if (endp terms)
      t
    (and (not (if-and-not-eval (first terms) a))
         (all-eval-to-false-with-if-and-not-eval (rest terms) a))))

(defthm all-eval-to-false-with-if-and-not-eval-when-not-consp
  (implies (not (consp terms))
           (all-eval-to-false-with-if-and-not-eval terms a))
  :hints (("Goal" :in-theory (enable all-eval-to-false-with-if-and-not-eval))))

(defthm all-eval-to-false-with-if-and-not-eval-of-cons
  (equal (all-eval-to-false-with-if-and-not-eval (cons term terms) a)
         (and (not (if-and-not-eval term a))
              (all-eval-to-false-with-if-and-not-eval terms a)))
  :hints (("Goal" :in-theory (enable all-eval-to-false-with-if-and-not-eval))))

(defthm all-eval-to-false-with-if-and-not-eval-of-append
  (equal (all-eval-to-false-with-if-and-not-eval (append terms1 terms2) a)
         (and (all-eval-to-false-with-if-and-not-eval terms1 a)
              (all-eval-to-false-with-if-and-not-eval terms2 a)))
  :hints (("Goal" :in-theory (enable all-eval-to-false-with-if-and-not-eval))))

(defthm if-and-not-eval-of-disjoin
  (iff (if-and-not-eval (disjoin terms) a)
       (not (all-eval-to-false-with-if-and-not-eval terms a)))
  :hints (("Goal" :in-theory (enable ALL-EVAL-TO-FALSE-WITH-IF-AND-NOT-EVAL))))

(defthm all-eval-to-false-with-if-and-not-eval-when-equal-of-disjoin-and-quote-nil
  (implies (equal (disjoin terms) *nil*)
           (all-eval-to-false-with-if-and-not-eval terms a))
  :hints (("Goal" :in-theory (enable all-eval-to-false-with-if-and-not-eval
                                     disjoin))))

(defthm not-all-eval-to-false-with-if-and-not-eval-when-equal-of-disjoin-and-quote-t
  (implies (equal (disjoin terms) *t*)
           (not (all-eval-to-false-with-if-and-not-eval terms a)))
  :hints (("Goal" :in-theory (enable all-eval-to-false-with-if-and-not-eval
                                     disjoin))))
