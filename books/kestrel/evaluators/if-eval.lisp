; An evaluator that knows about IF
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "defevaluator-plus")

(defevaluator+ if-eval if)

(defund all-eval-to-true-with-if-eval (terms a)
  (declare (xargs :guard (and (pseudo-term-listp terms)
                              (alistp a))))
  (if (endp terms)
      t
    (and (if-eval (first terms) a)
         (all-eval-to-true-with-if-eval (rest terms) a))))

(defthm all-eval-to-true-with-if-eval-when-not-consp
  (implies (not (consp terms))
           (all-eval-to-true-with-if-eval terms a))
  :hints (("Goal" :in-theory (enable all-eval-to-true-with-if-eval))))

(defthm all-eval-to-true-with-if-eval-of-cons
  (equal (all-eval-to-true-with-if-eval (cons term terms) a)
         (and (if-eval term a)
              (all-eval-to-true-with-if-eval terms a)))
  :hints (("Goal" :in-theory (enable all-eval-to-true-with-if-eval))))

(defthm if-eval-when-all-eval-to-true-with-if-eval-and-member-equal
  (implies (and (all-eval-to-true-with-if-eval terms a)
                (member-equal term terms))
           (if-eval term a))
  :hints (("Goal" :in-theory (enable all-eval-to-true-with-if-eval))))

;;;
;;; all-eval-to-false-with-if-eval
;;;

(defund all-eval-to-false-with-if-eval (terms a)
  (declare (xargs :guard (and (pseudo-term-listp terms)
                              (alistp a))))
  (if (endp terms)
      t
    (and (not (if-eval (first terms) a))
         (all-eval-to-false-with-if-eval (rest terms) a))))

(defthm all-eval-to-false-with-if-eval-when-not-consp
  (implies (not (consp terms))
           (all-eval-to-false-with-if-eval terms a))
  :hints (("Goal" :in-theory (enable all-eval-to-false-with-if-eval))))

(defthm all-eval-to-false-with-if-eval-of-cons
  (equal (all-eval-to-false-with-if-eval (cons term terms) a)
         (and (not (if-eval term a))
              (all-eval-to-false-with-if-eval terms a)))
  :hints (("Goal" :in-theory (enable all-eval-to-false-with-if-eval))))

(defthm all-eval-to-false-with-if-eval-of-append
  (equal (all-eval-to-false-with-if-eval (append terms1 terms2) a)
         (and (all-eval-to-false-with-if-eval terms1 a)
              (all-eval-to-false-with-if-eval terms2 a)))
  :hints (("Goal" :in-theory (enable all-eval-to-false-with-if-eval))))

(defthm if-eval-of-disjoin
  (iff (if-eval (disjoin terms) a)
       (not (all-eval-to-false-with-if-eval terms a)))
  :hints (("Goal" :in-theory (enable ALL-EVAL-TO-FALSE-WITH-IF-EVAL))))

(defthm all-eval-to-false-with-if-eval-when-equal-of-disjoin-and-quote-nil
  (implies (equal (disjoin terms) *nil*)
           (all-eval-to-false-with-if-eval terms a))
  :hints (("Goal" :in-theory (enable all-eval-to-false-with-if-eval
                                     disjoin))))

(defthm not-all-eval-to-false-with-if-eval-when-equal-of-disjoin-and-quote-t
  (implies (equal (disjoin terms) *t*)
           (not (all-eval-to-false-with-if-eval terms a)))
  :hints (("Goal" :in-theory (enable all-eval-to-false-with-if-eval
                                     disjoin))))
