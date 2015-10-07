;; Copyright (C) 2015, University of British Columbia
;; Written (originally) by Yan Peng (13th March, 2014)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with this software


;; Summation lemmas suggested by Mark

(in-package "ACL2")
(include-book "arithmetic/top-with-meta" :dir :system)
(include-book "global")

(encapsulate
  ( ((f * *) => *) )
  (local (defun f (x args) (+ x (car args))))
  (defthm return-type
    (implies (integerp x)
             (acl2-numberp (f x args)))
    :rule-classes :type-prescription)
  )

(defun summation (jlo jhi args)
  (declare (xargs :measure (if (or (not (integerp jhi))
                                   (not (integerp jlo))
                                   (< jhi jlo))
                             0
                             (1+ (- jhi jlo)))))
  (if (or (not (integerp jhi)) (not (integerp jlo)) (< jhi jlo)) 0
    (+ (summation jlo (- jhi 1) args) (f jhi args))))

(defthm peel-first-2-terms-lemma1 (equal (summation 0 -1 args) 0))
(defthm peel-first-2-terms-lemma2 (equal (summation 0 0 args) (+ (summation 0 -1 args) (f 0 args))))
(defthm peel-first-2-terms
  (implies (and (integerp j) (> j 0))
           (equal (summation 0 j args)
                  (+ (f 0 args) (f 1 args) (summation 2 j args))))
  :hints (("Goal"
           :expand ((:free (x) (hide x))))))

(defthm divide-in-the-middle
  (implies (and (integerp lo) (integerp mid) (integerp hi) 
                (<= lo mid) (<= mid hi))
           (equal (summation lo hi args)
                  (+ (summation lo (- mid 1) args) (f mid args) (summation (+ mid 1) hi args)))))

(defun summation1 (jlo jhi k args)
  (declare (xargs :measure (if (or (not (integerp jhi))
                                   (not (integerp jlo))
                                   (< jhi jlo))
                             0
                             (1+ (- jhi jlo)))))
  (if (or (not (integerp jlo)) (not (integerp jhi)) (< jhi jlo)) 0
    (+ (f (+ jhi k) args) (summation1 jlo (- jhi 1) k args))))

(defthm left-shift-the-sum
  (implies (and (integerp lo)
                (integerp hi)
                (integerp k))
           (equal (summation lo hi args)
                  (summation1 (- lo k) (- hi k) k args))))

(defun summation2 (jlo jhi args)
  (declare (xargs :measure (if (or (not (integerp jhi))
                                   (not (integerp jlo))
                                   (< jhi jlo))
                             0
                             (1+ (- jhi jlo)))))
  (if (or (not (integerp jlo)) (not (integerp jhi)) (< jhi jlo)) 0
    (+ (f jlo args) (summation2 (+ jlo 1) jhi args))))

(defthm reverse-the-sum
  (implies (and (integerp lo)
                (integerp hi))
           (equal (summation lo hi args)
                  (summation2 lo hi args)))
  :hints (("Goal"
           :in-theory (disable left-shift-the-sum))))

(defun summation3 (jlo jhi k args)
  (declare (xargs :measure (if (or (not (integerp jhi))
                                   (not (integerp jlo))
                                   (< jhi jlo))
                             0
                             (1+ (- jhi jlo)))))
  (if (or (not (integerp jlo)) (not (integerp jhi)) (< jhi jlo)) 0
    (+ (f (+ jlo k) args) (summation3 (+ jlo 1) jhi k args))))

(defthm reverse-the-sum-and-left-shift
  (implies (and (integerp lo)
                (integerp hi)
                (integerp k))
           (equal (summation lo hi args)
                  (summation3 (- lo k) (- hi k) k args))))

(defun summation4 (jlo jhi jlo-plus-jhi k args)
  (declare (xargs :measure (if (or (not (integerp jhi))
                                   (not (integerp jlo))
                                   (< jhi jlo))
                             0
                             (1+ (- jhi jlo)))))
  (if (or (not (integerp jlo)) (not (integerp jhi)) (< jhi jlo)) 0
    (+ (f (+ (- jlo-plus-jhi jhi) k) args) (summation4 jlo (- jhi 1) jlo-plus-jhi k args))))

(defthm equivalence-summation3-summation4-lemma1
  (implies (and (integerp i1)
                (integerp j1)
                (integerp j2)
                (integerp k))
           (equal (summation4 (- i1 k) (- j1 k) (+ i1 j2 (- k) (- k)) k args)
                  (summation3 (- (+ i1 (- j2 j1)) k) (- j2 k) k args)))
  :hints (("Goal"
           :induct (summation4 i1 j1 x k args))))

(defthm equivalence-summation3-summation4-lemma2
  (implies (and (integerp i1)
                (integerp j1)
                (integerp delta)
                (integerp k))
           (equal (summation4 (- i1 k) (- j1 k) (+ i1 (+ j1 delta) (- k) (- k)) k args)
                  (summation3 (- (+ i1 delta) k) (- (+ j1 delta) k) k args)))
  :hints (("Goal"
           :use ((:instance equivalence-summation3-summation4-lemma1 (j2 (+ j1 delta)))))))

(defthm equivalence-summation3-summation4
  (implies (and (integerp lo)
                (integerp hi)
                (integerp k))
           (equal (summation4 (- lo k) (- hi k) (+ lo hi (- k) (- k)) k args)
                  (summation3 (- lo k) (- hi k) k args)))
  :hints (("Goal"
           :use ((:instance equivalence-summation3-summation4-lemma2 (delta 0) (i1 lo) (j1 hi))))))
