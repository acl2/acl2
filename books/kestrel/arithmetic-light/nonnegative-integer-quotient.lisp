; A lightweight book about the built-in function nonnegative-integer-quotient.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "times"))
(local (include-book "plus"))

(in-theory (disable nonnegative-integer-quotient))

;; stronger than INVERSE-OF-*
;move
(defthm *-of-/-same
  (equal (* x (/ x))
         (if (equal 0 (fix x))
             0
           1))
  :hints (("Goal" :in-theory (e/d (--becomes-*-of--1)
                                  (*-OF--1)))))

;move
(defthm *-of-/-and---same
  (equal (* (/ Y) (- Y))
         (if (equal (fix y) 0)
             0
           -1))
  :hints (("Goal" :in-theory (e/d (--becomes-*-of--1)
                                  (*-OF--1)))))

(local
 (defthmd integerp-squeeze
   (implies (and (< 0 x)
                 (< x 1))
            (not (integerp x)))))

(local
 (defun nonnegative-integer-quotient-double-induct (i1 i2 j)
   (if (or (= (nfix j) 0) (< (ifix i1) j))
       (list i1 i2 j)
     (+ 1
        (nonnegative-integer-quotient-double-induct (- i1 j)
                                                    (- i2 j)
                                                    J)))))

;todo: make a linear rule
(defthm nonnegative-integer-quotient-weak-monotone
  (implies (and (<= i1 i2)
                (integerp i1)
                (integerp i2))
           (<= (nonnegative-integer-quotient i1 j) (nonnegative-integer-quotient i2 j)))
  :hints (("Goal" :induct (nonnegative-integer-quotient-double-induct i1 i2 j)
           :in-theory (enable nonnegative-integer-quotient))))

(defthm nonnegative-integer-quotient-upper-bound-linear
  (implies (and (integerp i)
                (<= 0 i)
                (integerp j)
                (<= 0 j))
           (<= (nonnegative-integer-quotient i j) (/ i j)))
  :rule-classes ((:linear :trigger-terms ((nonnegative-integer-quotient i j))))
  :hints (("Goal" :in-theory (enable nonnegative-integer-quotient))))

;; (local
;;  (defun nonnegative-integer-quotient-double-induct1 (i j1 j2)
;;    (if (or (= (nfix j1) 0) (< (ifix 1) j1))
;;        (list i j1 2)
;;      (nonnegative-integer-quotient-double-induct (- i j1)
;;                                                  (- i2 j)
;;                                                  J))))


(defthmd nonnegative-integer-quotient-of-+-of---same
  (implies (and (<= j i)
                (natp i)
                (posp j))
           (equal (nonnegative-integer-quotient (+ i (- j)) j)
                  (+ -1 (nonnegative-integer-quotient i j))))
  :hints (("Goal" :in-theory (enable nonnegative-integer-quotient))))

(defthm nonnegative-integer-quotient-of-0-arg1
  (equal (nonnegative-integer-quotient 0 j)
         0)
  :hints (("Goal" :expand (nonnegative-integer-quotient 0 j)
           :in-theory (enable nonnegative-integer-quotient))))

(defthm nonnegative-integer-quotient-of-0-arg2
  (equal (nonnegative-integer-quotient i 0)
         0)
  :hints (("Goal" :in-theory (enable nonnegative-integer-quotient))))

(defthm equal-of-nonnegative-integer-quotient-and-0
  (implies (and (natp i)
                (natp j))
           (equal (equal (nonnegative-integer-quotient i j) 0)
                  (if (equal 0 j)
                      t
                    (< i j))))
  :hints (("Goal" :in-theory (enable nonnegative-integer-quotient))))

(local
 (defun nonnegative-integer-quotient-double-double-induct (i1 i2 j1 j2)
   (if (or (= (nfix j2) 0) (< (ifix i2) j2))
       (list i1 i2 j1 j2)
     (+ 1
        (nonnegative-integer-quotient-double-double-induct (- i1 j1)
                                                           (- i2 j2)
                                                           J1
                                                           j2)))))

(defthm nonnegative-integer-quotient-weak-monotone-gen
  (implies (and (<= i1 i2)
                (<= j2 j1)
                (integerp i1)
                (integerp i2)
                (natp j1)
                (posp j2))
           (<= (nonnegative-integer-quotient i1 j1) (nonnegative-integer-quotient i2 j2)))
  :hints (("Goal" :induct (nonnegative-integer-quotient-double-double-induct i1 i2 j1 j2)
           :expand (nonnegative-integer-quotient i2 j2)
           :in-theory (enable nonnegative-integer-quotient))))

(defthm nonnegative-integer-quotient-weak-monotone-arg2
  (implies (and (<= j1 j2)
                (integerp i)
                (posp j1)
                (posp j2))
           (<= (nonnegative-integer-quotient i j2)
               (nonnegative-integer-quotient i j1)))
  :hints (("Goal" :in-theory (enable nonnegative-integer-quotient))))

;; (defthm nonnegative-integer-quotient-lower-bound-linear-eric
;;   (implies (and (integerp i)
;;                 (<= 0 i)
;;                 (integerp j)
;;                 (< 0 j))
;;            (< (+ -1 (/ i j))
;;               (nonnegative-integer-quotient i j)))
;;   :rule-classes ((:linear :trigger-terms ((nonnegative-integer-quotient i j))))
;;   :hints (("Goal" :in-theory (enable nonnegative-integer-quotient
;;                                      nonnegative-integer-quotient-of-+-of---same))))

;; avoids name clash with rtl
(defthm nonnegative-integer-quotient-lower-bound-linear2
  (implies (and (integerp i)
                (natp j))
           (<= (+ -1 (/ j) (/ i j))
               (nonnegative-integer-quotient i j)))
  :rule-classes ((:linear :trigger-terms ((nonnegative-integer-quotient i j))))
  :hints (("subgoal *1/1" :use (:instance <-of-*-and-*-cancel
                                          (x1 0)
                                          (x2 (+ -1 (/ J) (* I (/ J))))
                                          (y j)))
          ("Goal" :in-theory (e/d (nonnegative-integer-quotient
                                   nonnegative-integer-quotient-of-+-of---same)
                                  (<-of-*-and-*-cancel)))))

;; (thm
;;  (IMPLIES (AND (< X Y)
;;                (INTEGERP X)
;;                (<= 0 X)
;;                (INTEGERP Y)
;;                (< 0 y))
;;           (< (* X (/ Y)) 1)))

;; (thm
;;  (implies (and (integerp (/ x y))
;;                (natp x)
;;                (posp y))
;;           (equal (nonnegative-integer-quotient x y)
;;                  (/ x y)))
;;  :hints (("subGoal *1/1" :use (:instance integerp-squeeze
;;                                          (x (/ x y)))

;;           :in-theory (enable nonnegative-integer-quotient
;;                              ))
;;          ("Goal" :in-theory (enable nonnegative-integer-quotient
;;                                     ))))

(defthm nonnegative-integer-quotient-of-1-arg2
  (implies (natp i)
           (equal (nonnegative-integer-quotient i 1)
                  i))
  :hints (("Goal" :in-theory (enable nonnegative-integer-quotient))))

(defthm nonnegative-integer-quotient-when-<
  (implies (and (< i j)
                (natp i)
                (natp j))
           (equal (nonnegative-integer-quotient i j)
                  0))
  :hints (("Goal" :in-theory (enable nonnegative-integer-quotient))))
