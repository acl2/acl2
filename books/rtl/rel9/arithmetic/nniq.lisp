; RTL - A Formal Theory of Register-Transfer Logic and Computer Arithmetic
; Copyright (C) 1995-2013 Advanced Mirco Devices, Inc.
;
; Contact:
;   David Russinoff
;   1106 W 9th St., Austin, TX 78703
;   http://www.russsinoff.com/
;
; See license file books/rtl/rel9/license.txt.
;
; Author: David M. Russinoff (david@russinoff.com)

(in-package "ACL2")

(include-book "ground-zero")
(local (include-book "fp2"))
(local (include-book "denominator"))
(local (include-book "numerator"))
(local (include-book "predicate"))
(local (include-book "unary-divide"))
(local (include-book "product"))
(local (include-book "integerp"))
(local (include-book "arith"))

;lemmas if non-rat args?

(defthm nonnegative-integer-quotient-with-a-non-integer-arg
  (implies (not (integerp i))
           (equal (nonnegative-integer-quotient i j)
                  0))
  :hints (("Goal" :in-theory (enable nonnegative-integer-quotient))))

(defthm nonnegative-integer-quotient-with-a-non-integer-arg-2
  (implies (not (integerp j))
           (equal (nonnegative-integer-quotient i j)
                  0))
  :hints (("Goal" :in-theory (enable nonnegative-integer-quotient))))

(defthm nonnegative-integer-quotient-with-a-non-positive-arg
  (implies (<= i 0)
           (equal (nonnegative-integer-quotient i j)
                  0))
  :hints (("Goal" :in-theory (enable nonnegative-integer-quotient))))

(defthm nonnegative-integer-quotient-with-a-non-positive-arg-2
  (implies (<= j 0)
           (equal (nonnegative-integer-quotient i j)
                  0))
    :hints (("Goal" :in-theory (enable nonnegative-integer-quotient))))

;like doc's floor-m+1-3?
(defthm nonnegative-integer-quotient-upper-bound-rewrite
  (implies (and (case-split (<= 0 i))
                (case-split (<= 0 j))
                (case-split (rationalp j))
                )
           (<= (nonnegative-integer-quotient i j) (/ i j)))
  :hints (("Goal" :cases ((rationalp i)
                          )
           :in-theory (enable nonnegative-integer-quotient))))

;BOZO strict < when quotient isn't an integer
(defthm nonnegative-integer-quotient-upper-bound-linear
  (implies (and (case-split (<= 0 i))
                (case-split (<= 0 j))
                (case-split (rationalp j))
                )
           (<= (nonnegative-integer-quotient i j) (/ i j)))
  :rule-classes ((:linear :trigger-terms ((nonnegative-integer-quotient i j)))))

#|
(defthm nonnegative-integer-quotient-upper-bound-linear-strict
  (implies (and (not (integerp (NOT (INTEGERP (* I (/ J)))))) ;allows the strict bound
                (case-split (<= 0 i))
                (case-split (<= 0 j))
                (case-split (rationalp j))
                )
           (< (nonnegative-integer-quotient i j) (/ i j)))
  :hints (("Goal" :use  nonnegative-integer-quotient-upper-bound-linear
           ))
  :rule-classes ((:linear :trigger-terms ((nonnegative-integer-quotient i j)))))
|#


#|
;what should the trigger terms be?
(defthm nonnegative-integer-quotient-upper-bound-2
  (implies (and (case-split (<= 0 i))
                (case-split (<= 0 j))
;                (case-split (rationalp i))
                (case-split (rationalp j))
                )
           (<= (* j (nonnegative-integer-quotient i j)) i))
  :hints (("Goal" :cases ((rationalp i))
           :in-theory (enable nonnegative-integer-quotient)))
  :rule-classes (:rewrite (:linear :trigger-terms ((nonnegative-integer-quotient i j)))))
|#

#|
(defthm nonnegative-integer-quotient-upper-bound-3
  (implies (and (case-split (<= 0 i))
                (case-split (<= 0 j))
;                (case-split (rationalp i))
                (case-split (rationalp j))
                )
           (<= (* j (nonnegative-integer-quotient i j)) i))
  :hints (("Goal" :cases ((rationalp i))
           :in-theory (enable nonnegative-integer-quotient)))
  :rule-classes (:rewrite (:linear :trigger-terms ((* j (nonnegative-integer-quotient i j))))))
|#

;rewrite nniq to (/ i j) when quotient is known integer?
(defthm nonnegative-integer-quotient-max-value-rewrite
  (implies (and (case-split (<= 0 i))
                (case-split (<= 0 j))
                (case-split (integerp i))
                (case-split (integerp j))
                )
           (equal (equal (nonnegative-integer-quotient i j) (/ i j))
                  (integerp (/ i j))))
  :hints (("Goal" :in-theory (enable nonnegative-integer-quotient))))

(defthm nonnegative-integer-quotient-lower-bound-rewrite
  (implies (and (case-split (integerp i))
                (case-split (integerp j))
                (case-split (<= 0 i))
                (case-split (<= 0 j))
                )
           (< (+ -1 (/ i j)) (nonnegative-integer-quotient i j)))
  :hints (("Goal" :in-theory (enable nonnegative-integer-quotient))))

(defthm nonnegative-integer-quotient-lower-bound-linear
  (implies (and (case-split (integerp i))
                (case-split (integerp j))
                (case-split (<= 0 i))
                (case-split (<= 0 j))
                )
           (< (+ -1 (/ i j)) (nonnegative-integer-quotient i j)))
  :rule-classes ((:linear :trigger-terms ((nonnegative-integer-quotient i j)))))

#|
;what should the trigger terms be?
(defthm nonnegative-integer-quotient-lower-bound-2
  (implies (and (case-split (integerp i))
                (case-split (integerp j))
                (case-split (<= 0 i))
                (case-split (<= 0 j))
                (case-split (not (equal 0 j)))
                )
           (< (+ i (* -1 j)) (* j (nonnegative-integer-quotient i j))))
  :hints (("Goal" :in-theory (disable  nonnegative-integer-quotient-lower-bound)
           :use  nonnegative-integer-quotient-lower-bound))
  :rule-classes (:rewrite (:linear :trigger-terms ((nonnegative-integer-quotient i j)))))
|#

#|
(defthm nonnegative-integer-quotient-lower-bound-3
  (implies (and (case-split (integerp i))
                (case-split (integerp j))
                (case-split (<= 0 i))
                (case-split (<= 0 j))
                (case-split (not (equal 0 j)))
                )
           (< (+ i (* -1 j)) (* j (nonnegative-integer-quotient i j))))
  :hints (("Goal" :in-theory (disable  nonnegative-integer-quotient-lower-bound)
           :use  nonnegative-integer-quotient-lower-bound))
  :rule-classes (:rewrite (:linear :trigger-terms ((* j (nonnegative-integer-quotient i j))))))

|#

#|

         (<= (* J
                (NONNEGATIVE-INTEGER-QUOTIENT (NUMERATOR (* I (/ J)))
                                              (DENOMINATOR (* I (/ J)))))
             I)

|#


(defthm nonnegative-integer-quotient-upper-bound-linear-stronger
  (implies (and (case-split (<= 0 i))
                (case-split (<= 0 j))
                (NOT (INTEGERP (* I (/ J))))
                (case-split (acl2-numberp i))
                (case-split (rationalp j))
                (case-split (rationalp k))
                (case-split (< 0 k))
                )
           (< (* k (nonnegative-integer-quotient i j)) (* k (/ i j))))
  :hints (("Goal" :cases ((rationalp i))
           :in-theory (enable nonnegative-integer-quotient)))
  :rule-classes ((:linear :trigger-terms ((* k (nonnegative-integer-quotient i j))
                                          ))))


#|
;was this ever proved?
(defthm nonnegative-integer-quotient-upper-bound-linear-stronger
   (implies (and (case-split (<= 0 i))
                 (case-split (<= 0 j))
                 (NOT (INTEGERP (* I (/ J))))
                 (case-split (acl2-numberp i))
                 (case-split (rationalp j))
                 (case-split (rationalp k))
                 (case-split (< 0 k))
                 )
            (< (* k (nonnegative-integer-quotient i j)) (* k (/ i j))))
   :hints (("Goal" :cases ((rationalp i))
            :in-theory (enable nonnegative-integer-quotient)))
   :rule-classes ((:linear :trigger-terms ((* k (nonnegative-integer-quotient i j))))))



|#

(defthm nonnegative-integer-quotient-when-j-is-0
  (equal (nonnegative-integer-quotient i 0)
         0))


;gen?
(encapsulate ()
              (local (defthm nniq-no-rounding-to-do-all-but-j=0
                       (implies (and (integerp (* i (/ j)))
                                     (integerp i)
                                     (>= i 0)
                                     (integerp j)
                                     (> j 0)
                                     )
                                (equal (nonnegative-integer-quotient i j)
                                       (/ i j)))))

              (defthm nniq-no-rounding-to-do
                       (implies (and (integerp (* i (/ j)))
                                     (case-split (integerp i))
                                     (case-split (<= 0 i))
                                     (case-split (integerp j))
                                     (case-split (<= 0 j))
                                     )
                                (equal (nonnegative-integer-quotient i j)
                                       (/ i j)))))

;begin stuff from elib27/rel2/nniq
;i haven't organized the stuff below

;move!
;if the denom of a fraction is 1, the numerator is the whole fraction!
(defthm denom-1-means-num-is-all
  (implies (and (rationalp x)
                (equal (denominator x) 1))
           (equal (numerator x)
                  x))
  :hints (("Goal" :in-theory (disable rational-implies2)
           :use rational-implies2)))

(defthm nonnegative-integer-quotient-by-1
  (implies (and
            (integerp x)
            (<= 0 x))
           (equal (nonnegative-integer-quotient x 1)
                  x)))
#|
;drop?
;will backchain on (integerp x)!
(defthm integer-has-denom-1-other-way
  (implies (and
            (rationalp x) ;acl2-numberp?
            (equal (denominator x) 1))
           (integerp x))
   :hints (("Goal" :in-theory (disable rational-implies2)
           :use (rational-implies2
                 (:instance Lowest-terms
                           (n (denominator x))
                           (r x)
                           (q 1))))))
|#



(defthm division-by-zero-yields-zero
  (equal (/ m 0)
         0))

;expensive?
(defthm fraction-less-than-1
  (IMPLIES (AND (< (abs M) (abs N))
                (rationalp m)
                (rationalp n))
           (<= (* m (/ n)) 1))
  :hints (("Goal" :cases ((> n 0) (= n 0)))))

(defthm nniq-int
  (implies (and (integerp x)
                (case-split (<= 0 x))
                )
           (equal (nonnegative-integer-quotient (numerator x)
                                                (denominator x))
                  x)))



(encapsulate ()
             (local (include-book "../../../arithmetic/rationals"))
             (local (include-book "../../../arithmetic/idiv"))

             (defthm quotient-numer-denom
               (implies (and (integerp x) (< 0 x) (integerp y) (< 0 y))
                        (equal (nonnegative-integer-quotient (numerator (/ x y))
                                                             (denominator (/ x y)))
                               (nonnegative-integer-quotient x y))))

             (defthm
               acl2::Numerator-minus
               (equal (numerator (- i))
                      (- (numerator i))))

             (defthm
               acl2::Denominator-unary-minus
               (implies (rationalp x)
                        (equal (denominator (- x))
                               (denominator x))))

             (defthm
               acl2::Denominator-plus
               (implies (and (rationalp r)
                             (integerp i))
                        (equal (denominator (+ i r))
                               (denominator r))))
             (defthm
               Denominator-plus-2
               (implies (and (rationalp r)
                             (integerp i))
                        (equal (denominator (+ r i))
                               (denominator r))))

;add to arith books?
             (defthm numerator-plus
               (implies (and (rationalp x)
                             (integerp i))
                        (equal (numerator (+ x i))
                               (+ (* i (denominator x)) (numerator x))))
               :hints (("Goal" :in-theory (disable rational-implies2)
                        :use (:instance rational-implies2 (x (+ x i)))))))

(defthm numerator-plus-alt
  (implies (and (rationalp x)
                (integerp i))
           (equal (numerator (+ i x))
                  (+ (* i (denominator x)) (numerator x))))
  :hints (("Goal" :in-theory (disable numerator-plus)
           :use (:instance numerator-plus))))

(defthm Numerator-minus-eric
  (equal (numerator (* -1 i))
         (* -1 (numerator i)))
  :hints (("Goal" :in-theory (disable acl2::Numerator-minus)
           :use acl2::Numerator-minus)))

(defthm Denominator-unary-minus-eric
  (implies (rationalp x)
           (equal (denominator (* -1 x))
                  (denominator x)))
  :hints (("Goal" :in-theory (disable acl2::Denominator-unary-minus)
           :use acl2::Denominator-unary-minus)))



(encapsulate ()
              (local (defthm NONNEGATIVE-INTEGER-QUOTIENT-sum-on-top
                       (implies (and (integerp x)
                                     (>= x 0)
                                     (integerp y)
                                     (> y 0)
                                     )
                                (equal (NONNEGATIVE-INTEGER-QUOTIENT (+ x y) y)
                                       (+ 1 (NONNEGATIVE-INTEGER-QUOTIENT x y))))))

              (local (defun nniq-induct (x y a)
                       (if (zp a)
                           1
                         (* x y (nniq-induct x y (- a 1))))))

              (local (DEFTHM NONNEGATIVE-INTEGER-QUOTIENT-SUM-ON-TOP-GEN
                       (IMPLIES (AND (INTEGERP X)
                                     (>= X 0)
                                     (INTEGERP A)
                                     (INTEGERP Y)
                                     (> Y 0)
                                     (>= A 0)
                                     )
                                (EQUAL (NONNEGATIVE-INTEGER-QUOTIENT (+ X (* A Y))
                                                                     Y)
                                       (+ A (NONNEGATIVE-INTEGER-QUOTIENT X Y))))
                       :HINTS
                       (("subgoal *1/2" :IN-THEORY (DISABLE NONNEGATIVE-INTEGER-QUOTIENT-SUM-ON-TOP)
                         :USE
                         ((:INSTANCE NONNEGATIVE-INTEGER-QUOTIENT-SUM-ON-TOP
                                     (X (+ X (* (- A 1) Y))))))
                        ("Goal" :DO-NOT '(GENERALIZE)
                         :INDUCT (NNIQ-INDUCT X Y A)))))

              (local (defthm NONNEGATIVE-INTEGER-QUOTIENT-sum-on-top-back
                       (implies (and (integerp x)
                                     (>= x 0)
                                     (integerp y)
                                     (> y 0)
                                     (>= (+ x (- y)) 0)
                                     )
                                (equal (NONNEGATIVE-INTEGER-QUOTIENT (+ x (* -1 y)) y)
                                       (+ -1 (NONNEGATIVE-INTEGER-QUOTIENT x y))))))

              (local (defun nniq-induct-2 (x y a)
                       (if (or (not (integerp a)) (>= a 0))
                           1
                         (* x y (nniq-induct-2 x y (+ a 1))))))



              (local (DEFTHM NONNEGATIVE-INTEGER-QUOTIENT-SUM-ON-TOP-GEN-back
                       (IMPLIES (AND (INTEGERP X)
                                     (>= X 0)
                                     (INTEGERP A)
                                     (INTEGERP Y)
                                     (> Y 0)
                                     (< A 0)
                                     (<= 0 (+ x (* a y)))
                                     )
                                (EQUAL (NONNEGATIVE-INTEGER-QUOTIENT (+ X (* A Y))
                                                                     Y)
                                       (+ A (NONNEGATIVE-INTEGER-QUOTIENT X Y))))
                       :otf-flg t
                       :HINTS
                       (("subgoal *1/" :IN-THEORY (DISABLE NONNEGATIVE-INTEGER-QUOTIENT-SUM-ON-TOP-back)
                         :USE
                         ((:INSTANCE NONNEGATIVE-INTEGER-QUOTIENT-SUM-ON-TOP-back
                                     (X (+ X (* (+ A 1) Y))))))
                        ("Goal" :DO-NOT '(GENERALIZE)
                         :INDUCT (NNIQ-INDUCT-2 X Y A)))))

              (DEFTHM NONNEGATIVE-INTEGER-QUOTIENT-SUM-ON-TOP-GEN-both-cases
                (IMPLIES (AND (INTEGERP X)
                              (>= X 0)
                              (INTEGERP A)
                              (INTEGERP j)
                              (> j 0)
                              (<= 0 (+ x (* a j))) ;drop?
                              )
                         (EQUAL (NONNEGATIVE-INTEGER-QUOTIENT (+ X (* A j)) j)
                                (+ A (NONNEGATIVE-INTEGER-QUOTIENT X j))))
                :hints (("Goal" :cases ((>= a 0))))))

;(in-theory (disable NONNEGATIVE-INTEGER-QUOTIENT-sum-on-top))



(encapsulate ()
             (local (include-book "../../../arithmetic/idiv"))
             (local (INCLUDE-BOOK "../../../arithmetic/top-with-meta"))

             (defthm nniq-eric-1
               (implies (and (rationalp x)
                             (not (integerp x)))
                        (> (+ 1 (nonnegative-integer-quotient (numerator x) (denominator x))) ;the ceiling of x
                           x))
               :hints (("Goal" :in-theory (disable ACL2::QUOTIENT-UPPER-BOUND
                                                   NONNEGATIVE-INTEGER-QUOTIENT)
                        :use (:instance ACL2::QUOTIENT-UPPER-BOUND (x (numerator x)) (y (denominator x))))))
             )


;this sequence is used for nniq-lower-bound-non-integer-case
(defthm nniq-eric-2
  (implies (and (rationalp x)
                (not (integerp x)))
           (> (+ (denominator x) (* (denominator x) (nonnegative-integer-quotient (numerator x) (denominator x))))
              (numerator x)))
  :hints (("Goal" :in-theory  (disable nniq-eric-1 RATIONAL-IMPLIES2)
           :use  (nniq-eric-1 RATIONAL-IMPLIES2))))


(defthm nniq-eric-3
  (implies (and (rationalp x)
                (not (integerp x)))
           (>= (+ (denominator x) (* (denominator x) (nonnegative-integer-quotient (numerator x) (denominator x))))
              (+ 1 (numerator x))))
  :hints (("Goal" :in-theory  (disable nniq-eric-2)
           :use  (nniq-eric-2))))


(defthm nniq-eric-4
  (implies (and (rationalp x)
                (not (integerp x)))
           (>= (+ 1 (nonnegative-integer-quotient (numerator x) (denominator x)))
               (+ (/ (numerator x) (denominator x)) (/ (denominator x)))))
  :hints (("Goal" :in-theory  (disable nniq-eric-3 RATIONAL-IMPLIES2)
           :use  (nniq-eric-3))))

(defthm nniq-lower-bound-non-integer-case
  (implies (and (rationalp x)
                (not (integerp x)))
           (>= (+ 1 (nonnegative-integer-quotient (numerator x) (denominator x)))
               (+ x (/ (denominator x)))))
  :hints (("Goal" :in-theory  (disable NNIQ-ERIC-3 nniq-eric-4)
           :use  (nniq-eric-4))))


(in-theory (disable  nniq-eric-1  nniq-eric-2  nniq-eric-3  nniq-eric-4))



(defthm nniq-eric-5
  (implies (and (integerp p)
                (integerp q)
                (not (integerp (/ p q)))
                (< 0 p)
                (< 0 q))
           (< (nonnegative-integer-quotient p q)
              (/ p q)))
  :hints (("Goal" :in-theory  (disable nniq-eric-1 RATIONAL-IMPLIES2)
           :use  (nniq-eric-1 RATIONAL-IMPLIES2))))


(defthm nniq-eric-6
  (implies (and (integerp p)
                (integerp q)
                (not (integerp (/ p q)))
                (< 0 p)
                (< 0 q))
           (< (* q (nonnegative-integer-quotient p q))
              p))
  :hints (("Goal" :in-theory  (disable nonnegative-integer-quotient nniq-eric-5)
           :use  (nniq-eric-5))))

(defthm nniq-eric-7
  (implies (and (integerp p)
                (integerp q)
                (not (integerp (/ p q)))
                (< 0 p)
                (< 0 q))
           (<= (+ 1 (* q (nonnegative-integer-quotient p q)))
              p))
  :hints (("Goal" :in-theory  (disable nonnegative-integer-quotient nniq-eric-6)
           :use  (nniq-eric-6))))


(defthm nniq-eric-8
  (implies (and (integerp p)
                (integerp q)
                (not (integerp (/ p q)))
                (< 0 p)
                (< 0 q))
           (<= (+ (/ q) (nonnegative-integer-quotient p q))
               (/ p q)))
  :hints (("Goal" :in-theory  (disable nonnegative-integer-quotient nniq-eric-7)
           :use  (nniq-eric-7))))

(in-theory (disable  nniq-eric-5 nniq-eric-6 nniq-eric-7 nniq-eric-8))








#|
;too hard?
(DEFTHM NONNEGATIVE-INTEGER-QUOTIENT-split-sum-case-1
  (IMPLIES (AND (INTEGERP i1)
                (> i1 0)
                (INTEGERP i2)
                (> i2 0)
                (INTEGERP j)
                (> j 0)
                (< (+ (mod i1 j)
                      (mod i2 j)) j)
                )
           (EQUAL (NONNEGATIVE-INTEGER-QUOTIENT (+ i1 i2)
                                                j)
                  (+  (NONNEGATIVE-INTEGER-QUOTIENT i1 j)
                      (NONNEGATIVE-INTEGER-QUOTIENT i2 j))))


)










;integers
;nniq of x+a*y and y is nniq of x and y, + a



i/j = (nniq i j) + (mod/rem i j)












|#
