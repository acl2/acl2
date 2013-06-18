#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
(in-package "ACL2")

;This book has a lot of good stuff about logand, etc. that is proved in books/rtl/.

(local (include-book "rtl/rel8/support/support/logand" :dir :system))
(local (include-book "rtl/rel8/support/support/logxor" :dir :system))
(local (include-book "rtl/rel8/support/support/logior" :dir :system))
(local (include-book "rtl/rel8/arithmetic/integerp" :dir :system))



(defthm logand-non-negative
  (implies (or (<= 0 x) (<= 0 y))
           (<= 0 (logand x y)))
  :hints (("Goal" :in-theory (enable logand)
           :do-not '(generalize eliminate-destructors))))


(defthm logand-associative
  (equal (logand (logand i j) k)
         (logand i (logand j k))))

(defthm logand-commutative-2
  (equal (logand j i k)
         (logand i j k)))

;slightly different from what we have in rtl
(defthm logand-x-x
  (equal (logand x x)
         (if (integerp x)
             x
           0)))

(defthm logxor-associative
  (equal (logxor (logxor i j) k)
         (logxor i (logxor j k))))

(defthm logxor-commutative-2
  (equal (logxor j i k)
         (logxor i j k)))

(defthm logxor-self
  (equal (logxor i i)
         0))

(defthm logior-associative
  (equal (logior (logior i j) k)
         (logior i (logior j k))))

(defthm logior-commutative-2
  (equal (logior j i k)
         (logior i j k)))


(local (include-book "rtl/rel8/arithmetic/expt" :dir :system))

(defthm expt-2-positive-rational-type
  (and (rationalp (expt 2 i))
       (< 0 (expt 2 i)))
  :rule-classes (:rewrite (:type-prescription :typed-term (expt 2 i))))

(defthm integerp-sum-take-out-known-integer
   (implies (integerp n)
            (and (equal (integerp (+ n x))
                        (integerp (fix x)))
                 (equal (integerp (+ x n))
                        (integerp (fix x))))))

(defthm integerp-sum-take-out-known-integer-3
  (implies (integerp n)
           (and ;(equal (integerp (+ n x y))      ;this case not needed?
                 ;      (integerp (fix (+ x y))))
                (equal (integerp (+ x n y))
                       (integerp (fix (+ x y))))
                (equal (integerp (+ x y n))
                       (integerp (fix (+ x y)))))))

;this is better than EXPT2-INVERSE-INTEGER in the RTL books
(defthm integerp-of-inverse-of-expt
  (equal (integerp (/ (expt 2 n)))
         (or (not (integerp n))
             (<= n 0))))

(local (include-book "rtl/rel8/arithmetic/top" :dir :system))

;this is better than the one in RTL
;make a linear rule?
(defthm logior-bnd-eric
  (equal (<= x (logior x y))
         (if (integerp x)
             (if (integerp y)
                 (or (<= 0 y)
                     (< x 0))
               t)
           (<= x (ifix y))))
  :hints (("Goal" :in-theory (e/d () (LESS-THAN-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-LEFT-HAND-SIDE
                                      FL-<-INTEGER
                                      FL->-INTEGER
;FL-LOGIOR-BY-2
                                      FL-OF-EVEN/2
                                      )
                                  )
           :induct (LOG-INDUCT-allows-negatives x y))
          ("Subgoal *1/2" :use ((:instance logior-def (i x) (j y))
                                (:instance quot-mod (m x) (n 2))
;(:instance mod012)
;(:instance mod012 (x y))
                                ))))

(defthm logior-bnd-eric-linear
  (implies (and (integerp x)
                (or (<= 0 y)
                    (< x 0))
                )
         (<= x (logior x y)))
  :rule-classes ((:linear :trigger-terms ((logior x y))))
  :hints (("Goal" :use (:instance logior-bnd-eric)
           :in-theory (disable logior-bnd-eric)
           )))


;we disable this, because it can cause problems
(DEFthmd MOD-CANCEL
  (IMPLIES
   (SYNTAXP (NOT (AND (QUOTEP Y) (EQUAL (CADR Y) 1))))
   (EQUAL (MOD X Y)
          (IF (ACL2-NUMBERP X)
              (IF (ACL2-NUMBERP Y)
                  (IF (EQUAL 0 Y) X (* Y (MOD (/ X Y) 1)))
                  X)
              0))))



(DEFTHM INTEGERP-SUM-OF-ODDS-OVER-2-LEADING-CONSTANT
  (IMPLIES (AND (SYNTAXP (AND (QUOTEP X)
                              (INTEGERP (* 2 X))
                              (NOT (INTEGERP X))))
                (RATIONALP X)
                (RATIONALP Y)
                (INTEGERP (* 2 X))
                (NOT (INTEGERP X))
                (INTEGERP (* 2 Y))
                (NOT (INTEGERP Y)))
           (INTEGERP (+ X Y))))


(defthm equal-1-hack
  (implies (and (integerp x)
                (< x 2)
                (< 0 x))
           (equal (equal x 1)
                  t)))

;bzo rtl can prove this with equal-1-hack
(defthm rtl-a-million
  (IMPLIES (AND (INTEGERP I)
                (<= 0 I)
                (< I Y)
                (NOT (EQUAL I 0))
                (INTEGERP Y)
                (<= 0 Y)
                (INTEGERP (+ (/ Y) (* I (/ Y)))))
           (EQUAL (+ (/ Y) (* I (/ Y))) 1)))

(defthm rtl
  (IMPLIES (AND (INTEGERP I)
                     (INTEGERP I0)
                     (< I 32768)
                     (<= 32768 (+ I (* 32768 I0)))
                     (< 0 I0)
                     (<= 0 I0)
                     (INTEGERP (* 1/2 (FLOOR (* 1/16384 I) 1))))
                (< I 16384)))

;bzo from-rtl
(DEFthm MOD-SUMS-CANCEL-3
  (IMPLIES (AND (CASE-SPLIT (<= 0 Y))
                (CASE-SPLIT (RATIONALP K))
                (CASE-SPLIT (RATIONALP Y))
                (CASE-SPLIT (RATIONALP X1))
                (CASE-SPLIT (RATIONALP X2)))
           (EQUAL (EQUAL (MOD (+ X1 K) Y)
                         (MOD (+ X2 K) Y))
                  (EQUAL (MOD X1 Y) (MOD X2 Y)))))
