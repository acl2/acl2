; Rules about arithmetic
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; TODO: Deprecate this book in favor of arithmetic-light

(include-book "kestrel/utilities/equal-of-booleans" :dir :system)
(include-book "kestrel/arithmetic-light/plus" :dir :system)
(include-book "kestrel/arithmetic-light/expt" :dir :system)
(include-book "kestrel/arithmetic-light/minus" :dir :system)
(include-book "kestrel/arithmetic-light/times" :dir :system)
(local (include-book "kestrel/library-wrappers/arithmetic-inequalities" :dir :system))

(defthm commutativity-2-of-*
  (equal (* x (* y z))
         (* y (* x z))))

;hope this is okay
(defthm move-negative-addend-1
  (equal (< (+ x (- y)) z)
         (< x (+ y z))))

(defthm plus-cancel-hack-lemma
  (equal (+ (- M) x M)
         (fix x)))

(defthm distributivity-of-minus-over-+
  (equal (- (+ x y))
         (+ (- x) (- y))))

;dup?
(DEFTHM DISTRIBUTIVITY-OF-/-OVER-*
  (EQUAL (/ (* X Y)) (* (/ X) (/ Y))))

;dup
(DEFTHM FOLD-CONSTS-IN-+
  (IMPLIES (AND (SYNTAXP (QUOTEP X))
                (SYNTAXP (QUOTEP Y)))
           (EQUAL (+ X (+ Y Z)) (+ (+ X Y) Z))))

;loops with equal-/ ?
(defthmd half-hack
  (equal (EQUAL 1 (* 2 X))
         (equal x 1/2)))

;dup
(defthm expt-hack
  (implies (integerp n)
           (equal (* 2 (expt 2 (+ -1 n)))
                  (expt 2 n)))
  :hints (("Goal" :in-theory (enable expt))))

;dup
(DEFTHM FUNCTIONAL-COMMUTATIVITY-OF-MINUS-*-RIGHT
  (EQUAL (* X (- Y)) (- (* X Y)))
  :HINTS
  (("Goal"
    :USE FUNCTIONAL-COMMUTATIVITY-OF-MINUS-*-RIGHT-LEMMA)))

;dup
;todo: bad rule.  matches (BINARY-* '-1/2 LOW)
;loops with |(- (* c x))|
(DEFTHM FUNCTIONAL-COMMUTATIVITY-OF-MINUS-*-LEFT
  (EQUAL (* (- X) Y)
         (- (* X Y))))

;; ;dup
;; (DEFTHM EXPT-TYPE-PRESCRIPTION-INTEGERP
;;   (IMPLIES (AND (<= 0 I) (INTEGERP R))
;;            (INTEGERP (EXPT R I)))
;;   :RULE-CLASSES (;:TYPE-PRESCRIPTION
;;                  :GENERALIZE ;todo: do we want this?
;;                  ))

(defthmd even-not-equal-odd-hack
  (implies (and (evenp y)
                (not (evenp x)))
           (equal (equal x y)
                  nil)))

(defthm even-odd-expt-hack
  (implies (and (integerp x)
                (posp n))
           (equal (EQUAL (+ -1 (EXPT 2 N))
                         (* 2 x))
                  nil))
  :hints (("Goal" :in-theory (enable expt even-not-equal-odd-hack))))

(DEFTHM EXPT->-1
  (IMPLIES (AND (< 1 R)
                (< 0 I)
                (REAL/RATIONALP R)
                (INTEGERP I))
           (< 1 (EXPT R I)))
  :RULE-CLASSES :LINEAR)

(defthm integerp-of-/-of-expt
  (equal (integerp (/ (expt 2 m)))
         (or (not (integerp m))
             (<= m 0)))
  :hints (("Goal" :in-theory (enable expt))))

(defthm equal-of-plus-minus-move
  (implies (and (acl2-numberp x)
                (acl2-numberp y))
           (equal (equal (+ (- x) y) 0)
                  (equal y x))))

(defthm inverse-of-+-2
  (equal (+ x (+ (- x) y))
         (fix y)))

;or just include some arithmetic book?
(defthm collect-constants-over-<
  (implies (syntaxp (and (quotep k)
                         (quotep j)))
           (equal (< j (+ k x))
                  (< (- j k) x))))

(defthm collect-constants-over-<-2
  (implies (syntaxp (and (quotep k)
                         (quotep j)))
           (equal (< (+ k x) j)
                  (< x (- j k)))))

;one more in this series?
(defthm drop-<-hyps
  (implies (and (< free x)
                (syntaxp (and (quotep free) (quotep k)))
                (<= k free))
           (< k x)))

(defthm drop->-hyps
  (implies (and (< x free)
                (syntaxp (and (quotep free) (quotep k)))
                (<= free k))
           (< x k)))

(defthm drop-<=-hyps
  (implies (and (<= free x)
                (syntaxp (and (quotep free) (quotep k)))
                (<= k free))
           (not (< x k))))

(defthm integerp-of-/-of-expt-2
  (equal (integerp (/ (expt 2 i)))
         (or (not (integerp i))
             (<= i 0)))
  :hints (("Goal"
           :in-theory (disable integerp-of-expt-when-natp)
           :use (:instance integerp-of-expt-when-natp (r 2) (I (- i))))))

(local (include-book "arithmetic/rationals" :dir :system))

(defthmd integerp-squeeze
  (implies (and (< 0 x)
                (< x 1))
           (not (integerp x))))

(defthmd integerp-squeeze-neg
  (implies (and (< -1 x)
                (< x 0))
           (not (integerp x))))

(defthm integerp-of-/
  (implies (integerp n)
           (equal (integerp (/ n))
                  (or (equal -1 n)
                      (equal 1 n)
                      (equal 0 n))))
  :hints (("Goal" :cases ((< n 0) (< 0 n))
           :in-theory (enable integerp-squeeze-neg
                              integerp-squeeze))))


(defthm expt-2-positive
  (< 0 (expt 2 i)))

(defthmd expt-gather-times
  (implies (and (integerp m)
                (integerp n))
           (equal (* X (EXPT 2 M) (/ (EXPT 2 N)))
                  (* X (expt 2 (- m n)))))
  :hints (("Goal" :in-theory (enable expt-of-+))))

(defthm integerp-times-expts
  (implies (and (natp n)
                (< 0 n)
                (integerp m)
                (<= n m)
                (integerp x))
           (integerp (* x (expt 2 m) (/ (expt 2 n)))))
  :hints (("Goal" :in-theory (e/d (expt-gather-times) (integerp-of-* exponents-add)))))

;from arithmetic
(DEFTHM FUNCTIONAL-SELF-INVERSION-OF-/
  (EQUAL (/ (/ X))
         (FIX X)))

(DEFTHM /-CANCELLATION-ON-LEFT
  (IMPLIES (AND (ACL2-NUMBERP X)
                (NOT (EQUAL 0 X)))
           (EQUAL (* X (/ X) Y) (FIX Y)))
  :HINTS (("Goal" :USE /-CANCELLATION-ON-RIGHT)))

;gen and rename
(defthm expt-collect-hack
  (implies (natp x)
           (equal (* 1/2 (expt 2 (+ -1 x)))
                  (expt 2 (+ -2 x)))))

(theory-invariant (incompatible (:rewrite expt-diff-collect) (:rewrite EXPONENTS-ADD)))
(theory-invariant (incompatible (:rewrite expt-diff-collect) (:rewrite EXPONENTS-ADD-unrestricted)))

(defthm integerp-of-pow2-lemma-another
  (implies (and (integerp size1)
                (integerp size2))
           (equal (integerp (* 2 (expt 2 size1) (/ (expt 2 size2))))
                  (<= size2 (+ 1 size1))))
  :hints (("Goal" :use (:instance integerp-of-expt-when-natp (r 2) (i (+ 1 (- size1 size2))))
           :in-theory (e/d (expt-of-+)
                           (integerp-of-expt-when-natp)))))

(defthm inverse-of-*-better
  (equal (* x (/ x))
         (if (equal 0 (fix x))
             0
           1)))

(defthm plus-of-minus-and-times-two
  (equal (+ (- x) (* 2 x) y)
         (+ x y)))

(defthm plus-of-expt-and-minus-of-expt-one-less
  (implies (natp size)
           (equal (+ (EXPT 2 SIZE) (- (EXPT 2 (+ -1 SIZE))))
                  (EXPT 2 (+ -1 SIZE))))
  :hints (("Goal" :in-theory (enable expt-of-+))))

(defthm plus-of-expt-and-minus-of-expt-one-less-extra
  (implies (natp size)
           (equal (+ (EXPT 2 SIZE) (- (EXPT 2 (+ -1 SIZE))) y)
                  (+ (EXPT 2 (+ -1 SIZE)) y)))
  :hints (("Goal" :in-theory (enable expt-of-+))))

;gen
(defthm /-equal-0
  (equal (equal (/ x) 0)
         (equal (fix x) 0)))

(defthm plus-of-expt-and-expt-one-less
  (implies (integerp size)
           (equal (+ (expt 2 size)
                     (- (expt 2 (+ -1 size)))
                     x)
                  (+ (expt 2 (+ -1 size))
                     x)))
  :hints (("Goal" :in-theory (enable expt-of-+))))

(defthm <-of-expt-and-plus-of-expt-one-less
  (implies (natp size)
           (equal (< (EXPT 2 SIZE) (+ (EXPT 2 (+ -1 SIZE)) x))
                  (< (EXPT 2 (+ -1 SIZE)) x)))
  :hints (("Goal" :in-theory (enable expt-of-+))))

(defthm move-negative-addend-2
  (equal (< z (+ x (- y)))
         (< (+ y z) x)))

(defthm equal-of-sum-cancel-3
  (implies (acl2-numberp x)
           (equal (equal x (+ y z x))
                  (equal 0  (+ y z)))))

(defthm equal-when-<-of-+
  (implies (and (< (+ free y) x)
                (syntaxp (quotep free))
                (<= 0 free))
           (equal (equal x y)
                  nil)))

(defthm equal-when-<-of-+-alt
  (implies (and (< (+ free y) x)
                (syntaxp (quotep free))
                (<= 0 free))
           (equal (equal y x)
                  nil)))

;more generally, (* m n) + (* n x) should become (* (+ m n) x) when m and n are constants
(defthm hack1
  (equal (+ x x rest)
         (+ (* 2 x) rest)))

;rename this series:
(defthm equal-of-same-cancel-1
  (EQUAL (EQUAL (+ X Y) X)
         (AND (ACL2-NUMBERP X)
              (EQUAL (FIX Y) 0))))

(defthm equal-of-same-cancel-2
  (EQUAL (EQUAL X (+ X Y))
         (AND (ACL2-NUMBERP X)
              (EQUAL (FIX Y) 0))))

(defthm equal-of-same-cancel-3
  (EQUAL (EQUAL (+ Y X) X)
         (AND (ACL2-NUMBERP X)
              (EQUAL (FIX Y) 0))))

(defthm equal-of-same-cancel-4
  (EQUAL (EQUAL X (+ Y X))
         (AND (ACL2-NUMBERP X)
              (EQUAL (FIX Y) 0))))

(defthm <-of-*-and-0
  (implies (and (rationalp x)
                (rationalp y))
           (equal (< (* x y) 0)
                  (or (and (< x 0)
                           (< 0 y))
                      (and (< y 0)
                           (< 0 x))))))

(defthm collect-constants-times-equal
  (implies (and (syntaxp (and (quotep k)
                              (quotep k2)))
                (not (equal 0 k))
                (not (equal 0 k2))
                (acl2-numberp k)
                (acl2-numberp k2)
                )
           (equal (equal (* k2 x) k)
                  (equal x (/ k k2)))))


(defthm <-of-+-cancel-second-of-more-and-only
  (equal (< (+ y x z) x)
         (< (+ y z) 0)))

(defthm <-of-+-cancel-only-and-third-of-more
  (equal (< x (+ y z x w))
         (< 0 (+ y z w))))

(defthm <-of-+-cancel-third-of-more-and-only
  (equal (< (+ y z x w) x)
         (< (+ y z w) 0)))

(defthm commutativity-2-of-+-when-constant
  (implies (syntaxp (and (quotep y)
                         (not (quotep x))))
           (equal (+ x (+ y z))
                  (+ y (+ x z)))))

;uses the equal phrasing
(defthm rationalp-of-+
  (implies (and (rationalp x)
                (rationalp y))
           (rationalp (+ x y))))

(in-theory (disable rationalp-+))

(defthm commutativity-of-*-when-constant
  (implies (syntaxp (and (quotep y)
                         (not (quotep x))))
           (equal (* x y)
                  (* y x))))

(defthm cancel-1-2
  (equal (equal (+ x y) (+ z x w))
         (equal (fix y) (+ z w))))

(defthm cancel-2-2
  (equal (equal (+ v x y) (+ z x w))
         (equal (+ v y) (+ z w))))

(defthmd rationalp-*2
  (implies (and (rationalp x) (rationalp y))
           (rationalp (* x y))))

(defthm equal-of-0-and-+-of-minus
  (implies (and (rationalp i) (rationalp j))
           (equal (equal 0 (+ i (- j)))
                  (equal i j))))

(defthm equal-of-+-and-+-cancel-cross
  (implies (and ;(acl2-numberp x)
                (acl2-numberp y)
                (acl2-numberp k))
           (equal (equal (+ k x) (+ x y))
                  (equal k y))))

(defthm <-of-expt-and-expt
  (implies (and (< 1 r)
                (rationalp r)
                (integerp i)
                (integerp j))
           (equal (< (expt r i) (expt r j))
                  (< i j)))
  :hints (("Goal" :use (:instance expt-is-increasing-for-base>1))))

;should be cheap
;complete set of these?!
(defthm <-of-constant-when-<=-of-free
  (implies (and (syntaxp (quotep k1))
                (<= x free)
                (syntaxp (quotep free))
                (<= free k1))
           (not (< k1 x))))

;could be expensive
;dup
(defthm rationalp-when-integerp
  (implies (integerp x)
           (rationalp x)))

;dup
(defund power-of-2p (x)
  (declare (xargs :guard t))
  (and (natp x) ;otherwise, this would count 1/2 but not 1/4
       (= x (expt 2 (+ -1 (integer-length x))))))


(defthm integerp-of-power2-hack
  (implies (and (syntaxp (quotep k))
                (power-of-2p k)
                (integerp n))
           (equal (integerp (binary-* k (unary-/ (expt '2 n))))
                  (<= n (+ -1 (integer-length k)))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (expt-of-+ power-of-2p) (integerp-of-expt-when-natp))
           :use (:instance integerp-of-expt-when-natp
                           (r 2)
                           (i (- (+ -1 (integer-length k)) n))))))

(defthm integerp-of-power2-hack-another-factor
  (implies (and (syntaxp (quotep k))
                (power-of-2p k)
                (<= n (+ -1 (integer-length k)))
                (Integerp y)
                (integerp n))
           (integerp (* k (unary-/ (expt '2 n)) y)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (expt-of-+ power-of-2p) ( integerp-of-expt-when-natp))
           :use ((:instance integerp-of-* (x (* k (unary-/ (expt '2 n)))))
                 (:instance integerp-of-expt-when-natp
                            (r 2)
                            (i (- (+ -1 (integer-length k)) n)))))))

(defthm integerp-of-power2-hack-another-factor-alt
  (implies (and (syntaxp (quotep k))
                (power-of-2p k)
                (<= n (+ -1 (integer-length k)))
                (Integerp y)
                (integerp n))
           (integerp (* k y (unary-/ (expt '2 n)))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (expt-of-+ power-of-2p) ( integerp-of-expt-when-natp))
           :use ((:instance integerp-of-* (x (* k (unary-/ (expt '2 n)))))
                 (:instance integerp-of-expt-when-natp
                            (r 2)
                            (i (- (+ -1 (integer-length k)) n)))))))

(defthm <-of-sums-cancel
  (equal (< x (+ x y))
         (< 0 y)))

;linear can get this, but maybe this will keep us from generating trivial cases?...
(defthm no-room-between-ints-lemma
  (IMPLIES (AND (syntaxp (and (quotep k) (integerp (unquote k))))
                (< x (+ free y))
                (syntaxp (quotep free))
                (<= free (+ 1 k))
                (integerp k)
                (integerp x)
                (integerp y)
                )
           (not (< (+ k y) x))))

(defthm <-of-expt-cancel-lemma
  (implies (integerp size)
           (equal (< (+ x y (expt 2 size)) (expt 2 (+ -1 size)))
                  (< (+ x y (expt 2 (+ -1 size))) 0)))
  :hints (("Goal" :in-theory (enable expt-of-+))))

(defthm <-of-expt-cancel-lemma-2
  (implies (integerp size)
           (equal (< (+ x (expt 2 size)) (expt 2 (+ -1 size)))
                  (< (+ x (expt 2 (+ -1 size))) 0)))
  :hints (("Goal" :in-theory (enable expt-of-+))))

(defthm <-of-expt-cancel-lemma-3
  (implies (integerp size)
           (equal (< (expt 2 (+ -1 size)) (+ (expt 2 size) x))
                  (< 0 (+ (expt 2 (+ -1 size)) x))))
  :hints (("Goal" :in-theory (enable expt-of-+))))

;it helps to have this be a rewrite rule, even though linear and tau can get it
; (e.g., when ACL2 decides whether to open a function)
;; todo: gen the 1 (but this is a "simple" rule, so perhaps also keep this)
(defthm <-of-one-more
  (< n (+ 1 n)))

;gen the 1...
(defthm <-of-/-and-1
  (implies (rationalp x)
           (equal (< (/ x) 1)
                  (or (<= x 0)
                      (< 1 x)))))
