#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
(in-package "ACL2")

(include-book "ihs/quotient-remainder-lemmas" :dir :system)
(include-book "ihs/math-lemmas" :dir :system)
(include-book "eric")
(include-book "from-rtl")

;this was causing lots of generalization to occur, introducing mod into goals which had nothing to do with mod.
(in-theory (disable (:generalize MOD-X-Y-=-X+Y)))

(in-theory (disable 
            (:DEFINITION NONNEGATIVE-INTEGER-QUOTIENT)
            (:DEFINITION FLOOR)
            (:DEFINITION CEILING)
            (:DEFINITION TRUNCATE)
            (:DEFINITION ROUND)
            (:DEFINITION MOD)
            (:DEFINITION REM)
            (:DEFINITION EXPT)
            ))

;alternate form of the built-in rule distributivity
(defthm distributivity-alt
  (equal (* (+ y z) x)
         (+ (* x y) (* x z))))

;generalize?
(defthm expt-2-cruncher
  (implies (integerp m)
           (equal (* 2 (expt 2 (+ -1 m)))
                  (expt 2 m)))
  :hints (("Goal" :in-theory (enable expt))))

(defthm integerp-unary-
  (equal (integerp (- a))
         (integerp (fix a)))
  :hints (("Goal" :cases ((integerp a)))))

(defthm <-+-constant-constant
  (implies (and (syntaxp (quotep a))
                (syntaxp (quotep b)))
           (and (equal (< a (+ b c))
                       (< (- a b) c))
                (equal (< (+ b c) a)
                       (< c (- a b))))))

(defthm move---to-constant-in-equal
  (implies (and (syntaxp (quotep y))
                (acl2-numberp y)
                (acl2-numberp x))
           (equal (equal y (- x))
                  (equal (- y) x)))
  :hints (("goal" :in-theory (enable fix)))
  :rule-classes ((:rewrite :loop-stopper nil)))

(defthm integerp-0-1
  (implies (or (and (< 0 x) (< x 1))
               (and (< -1 x) (< x 0)))
           (not (integerp x)))
  :rule-classes nil)

(defthm integerp-/
  (implies (and (integerp n)
                (not (equal n 0)))
           (equal (integerp (/ n)) 
                  (or (equal n 1) (equal n -1))))
  :hints (("goal" :use ((:instance integerp-0-1 (x (/ n)))
                        (:instance integerp-0-1 (x (/ n)))))))

;rename?
;where should this go?
;compare to EXPT-TYPE-PRESCRIPTION-INTEGERP
(defthm integerp-expt-1
  (implies (and (<= 0 i) (integerp r))
           (integerp (expt r i))))

(defthm integerp-expt
  (implies (integerp n)
           (equal (integerp (expt 2 n))
                  (<= 0 n)))
  :hints (("goal" :in-theory (enable expt))))

;for some reason, this is still needed for the rule below
(defthm integerp-*-constant-means-1
  (implies (and (rationalp x)
                (integerp (* 1/2 x)))
           (integerp x)))

;; (defthm integerp-*-constant-means-2
;;   (implies (and (integerp (* 1/4 x))
;;                 (rationalp x))
;;            (integerp x))
;;   :rule-classes :forward-chaining)


(defthm integerp-*-1/2-expt
  (iff (integerp (* 1/2 (expt 2 n)))
       (not (zp n)))
  :hints (("goal" :in-theory (e/d (expt exponents-add)))))

(defthm integerp-*-1/4-expt
  (implies (and (integerp n)
                (<= 0 n))
           (equal (integerp (* 1/4 (expt 2 n)))
                  (and (not (zp n)) (not (equal n 1)))))
  :hints (("goal" :in-theory (enable expt))))

(defthm integer-length-expt
  (equal (integer-length (expt 2 n))
         (if (integerp n)
             (if (<= 0 n)
                 (1+ n)
               0)
           1))
  :hints (("goal" :in-theory (enable expt integer-length))))

(defthm <-integer-length-1
  (implies (integerp x)
           (equal (< (integer-length x) 1)
                  (or (equal x -1) (equal x 0))))
  :hints (("goal" :in-theory (enable integer-length))))

;; from guard-lemmas.lisp
(defthm expt-less-1
  (implies (and (integerp s)
                (integerp n)
                (<= s 0)
                (<= 0 n))
           (<= (expt n s) 1))
  :hints (("goal" :in-theory (enable expt))))

(defthm <-1-expt
  (equal (< 1 (expt 2 n))
         (and (integerp n)
              (< 0 n)))
  :hints (("Goal" :in-theory (enable expt))))

(defthm integerp-*-1/2*x*expt-bridge
  (implies (and (integerp a)
                (integerp (* b c)))
           (integerp (* b a c))))

(defthm integerp-*-1/2*x*expt-bridge2
  (implies (and (integerp a)
                (integerp b)
                (integerp (* c d)))
           (integerp (* c a d b))))

(defthm floor-1-helper
  (implies (and (rationalp x)
                (rationalp y)
                (<= x y))
           (<= (floor x 1) y)))


(encapsulate
 ()
 (local (include-book "rtl/rel4/arithmetic/floor" :dir :system))
 (local (include-book "rtl/rel4/arithmetic/fl" :dir :system))

    ;add to rtl?
    ;bzo loops
 (defthmd floor-normalizes-to-have-j-be-1
   (implies (syntaxp (not (equal j ''1))) 
            (equal (floor i j)
                   (floor (/ i j) 1))))

 (DEFTHM FLOOR-OF-INTEGER-BY-1
   (IMPLIES (INTEGERP I)
            (EQUAL (FLOOR I 1) I)))

 
 )


(defthm expt-when-i-is-not-an-integerp
  (implies (not (integerp i))
           (equal (expt r i)
                  1))
  :hints (("Goal" :in-theory (enable expt))))

(defthm integerp-floor
  (integerp (floor x y)))

;bzo move
(defthm mod-by-2-less-than-1
  (implies (integerp x)
           (equal (< (mod x 2) 1)
                  (equal 0 (mod x 2)))))

(defthm collect-constants-+-lemma
  (implies (syntaxp (and (quotep k1) (quotep k2)))
           (equal (< (+ k1 a) (+ k2 b))
                  (< (+ (- k1 k2) a) b))))

(defthm arithhack
  (equal (+ (- x) (* 2 x) y)
         (+ x y)))

(local (include-book "rtl/rel4/arithmetic/denominator" :dir :system))

(defthm denominator-of-unary-/
 (implies (and (integerp x) ;generalize?
               ;(< 0 x)
;               (not (equal 0 x))
               )
          (equal (denominator (/ x))
                 (if (equal x 0)
                     1
                   (abs x)
                   )))
 :hints (("Goal" :use ((:instance acl2::Rational-implies2 (acl2::x (/ x))) (:instance acl2::numerator-/x (acl2::x x)))
          :in-theory (e/d (denominator) (acl2::Rational-implies2 ACL2::NUMERATOR-/X ACL2::*-R-DENOMINATOR-R)))))

(defthm mod-when-x-is-not-an-acl2-numberp
  (implies (not (acl2-numberp x))
           (equal (mod x y)
                  0))
  :hints (("Goal" :in-theory (enable mod floor))))

(defthm mod-when-y-is-not-an-acl2-numberp
  (implies (not (acl2-numberp y))
           (equal (mod x y)
                  (fix x)))
  :hints (("Goal" :in-theory (enable mod floor))))

;generalize?

(defthm odd-number-mod-1
  (IMPLIES (AND (INTEGERP I)
                (NOT (INTEGERP (* 1/2 I)))
                )
           (EQUAL (MOD (* 1/2 I) 1)
                  1/2))
  :hints (("Goal" :in-theory (e/d (evenp mod) (;ACL2::EVENP-COLLAPSE
                                               )))))

;restrict to when y is a constant?
(defthmd mod-stretch-base
  (IMPLIES (AND (INTEGERP (* 1/2 (FLOOR x y)))
                (INTEGERP y)
                (INTEGERP x) ;(rationalp x)
                )
           (EQUAL (MOD x y)
                  (if (equal 0 y)
                      x
                    (if (equal 0 x)
                        0
                      (MOD x (* 2 y))))))
  :hints (("Goal" :in-theory (enable mod-cancel))))

;can we generalize this?
(defthm mod-of-prod-of-mod
  (implies (and (integerp k)
                (integerp x)
                (integerp y)
                )
           (equal (mod (* k (mod x y)) y)
                  (mod (* k x) y)))
  :hints (("Goal" :in-theory (disable mod-cancel))))


;; (defthm floor-of-shift-right-2agen
;;   (implies (and (and (rationalp x)
;;                      (integerp n)
;;                      (<= 0 n))
;;                 (integerp (* (/ n) (floor x 1))))
;;            (equal (floor (* (/ n) x) 1)
;;                   (/ (floor x 1) n)))
;; )


;like  FL-EQUAL-REWRITE in RTL but about floor and a hyp is moved to conclusion
;arithmetic-3 doesn't have this
(defthm floor-equal-rewrite
  (implies (rationalp x)
           (equal (equal (floor x 1) n)
                  (and (<= n x)
                       (integerp n)
                       (< x (+ 1 n))))))

;generalize the 2's and 1/2's?
(defthm floor-of-shift-right-2
  (implies (rationalp x)
           (equal (floor (* 1/2 x) 1)
                  (if (integerp (* 1/2 (floor x 1)))
                      (* 1/2 (floor x 1))
                    (+ -1/2 (* 1/2 (floor x 1))))))
  :hints (("Goal" :in-theory (enable))))

(defthm floor-by-0
  (equal (FLOOR i 0)
         0
         )
  :hints (("Goal" :in-theory (enable floor))))

(defthm floor-by-twice-hack
 (implies (and (rationalp x)
               (rationalp y))
          (equal (FLOOR X (* 2 Y))
                 (FLOOR (* 1/2 X) Y)))
 :hints (("Goal" :cases ((equal 0 y)))))

;this may loop too
;trying to prove this without opening mod might yield some nice lemmas?
(defthmd mod-stretch-base-2
  (implies (and (not (integerp (* 1/2 (floor x y))))
                (integerp y)
                (integerp x) ;(rationalp a)
                )
           (equal (mod x y)
                  (- (mod x (* 2 y))
                     y)))
  :otf-flg t
  :hints (("Goal" :in-theory (e/d (evenp mod
                                         FLOOR-NORMALIZES-TO-HAVE-J-BE-1) 
                                  (;acl2::evenp-collapse 
                                   mod-cancel)))))

(DEFTHM INTEGERP-+-MINUS-*-1
  (IMPLIES (INTEGERP I) (INTEGERP (- I))))

(DEFTHM INTEGERP-+-MINUS-*-2
  (IMPLIES (AND (INTEGERP I) (INTEGERP J))
           (INTEGERP (+ I J))))

(DEFTHM INTEGERP-+-MINUS-*-3
  (IMPLIES (AND (INTEGERP I) (INTEGERP J))
           (INTEGERP (- I J))))

(DEFTHM INTEGERP-+-MINUS-*-4
  (IMPLIES (AND (INTEGERP I) (INTEGERP J))
           (INTEGERP (* I J))))
 
(in-theory (disable INTEGERP-+-MINUS-*)) ;bzo


(defthm ifix-integerp
  (implies (integerp x)
           (equal (ifix x) x)))


;bzo
;this seems like it could be expensive; do we need it?
(defthmd integer-=>-rational
  (implies (integerp x)
           (rationalp x)))

;is this fact built into acl2's type system? maybe that's why this isn't a t=p rule
(defthm denominator-is-positive
  (< 0 (denominator x))
  :rule-classes (:rewrite :linear))

;make t-p rules too?
(defthm positive-numerator
  (implies (rationalp v)
           (equal (< 0 (numerator v))
                  (< 0 v))))

(defthm negative-numerator
  (implies (rationalp v)
           (equal (< (numerator v) 0)
                  (< v 0))))

(defthm floor-when-i-is-not-an-acl2-numberp
  (implies (not (acl2-numberp i))
           (equal (floor i j)
                  0))
  :hints (("Goal" :in-theory (enable floor))))

(defthm floor-when-j-is-not-an-acl2-numberp
  (implies (not (acl2-numberp j))
           (equal (floor i j)
                  0))
  :hints (("Goal" :in-theory (enable floor))))

;bzo The move-negated-term rules cover just a few of the many cases that can arise.
;Come up with a general theory (a :meta rule?) to handle this?
;Does such a rule already exist?

(defthm move-negated-term-to-other-side-of-<-term-1-on-lhs
  (implies (syntaxp (not (quotep x))) ;without the not-quotep test, the rule matches things like: (< -1 x)
           (equal (< (- x) y)
                  (< 0 (+ x y)))))
  
(defthm move-negated-term-to-other-side-of-<-term-1-on-rhs
  (implies (syntaxp (not (quotep y))) ;without the not-quotep test, the rule matches things like: (< x -1) ?
           (equal (< x (- y))
                  (< (+ y x) 0))))

(defthm move-negated-term-to-other-side-of-<-term-2-on-lhs
  (equal (< (+ Y (- x)) z)
         (< Y (+ x z))))

(defthm move-negated-term-to-other-side-of-<-term-2-on-rhs
  (equal (< z (+ Y (- x)))
         (< (+ x z) Y)))

(defthm expt-plus-expt-special-case
  (implies (integerp n)
           (equal (+ (expt 2 (+ -1 n)) (expt 2 (+ -1 n)))
                  (expt 2 n)))
  :hints (("Goal" :in-theory (enable exponents-add-unrestricted))))


(defthm equal-negation-same-sign
  (implies (and (integerp x)
                (integerp y)
                (equal (<= 0 x)
                       (<= 0 y)))
           (equal (equal x (- y))
                  (and (equal x 0) (equal y 0)))))


(defthm integerp-prod-3
  (implies (and (integerp x)
                (integerp y)
                (integerp z))
           (integerp (* x y z))))


(defthm floor-when-j-is-0
  (equal (FLOOR i 0)
         0)
  :hints (("Goal" :in-theory (enable floor))))


;disable other one
(DEFTHM FLOOR-BOUNDS-better
  (IMPLIES (AND (RATIONALP X)
                (RATIONALP Y)
                ;(FORCE (NOT (EQUAL 0 Y)))
                )
           (AND (< (- (/ X Y) 1) (FLOOR X Y))
                (<= (FLOOR X Y) (/ X Y))))
  :RULE-CLASSES
  ((:LINEAR :TRIGGER-TERMS ((FLOOR X Y)))
   (:GENERALIZE))
:hints (("Goal" :use (:instance FLOOR-BOUNDS) :in-theory (disable FLOOR-BOUNDS))))

(in-theory (disable FLOOR-BOUNDS))


(defthm integer-length-of-floor-by-2
  (implies (integerp x)
           (equal (integer-length (floor x 2))
                  (if (and (not (equal 0 x)) (not (equal -1 x)))
                      (+ -1 (integer-length x))
                    0)))
  :otf-flg t
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable integer-length))))


(defthm integer-length-when-i-is-not-an-integerp
  (implies (not (integerp i))
           (equal (integer-length i)
                  0)))

(defthm truncate-when-j-is-zero
  (equal (truncate i 0)
         0)
  :hints (("Goal" :in-theory (enable truncate))))

;bzo ACL2::TRUNCATE-TYPE should be improved (for instance, it shouldn't require j not to be 0 so often).
(defthm truncate-nonnegative-type
  (IMPLIES (AND (INTEGERP I)
                (<= 0 I)
                (<= 0 J)
                (INTEGERP J))
           (<= 0 (TRUNCATE I J)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :use (:instance ACL2::TRUNCATE-TYPE (acl2::x i) (acl2::y j))
           :in-theory (disable ACL2::TRUNCATE-TYPE))))

(defthm truncate-nonpositive-type
  (IMPLIES (AND (INTEGERP I)
                (<= 0 I)
                (<= J 0) ;note this
                (INTEGERP J))
           (<= (TRUNCATE I J) 0))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :use (:instance ACL2::TRUNCATE-TYPE (acl2::x i) (acl2::y j))
           :in-theory (disable ACL2::TRUNCATE-TYPE))))

(defthm truncate-nonpositive-type2
  (IMPLIES (AND (INTEGERP I)
                (<= I 0) ;note this
                (<= 0 J) ;bzo
                (INTEGERP J))
           (<= (TRUNCATE I J) 0))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :use (:instance ACL2::TRUNCATE-TYPE (acl2::x i) (acl2::y j))
           :in-theory (disable ACL2::TRUNCATE-TYPE))))

(defthm truncate-nonnegative-type-2
  (IMPLIES (AND (INTEGERP I)
                (<= I 0) ;note this
                (<= J 0) ;note this
                (INTEGERP J))
           (<= 0 (TRUNCATE I J)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :use (:instance ACL2::TRUNCATE-TYPE (acl2::x i) (acl2::y j))
           :in-theory (disable ACL2::TRUNCATE-TYPE))))

(encapsulate
 ()
 (local
  (defthm truncate-upper-bound
    (implies (and (<= 0 i)
                  (integerp i)
                  (< 0 j)
                  (integerp j))
             (<= (truncate i j) i))
    :rule-classes (:rewrite :linear)
    :hints (("Goal" :nonlinearp t
             :use (:instance acl2::truncate-bounds (acl2::x i) (acl2::y j))
             :in-theory (disable acl2::truncate-bounds)))))

 (defthm truncate-upper-bound-better
   (implies (and (<= 0 i)
                 (integerp i)
                 (integerp j))
            (<= (truncate i j) i))
   :rule-classes (:rewrite :linear)
   :hints (("Goal" :nonlinearp t
            :use (:instance truncate-upper-bound)
            :in-theory (disable truncate-upper-bound)))))

(encapsulate
 ()
 (local
  (defthm truncate-lower-bound
    (implies (and (<= i 0)
                  (integerp i)
                  (< 0 j)
                  (integerp j))
             (<= i (truncate i j)))
    :rule-classes (:rewrite :linear)
    :hints (("Goal" :nonlinearp t
             :use (:instance acl2::truncate-bounds (acl2::x i) (acl2::y j))
             :in-theory (disable acl2::truncate-bounds)))))

 (defthm truncate-lower-bound-better
   (implies (and (<= i 0) ;note this
                 (integerp i)
                 (integerp j))
            (<= i (truncate i j)))
   :rule-classes (:rewrite :linear)
   :hints (("Goal" :nonlinearp t
            :use (:instance truncate-lower-bound)
            :in-theory (disable truncate-lower-bound)))))

(encapsulate
 ()
 (local
  (defthm truncate-upper-bound
    (implies (and (<= i 0)
                  (integerp i)
                  (< j 0)
                  (integerp j))
             (<= (truncate i j) (- i)))
    :rule-classes (:rewrite :linear)
    :hints (("Goal" :nonlinearp t
             :use (:instance acl2::truncate-bounds (acl2::x i) (acl2::y j))
             :in-theory (disable acl2::truncate-bounds)))))

 (defthm truncate-upper-bound-better2
   (implies (and (<= i 0)
                 (integerp i)
                 (integerp j))
            (<= (truncate i j) (- i)))
   :rule-classes (:rewrite :linear)
   :hints (("Goal" :nonlinearp t
            :do-not '(generalize eliminate-destructors)
            :use (:instance truncate-upper-bound)
            :in-theory (disable truncate-upper-bound)))))

(encapsulate
 ()
 (local
  (defthm truncate-lower-bound
    (implies (and (<= 0 i)
                  (integerp i)
                  (< j 0)
                  (integerp j))
             (<= (- i) (truncate i j)))
    :rule-classes (:rewrite :linear)
    :hints (("Goal" :nonlinearp t
             :use (:instance acl2::truncate-bounds (acl2::x i) (acl2::y j))
             :in-theory (disable acl2::truncate-bounds)))))

 (defthm truncate-lower-bound-better2
   (implies (and (<= 0 i) ;note this
                 (integerp i)
                 (integerp j))
            (<= (- i) (truncate i j)))
   :rule-classes (:rewrite :linear)
   :hints (("Goal" :nonlinearp t
            :use (:instance truncate-lower-bound)
            :in-theory (disable truncate-lower-bound)))))

;loops with expt-minus
;add theory-inv
(defthmd unary-/-of-expt
  (equal (/ (EXPT 2 M))
         (expt 2 (- m))))

;loops!
;add theory-inv
(defthmd expt-gather
 (implies (and (integerp m)
               (integerp n))
          (equal (* (EXPT 2 m) (EXPT 2 n))
                 (expt 2 (+ m n))))
 :hints (("Goal" :in-theory (enable EXPONENTS-ADD-UNRESTRICTED))))


(defthm expt-less-than-1-hack
  (implies (and (< n 0)
                (integerp n))
           (< (expt 2 n) 1)
           )
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable expt))))

(defthm expt-2-equal-1-rewrite
  (equal (equal (expt 2 n) 1)
         (or (not (integerp n))
             (= n 0)))
  :hints (("Goal" :use (:instance expt-less-than-1-hack)
           :in-theory (disable expt-less-than-1-hack))))

(DEFTHM FLOOR-BOUNDS-BETTER-1-alt
  (IMPLIES (AND (< 0 y)
                (RATIONALP X)
                (RATIONALP Y)
                )
           (<= (* y (FLOOR X Y)) X))
  :RULE-CLASSES
  (:rewrite (:LINEAR :TRIGGER-TERMS ((FLOOR X Y))))
  :HINTS
  (("Goal" :USE (:INSTANCE FLOOR-BOUNDS)
    :IN-THEORY (DISABLE FLOOR-BOUNDS))))

(DEFTHM FLOOR-BOUNDS-BETTER-2-alt
  (IMPLIES (AND (< 0 y)
                (RATIONALP X)
                (RATIONALP Y)
                )
           (< X (+ y (* y (FLOOR X Y)))))
  :RULE-CLASSES
  (:rewrite (:LINEAR :TRIGGER-TERMS ((FLOOR X Y))))
  :HINTS
  (("Goal" :USE (:INSTANCE FLOOR-BOUNDS)
    :IN-THEORY (DISABLE FLOOR-BOUNDS))))

(defthm integerp-of-quotient-of-expts
  (implies (and (integerp n1)
                (integerp n2))
           (equal (integerp (* (expt 2 n1) (/ (expt 2 n2))))
                  (<= n2 n1)))
  :hints (("Goal" :use (:instance acl2::integerp-expt (n (- n1 n2)))
           :in-theory (disable acl2::integerp-expt))))

(defthm integerp-prod-of-3-first-two
  (implies (and (integerp (* a b)) 
                (integerp c))
           (integerp (* a b c)))
  :hints (("Goal" :in-theory (disable acl2::integerp-+-minus-*-4)
           :use (:instance acl2::integerp-+-minus-*-4 (acl2::i (* a b)) (acl2::j c)))))


;drop?
(defthm expt-hack-1
  (implies (integerp n)
           (equal (+ (EXPT 2 (+ -1 N)) (EXPT 2 (+ -1 N)))
                  (expt 2 n)))
  :hints (("Goal" :in-theory (enable EXPONENTS-ADD-UNRESTRICTED))))


(defthm arith-move-negated-term
  (implies (and (acl2-numberp x)
                (acl2-numberp z))
           (equal (EQUAL (+ x (- y)) z)
                  (equal x (+ y z)))))

(defthm mod-same
  (equal (mod x x)
         0)
  :hints (("Goal" :in-theory (enable acl2::mod-cancel))))

(defthm combine-constants-in-equal-of-times
  (implies (and (syntaxp (and (quotep k) (quotep j)))
                (acl2-numberp k)
                (acl2-numberp x)
                (acl2-numberp j)
                )
           (equal (EQUAL (* k x) j)
                  (if (equal 0 k)
                      (equal 0 j)
                    (equal x (/ j k))))))

(DEFTHM my-EQUAL-/
  (IMPLIES (AND (syntaxp (not (quotep x))) ;otherwise can loop with ACL2::COMBINE-CONSTANTS-IN-EQUAL-OF-TIMES
                (FC (ACL2-NUMBERP X))
                (FC (NOT (EQUAL 0 X))))
           (EQUAL (EQUAL (/ X) Y)
                  (EQUAL 1 (* X Y))))
  :HINTS (("Goal" :by EQUAL-/)))

(in-theory (disable EQUAL-/))


;for example, rewrites (<= 2 n) to t, when we know (<= 5 n)
(defthm remove-redundant-<=-hyps
  (implies (and (syntaxp (quotep small))
                (<= large N) ;large is a free variable - will this match?
                (syntaxp (quotep large))
                (<= small large)
                )
           (equal (< n small)
                  nil)))

;for example, rewrites (< 2 n) to t, when we know (< 5 n)
(defthm remove-redundant-less-thans
  (implies (and (syntaxp (quotep small))
                (< large N) ;large is a fre variable
                (syntaxp (quotep large))
                (<= small large)
                )
           (equal (< small n)
                  t)))

;trying disabled
(defthmd floor-*-1/2-expt-2
  (implies (and (integerp n)
                (< 1 n))
           (equal (floor (* 1/2 (expt 2 n)) 2)
                  (* 1/4 (expt 2 n))))
  :hints (("goal" :in-theory (enable expt floor))))
