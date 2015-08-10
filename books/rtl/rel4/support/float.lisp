;;;***************************************************************
;;;An ACL2 Library of Floating Point Arithmetic

;;;David M. Russinoff
;;;Advanced Micro Devices, Inc.
;;;February, 1998
;;;***************************************************************

;todo: disable expt in this file (and everywhere)
;disable abs, sgn

;move some of this stuff to books in arithmetic/

(in-package "ACL2")

(local (include-book "../arithmetic/top"))
(include-book "../arithmetic/negative-syntaxp")
(include-book "../arithmetic/basic") ;BOZO! make this local
(include-book "../arithmetic/power2p")
(local (include-book "../arithmetic/fl"))
(local (include-book "../arithmetic/cg"))

(local (in-theory (enable expt-minus)))

(defund fl (x)
  (declare (xargs :guard (real/rationalp x)))
  (floor x 1))

(defund cg (x)
  (declare (xargs :guard (real/rationalp x)))
  (- (fl (- x))))

(defun expo-measure (x)
;  (declare (xargs :guard (and (real/rationalp x) (not (equal x 0)))))
  (cond ((not (rationalp x)) 0)
	((< x 0) '(2 . 0))
	((< x 1) (cons 1 (fl (/ x))))
	(t (fl x))))

(defund expo (x)
  (declare (xargs :guard t
                  :measure (expo-measure x)))
  (cond ((or (not (rationalp x)) (equal x 0)) 0)
	((< x 0) (expo (- x)))
	((< x 1) (1- (expo (* 2 x))))
	((< x 2) 0)
	(t (1+ (expo (/ x 2))))))

;could redefine to divide by the power of 2 (instead of making it a negative power of 2)...
(defund sig (x)
  (declare (xargs :guard t))
  (if (rationalp x)
      (if (< x 0)
          (- (* x (expt 2 (- (expo x)))))
        (* x (expt 2 (- (expo x)))))
    0))

;make defund?
(defun sgn (x)
  (declare (xargs :guard t))
  (if (or (not (rationalp x)) (equal x 0))
      0
    (if (< x 0)
        -1
      1)))

;fp rep

(defthm fp-rep
  (implies (rationalp x)
           (equal x (* (sgn x) (sig x) (expt 2 (expo x)))))
  :hints (("Goal" :in-theory (enable sig)))
  :rule-classes ())

(defthm fp-abs
  (implies (rationalp x)
           (equal (abs x) (* (sig x) (expt 2 (expo x)))))
  :hints (("Goal" :use fp-rep))
  :rule-classes ())




;expo


(defthm expo-lower-bound
  (implies (and (rationalp x)
                (not (equal x 0)))
           (<= (expt 2 (expo x)) (abs x)))
  :rule-classes :linear)

(defthm expo-lower-pos
  (implies (and (< 0 x)
                (rationalp x)
                )
           (<= (expt 2 (expo x)) x))
  :rule-classes :linear)

(defthm expo-of-not-rationalp
  (implies (not (rationalp x))
           (equal (expo x) 0)))

;make a vesion whose max term is consistent with split exponents?
(defthm expo-upper-bound
  (implies (rationalp x)
           (< (abs x) (expt 2 (1+ (expo x)))))
  :rule-classes :linear
)

(defthm expo-upper-pos
  (implies (rationalp x)
           (< x (expt 2 (1+ (expo x)))))
  :rule-classes :linear)

;be careful: if you enable expo, the x<0 case of expo can loop with expo-minus
;BOZO add theory-invariant
(defthm expo-minus
  (equal (expo (* -1 x))
         (expo x)))

(local
 (defthm expo-unique-2
   (implies (and (rationalp x)
                 (not (equal x 0))
                 (integerp n)
                 (> n (expo x)))
            (> (expt 2 n) (abs x)))
   :rule-classes ()
   :hints (("Goal" :in-theory (disable abs)
            :use ( ;(:instance expo-upper-bound)
                  (:instance expt-weak-monotone (n (1+ (expo x))) (m n)))))))

(local
 (defthm expo-unique-1
   (implies (and (rationalp x)
                 (not (equal x 0))
                 (integerp n)
                 (< n (expo x)))
            (<= (expt 2 (1+ n)) (abs x)))
   :rule-classes ()
   :hints (("Goal" :in-theory (disable abs)
            :use ((:instance expt-weak-monotone (n (1+ n)) (m (expo x))))))))



(defthm expo-unique
  (implies (and (<= (expt 2 n) (abs x))
                (< (abs x) (expt 2 (1+ n)))
                (rationalp x)
                (integerp n)
                )
           (equal n (expo x)))
  :hints (("Goal" :in-theory (disable abs)
           :use ((:instance expo-unique-1)
                 (:instance expo-unique-2))))
  :rule-classes ())


(defthmd expo-monotone
  (implies (and (<= (abs x) (abs y))
                (case-split (rationalp x))
                (case-split (not (equal x 0)))
                (case-split (rationalp y))
                )
           (<= (expo x) (expo y)))
  :rule-classes :linear
  :hints (("Goal"
           :use (;(:instance expo-lower-bound)
                 (:instance expo-unique-2 (n (expo x)) (x y))))))


(defthm expo-2**n
  (implies (integerp n)
           (equal (expo (expt 2 n))
                  n))
  :hints (("Goal" :use ((:instance expo-unique (x (expt 2 n)))
			(:instance expt-strong-monotone (m (1+ n)))))))


;sig

;BOZO looped with sig-minus??
(defthmd sig-minus
  (equal (sig (* -1 x))
         (sig x))
  :hints (("Goal" :in-theory (enable sig)
           :cases ((rationalp x)))))

(defthm sig-minus-gen
  (implies (syntaxp (negative-syntaxp x))
           (equal (sig x)
                  (sig (* -1 x))))
  :hints (("Goal" :in-theory (enable sig-minus))))

(defthm sig-lower-bound
  (implies (and (rationalp x)
                (not (equal x 0)))
           (<= 1 (sig x)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory  (disable abs)
           :use ((:instance fp-abs)))))

(defthm sig-of-not-rationalp
  (implies (not (rationalp x))
           (equal (sig x)
                  0))
  :hints (("Goal" :in-theory (enable sig))))

(defthm sig-rationalp-type-prescription
  (rationalp (sig x))
  :rule-classes (:type-prescription))

(defthm sig-positive-type-prescription
  (implies (and (case-split (rationalp x))
                (case-split (not (equal x 0))))
           (< 0 (sig x)))
  :hints (("Goal" :in-theory (enable sig)))
  :rule-classes (:type-prescription))

(defthm sig-non-negative-type-prescription
  (<= 0 (sig x))
  :rule-classes (:type-prescription))

;rephrase
(defthm x-0-iff-sig-x-0
  (implies (rationalp x)
           (equal (equal (sig x) 0)
                  (equal x 0))))

;would like to reduce the number of hints here...
(defthm sig-upper-bound
  (< (sig x) 2)
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :use (:instance expo-upper-bound)
           :in-theory (e/d (sig expt-split) (expo-bound-eric)))))






;sgn

;Do we plan to enable sgn in our proofs?

(defthm sgn-minus
  (equal (sgn (* -1 x))
         (* -1 (sgn x)))
  :hints (("Goal" :cases ((rationalp x)))))

(defthm sgn+1
  (implies (and (< 0 x)
                (rationalp x)
                )
           (equal (sgn x)
                  1))
  :rule-classes ())

(defthm sgn-1
  (implies (and (< x 0)
                (rationalp x))
           (equal (sgn x)
                  -1))
  :rule-classes ())

;gen to multiplying by anything positive?
(defthm sgn-shift
  (equal (sgn (* x (expt 2 k)))
         (sgn x)))

(defthm sgn-sig
  (implies (and (case-split (rationalp x))
                (case-split (not (equal x 0))))
           (equal (sgn (sig x))
                  1))
  :hints (("Goal" :in-theory (enable sgn sig))))

(defthm sgn-prod
  (implies (and (case-split (rationalp x))
                (case-split (rationalp y))
                )
           (equal (sgn (* x y))
                  (* (sgn x) (sgn y))))
  :hints (("Goal" :in-theory (enable sgn))))

(defthm sgn-sgn
  (equal (sgn (sgn x))
         (sgn x))
  :hints (("Goal" :in-theory (enable sgn))))

(defthm sgn-expt
  (equal (sgn (expt 2 x))
         1)
  :hints (("Goal" :in-theory (enable sgn))))

(defthm sgn-equal-0
  (equal (equal (sgn x) 0)
         (or (equal x 0)
             (not (rationalp x))))
  :hints (("goal" :in-theory (enable sgn))))

(defthm sig-equal-0
  (equal (equal (sig x) 0)
         (or (equal x 0)
             (not (rationalp x))))
  :hints (("goal" :in-theory (enable sig))))

(defthm sig-*-sgn
  (implies (and (case-split (rationalp x))
                (case-split (not (equal x 0)))
                )
           (equal (sig (* (sgn x) y))
                  (sig y)))
  :hints (("Goal" :in-theory (enable sig sgn))))

(defthm sig-of-non-rational
  (implies (not (rationalp x))
           (equal (sig x)
                  0))
  :hints (("Goal" :in-theory (enable sig))))

(defthm sgn-of-non-rational
  (implies (not (rationalp x))
           (equal (sgn x)
                  0))
  :hints (("Goal" :in-theory (enable sgn))))

(defthm expo-*-sgn
  (implies (and (case-split (rationalp x))
                (case-split (not (equal x 0)))
                )
           (equal (expo (* (sgn x) y))
                  (expo y)))
      :hints (("goal" :in-theory (enable sgn))))

(defthm fp-unique-1
    (implies (and (rationalp m)
		  (integerp e)
		  (<= 1 m)
		  (< 0 e))
	     (<= 2 (* m (expt 2 e))))
    :hints (("Goal" :in-theory (enable expt))) ;yuck
             :rule-classes ())

(defthm fp-unique-2
  (implies (and (rationalp m)
                (integerp e)
                (< m 2)
                (< e 0))
           (< (* m (expt 2 e)) 1))
  :hints (("Goal" :in-theory (enable expt))) ;yuck
  :rule-classes ())

(defthm fp-unique-3
    (implies (and (rationalp m)
		  (integerp e)
		  (<= 1 m)
		  (< m 2)
		  (<= 1 (* m (expt 2 e)))
		  (< (* m (expt 2 e)) 2))
	     (equal e 0))
  :rule-classes ()
  :hints (("Goal" :use ((:instance fp-unique-1)
			(:instance fp-unique-2)))))



(defthm =*
  (implies (and (rationalp x1)
                (rationalp x2)
                (rationalp y)
                (not (equal y 0))
                (equal x1 x2))
           (equal (* x1 y) (* x2 y)))
  :rule-classes ())

(defthm fp-unique-4
    (implies (and (rationalp m1)
		  (integerp e1)
		  (rationalp m2)
		  (integerp e2)
		  (= (* m1 (expt 2 e1)) (* m2 (expt 2 e2))))
	     (= (* m1 (expt 2 (- e1 e2))) m2))
  :rule-classes ()
  :hints (("Goal" :in-theory (e/d (expt-split
                                   ) ())
           :use (;(:instance expt- (a e1) (b e2))
                 (:instance =* (x1 (* m1 (expt 2 e1))) (x2 (* m2 (expt 2 e2))) (y (expt 2 (- e2))))))))

(defthm fp-unique-5
    (implies (and (rationalp m1)
		  (integerp e1)
		  (rationalp m2)
		  (integerp e2)
		  (<= 1 m1)
		  (< m1 2)
		  (<= 1 m2)
		  (< m2 2)
		  (= (* m1 (expt 2 e1)) (* m2 (expt 2 e2))))
	     (= e1 e2))
  :rule-classes ()
  :hints (("Goal" :use ((:instance fp-unique-3 (m m1) (e (- e1 e2)))
			(:instance fp-unique-4)))))

(defthm *cancell
    (implies (and (rationalp x)
		  (rationalp y)
		  (rationalp z)
		  (not (= z 0))
		  (= (* x z) (* y z)))
	     (= x y))
  :rule-classes ()
  :hints (("Goal" :use ((:instance =* (x1 (* x z)) (x2 (* y z)) (y (/ z)))))))

(defthm fp-unique-6
    (implies (and (rationalp m1)
		  (integerp e1)
		  (rationalp m2)
		  (integerp e2)
		  (<= 1 m1)
		  (< m1 2)
		  (<= 1 m2)
		  (< m2 2)
		  (= (* m1 (expt 2 e1)) (* m2 (expt 2 e2))))
	     (= m1 m2))
  :rule-classes ()
  :hints (("Goal" :use ((:instance fp-unique-5)
			(:instance cancel-equal-* (r m1) (s m2) (a (expt 2 e1)))))))

(defthm fp-rep-unique
    (implies (and (rationalp x)
		  (not (= x 0))
		  (rationalp m)
		  (<= 1 m)
		  (< m 2)
		  (integerp e)
		  (= (abs x) (* m (expt 2 e))))
	     (and (= m (sig x))
		  (= e (expo x))))
  :rule-classes ()
  :hints (("Goal"
		  :use ((:instance fp-rep)
			(:instance sig-lower-bound)
			(:instance sig-upper-bound)
			(:instance fp-unique-5 (m1 m) (m2 (sig x)) (e1 e) (e2 (expo x)))
			(:instance fp-unique-6 (m1 m) (m2 (sig x)) (e1 e) (e2 (expo x)))))))

;drop this?
(defthm sig-expo-shift
  (implies (and (rationalp x)
                (not (= x 0))
                (integerp n))
           (and (= (sig (* (expt 2 n) x)) (sig x))
                (= (expo (* (expt 2 n) x)) (+ n (expo x)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable sig)
           :use ((:instance sgn+1)
                 (:instance fp-rep)

                 (:instance sig-lower-bound)
                 (:instance sig-upper-bound)
                 (:instance fp-rep-unique (x (* (expt 2 n) x)) (m (sig x)) (e (+ n (expo x))))))))


(defthm expo-shift
  (implies (and (rationalp x)
                (not (equal x 0))
                (integerp n))
           (equal (expo (* (expt 2 n) x))
                  (+ n (expo x))))
  :hints (("Goal" :use (sig-expo-shift))))

(defthm expo-shift-2
  (implies (and (case-split (rationalp x))
                (case-split (not (equal x 0)))
                (case-split (integerp n)))
           (equal (expo (* x (expt 2 n)))
                  (+ n (expo x))))
  :hints (("Goal" :in-theory (disable expo-shift)
           :use expo-shift)))

;(in-theory (disable expo-shift-2)) ; can cause loops if enabled?

(defthm sig-shift
  (equal (sig (* (expt 2 n) x))
         (sig x))
  :hints (("Goal" :in-theory (set-difference-theories (enable sig expt)
                                                      '( expo-shift-2))
           :use (sig-expo-shift))))

(defthm sig-shift-2
  (equal (sig (* x (expt 2 n)))
         (sig x))
  :hints (("Goal" :in-theory (disable sig-shift)
           :use (sig-shift))))

(defthm sig-shift-by-constant-power-of-2
  (implies (and (syntaxp (and (quotep k)))
                (power2p k)
                )
           (equal (sig (* k x))
                  (sig x)))
  :hints (("Goal" :in-theory (enable power2p-rewrite))))

(defthm sig-shift-by-power-of-2
  (implies (and (syntaxp (power2-syntaxp k))
                (force (power2p k))
                )
           (equal (sig (* k x))
                  (sig x)))
  :hints (("Goal" :in-theory (enable power2p-rewrite))))

(defthm sig-shift-by-power-of-2-2
  (implies (and (syntaxp (power2-syntaxp k))
                (force (power2p k))
                )
           (equal (sig (* x k))
                  (sig x)))
  :hints (("Goal" :in-theory (enable power2p-rewrite))))



;(in-theory (disable sig-shift-2)) ;can cause loops if enabled?


(defthm sig-sig
  (equal (sig (sig x))
         (sig x))
  :hints (("Goal" :in-theory (enable sig))))


#|
(defthm expt-non-neg
    (implies (integerp n)
	     (not (< (expt 2 n) 0))))
|#

;move?
(defthm expo-prod-lower
  (implies (and (rationalp x)
                (not (= x 0))
                (rationalp y)
                (not (= y 0)))
           (<= (+ (expo x) (expo y)) (expo (* x y))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable a15)
           :use ((:instance *-doubly-monotonic
                            (x (expt 2 (expo x)))
                            (y (abs x))
                            (a (expt 2 (expo y)))
                            (b (abs y)))
                 (:instance expo-lower-bound)
                 (:instance expo-lower-bound (x y))
                 (:instance expo-unique-2 (x (* x y)) (n (+ (expo x) (expo y))))))))

(defthm *-doubly-strongly-monotonic
  (implies (and (rationalp x)
                (rationalp y)
                (rationalp a)
                (rationalp b)
                (< 0 x)
                (< 0 y)
                (< 0 a)
                (< 0 b)
                (< x y)
                (< a b))
           (< (* x a) (* y b)))
  :rule-classes ())

(defthm expo-prod-upper
    (implies (and (rationalp x)
		  (not (= x 0))
		  (rationalp y)
		  (not (= y 0)))
	     (>= (+ (expo x) (expo y) 1) (expo (* x y))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable a15)
		  :use ((:instance *-doubly-strongly-monotonic
				   (x (abs x))
				   (y (expt 2 (1+ (expo x))))
				   (a (abs y))
				   (b (expt 2 (1+ (expo y)))))
			(:instance expo-upper-bound)
			(:instance expo-upper-bound (x y))
			(:instance expo-unique-1 (x (* x y)) (n (+ (expo x) (expo y) 1)))))))



;exactp

(defund exactp (x n)
;  (declare (xargs :guard (and (real/rationalp x) (integerp n))))
  (integerp (* (sig x) (expt 2 (1- n)))))

(defthm exactp-0
  (exactp 0 n)
  :hints (("Goal" :in-theory (enable exactp))))

;drop -x from name
(defthm exactp-sig-x
  (equal (exactp (sig x) n)
         (exactp x n))
  :hints (("Goal" :in-theory (enable exactp))))

(defthmd exactp-minus
  (equal (exactp (* -1 x) n)
         (exactp x n))
  :hints (("Goal" :in-theory (enable exactp))))

(defthm exactp-minus-gen
  (implies (syntaxp (negative-syntaxp x))
           (equal (exactp x n)
                  (exactp (* -1 x) n)))
  :hints (("Goal" :in-theory (enable exactp-minus))))

#| kill
;make negative-syntaxp version
;add? ;three summand version?
(defthm exactp-minus-dist
  (equal (exactp (+ (* -1 x) (* -1 y)) n)
         (exactp (+ x y) n))
  :hints (("Goal" :in-theory (disable exactp-minus)
          :use (:instance exactp-minus (x (* -1 (+ x y)))))))
|#


;similar to other hacks?
(defthmd between-0-and-1-means-not-integerp
  (implies (and (< 0 x)
                (< x 1))
           (not (integerp x))))

(defthm sig-prod-linear
  (implies (and (<= 0 y)
                (rationalp x)
                (rationalp y))
           (<= (* (sig x) y) (* 2 y)))
  :rule-classes (:linear)
  )

;rephrase?
(defthmd only-0-is-0-or-negative-exact
  (implies (and (<= n 0)
                (integerp n)
                (case-split (rationalp x))
                (case-split (not (= x 0))))
           (not (exactp x n)))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable exactp expt-split ;expt
                                      )
                              '( fl-equal-0 ;why was this needed?
                                    ))
           :use (:instance between-0-and-1-means-not-integerp (x (* (SIG X) (EXPT 2 (+ -1 N))))))))

#|
;gross?
;just enable sig?
(defthm exactp-lemma
  (implies (and (rationalp x)
                (integerp n))
           (equal (* (sig x) (expt 2 (1- n)))
                  (* (abs x) (expt 2 (- (1- n) (expo x))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable sig))))

|#




;not needed?
;bad name?
;reorder and call exactp-abs and make rewrite
;more rules to drop abs?
(defthm exact-neg
  (equal (exactp x n)
         (exactp (abs x) n))
  :hints (("Goal" :in-theory (enable exactp)))
  :rule-classes ())

;make this a definition rule?
(defthmd exactp2
  (implies (and (rationalp x)
                (integerp n))
           (equal (exactp x n)
                  (integerp (* x (expt 2 (- (1- n) (expo x)))))))
  :hints (("Goal" :in-theory (e/d (exactp sig expt-split) ()))))


#| kill
;could this be a rewrite rule?
(defthm exactp-shift
  (implies (and (rationalp x)
                (integerp m)
                (integerp n)
                (exactp x m))
           (exactp (* (expt 2 n) x) m))
  :rule-classes nil
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable exactp2)
                              '( sgn))
           :cases ((= x 0)))))
|#

;consider enabling?
;reorder product in lhs?
(defthmd exactp-shift
  (implies (and (rationalp x)
                (integerp m)
                (integerp n)
                )
           (equal (exactp (* (expt 2 n) x) m)
                  (exactp x m)))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable exactp2 a15)
                              '( sgn))
           :cases ((= x 0)))))

(defthmd exactp-shift-2
  (implies (and (rationalp x)
                (integerp m)
                (integerp n)
                )
           (equal (exactp (* x (expt 2 n)) m)
                  (exactp x m)))
  :hints (("Goal" :use  exactp-shift)))

(defthm exactp-shift-by-constant-power-of-2
  (implies (and (syntaxp (and (quotep k)))
                (power2p k)
                (rationalp x)
                (integerp n)
                )
           (equal (exactp (* k x) n)
                  (exactp x n)))
  :hints (("Goal" :in-theory (enable exactp-shift-2 power2p-rewrite))))

(defthm exactp-shift-by-power-of-2
  (implies (and (syntaxp (power2-syntaxp k))
                (force (power2p k))
                (rationalp x)
                (integerp n)
                )
           (equal (exactp (* k x) n)
                  (exactp x n)))
  :hints (("Goal" :in-theory (enable  exactp-shift-2 power2p-rewrite))))

(defthm exactp-shift-by-power-of-2-2
  (implies (and (syntaxp (power2-syntaxp k))
                (force (power2p k))
                (rationalp x)
                (integerp n)
                )
           (equal (exactp (* x k) n)
                  (exactp x n)))
  :hints (("Goal" :in-theory (enable  exactp-shift-2 power2p-rewrite))))



(defthm exactp-prod-1
    (implies (and (rationalp x)
		  (rationalp y)
		  (integerp n)
		  (integerp m))
	     (= (expt 2 (+ m n -1 (- (expo (* x y)))))
		(* (expt 2 (- (1- m) (expo x)))
		   (expt 2 (- (1- n) (expo y)))
		   (expt 2 (+ (expo x) (expo y) 1 (- (expo (* x y))))))))
  :rule-classes ())

(defthm exactp-prod-2
    (implies (and (rationalp x)
		  (not (= x 0))
		  (rationalp y)
		  (not (= y 0)))
	     (integerp (expt 2 (+ (expo x) (expo y) 1 (- (expo (* x y)))))))
  :rule-classes ()
  :hints (("Goal"
		  :use ((:instance expo-prod-upper)))))

(defthm integerp-x-y-z
    (implies (and (integerp x) (integerp y) (integerp z))
	     (integerp (* x y z)))
  :rule-classes ())

(defthm exactp-prod
    (implies (and (rationalp x)
		  (rationalp y)
		  (integerp m)
		  (integerp n)
		  (exactp x m)
		  (exactp y n))
	     (exactp (* x y) (+ m n)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable exactp2 expt-split)
		  :use ((:instance exactp-prod-1)
			(:instance exactp-prod-2)
			(:instance integerp-x-y-z
				   (x (* x (expt 2 (- (1- m) (expo x)))))
				   (y (* y (expt 2 (- (1- n) (expo y)))))
				   (z (expt 2 (+ (expo x) (expo y) 1 (- (expo (* x y)))))))))))

(defthm exactp-x2-1
    (implies (and (rationalp x)
		  (integerp n))
	     (= (* 2 (expt 2 n) (expt 2 n))
		(expt 2 (+ n n 1))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance expt-split (r 2) (i m) (j n))
			(:instance expt-split (r 2) (i (* 2 n)) (j 1))))))

(defthm exactp-x2-2
    (implies (and (rationalp x)
		  (rationalp y))
	     (= (* 2 (* x y) (* x y))
		(* (* x x) (* 2 y y))))
  :rule-classes ())

(defthm exactp-x2-3
    (implies (and (rationalp x)
		  (integerp n))
	     (= (* 2 (* x (expt 2 n)) (* x (expt 2 n)))
		(* (* x x) (expt 2 (+ n n 1)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance exactp-x2-1)
			(:instance exactp-x2-2 (y (expt 2 n)))))))

(defthm exactp-x2-4
    (implies (and (rationalp x)
		  (integerp n)
		  (integerp e))
	     (= (* 2 (* x (expt 2 (- (1- n) e))) (* x (expt 2 (- (1- n) e))))
		(* (* x x) (expt 2 (- (1- (* 2 n)) (* 2 e))))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance exactp-x2-3 (n (- (1- n) e)))))))

(defthm exactp-x2-5
    (implies (and (rationalp x)
		  (integerp n)
		  (integerp e)
		  (integerp e2))
	     (= (* 2 (* x (expt 2 (- (1- n) e))) (* x (expt 2 (- (1- n) e))))
		(* (* (* x x) (expt 2 (- (1- (* 2 n)) e2)))
		   (expt 2 (- e2 (* 2 e))))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance exactp-x2-4)
			(:instance expt-split (r 2) (i (- (1- (* 2 n)) e2)) (j (- e2 (* 2 e))))))))

(defthm integerp-x-y
    (implies (and (integerp x)
		  (integerp y))
	     (integerp (* x y)))
  :rule-classes ())

(defthm exactp-x2-6
    (implies (and (rationalp x)
		  (not (= x 0))
		  (integerp n)
		  (exactp (* x x) (* 2 n)))
	     (integerp (* 2 (* x (expt 2 (- (1- n) (expo x)))) (* x (expt 2 (- (1- n) (expo x)))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (e/d (expt-split exactp2 expt-with-product-exponent) ())
		  :use ((:instance expo-prod-lower (y x))
			(:instance integerp-x-y
				   (x (* (* x x) (expt 2 (- (1- (* 2 n)) (expo (* x x))))))
				   (y (expt 2 (- (expo (* x x)) (* 2 (expo x))))))
			(:instance exactp-x2-5 (e (expo x)) (e2 (expo (* x x))))))))

;what's the role of k here?
(defthm exactp-x2-not-zero
    (implies (and (rationalp x)
		  (not (= x 0))
		  (integerp k)
		  (exactp x k)
		  (integerp n)
		  (exactp (* x x) (* 2 n)))
	     (exactp x n))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable exactp2 expt-split)
		  :use ((:instance exactp-x2-6)
			(:instance x-2xx (k (- k n)) (x (* x (expt 2 (- (1- n) (expo x))))))))))

;what's the role of k here?
(defthm exactp-x2
    (implies (and (rationalp x)
		  (integerp k)
		  (exactp x k)
		  (integerp n)
		  (exactp (* x x) (* 2 n)))
	     (exactp x n))
  :rule-classes ()
  :hints (("Goal"
		  :use ((:instance exactp-x2-not-zero)))))

(defthmd exactp-<=
  (implies (and (exactp x m)
                (<= m n)
                (rationalp x)
                (integerp n)
                (integerp m)
                )
           (exactp x n))
  :hints (("Goal" :in-theory (enable exactp2 expt-split)
           :use (;(:instance expt-split (r 2) (i (- (1- m) (expo x))) (j (- n m)))
                 (:instance integerp-x-y
                            (x (* x (expt 2 (- (1- m) (expo x)))))
                            (y (expt 2 (- n m))))))))


(defthm exactp-<=-expo
  (implies (and (rationalp x)
                (integerp n)
                (integerp e)
                (<= e (expo x))
                (exactp x n))
           (integerp (* x (expt 2 (- (1- n) e)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable exactp2 expt-split)
           :use ( ;(:instance expt-split (r 2) (i (- (1- n) (expo x))) (j (- (expo x) e)))
                 (:instance integerp-x-y
                            (x (* x (expt 2 (- (1- n) (expo x)))))
                            (y (expt 2 (- (expo x) e))))))))

(defthm exactp->=-expo
    (implies (and (rationalp x)
		  (integerp n)
		  (integerp e)
		  (>= e (expo x))
		  (integerp (* x (expt 2 (- (1- n) e)))))
	     (exactp x n))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable exactp2 expt-split)
           :use ((:instance expt-split (r 2) (i (- (1- n) e)) (j (- e (expo x))))
			(:instance integerp-x-y
				   (x (* x (expt 2 (- (1- n) e))))
				   (y (expt 2 (- e (expo x)))))))))

(defthm exactp-diff
    (implies (and (rationalp x)
		  (rationalp y)
		  (integerp k)
		  (integerp n)
		  (> n 0)
		  (> n k)
		  (exactp x n)
		  (exactp y n)
		  (<= (+ k (expo (- x y))) (expo x))
		  (<= (+ k (expo (- x y))) (expo y)))
	     (exactp (- x y) (- n k)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable exactp2)
		  :use ((:instance exactp-<=-expo (e (+ k (expo (- x y)))))
			(:instance exactp-<=-expo (e (+ k (expo (- x y)))) (x y))))))

(defthm exactp-diff-0
    (implies (and (rationalp x)
		  (rationalp y)
		  (integerp n)
		  (> n 0)
		  (exactp x n)
		  (exactp y n)
		  (<= (expo (- x y)) (expo x))
		  (<= (expo (- x y)) (expo y)))
	     (exactp (- x y) n))
  :rule-classes ()
  :hints (("Goal"
		  :use ((:instance exactp-diff (k 0))))))

;bad name?
(defthm exactp-diff-cor
  (implies (and (rationalp x)
                (rationalp y)
                (integerp n)
                (> n 0)
                (exactp x n)
                (exactp y n)
                (<= (abs (- x y)) (abs x))
                (<= (abs (- x y)) (abs y)))
           (exactp (- x y) n))
  :rule-classes ()
  :hints (("Goal" :use ((:instance exactp-diff-0)
                        (:instance expo-monotone (x (- x y)) (y x))
                        (:instance expo-monotone (x (- x y)))))))

(defun fp+ (x n)
  (+ x (expt 2 (- (1+ (expo x)) n))))

(defthm fp+-positive
  (implies (<= 0 x)
           (< 0 (fp+ x n)))
  :rule-classes :type-prescription)

(defthm fp+1-1
    (implies (and (rationalp x)
		  (> x 0)
		  (rationalp y)
		  (> y x)
		  (integerp n)
		  (> n 0)
		  (exactp x n)
		  (exactp y n))
	     (integerp (* (- y x) (expt 2 (- (1- n) (expo x))))))
    :otf-flg t
  :rule-classes ()
  :hints (("Goal" :in-theory (e/d (exactp2 expt-split)())
           :use ((:instance expo-monotone)
                 (:instance exactp-<=-expo (x y) (e (expo x)))))))


(defthm fp+1-1
    (implies (and (rationalp x)
		  (> x 0)
		  (rationalp y)
		  (> y x)
		  (integerp n)
		  (> n 0)
		  (exactp x n)
		  (exactp y n))
	     (integerp (* (- y x) (expt 2 (- (1- n) (expo x))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable exactp2)
           :use ((:instance expo-monotone)
                 (:instance exactp-<=-expo (x y) (e (expo x)))))))

(defthm int>0
  (implies (and (integerp n)
                (> n 0))
           (>= n 1))
  :rule-classes ())

(defthm fp+1
    (implies (and (rationalp x)
		  (> x 0)
		  (rationalp y)
		  (> y x)
		  (integerp n)
		  (> n 0)
		  (exactp x n)
		  (exactp y n))
	     (>= y (fp+ x n)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable expt-split)
		  :use (;(:instance expt-split (r 2) (i (- (1- n) (expo x))) (j (- (1+ (expo x)) n)))
			(:instance fp+1-1)
			(:instance int>0 (n (* (- y x) (expt 2 (- (1- n) (expo x))))))))))



(defthm fp+2-1
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0)
		  (exactp x n))
	     (<= (fp+ x n) (expt 2 (1+ (expo x)))))
  :rule-classes ()
  :hints (("Goal"  :in-theory (enable exactp2)
		  :use ((:instance fp+1 (y (expt 2 (1+ (expo x)))))
			(:instance expo-upper-bound)))))

(defthm x<fp+
    (implies (and (rationalp x)
		  (integerp n))
	     (> (fp+ x n) x))
  :rule-classes ())

;export in lib/?
(defthm ratl-fp+
  (implies (rationalp x)
           (rationalp (fp+ x n)))
  :rule-classes (:rewrite :type-prescription))

(defthm expo-sig
  (equal (expo (sig x))
         0)
  :hints (("Goal" :in-theory (enable sig))))

(defthm fp+2-2
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0)
		  (exactp x n))
	     (or (= (fp+ x n) (expt 2 (1+ (expo x))))
		 (= (expo (fp+ x n)) (expo x))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable fp+)
		  :use ((:instance fp+2-1)
			(:instance x<fp+)
			(:instance expo-lower-bound)
			(:instance expo-unique (x (fp+ x n)) (n (expo x)))))))

(defthm fp+2
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0)
		  (exactp x n))
	     (exactp (fp+ x n) n))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable exactp2)
		  :use ((:instance fp+2-2)))))

(defthm expo-diff-min-1
    (implies (and (rationalp x)
		  (rationalp y)
		  (> x 0)
		  (> y 0)
		  (integerp n)
		  (> n 0)
		  (exactp x n)
		  (exactp y n)
		  (> y x))
	     (>= (expo (- y x)) (- (1+ (expo x)) n)))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable EXPO-COMPARISON-REWRITE-TO-BOUND)
		  :use ((:instance fp+1)
			(:instance expo-monotone (y (- y x)) (x (expt 2 (- (1+ (expo x)) n))))))))

(defthm expo-diff-min-2
    (implies (and (rationalp x)
		  (rationalp y)
		  (> x 0)
		  (> y 0)
		  (integerp n)
		  (> n 0)
		  (exactp x n)
		  (exactp y n)
		  (> y x))
	     (>= (expo (- y x)) (- (1+ (min (expo x) (expo y))) n)))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable EXPO-COMPARISON-REWRITE-TO-BOUND-2
                                       EXPO-COMPARISON-REWRITE-TO-BOUND)
		  :use ((:instance expo-diff-min-1)
			(:instance expo-monotone)))))



(defthm expo-diff-min
    (implies (and (rationalp x)
		  (rationalp y)
		  (> x 0)
		  (> y 0)
		  (integerp n)
		  (> n 0)
		  (exactp x n)
		  (exactp y n)
		  (not (= y x)))
	     (>= (expo (- y x)) (- (1+ (min (expo x) (expo y))) n)))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable expo-minus  EXPO-COMPARISON-REWRITE-TO-BOUND
                                      EXPO-COMPARISON-REWRITE-TO-BOUND-2)
		  :use ((:instance expo-diff-min-2)
			(:instance expo-diff-min-2 (x y) (y x))
			(:instance expo-minus (x (- y x)))))))



;make into a rewrite (rewrite to a claim about m?)
;change param names to i and n?
(defthmd exactp-2**n
  (implies (and ;(case-split (integerp n)) ;drop?
                (case-split (integerp m))
                (case-split (> m 0))
                )
           (exactp (expt 2 n) m))
  :hints (("Goal" :in-theory (enable exactp2)))
  )

;change param names to i and n?
;gen to any power of 2 (e.g., (* 2 (expt n) (/ (expt m)))
(defthm exactp-2**n-rewrite
  (implies (case-split (integerp m)) ;move to conclusion?
           (equal (exactp (expt 2 n) m)
                  (< 0 m)))
  :hints (("Goal" :in-theory (enable exactp2)))
  )


(defthmd expo-upper-2
    (implies (and (< (abs x) (expt 2 n)) ;i don't like abs here
                  (< 0 x)
                  (rationalp x)
		  (integerp n)
		  )
	     (< (expo x) n))
  :rule-classes :linear
  :hints (("Goal"
		  :use ((:instance expo-lower-bound)
			(:instance expt-strong-monotone (n (expo x)) (m n))))))


#|
(defthm xy2-1
    (implies (and (rationalp z)
		  (<= (abs (- 1 z)) 1/2))
	     (and (<= -1 (expo z))
		  (<= (expo z) 0)))
  :rule-classes ()
  :hints (("Goal"
		  :use ((:instance expo-monotone (x 1/2) (y z))
			(:instance expo-monotone (x z) (y 3/2))))))

(defthm xy2-2
    (implies (and (rationalp z)
		  (<= (abs (- 1 z)) 1/2))
	     (<= (abs (expo z)) 1))
  :rule-classes ()
  :hints (("Goal" :use ((:instance xy2-1)))))
|#

;move?
(defthm abs+2
    (implies (and (rationalp x1)
		  (rationalp x2))
	     (<= (abs (+ x1 x2)) (+ (abs x1) (abs x2))))
  :rule-classes ())

;move
(defthm abs+3
  (implies (and (rationalp x1)
                (rationalp x2)
                (rationalp x3))
           (<= (abs (+ x1 x2 x3)) (+ (abs x1) (abs x2) (abs x3))))
  :rule-classes ())

#|
(defthm xy2-3
  (implies (and (rationalp x)
                (rationalp y)
                (<= (abs (- 1 (* x y y))) 1/2))
           (and (not (= x 0)) (not (= y 0))))
  :rule-classes ()
  :hints (("Goal"
           :use ((:instance xy2-1)))))


(defthm xy2-4
    (implies (and (rationalp x)
		  (rationalp y)
		  (<= (abs (- 1 (* x y y))) 1/2))
	     (<= (abs (- (* 2 (expo y)) (expo (* y y)))) 1))
  :rule-classes ()
  :hints (("Goal"
		  :use ((:instance xy2-3)
			(:instance expo-prod-lower (x y))
			(:instance expo-prod-upper (x y))))))

(defthm xy2-5
    (implies (and (rationalp x)
		  (rationalp y)
		  (<= (abs (- 1 (* x y y))) 1/2))
	     (<= (abs (- (+ (expo (* y y)) (expo x)) (expo (* x y y)))) 1))
  :rule-classes ()
  :hints (("Goal"
		  :use ((:instance xy2-3)
			(:instance expo-prod-lower (y (* y y)))
			(:instance expo-prod-upper (y (* y y)))))))

(defthm xy2-6
    (implies (and (rationalp x)
		  (rationalp y)
		  (<= (abs (- 1 (* x y y))) 1/2))
	     (<= (abs (+ (* 2 (expo y)) (expo x))) 3))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable abs)
		  :use ((:instance xy2-2 (z (* x y y)))
			(:instance xy2-4)
			(:instance xy2-5)
			(:instance abs+3
				   (x1 (- (* 2 (expo y)) (expo (* y y))))
				   (x2 (expo (* x y y)))
				   (x3 (- (+ (expo (* y y)) (expo x)) (expo (* x y y)))))))))
|#

;move
(defthm abs-2
    (implies (and (rationalp x1)
		  (rationalp x2))
	     (<= (abs (- x1 x2)) (+ (abs x1) (abs x2))))
  :rule-classes ())

#|
(defthm xy2-7
    (implies (and (rationalp x)
		  (rationalp y)
		  (<= (abs (- 1 (* x y y))) 1/2))
	     (<= (abs (* 2 (expo y))) (+ 3 (abs (expo x)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable abs)
		  :use ((:instance xy2-6)
			(:instance abs-2
				   (x1 (+ (* 2 (expo y)) (expo x)))
				   (x2 (expo x)))))))

(defthm xy2-a
    (implies (and (rationalp x)
		  (rationalp y)
		  (<= (abs (- 1 (* x y y))) 1/2))
	     (< (abs (expo y)) (+ (/ (abs (expo x)) 2) 2)))
  :rule-classes ()
  :hints (("Goal"
		  :use ((:instance xy2-7)))))

(defthm xy2-8
    (implies (and (rationalp x)
		  (rationalp y)
		  (rationalp xp)
		  (not (= xp 0))
		  (<= (abs (- 1 (* x y y))) 1/2))
	     (<= (abs (* 2 (- (expo (* xp y)) (+ (expo xp) (expo y)))))
		 2))
  :rule-classes ()
  :hints (("Goal"
		  :use ((:instance xy2-3)
			(:instance expo-prod-lower (x xp))
			(:instance expo-prod-upper (x xp))))))

(defthm hack4
    (implies (and (rationalp a)
		  (rationalp b)
		  (rationalp c))
	     (= (+ (* 2 a)
		   (* 2 b)
		   (* -2 a)
		   (* -2 b)
		   (* 2 c))
		(* 2 c)))
  :rule-classes ())

(defthm xy2-9
    (implies (and (rationalp x)
		  (rationalp y)
		  (rationalp xp)
		  (= (expo xp) (expo x))
		  (not (= xp 0))
		  (<= (abs (- 1 (* x y y))) 1/2))
	     (<= (abs (* 2 (expo (* xp y))))
		 (+ 5 (abs (expo x)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable abs)
		  :use ((:instance abs+3
				   (x1 (* 2 (- (expo (* xp y)) (+ (expo xp) (expo y)))))
				   (x2 (+ (* 2 (expo y)) (expo xp)))
				   (x3 (expo xp)))
			(:instance hack4 (a (expo x)) (b (expo y)) (c (expo (* xp y))))
			(:instance xy2-8)
			(:instance xy2-6)))))

(defthm xy2-10
    (implies (and (rationalp x)
		  (rationalp y)
		  (rationalp xp)
		  (= (expo xp) (expo x))
		  (<= (abs (- 1 (* x y y))) 1/2))
	     (<= (abs (* 2 (expo (* xp y))))
		 (+ 5 (abs (expo x)))))
  :rule-classes ()
  :hints (("Goal"
		  :use ((:instance xy2-9)))))

;who uses this or any of the xy2-... lemmas??
(defthm xy2-b
    (implies (and (rationalp x)
		  (rationalp y)
		  (rationalp xp)
		  (= (expo xp) (expo x))
		  (<= (abs (- 1 (* x y y))) 1/2))
	     (< (abs (expo (* xp y))) (+ (/ (abs (expo x)) 2) 3)))
  :rule-classes ()
  :hints (("Goal"
		  :use ((:instance xy2-10)))))

|#

(defthm expo-diff-abs-1
    (implies (and (rationalp x)
		  (rationalp y)
		  (> x y)
		  (> y 0)
		  (integerp n)
		  (> n 0)
		  (exactp x n)
		  (exactp y n))
	     (>= (expo (- y x))
		 (- (expo y) (1- n))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable EXPO-COMPARISON-REWRITE-TO-BOUND-2
                                      EXPO-COMPARISON-REWRITE-TO-BOUND)
		  :use ((:instance expo-diff-min)
			(:instance expo-monotone (x y) (y x))))))

(defthm expo-diff-abs-2
    (implies (and (rationalp x)
		  (rationalp y)
		  (> x y)
		  (> y 0)
		  (integerp n)
		  (> n 0)
		  (exactp x n)
		  (exactp y n))
	     (<= (expo (- y x))
		 (expo x)))
  :rule-classes ()
  :hints (("Goal"
		  :use ((:instance expo-monotone (x (- y x)) (y x))))))

(defthm expo-diff-abs-3
    (implies (and (rationalp x)
		  (rationalp y)
		  (integerp n)
		  (> n 0))
	     (<= (abs (- (expo y) (1- n)))
		 (+ (max (abs (expo x)) (abs (expo y))) (1- n))))
    :hints (("Goal" :in-theory (disable EXPO-COMPARISON-REWRITE-TO-BOUND
                                        EXPO-COMPARISON-REWRITE-TO-BOUND-2)))
  :rule-classes ())

(defthm expo-diff-abs-4
    (implies (and (rationalp x)
		  (rationalp y)
		  (integerp n)
		  (> n 0))
	     (<= (abs (expo x))
		 (+ (max (abs (expo x)) (abs (expo y))) (1- n))))
    :hints (("Goal" :in-theory (disable EXPO-COMPARISON-REWRITE-TO-BOUND
                                        EXPO-COMPARISON-REWRITE-TO-BOUND-2)))
    :rule-classes ())

;move?
(defthmd abs-squeeze
    (implies (and (rationalp x)
		  (rationalp y)
		  (rationalp z)
		  (rationalp m)
		  (<= x y)
		  (<= y z)
		  (<= (abs x) m)
		  (<= (abs z) m))
	     (<= (abs y) m))
  :rule-classes :linear)

;move?
(defthm rationalp-abs
  (implies (case-split (rationalp x))
           (rationalp (abs x)))
  :rule-classes (:rewrite :type-prescription))

;yuck
(local (in-theory (disable EXPO-COMPARISON-REWRITE-TO-BOUND-2
                           EXPO-COMPARISON-REWRITE-TO-BOUND)))

(defthm expo-diff-abs-5
    (implies (and (rationalp x)
		  (rationalp y)
		  (> x y)
		  (> y 0)
		  (integerp n)
		  (> n 0)
		  (exactp x n)
		  (exactp y n))
	     (<= (abs (expo (- y x)))
		 (+ (max (abs (expo x)) (abs (expo y))) (1- n))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable abs)
		  :use ((:instance abs-squeeze
				   (m (+ (max (abs (expo x)) (abs (expo y))) (1- n)))
				   (x (- (expo y) (1- n)))
				   (y (expo (- y x)))
				   (z (expo x)))
			(:instance expo-diff-abs-1)
			(:instance expo-diff-abs-2)
			(:instance expo-diff-abs-3)
			(:instance expo-diff-abs-4)))))


(defthm expo-diff-abs-6
    (implies (and (rationalp x)
		  (rationalp y)
		  (> x 0)
		  (> y 0)
		  (not (= x y))
		  (integerp n)
		  (> n 0)
		  (exactp x n)
		  (exactp y n))
	     (<= (abs (expo (- x y)))
		 (+ (max (abs (expo x)) (abs (expo y))) (1- n))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable abs expo-minus)
		  :use ((:instance expo-diff-abs-5)
			(:instance expo-diff-abs-5 (x y) (y x))
			(:instance expo-minus (x (- x y)))))))



(defthm expo-diff-abs
    (implies (and (rationalp x)
		  (rationalp y)
		  (> x 0)
		  (> y 0)
		  (integerp n)
		  (> n 0)
		  (exactp x n)
		  (exactp y n))
	     (<= (abs (expo (- x y)))
		 (+ (max (abs (expo x)) (abs (expo y))) (1- n))))
  :rule-classes ()
  :hints (("Goal" ;:in-theory (disable abs)
		  :use ((:instance expo-diff-abs-6)
			))))

(defthm expo-diff-abs-neg-1
    (implies (and (rationalp x)
		  (rationalp y)
		  (> x 0)
		  (> y 0)
		  (>= x y)
		  (integerp n)
		  (> n 1)
		  (exactp x n)
		  (exactp y n))
	     (<= (expo (+ x y))
		 (+ (expo x) (1- n))))
  :rule-classes ()
  :hints (("Goal"
		  :use (;(:instance expo-2x-upper)
			(:instance expo-monotone (x (+ x y)) (y (* 2 x)))))))

(defthm expo-diff-abs-neg-2
    (implies (and (rationalp x)
		  (rationalp y)
		  (> x 0)
		  (> y 0)
		  (>= x y)
		  (integerp n)
		  (> n 1)
		  (exactp x n)
		  (exactp y n))
	     (<= (expo x) (expo (+ x y))))
  :rule-classes ()
  :hints (("Goal"
		  :use ((:instance expo-monotone (y (+ x y)))))))

;move or remove?
(defthm abs-pos
    (implies (<= 0 x)
	     (equal (abs x) x)))

(defthm expo-diff-abs-neg-3
    (implies (and (rationalp x)
		  (rationalp y)
		  (> x 0)
		  (> y 0)
		  (>= x y)
		  (integerp n)
		  (> n 1)
		  (exactp x n)
		  (exactp y n))
	     (<= (abs (expo (+ x y)))
		 (+ (max (abs (expo x)) (abs (expo y))) (1- n))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable abs)
		  :use ((:instance expo-diff-abs-neg-1)
			(:instance expo-diff-abs-neg-2)
			(:instance abs-squeeze
				   (m (+ (max (abs (expo x)) (abs (expo y))) (1- n)))
				   (x (expo x))
				   (y (expo (+ y x)))
				   (z (+ (expo x) (1- n))))
			(:instance abs+2 (x1 (expo x)) (x2 (1- n)))))))

(defthm expo-diff-abs-neg-4
    (implies (and (rationalp x)
		  (rationalp y)
		  (> x 0)
		  (> y 0)
		  (integerp n)
		  (> n 1)
		  (exactp x n)
		  (exactp y n))
	     (<= (abs (expo (+ x y)))
		 (+ (max (abs (expo x)) (abs (expo y))) (1- n))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable abs)
		  :use ((:instance expo-diff-abs-neg-3)
			(:instance expo-diff-abs-neg-3 (x y) (y x))))))

(defthm expo-diff-abs-neg-5
    (implies (and (rationalp x)
		  (rationalp y)
		  (> x 0)
		  (< y 0)
		  (integerp n)
		  (> n 1)
		  (exactp x n)
		  (exactp y n))
	     (<= (abs (expo (- x y)))
		 (+ (max (abs (expo x)) (abs (expo y))) (1- n))))
  :rule-classes ()
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable exactp2)
                              '( abs expo-minus))
		  :use ((:instance expo-diff-abs-neg-4 (y (- y)))
			(:instance expo-minus (x y))))))

(defthm expo-diff-abs-neg-6
    (implies (and (rationalp x)
		  (rationalp y)
		  (< x 0)
		  (> y 0)
		  (integerp n)
		  (> n 1)
		  (exactp x n)
		  (exactp y n))
	     (<= (abs (expo (- x y)))
		 (+ (max (abs (expo x)) (abs (expo y))) (1- n))))
  :rule-classes ()
  :hints (("Goal" :in-theory  (set-difference-theories
                              (enable exactp2)
                              '( abs expo-minus))
		  :use ((:instance expo-diff-abs-neg-4 (x (- x)))
			(:instance expo-minus (x (- x y)))
			(:instance expo-minus)))))

(defthm expo-diff-abs-neg-neg
    (implies (and (rationalp x)
		  (rationalp y)
		  (< x 0)
		  (< y 0)
		  (integerp n)
		  (> n 1)
		  (exactp x n)
		  (exactp y n))
	     (<= (abs (expo (- x y)))
		 (+ (max (abs (expo x)) (abs (expo y))) (1- n))))
  :rule-classes ()
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable exactp2)
                              '( abs max expo-minus))
		  :use ((:instance expo-diff-abs (x (- x)) (y (- y)))
			(:instance expo-minus)
			(:instance expo-minus (x (- x y)))
			(:instance expo-minus (x y))))))

(defthm expo-diff-abs-zero-y
    (implies (and (rationalp x)
		  (rationalp y)
		  (= y 0)
		  (integerp n)
		  (> n 1)
		  (exactp x n)
		  (exactp y n))
	     (<= (abs (expo (- x y)))
		 (+ (max (abs (expo x)) (abs (expo y))) (1- n))))
  :rule-classes ())

(defthm expo-diff-abs-zero-x
    (implies (and (rationalp x)
		  (rationalp y)
		  (= x 0)
		  (integerp n)
		  (> n 0)
		  (exactp x n)
		  (exactp y n))
	     (<= (abs (expo (- x y)))
		 (+ (max (abs (expo x)) (abs (expo y))) (1- n))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable expo-minus)
		  :use ((:instance expo-minus (x y))))))

(defthm expo-diff-abs-neg-x
    (implies (and (rationalp x)
		  (rationalp y)
		  (< x 0)
		  (integerp n)
		  (> n 1)
		  (exactp x n)
		  (exactp y n))
	     (<= (abs (expo (- x y)))
		 (+ (max (abs (expo x)) (abs (expo y))) (1- n))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable max abs)
		  :use ((:instance expo-diff-abs-zero-y)
			(:instance expo-diff-abs-neg-6)
			(:instance expo-diff-abs-neg-neg)))))

(defthm expo-diff-abs-pos-x
    (implies (and (rationalp x)
		  (rationalp y)
		  (> x 0)
		  (integerp n)
		  (> n 1)
		  (exactp x n)
		  (exactp y n))
	     (<= (abs (expo (- x y)))
		 (+ (max (abs (expo x)) (abs (expo y))) (1- n))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable max abs)
		  :use ((:instance expo-diff-abs-zero-y)
			(:instance expo-diff-abs)
			(:instance expo-diff-abs-neg-5)))))

(defthm expo-diff-abs-any
    (implies (and (exactp x n)
		  (exactp y n)
                  (rationalp x)
		  (rationalp y)
		  (integerp n)
		  (> n 1)
		  )
	     (<= (abs (expo (- x y)))
		 (+ (max (abs (expo x)) (abs (expo y))) (1- n))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable max abs)
		  :use ((:instance expo-diff-abs-zero-x)
			(:instance expo-diff-abs-neg-x)
			(:instance expo-diff-abs-pos-x)))))
;move?
;try as a rewrite rule (perhaps with a backchain limit?)
;why disabled?
(defthm expo>=
  (implies (and (<= (expt 2 n) x)
                (rationalp x)
                (integerp n)
                )
           (<= n (expo x)))
  :otf-flg t
  :rule-classes :linear
  :hints (("goal" :use ((:instance expo-monotone (x (expt 2 n)) (y x))))))

;move?
;try as a rewrite rule (perhaps with a backchain limit?)
;why disabled?
(defthmd expo<=
  (implies (and (< x (* 2 (expt 2 n)))
                (< 0 x)
                (rationalp x)
                (integerp n)
                )
           (<= (expo x) n))
  :rule-classes :linear
  :hints (("goal" :use (expo-lower-bound
			(:instance expt-split (r 2) (i 1) (j n))
			(:instance expt-weak-monotone (n (1+ n)) (m (expo x)))))))

(defthm sig-does-nothing
  (implies (and (< x 2)
                (<= 1 x)
                (rationalp x)
                )
           (equal (sig x)
                  x))
  :hints (("Goal" :use ((:instance fp-rep-unique
                                   (x x)
                                   (m x)
                                   (e (expo x))))
           :in-theory (enable sig))))


;proved in expo
(defthm expo-x+2**k
    (implies (and (< (expo x) k)
                  (<= 0 x)
                  (case-split (integerp k))
		  (case-split (rationalp x))
		  )
	     (equal (expo (+ x (expt 2 k)))
		    k)))


;remove? or move elsewhere?
#|
bad name
(defthm only-1-has-integerp-sig
  (implies (and
            (rationalp x)
            (not (equal x 0))
            (integerp (sig x)))
           (= (sig x) 1))
  :hints (("Goal" :in-theory (disable sig-upper-bound)
           :use (sig-upper-bound sig-lower-bound)))
)
|#


;dup?
(defthm exactp-shift-rewrite
  (implies (and (rationalp x)
                (integerp m)
                (integerp n))
           (and (equal (exactp (* (expt 2 n) x) m)
                       (exactp x m))
                (equal (exactp (* x (expt 2 n)) m)
                       (exactp x m))))
  :hints (("Goal" :use exactp-shift)))

(defthm exactp-one-plus-expo
  (implies (case-split (rationalp x)) ;gen?
           (equal (exactp x (+ 1 (expo x)))
                  (integerp x)))
  :hints (("Goal" :in-theory (enable exactp)
           :use ((:instance fp-rep)))))

(defthmd sgn*
    (implies (and (rationalp x) (rationalp y))
	     (= (sgn (* x y)) (* (sgn x) (sgn y)))))

(defthm already-sig
  (implies (and (rationalp x)
                (<= 1 x)
                (< x 2))
           (= (sig x) x)))

(defthm sig-shift-4-alt
  (implies (and (rationalp a)
                (integerp n)
                (case-split (not (equal a 0)))
                )
           (equal (sig (* a (EXPT 2 n)))
                  (sig a)))
  :HINTS (("Goal" :USE (:instance SIG-EXPO-SHIFT (x a)))))

;add to lib?
;can save you from having to :use fp-rep
(defthmd fp-rep-cancel-expo
  (implies (rationalp x)
           (equal (* x (expt 2 (- (expo x))))
                  (* (sgn x) (sig x))))
  :hints (("Goal" :in-theory (enable sig
                                     )
           :use (fp-rep))))

;do we need this?
(defthmd fp-rep-cancel-sig
  (equal (/ x (sig x))
         (* (sgn x) (expt 2 (expo x))))
  :hints (("Goal" :use (fp-rep))))

;useful?
; could be made more general?
(defthm sig-x+2**k-non-neg
  (implies (and (< x (expt 2 k))
                (integerp k)
                (rationalp x)
                (<= 0 x)
                )
           (equal (sig (+ (expt 2 k) x))
                  (+ 1 (/ x (expt 2 k)))))
  :hints (("Goal" :in-theory (e/d () ( sig-does-nothing sig-shift))
           :use ((:instance sig-shift
                            (x (+ 1 (/ x (expt 2 k))))
                            (n k))
                 (:instance sig-does-nothing
                            (x (+ 1 (/ x (expt 2 k)))))))))

;rename?
;what's the role of n here?
;this does not mention trunc!
;conceptually, x and y don't overlap
(defthm expo-of-sum-of-disjoint
  (implies (and (< y (expt 2 (- (1+ (expo x)) n)))
                (exactp x n)
                (rationalp x)
                (> x 0)
                (rationalp y)
                (>= y 0)
                (integerp n)
                )
           (equal (expo (+ x y))
                  (expo x)
                  ))
  :hints (("Goal"  :in-theory (set-difference-theories
                               (enable exactp sgn
                                       expt-split expt-minus
                                       sig
                                       )
                               '(expo-x+a*2**k
                                 EXPT-COMPARE-EQUAL
                                 EXPO-COMPARISON-REWRITE-TO-BOUND
  ;                               EXPO-SHIFT-4-ALT-2
                                 ))
           :use (;(:instance expt-split (r 2) (i 1) (j (+ (EXPO X) (* -1 N))))
                 (:instance expo<= (x y) (n (+ (EXPO X) (* -1 N))))
                 ;(:instance fp-rep-cancel-expo)
                 (:instance
                  expo-x+a*2**k
                  (x y)
                  (k (+ (expo x) (- n) 1))
                  (a (/ x (expt 2 (+ (expo x) (- n) 1)))))
                 ))
          )
  :rule-classes nil
  )




(defthm exactp-with-n-not-integer
  (implies (not (integerp n))
           (equal (exactp x n)
                  (or (equal 0 x)
                      (not (rationalp x))
                      (and (acl2-numberp n)
                           (power2p (abs x))))))
  :hints (("Goal" :in-theory (enable exactp sig expt-minus expt-split))))

;BOZO could say power2p in conclusion?
(defthm sig-x-1-means-power-of-2
  (implies (and (rationalp x)
;                (> x 0) ;gen?
                )
           (equal (equal (sig x) 1)
                  (equal (expt 2 (expo x)) (abs x))))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable sig expt-minus)
                              '(expt-inverse))

           :use ())))

(defthm sig-less-than-1-means-x-0
  (equal (< (sig x) 1)
	 (or (equal 0 x)
             (not (rationalp x)))))

(defthm sig-integer-rewrite
  (equal (integerp (sig x))
         (or (not (rationalp x))
             (equal 0 x)
             (equal 1 (sig x))))
  :hints (("goal" :in-theory (disable sig-x-1-means-power-of-2)))
  )

(defthm cg-sig
  (equal (cg (sig x))
         (if (or (not (rationalp x)) (equal 0 x))
             0
           (if (power2p (abs x))
               1
             2)))
  :hints (("goal" :in-theory (enable cg power2p-rewrite)))
  )

(defthm sig-times-half-not-integer
  (equal (integerp (* 1/2 (sig x)))
         (or (equal 0 x)
             (not (rationalp x))))
  :hints (("goal" :in-theory (enable sig))))

(defthm cg-half-sig
  (equal (cg (* 1/2 (sig x)))
         (if (or (not (rationalp x)) (equal 0 x))
             0
           1))
  :hints (("goal" :in-theory (enable cg))))



