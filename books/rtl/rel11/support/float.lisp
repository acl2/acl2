(in-package "RTL")

(include-book "tools/with-arith5-help" :dir :system)
(local (acl2::allow-arith5-help))
(local (in-theory (acl2::enable-arith5)))

(local (include-book "basic"))
(include-book "definitions")
(include-book "projects/quadratic-reciprocity/euclid" :dir :system)

(defrule abs-type
  (implies (real/rationalp x)
           (real/rationalp (abs x)))
  :rule-classes :type-prescription)

; Prove it without including log.lisp to certify by ACL2r
(defrulel logior-bvecp
  (implies (and (bvecp x n)
                (bvecp y n))
           (bvecp (logior x y) n))
  :prep-books ((include-book "ihs/logops-lemmas" :dir :system))
  :enable bvecp
  :disable acl2::unsigned-byte-p-logior
  :use (:instance acl2::unsigned-byte-p-logior
                  (i x)
                  (j y)
                  (size n)))

;;;**********************************************************************
;;;                 Sign, Significand, and Exponent with Radix
;;;**********************************************************************

(defrule signum-minus
  (equal (signum (- x)) (- (signum (fix x)))))

(defrule signum-mult
  (implies (real/rationalp r)
           (equal (signum (* x r))
             (cond ((> r 0) (signum (fix x)))
                   ((< r 0) (- (signum (fix x))))
                   (t 0))))
  :rule-classes ())

(in-theory (disable signum))

; (defund expe (x b) ... )

(local (defrule expe-x=0
  (equal (expe 0 b) 0)
  :enable expe))

(local (defrule expe-x-default
  (implies (not (real/rationalp x))
           (equal (expe x b) 0))
  :enable expe))

(local (defrule expe-b-default
  (implies (not (radixp b))
           (equal (expe x b) 0))
  :enable expe))

; (defund sigm (x b) ... )

(defrule sigm-type
  (implies (radixp b)
           (and (real/rationalp (sigm x b))
                (>= (sigm x b) 0)))
  :enable sigm
  :rule-classes :type-prescription)

(local (defrule sigm-x=0
  (equal (sigm 0 b) 0)
  :enable sigm))

(local (defrule sigm-x-default
  (implies (not (real/rationalp x))
           (equal (sigm x b) 0))
  :enable sigm))

(local (defrule sigm-b-default
  (implies (not (radixp b))
           (equal (sigm x b) 0))
  :enable sigm))

(defrule expe-minus
  (equal (expe (- x) b) (expe x b))
  :expand ((expe (- x) b) (expe x b)))

(defrule sigm-minus
  (equal (sigm (- x) b) (sigm x b))
  :enable sigm)

(defruled expe-lower-bound
  (implies (and (real/rationalp x)
                (not (equal x 0))
                (radixp b))
           (<= (expt b (expe x b)) (abs x)))
  :enable expe
  :induct (expe x b)
  :rule-classes :linear)

(defruled expe-upper-bound
    (implies (and (real/rationalp x) (radixp b))
	     (< (abs x) (expt b (1+ (expe x b)))))
  :enable expe
  :induct (expe x b)
  :rule-classes :linear)

(defrule expe-unique
  (implies (and (<= (expt b n) (abs x))
                (< (abs x) (expt b (1+ n)))
                (real/rationalp x)
                (integerp n)
                (radixp b))
           (equal n (expe x b)))
  :enable (expe-lower-bound expe-upper-bound)
  :cases ((<= (1+ n) (expe x b))
          (>= n (1+ (expe x b))))
  :rule-classes ())

(defrule fp-rep-em
  (implies (radixp b)
           (equal (realfix x) (* (signum x) (sigm x b) (expt b (expe x b)))))
  :enable (signum sigm)
  :rule-classes ())

(defrule fp-abs-em
  (implies (radixp b)
           (equal (abs (realfix x)) (* (sigm x b) (expt b (expe x b)))))
  :enable signum
  :use fp-rep-em
  :rule-classes ())

(defruled expe>=
    (implies (and (<= (expt b n) x)
                  (real/rationalp x)
		  (integerp n)
                  (radixp b))
	     (<= n (expe x b)))
  :use expe-upper-bound
  :cases ((>= n (1+ (expe x b))))
  :rule-classes :linear)

(defruled expe<=
    (implies (and (< x (* b (expt b n)))
                  (< 0 x)
                  (real/rationalp x)
		  (integerp n)
                  (radixp b))
	     (<= (expe x b) n))
  :enable expe-lower-bound
  :cases ((<= (1+ n) (expe x b)))
  :rule-classes :linear)

(defrule expe-b**n
    (implies (and (integerp n)
                  (radixp b))
	     (equal (expe (expt b n) b)
		    n))
  :cases ((< (expe (expt b n) b) n)
          (> (expe (expt b n) b) n))
  :hints (
    ("subgoal 2" :use (:instance expe>=
                        (x (expt b n))))
    ("subgoal 1" :use (:instance expe<=
                        (x (expt b n))))))

(defruled expe-monotone
  (implies (and (<= (abs x) (abs y))
                (case-split (real/rationalp x))
                (case-split (not (equal x 0)))
                (case-split (real/rationalp y))
                (radixp b))
           (<= (expe x b) (expe y b)))
  :enable expe-lower-bound
  :use (:instance expe>=
         (x (abs y))
         (n (expe x b)))
  :rule-classes :linear)

(defruled dvecp-expe
    (implies (and (case-split (natp x))
                  (case-split (radixp b)))
	     (dvecp x (1+ (expe x b)) b))
  :enable (dvecp expe-upper-bound)
  :cases ((not (natp (expe x b)))
          (not (real/rationalp x)))
  :hints (("subgoal 2" :use (:instance expe>=
                              (n 0)))))

(defruled mod-expe-2
  (implies (and (< 0 x)
                (real/rationalp x))
           (equal (mod x (expt 2 (expe x 2)))
                  (- x (expt 2 (expe x 2)))))
  :enable (expe-lower-bound expe-upper-bound)
  :use (:instance mod-force
         (m x)
         (n (expt 2 (expe x 2)))
         (a 1)))

(defruled sigm-lower-bound
  (implies (and (real/rationalp x)
                (not (equal x 0))
                (radixp b))
           (<= 1 (sigm x b)))
  :prep-lemmas (
    (acl2::with-arith5-nonlinear-help (defrule lemma
      (implies (and (radixp b) (<= (expt b (- n)) x))
               (<= 1 (* x (expt b n)))))))
  :enable sigm
  :disable abs
  :use expe-lower-bound
  :rule-classes (:rewrite :linear))

(defrule sigm-type-x-nonzero
  (implies (and (real/rationalp x)
                (not (equal x 0))
                (radixp b))
           (and (real/rationalp (sigm x b))
                (> (sigm x b) 0)))
  :enable sigm-lower-bound
  :rule-classes :type-prescription)

(defruled sigm-upper-bound
  (implies (radixp b)
           (< (sigm x b) b))
  :prep-lemmas (
    (acl2::with-arith5-nonlinear-help (defrule lemma
      (implies (and (radixp b) (< x (expt b (- n))))
               (< (* x (expt b n)) 1)))))
  :enable sigm
  :disable abs
  :use expe-upper-bound
  :rule-classes (:rewrite :linear))

(defrule expe-sigm
  (equal (expe (sigm x b) b) 0)
  :enable (sigm-lower-bound sigm-upper-bound)
  :cases ((and (real/rationalp x) (not (= x 0)) (radixp b)))
  :hints (
    ("subgoal 2" :in-theory (enable sigm expe))
    ("subgoal 1" :use (:instance  expe-unique
                        (x (sigm x b))
                        (n 0)))))

(defruled sigm-self
  (implies (and (real/rationalp x)
                (<= 1 x)
                (< x b)
                (radixp b))
           (equal (sigm x b) x))
  :enable sigm
  :use (:instance expe-unique
         (n 0)))

(defrule sigm-sigm
  (equal (sigm (sigm x b) b)
         (sigm x b))
  :enable (sigm-lower-bound sigm-upper-bound)
  :use (:instance sigm-self
         (x (sigm x b)))
  :cases ((and (real/rationalp x) (not (= x 0)) (radixp b)))
  :hints (("subgoal 2" :in-theory (enable sigm))))

(defrule fp-rep-em-unique
  (implies (and (real/rationalp m)
                (<= 1 m)
                (< m b)
                (integerp e)
                (radixp b)
                (= (abs x) (* m (expt b e))))
           (and (= m (sigm x b))
                (= e (expe x b))))
  :enable sigm
  :disable abs
  :use (:instance expe-unique
         (n e))
  :cases ((real/rationalp x))
  :hints (("subgoal 2" :in-theory (enable abs)))
  :rule-classes ())

(defruled signum-shift
  (implies (and (real/rationalp x)
                (radixp b))
           (equal (signum (* x (expt b k)))
                  (signum x)))
  :use (:instance signum-mult
         (r (expt b k))))

(defruled expe-shift
  (implies (and (real/rationalp x)
                (not (equal x 0))
                (integerp n)
                (radixp b))
           (equal (expe (* (expt b n) x) b)
                  (+ n (expe x b))))
  :enable (expe-lower-bound)
  :use ((:instance expe-unique
          (x (* (expt b n) x))
          (n (+ n (expe x b))))
        expe-upper-bound))

(defruled sigm-shift
  (equal (sigm (* x (expt b n)) b)
         (sigm x b))
  :enable (sigm)
  :cases ((and (real/rationalp x) (not (= x 0)) (integerp n)))
  :hints (
    ("subgoal 2" :in-theory (enable expe expt))
    ("subgoal 1" :use expe-shift)))

(defruled signum-prod
  (implies (and (case-split (real/rationalp x))
                (case-split (real/rationalp y)))
           (equal (signum (* x y))
                  (* (signum x) (signum y))))
  :enable signum)

(defruled expe-prod
    (implies (and (real/rationalp x)
		  (not (= x 0))
		  (real/rationalp y)
		  (not (= y 0))
                  (radixp b))
	     (equal (expe (* x y) b)
		    (if (< (* (sigm x b) (sigm y b)) b)
			(+ (expe x b) (expe y b))
		      (+ 1 (expe x b) (expe y b)))))
  :prep-lemmas (
    (acl2::with-arith5-nonlinear-help (defrule lemma1
      (implies (and (real/rationalp mx) (<= 1 mx) (< mx b) (integerp ex)
                    (real/rationalp my) (<= 1 my) (< my b) (integerp ey)
                    (radixp b))
               (equal (expe (* (* mx (expt b ex)) (* my (expt b ey))) b)
                      (if (< (* mx my) b) (+ ex ey) (+ 1 ex ey))))
      :use (:instance expe-unique
             (x (* (* mx (expt b ex)) (* my (expt b ey))))
             (n (if (< (* mx my) b) (+ ex ey) (+ 1 ex ey))))))
    (defrule lemma2
      (implies (and (real/rationalp x) (> x 0)
                    (real/rationalp y) (> y 0)
                    (radixp b))
	     (equal (expe (* x y) b)
		    (if (< (* (sigm x b) (sigm y b)) b)
			(+ (expe x b) (expe y b))
		      (+ 1 (expe x b) (expe y b)))))
      :enable (signum sigm-lower-bound sigm-upper-bound)
      :use (
        (:instance fp-rep-em
          (x x))
        (:instance fp-rep-em
          (x y))
        (:instance lemma1
          (mx (sigm (abs x) b))
          (ex (expe (abs x) b))
          (my (sigm (abs y) b))
          (ey (expe (abs y) b))))))
  :use (:instance lemma2
         (x (abs x))
         (y (abs y))))

(defruled expe-prod-lower
    (implies (and (real/rationalp x)
		  (not (= x 0))
		  (real/rationalp y)
		  (not (= y 0)))
	     (<= (+ (expe x b) (expe y b)) (expe (* x y) b)))
  :use expe-prod
  :rule-classes :linear)

(defruled expe-prod-upper
    (implies (and (real/rationalp x)
		  (not (= x 0))
		  (real/rationalp y)
		  (not (= y 0)))
	     (>= (+ (expe x b) (expe y b) 1) (expe (* x y) b)))
  :use expe-prod
  :rule-classes :linear)

(defruled sigm-prod
    (implies (and (real/rationalp x)
		  (not (= x 0))
		  (real/rationalp y)
		  (not (= y 0)))
	     (equal (sigm (* x y) b)
		    (if (< (* (sigm x b) (sigm y b)) b)
			(* (sigm x b) (sigm y b))
		      (* (/ b) (sigm x b) (sigm y b)))))
  :enable (sigm expe-prod)
  :disable abs
  :cases ((equal (abs (* x y)) (* (abs x) (abs y))))
  :hints (("subgoal 2" :in-theory(enable abs))))

(defruled expe-fl
  (implies (and (real/rationalp x)
                (>= x 1)
                (radixp b))
	   (equal (expe (fl x) b) (expe x b)))
  :use (expe-lower-bound
        (:instance expe-monotone (x (fl x)) (y x))
        (:instance expe>= (n 0))
        (:instance expe>= (x (fl x)) (n (expe x b)))))

(defruled compare-abs-em
  (implies (and (real/rationalp x)
                (real/rationalp y)
                (radixp b))
           (equal (signum (- (abs x) (abs y)))
                  (cond ((and (= x 0) (= y 0)) 0)
                        ((= x 0) -1)
                        ((= y 0) 1)
                        ((< (expe x b) (expe y b)) -1)
                        ((> (expe x b) (expe y b)) 1)
                        ((< (sigm x b) (sigm y b)) -1)
                        ((> (sigm x b) (sigm y b)) 1)
                        (t 0))))
  :prep-lemmas (
    (defrule lemma1
      (implies (and (real/rationalp mx) (<= 1 mx) (< mx b) (integerp ex)
                    (real/rationalp my) (<= 1 my) (< my b) (integerp ey)
                    (< ex ey)
                    (radixp b))
               (< (* mx (expt b ex)) (* my (expt b ey))))
      :cases ((not (< (* mx (expt b ex)) (expt b (1+ ex))))
              (not (>= (* my (expt b ey)) (expt b ey)))
              (not (<= (expt b (1+ ex)) (expt b ey))))
      :rule-classes ())
    (defruled lemma2
      (implies (and (real/rationalp mx) (<= 1 mx) (< mx b) (integerp ex)
                    (real/rationalp my) (<= 1 my) (< my b) (integerp ey)
                    (radixp b))
               (equal (signum (- (* mx (expt b ex)) (* my (expt b ey))))
                              (cond ((< ex ey) -1)
                                    ((> ex ey) 1)
                                    ((< mx my) -1)
                                    ((> mx my) 1)
                                    (t 0))))
      :enable (acl2::scatter-exponents-theory signum)
      :disable (acl2::gather-exponents-theory)
      :cases ((= ex ey)
              (< ex ey)
              (> ex ey))
      :hints (
        ("subgoal 2" :use (:instance lemma1 (ex ex) (ey ey) (mx mx) (my my)))
        ("subgoal 1" :use (:instance lemma1 (ex ey) (ey ex) (mx my) (my mx))))))
  :enable (signum sigm-upper-bound)
  :cases ((= x 0)
          (= y 0))
  :hints (
    ("subgoal 3" :in-theory (disable abs) :use (
      (:instance fp-abs-em
        (x x))
      (:instance fp-abs-em
        (x y))
      (:instance lemma2
                        (ex (expe x b))
                        (ey (expe y b))
                        (mx (sigm x b))
                        (my (sigm y b)))))))

;;;**********************************************************************
;;;                 Sign, Significand, and Exponent
;;;**********************************************************************

; (defnd sgn (x) ... )
; (defnd expo (x) ... )
; (defnd sig (x) ... )

(local (defrule sgn-as-signum
  (equal (sgn x)
         (if (rationalp x) (signum x) 0))
  :enable (sgn signum)))

(local (defrule expo-as-expe
  (equal (expo x)
         (if (rationalp x) (expe x 2) 0))
  :enable (expo expe)))

(local (defrule sig-as-sigm
  (equal (sig x)
         (if (rationalp x) (sigm x 2) 0))
  :enable (sig sigm)))

(defthm expo-minus
  (implies (rationalp x)
           (equal (expo (- x)) (expo x))))

(defthm sig-minus
  (implies (rationalp x)
           (equal (sig (- x)) (sig x))))

(defruled expo-lower-bound
    (implies (and (rationalp x)
		  (not (equal x 0)))
	     (<= (expt 2 (expo x)) (abs x)))
  :enable expe-lower-bound
  :rule-classes :linear)

(defruled expo-upper-bound
    (implies (and (rationalp x))
	     (< (abs x) (expt 2 (1+ (expo x)))))
  :enable expe-upper-bound
  :rule-classes :linear)

(defrule expo-unique
  (implies (and (<= (expt 2 n) (abs x))
                (< (abs x) (expt 2 (1+ n)))
                (rationalp x)
                (integerp n))
           (equal n (expo x)))
  :use (:instance expe-unique (b 2))
  :rule-classes ())

(defrule fp-rep
    (implies (rationalp x)
	     (equal x (* (sgn x) (sig x) (expt 2 (expo x)))))
  :use (:instance fp-rep-em (b 2))
  :rule-classes ())

(defrule fp-abs
    (implies (rationalp x)
	     (equal (abs x) (* (sig x) (expt 2 (expo x)))))
  :use (:instance fp-abs-em (b 2))
  :rule-classes ())

(defruled expo>=
    (implies (and (<= (expt 2 n) x)
                  (rationalp x)
		  (integerp n))
	     (<= n (expo x)))
  :enable expe>=
  :rule-classes :linear)

(defruled expo<=
    (implies (and (< x (* 2 (expt 2 n)))
                  (< 0 x)
                  (rationalp x)
		  (integerp n))
	     (<= (expo x) n))
  :use (:instance expe<= (b 2))
  :rule-classes :linear)

(defthm expo-2**n
    (implies (integerp n)
	     (equal (expo (expt 2 n))
		    n)))

(defruled expo-monotone
  (implies (and (<= (abs x) (abs y))
                (case-split (rationalp x))
                (case-split (not (equal x 0)))
                (case-split (rationalp y)))
           (<= (expo x) (expo y)))
  :use (:instance expe-monotone (b 2))
  :rule-classes :linear)

(defruled bvecp-expo
    (implies (case-split (natp x))
	     (bvecp x (1+ (expo x))))
  :enable (bvecp dvecp)
  :use (:instance dvecp-expe (b 2)))

(defruled mod-expo
  (implies (and (< 0 x)
                (rationalp x))
           (equal (mod x (expt 2 (expo x)))
                  (- x (expt 2 (expo x)))))
  :enable mod-expe-2)

(defruled sig-lower-bound
  (implies (and (rationalp x)
                (not (equal x 0)))
           (<= 1 (sig x)))
  :enable sigm-lower-bound
  :rule-classes (:rewrite :linear))

(defruled sig-upper-bound
  (< (sig x) 2)
  :enable sigm-upper-bound
  :rule-classes (:rewrite :linear))

(defthm expo-sig
  (implies (rationalp x)
           (equal (expo (sig x)) 0)))

(defruled sig-self
  (implies (and (rationalp x)
                (<= 1 x)
                (< x 2))
           (equal (sig x) x))
  :enable sigm-self)

(defrule sig-sig
    (equal (sig (sig x))
	   (sig x))
  :cases ((rationalp (sig x)))
  :use (:instance sigm-sigm (b 2)))

(defrule fp-rep-unique
    (implies (and (rationalp x)
		  (rationalp m)
		  (<= 1 m)
		  (< m 2)
		  (integerp e)
		  (= (abs x) (* m (expt 2 e))))
	     (and (= m (sig x))
		  (= e (expo x))))
  :use (:instance fp-rep-em-unique (b 2))
  :rule-classes ())

(defruled sgn-shift
  (equal (sgn (* x (expt 2 k)))
         (sgn x))
  :enable signum-shift)

(defruled expo-shift
  (implies (and (rationalp x)
                (not (equal x 0))
                (integerp n))
           (equal (expo (* (expt 2 n) x))
                  (+ n (expo x))))
  :use (:instance expe-shift (b 2)))

(defruled sig-shift
  (equal (sig (* (expt 2 n) x))
         (sig x))
  :use (:instance sigm-shift (b 2)))

(defruled sgn-prod
  (implies (and (case-split (rationalp x))
                (case-split (rationalp y)))
           (equal (sgn (* x y))
                  (* (sgn x) (sgn y))))
  :enable signum-prod)

(defruled expo-prod
    (implies (and (rationalp x)
		  (not (= x 0))
		  (rationalp y)
		  (not (= y 0)))
	     (equal (expo (* x y))
		    (if (< (* (sig x) (sig y)) 2)
			(+ (expo x) (expo y))
		      (+ 1 (expo x) (expo y)))))
  :enable expe-prod)

(defruled expo-prod-lower
    (implies (and (rationalp x)
		  (not (= x 0))
		  (rationalp y)
		  (not (= y 0)))
	     (<= (+ (expo x) (expo y)) (expo (* x y))))
  :enable expe-prod-lower
  :rule-classes :linear)

(defruled expo-prod-upper
    (implies (and (rationalp x)
		  (not (= x 0))
		  (rationalp y)
		  (not (= y 0)))
	     (>= (+ (expo x) (expo y) 1) (expo (* x y))))
  :enable expe-prod-upper
  :rule-classes :linear)

(defruled sig-prod
    (implies (and (rationalp x)
		  (not (= x 0))
		  (rationalp y)
		  (not (= y 0)))
	     (equal (sig (* x y))
		    (if (< (* (sig x) (sig y)) 2)
			(* (sig x) (sig y))
		      (* 1/2 (sig x) (sig y)))))
  :enable sigm-prod)

(defruled expo-fl
  (implies (and (rationalp x)
                (>= x 1))
	   (equal (expo (fl x)) (expo x)))
  :enable expe-fl)

; There is no radix-aware version:
; Let x=2 y=9 b=10
; (expe x b) 0
; (expe y b) 0
; (logior x y) 11
; (expe (logior x y) b) 1
;
(defruled expo-logior
  (implies (and (natp x)
                (natp y)
		(<= (expo x) (expo y)))
	   (equal (expo (logior x y))
	          (expo y)))
  :enable bvecp
  :nonlinearp t
  :use (expo-upper-bound
        (:instance expo-upper-bound (x y))
        (:instance expo-lower-bound (x y))
        (:instance logior-bvecp (n (1+ (expo y))))
        (:instance expo<= (x (logior x y)) (n (expo y)))
        (:instance expo>= (x (logior x y)) (n (expo y)))))


;;;**********************************************************************
;;;                 Integer Significand with its corresponding Exponent
;;;**********************************************************************

; (defund expq (x p b) ... )

(defrule expq-type
  (implies
    (integerp p)
    (integerp (expq x p b)))
  :enable expq
  :rule-classes :type-prescription)

(local (defrule expq-x=0
  (equal (expq 0 p b) (- 1 p))
  :enable expq))

(local (defrule expq-x-default
  (implies (not (real/rationalp x))
           (equal (expq x p b) (- 1 p)))
  :enable expq))

(local (defrule expq-b-default
  (implies (not (radixp b))
           (equal (expq x p b) (- 1 p)))
  :enable expq))

; (defund sigc (x p b) ... )

(local (defrule sigc-x=0
  (equal (sigc 0 p b) 0)
  :enable sigc))

(local (defrule sigc-x-default
  (implies (not (real/rationalp x))
           (equal (sigc x p b) 0))
  :enable sigc))

(local (defrule sigc-p-default
  (implies
    (not (integerp p))
    (equal (sigc x p b)
           (if (acl2-numberp p)
               (sigm x b)
               (/ (sigm x b) b))))
  :enable sigc))

(local (defrule sigc-b-default
  (implies (not (radixp b))
           (equal (sigc x p b) 0))
  :enable sigc))

(defrule expq-minus
  (equal (expq (- x) p b) (expq x p b))
  :enable expq)

(defrule sigc-minus
  (equal (sigc (- x) p b) (sigc x p b))
  :enable sigc)

(defruled expq-lower-bound
  (implies (and (real/rationalp x)
                (not (equal x 0))
                (radixp b))
           (<= (expt b (+ -1 p (expq x p b))) (abs x)))
  :enable (expq expe-lower-bound)
  :disable abs
  :rule-classes :linear)

(defruled expq-upper-bound
    (implies (and (real/rationalp x)
                  (radixp b))
	     (< (abs x) (expt b (+ p (expq x p b)))))
  :enable (expq expe-upper-bound)
  :rule-classes :linear)

(defrule expq-unique
  (implies (and (<= (expt b (+ -1 n p)) (abs x))
                (< (abs x) (expt b (+ n p)))
                (integerp n)
                (real/rationalp x)
                (radixp b))
           (equal n (expq x p b)))
  :enable expq
  :use (:instance expe-unique
         (n (+ -1 n p)))
  :rule-classes ())

(defrule fp-rep-qc
  (implies (and (real/rationalp x)
                (integerp p)
                (radixp b))
           (equal x (* (signum x) (sigc x p b) (expt b (expq x p b)))))
  :enable (sigc expq)
  :use fp-rep-em
  :rule-classes ())

(defrule fp-abs-qc
  (implies (and (real/rationalp x)
                (integerp p)
                (radixp b))
           (equal (abs x) (* (sigc x p b) (expt b (expq x p b)))))
  :enable (sigc expq)
  :use fp-abs-em
  :rule-classes ())

(defruled expq>=
    (implies (and (<= (expt b (+ -1 n p)) x)
                  (real/rationalp x)
		  (integerp n)
                  (integerp p)
                  (radixp b))
	     (<= n (expq x p b)))
  :enable (expq expe>=)
  :rule-classes :linear)

(defruled expq<=
    (implies (and (< x (expt b (+ n p)))
                  (< 0 x)
                  (real/rationalp x)
		  (integerp n)
                  (integerp p)
                  (radixp b))
	     (<= (expq x p b) n))
  :enable (expq)
  :use (:instance expe<=
         (n (+ -1 n p)))
  :rule-classes :linear)

(defrule expq-b**n
    (implies (and (integerp n)
                  (radixp b))
	     (equal (expq (expt b n) p b)
		    (+ 1 n (- p))))
  :enable expq)

(defruled expq-monotone
  (implies (and (<= (abs x) (abs y))
                (case-split (real/rationalp x))
                (case-split (not (equal x 0)))
                (case-split (real/rationalp y))
                (radixp b))
           (<= (expq x p b) (expq y p b)))
  :enable (expq expe-monotone)
  :disable abs)

(defruled dvecp-expq
    (implies (and (case-split (natp x))
                  (case-split (radixp b)))
	     (dvecp x (+ p (expq x p b)) b))
  :enable (expq dvecp-expe))

(defruled mod-expq-2
  (implies (and (< 0 x)
                (real/rationalp x))
           (equal (mod x (expt 2 (+ -1 p (expq x p 2))))
                  (- x (expt 2 (+ -1 p (expq x p 2))))))
  :enable (expq mod-expe-2))

(defruled sigc-lower-bound
  (implies (and (real/rationalp x)
                (not (equal x 0))
                (radixp b))
           (<= (expt b (1- p)) (sigc x p b)))
  :enable sigc
  :rule-classes (:rewrite (:linear :trigger-terms ((sigc x p b)))))

(defrule sigc-type-x-nonzero
  (implies (and (real/rationalp x)
                (not (equal x 0))
                (radixp b))
           (and (real/rationalp (sigc x p b))
                (> (sigc x p b) 0)))
  :enable sigc
  :rule-classes :type-prescription)

(defruled sigc-upper-bound
  (implies (and (integerp p)
                (radixp b))
           (< (sigc x p b) (expt b p)))
  :enable (sigc sigm-upper-bound)
  :rule-classes (:rewrite (:linear :trigger-terms ((sigc x p b)))))

(defrule expq-sigc
  (implies (and (real/rationalp x)
                (not (equal x 0))
                (integerp p)
                (radixp b))
           (equal (expq (sigc x p b) p b) 0))
  :enable (sigc expq sigm)
  :cases ((and (real/rationalp x) (> x 0))
          (and (real/rationalp x) (< x 0)))
  :hints (
    ("subgoal 2" :use (:instance expe-shift
                       (n (- (expq x p b)))))
    ("subgoal 1" :use (:instance expe-shift
                        (n (- (expq x p b)))))))

(defruled sigc-self
  (implies (and (real/rationalp x)
                (integerp p)
                (radixp b)
                (<= (expt b (1- p)) x)
                (< x (expt b p)))
           (equal (sigc x p b) x))
  :enable signum
  :cases ((equal (expq x p b) 0))
  :hints (
    ("subgoal 2" :use (:instance expq-unique
                        (n 0)))
    ("subgoal 1" :use fp-rep-qc)))

(defrule sigm-sigc
  (implies (radixp b)
           (equal (sigm (sigc x p b) b)
                  (sigm x b)))
  :enable sigc
  :cases ((not (acl2-numberp p))
          (integerp p))
  :hints (
    ("subgoal 2" :use (:instance sigm-shift
                        (x (sigm x b))
                        (n -1)))
    ("subgoal 1" :use (:instance sigm-shift
                        (x (sigm x b))
                        (n (1- p))))))

(defrule sigc-sigm
  (implies (radixp b)
           (equal (sigc (sigm x b) p b)
                  (sigc x p b)))
  :enable sigc)

(defrule sigc-sigc
 (implies (radixp b)
          (equal (sigc (sigc x s b) p b)
                 (sigc x p b)))
  :disable sigm-sigc
  :cases ((equal (sigm (sigc x s b) b) (sigm x b)))
  :hints (
    ("subgoal 2" :in-theory (enable sigm-sigc))
    ("subgoal 1" :in-theory (enable sigc))))

(defrule fp-rep-qc-unique
  (implies (and (real/rationalp c)
                (<= (expt b (1- p)) c)
                (< c (expt b p))
                (integerp q)
                (= (abs x) (* c (expt b q)))
                (integerp p)
                (radixp b))
           (and (= c (sigc x p b))
                (= q (expq x p b))))
  :prep-lemmas (
    (acl2::with-arith5-nonlinear-help (defrule lemma1
      (implies
        (and
          (<= (expt b (- n)) c)
          (posp b))
        (>= (* c (expt b n)) 1))
      :rule-classes :linear))
    (acl2::with-arith5-nonlinear-help (defrule lemma2
      (implies
        (and
          (< c (expt b (- n)))
          (posp b))
        (<  (* c (expt b n)) 1))
      :rule-classes :linear)))
  :enable (sigc expq)
  :disable abs
  :use (:instance fp-rep-em-unique
         (m (/ c (expt b (- p 1))))
         (e (+ q (1- p))))
  :rule-classes ())

(defruled expq-shift
  (implies (and (real/rationalp x)
                (not (equal x 0))
                (integerp n)
                (integerp p)
                (radixp b))
           (equal (expq (* (expt b n) x) p b)
                  (+ n (expq x p b))))
  :enable (expq-lower-bound)
  :use ((:instance expq-unique
          (x (* (expt b n) x))
          (n (+ n (expq x p b))))
        expq-upper-bound))

(defruled sigc-shift
  (implies (and (integerp p)
                (radixp b))
           (equal (sigc (* x (expt b n)) p b)
                  (sigc x p b)))
  :enable (sigc expq sigm-shift))

(defruled expq-prod
  (implies (and (real/rationalp x)
                (not (= x 0))
                (real/rationalp y)
                (not (= y 0))
                (integerp p)
                (radixp b))
           (equal (expq (* x y) p b)
                  (if (< (* (sigc x p b) (sigc y p b))
                         (expt b (+ -1 (* 2 p))))
                      (+ -1 p (expq x p b) (expq y p b))
                    (+ p (expq x p b) (expq y p b)))))
  :enable (sigc expq expe-prod))

(defruled expq-prod-lower
    (implies (and (real/rationalp x)
		  (not (= x 0))
		  (real/rationalp y)
		  (not (= y 0))
                  (integerp p)
                  (radixp b))
	     (<= (+ -1 p (expq x p b) (expq y p b)) (expq (* x y) p b)))
  :use expq-prod
  :rule-classes :linear)

(defruled expq-prod-upper
    (implies (and (real/rationalp x)
		  (not (= x 0))
		  (real/rationalp y)
		  (not (= y 0))
                  (integerp p)
                  (radixp b))
	     (>= (+ p (expq x p b) (expq y p b) 1) (expq (* x y) p b)))
  :use expq-prod
  :rule-classes :linear)

(defruled sigc-prod
  (implies (and (real/rationalp x)
                (not (= x 0))
                (real/rationalp y)
                (not (= y 0))
                (integerp p)
                (radixp b))
           (equal (sigc (* x y) p b)
                  (* (expt b
                           (if (< (* (sigc x p b) (sigc y p b))
                                  (expt b (+ -1 (* 2 p))))
                               (- 1 p)
                             (- p)))
                     (sigc x p b)
                     (sigc y p b))))
  :enable (sigc expq sigm-prod))

(defruled compare-abs-qc
  (implies (and (real/rationalp x) (> x 0)
                (real/rationalp y) (> y 0)
                (integerp p)
                (radixp b))
           (equal (signum (- (abs x) (abs y)))
                  (cond ((and (= x 0) (= y 0)) 0)
                        ((= x 0) -1)
                        ((= y 0) 1)
                        ((< (expq x p b) (expq y p b)) -1)
                        ((> (expq x p b) (expq y p b)) 1)
                        ((< (sigc x p b) (sigc y p b)) -1)
                        ((> (sigc x p b) (sigc y p b)) 1)
                        (t 0))))
  :enable (expq sigc)
  :use compare-abs-em)

;;;**********************************************************************
;;;                          Exactness with Radix
;;;**********************************************************************

; (defnd exactrp (x p b) ... )

(defrule exactrp-forward
  (implies (exactrp x p b)
           (and (rationalp x)
                (integerp p)
                (radixp b)))
  :enable (exactrp sigc sigm)
  :rule-classes :forward-chaining)

(defruled exactrp-forward-p<1
  (implies (and (exactrp x p b)
                (< p 1))
           (= x 0))
  :enable (exactrp sigc-upper-bound)
  :cases ((< (sigc x p b) 1))
  :rule-classes :forward-chaining)

(defruled exactrp-forward-p<1-2
  (implies (exactrp x p b)
           (implies (< p 1) (= x 0)))
  :enable (exactrp sigc-upper-bound)
  :cases ((< (sigc x p b) 1))
  :rule-classes :forward-chaining)

(local (defrule exactrp-x=0
  (equal (exactrp 0 p b)
         (and (integerp p)
              (radixp b)))
  :enable exactrp))

(defrule exactrp-sigm
  (equal (exactrp (sigm x b) p b)
         (if (real/rationalp x)
             (exactrp x p b)
             (and (integerp p) (radixp b))))
  :enable exactrp)

(defrule exactrp-sigc
  (equal (exactrp (sigc x s b) p b)
         (if (real/rationalp x)
             (exactrp x p b)
             (and (integerp p) (radixp b))))
  :enable (exactrp sigc)
  :use (:instance sigm-shift
         (x (sigm x b))
         (n (1- (ifix s)))))

(defrule minus-exactrp
  (equal (exactrp (- x) p b)
         (exactrp (fix x) p b))
  :enable (exactrp))

(defthm exactrp-abs
  (equal (exactrp (abs x) p b)
         (exactrp x p b)))

(defruled exactrp-shift
  (implies (integerp p)
           (equal (exactrp (* (expt b k) x) p b)
                  (exactrp (fix x) p b)))
  :enable (exactrp sigc expq sigm-shift))

(defruled exactrp-<=
  (implies (and (exactrp x s b)
                (<= s p)
                (integerp p))
           (exactrp x p b))
  :prep-lemmas (
    (defrule lemma
      (implies (and (integerp m)
                    (natp n)
                    (radixp b)
                    (integerp (* x (expt b m))))
               (integerp (* x (expt b (+ n m)))))
      :enable (acl2::scatter-exponents-theory)
      :disable (acl2::gather-exponents-theory)
      :rule-classes ()))
  :enable (exactrp sigc)
  :use (:instance lemma
         (x (sigm x b))
         (m (1- s))
         (n (- p s))))

(defruled exactrp-b**n
  (equal (exactrp (expt b n) p b)
         (and (posp p)
              (radixp b)))
  :enable (exactrp sigc sigm expe))

(defrule dvecp-exactrp
  (implies (and (dvecp x p b)
                (integerp p)
                (radixp b))
           (exactrp x p b))
  :prep-lemmas (
    (defrule lemma1
      (implies (and (natp x)
                    (radixp b))
               (exactrp x (1+ (expe x b)) b))
      :enable (exactrp sigc sigm))
    (defrule lemma2
      (implies (and (< x (expt b p))
                    (natp x)
                    (posp p)
                    (radixp b))
               (<= (1+ (expe x b)) p))
      :use (:instance expe<=
             (n (1- p)))
      :rule-classes :linear))
  :enable dvecp
  :cases ((posp p))
  :hints (("subgoal 1" :use (:instance exactrp-<=
                              (s (1+ (expe x b)))))))

(defrule exactrp-prod
  (implies (and (exactrp x px b)
                (integerp px)
                (exactrp y py b)
                (integerp py))
          (exactrp (* x y) (+ px py) b))
  :prep-lemmas (
    (defrule lemma
      (implies (and
                 (integerp p)
                 (integerp n)
                 (radixp b))
               (equal (sigc x (+ p n) b)
                      (* (sigc x p b) (expt b n))))
      :enable sigc
      :rule-classes ()))
  :enable (exactrp sigc-prod)
  :use ((:instance lemma
          (x x)
          (p px)
          (n py))
        (:instance lemma
          (x y)
          (p py)
          (n px)))
  :cases ((= x 0)
          (= y 0))
  :rule-classes ())

(defrule sigc-rationalp
  (implies (and (rationalp x)
                (radixp b))
           (rationalp (sigc x p b)))
  :enable (sigc sigm)
  :rule-classes :type-prescription)

(defrule exactrp-x2
    (implies (and (rationalp x)
                  (integerp p)
		  (primep b)
		  (exactrp (* x x) (* 2 p) b))
	     (exactrp x p b))
  :prep-lemmas (
    (defrule lemma-p<=0
      (implies (and (rationalp x)
                    (<= p 0)
                    (exactrp (* x x) p b))
               (equal x 0))
      :enable exactrp-forward-p<1
      :rule-classes ())
    (defrule lemma-sigc
      (implies (and (real/rationalp x)
                    (integerp p)
                    (exactrp (* x x) (* 2 p) b))
               (or (integerp (* b (sigc x p b) (sigc x p b)))
                   (integerp (* (sigc x p b) (sigc x p b)))))
      :enable (exactrp sigc)
      :use (:instance sigm-prod (x x) (y x))
      :rule-classes ())
    (defrule divides-p-when-divides-p*p
      (implies (and (posp p) (divides (* p p) x))
               (divides p x))
      :enable (divides acl2::intp-*)
      :use (:instance acl2::intp-1
             (x (/ x (* p p)))
             (y p)))
    (defrule divides-p-n*n
      (implies (and (integerp n)
                    (primep p)
                    (divides (* p p) (* b n n))
                    (or (primep b) (= b 1)))
               (divides p (* n n)))
      :cases ((divides p (* b n n)))
      :hints (
        ("subgoal 1" :cases ((= p b)))
        ("subgoal 1.2" :cases ((divides p b)))
        ("subgoal 1.2.2" :use (:instance euclid
                               (a b)
                               (b (* n n))))
        ("subgoal 1.2.1" :use (:instance primep-no-divisor
                                (p b)
                                (d p)))
        ("subgoal 1.1" :in-theory (enable divides)))
      :rule-classes ())
    (defrule divides-p-n
      (implies (and (integerp n)
                    (primep p)
                    (divides (* p p) (* b n n))
                    (or (primep b) (= b 1)))
               (divides p n))
      :use (divides-p-n*n
            (:instance euclid (a n) (b n)))
      :rule-classes ())
    (defrule kkkk
      (implies (and (posp p)
                    (posp d)
                    (divides p d)
                    (integerp (* b (/ n d) (/ n d))))
        (divides (* p p) (* b n n)))
     :enable (divides acl2::intp-*)
     :use ((:instance acl2::intp-1
             (x (/ d p))
             (y (/ d p)))
           (:instance acl2::intp-1
             (x (* (/ d p) (/ d p)))
             (y (* b (/ n d) (/ n d))))))
    (defrule ttt
      (implies (and (integerp n)
                    (posp d)
                    (primep p)
                    (divides p d)
                    (integerp (* b (/ n d) (/ n d)))
                    (or (primep b) (= b 1)))
               (divides p n))
      :use (divides-p-n kkkk))
    (defrule least-divisor-denominator
      (implies (and (rationalp c)
                    (not (integerp c)))
               (and (primep (least-divisor 2 (denominator c)))
                    (divides (least-divisor 2 (denominator c))
                             (denominator c))
                    (not (divides (least-divisor 2 (denominator c))
                                  (numerator c)))))
      :enable divides
      :use ((:instance primep-least-divisor
              (n (denominator c)))
            (:instance least-divisor-divides
              (k 2)
              (n (denominator c)))
            (:instance lowest-terms
             (x c)
             (n (least-divisor 2 (denominator c)))
             (r (/ (numerator c) (least-divisor 2 (denominator c))))
             (q (/ (denominator c) (least-divisor 2 (denominator c)))))))
    (defrule lemma2
      (implies (and (rationalp c)
                    (integerp (* b c c))
                    (or (primep b) (= b 1)))
               (integerp c))
      :use (least-divisor-denominator
            (:instance ttt
              (n (numerator c))
              (d (denominator c))
              (p (least-divisor 2 (denominator c))))))
    (defrule lemma3
      (implies (and (rationalp x)
                    (integerp p)
                    (primep b)
                    (exactrp (* x x) (* 2 p) b))
               (integerp (sigc x p b)))
      :use (lemma-sigc
            (:instance lemma2
              (c (sigc x p b))
              (b 1))
            (:instance lemma2
              (c (sigc x p b))
              (b b)))))
  :cases ((= x 0) (not (posp p)))
  :hints (
     ("subgoal 3" :in-theory (enable exactrp)
                  :use lemma3)
     ("subgoal 1" :use (:instance lemma-p<=0 (p (* 2 p)))))
  :rule-classes ())
#|
(defthm exactp-factors
  (implies (and (real/rationalp x)
                (real/rationalp y)
                (integerp k)
                (integerp n)
                (not (zerop x))
                (not (zerop y))
                (exactrp x k 2)
                (exactrp y k 2)
                (exactrp (* x y) n 2))
           (exactrp x n 2))
  :rule-classes ())
|#
(defrule exact-digits-1
  (implies (and (acl2-numberp x)
                (integerp k)
                (radixp b))
           (equal (integerp (/ x (expt b k)))
                  (exactrp x (+ 1 (- k) (expe x b)) b)))
  :enable (exactrp sigc sigm)
  :rule-classes ())

(defrule exact-digits-2
  (implies (and (<= 0 x)
                (integerp k)
                (radixp b))
           (equal (integerp (/ x (expt b k)))
		  (equal (digits x (expe x b) k b)
                         (/ x (expt b k)))))
  :enable (digits expe-upper-bound)
  :rule-classes ())

(defrule exact-digits-3
  (implies (and (integerp x)
                (radixp b))
           (equal (integerp (/ x (expt b k)))
		  (equal (digits x (1- k) 0 b)
                         0)))
  :enable digits
  :cases ((integerp (/ x (expt b k))))
  :hints (("subgoal 2" :cases ((posp k))))
  :rule-classes ())

(defrule exact-digit-k+1
    (implies (and (integerp k)
                  (radixp b)
		  (exactrp x (+ 1 (- k) (expe x b)) b))
	     (equal (exactrp x (+ (- k) (expe x b)) b)
                    (= (digitn x k b) 0)))
  :prep-lemmas (
    (defrule lemma
      (implies (and (integerp (* x (expt b (- k))))
                    (integerp k)
                    (radixp b))
               (equal (integerp (* x (expt b (+ -1 (- k)))))
                      (= (digitn x k b) 0)))
      :enable (digitn digits)))
  :enable (digitn digits)
  :use ((:instance exact-digits-1 (k k))
        (:instance exact-digits-1 (k (1+ k))))
  :rule-classes ())

(defrule exactrp-diff
    (implies (and (integerp k)
		  (> p k)
		  (exactrp x p b)
		  (exactrp y p b)
		  (<= (+ k (expe (- x y) b)) (expe x b))
		  (<= (+ k (expe (- x y) b)) (expe y b)))
	     (exactrp (- x y) (- p k) b))
  :prep-lemmas (
    (defrule lemma1
      (implies
         (and
           (integerp x)
           (natp n)
           (radixp b))
         (integerp (* x (expt b n))))
      :rule-classes ())
    (defrule lemma2
      (implies
         (and
           (integerp (* x (expt b m)))
           (<= m n)
           (integerp m)
           (integerp n)
           (radixp b))
         (integerp (* x (expt b n))))
      :use (:instance lemma1
             (x (* x (expt b m)))
             (n (- n m)))))
  :use (
    (:instance exact-digits-1
      (x (- x y))
      (k (+ 1 (expe (- x y) b) (- k p))))
    (:instance exact-digits-1
      (x x)
      (k (+ 1 (expe x b) (- p))))
    (:instance exact-digits-1
      (x y)
      (k (+ 1 (expe y b) (- p)))))
  :rule-classes ())

(defrule exactrp-diff-cor
  (implies (and (exactrp x p b)
                (exactrp y p b)
                (<= (abs (- x y)) (abs x))
                (<= (abs (- x y)) (abs y)))
           (exactrp (- x y) p b))
  :prep-lemmas (
    (defrule lemma
      (implies (and (real/rationalp x)
                    (real/rationalp y)
                    (radixp b)
                    (not (equal (- x y) 0))
                    (<= (abs (- x y)) (abs x))
                    (<= (abs (- x y)) (abs y)))
               (and
                 (<= (expe (- x y) b) (expe x b))
                 (<= (expe (- x y) b) (expe y b))))
      :use ((:instance expe-monotone
              (x (- x y))
              (y x))
            (:instance expe-monotone
              (x (- x y))
              (y y)))
      :disable abs
      :rule-classes :linear))
  :enable exactrp-forward-p<1
  :disable abs
  :use (:instance exactrp-diff
         (k 0))
  :cases ((= x y))
  :rule-classes ())

; (defun fpr+ (x p b) ... )

(defrule fpr+-positive
  (implies (and (<= 0 x)
                (radixp b))
           (< 0 (fpr+ x p b)))
  :rule-classes :type-prescription)

(defrule fpr+-real/rationalp
  (implies (and (real/rationalp x)
                (radixp b))
           (real/rationalp (fpr+ x p b)))
  :rule-classes :type-prescription)

(defrule fpr+-rationalp
  (implies (and (rationalp x)
                (radixp b))
           (rationalp (fpr+ x p b)))
  :rule-classes :type-prescription)

(local (defruled fpr+-rep-qc
  (implies (and (real/rationalp x)
                (> x 0)
                (posp p)
                (radixp b)
                (< (sigc x p b) (1- (expt b p))))
           (and
             (equal (expq (fpr+ x p b) p b) (expq x p b))
             (equal (sigc (fpr+ x p b) p b) (1+ (sigc x p b)))))
  :enable (signum sigc-lower-bound)
  :use (fp-rep-qc
        (:instance fp-rep-qc-unique
          (x (fpr+ x p b))
          (q (expq x p b))
          (c (1+ (sigc x p b)))))))

(local (defruled fpr+1-rep-qc
  (implies (and (real/rationalp x)
                (> x 0)
                (posp p)
                (radixp b)
                (= (sigc x p b) (1- (expt b p))))
           (and
             (equal (expq (fpr+ x p b) p b) (1+ (expq x p b)))
             (equal (sigc (fpr+ x p b) p b) (expt b (1- p)))))
  :enable signum
  :use (fp-rep-qc
        (:instance fp-rep-qc-unique
          (x (fpr+ x p b))
          (q (1+ (expq x p b)))
          (c (expt b (1- p)))))))

(defrule fpr+1
    (implies (and (> x 0)
                  (exactrp x p b))
             (exactrp (fpr+ x p b) p b))
  :enable (exactrp-forward-p<1 sigc-upper-bound
           fpr+-rep-qc fpr+1-rep-qc)
  :disable fpr+
  :cases ((and (rationalp x) (posp p)))
  :hints (("subgoal 1" :in-theory (enable exactrp)
                       :cases ((< (sigc x p b) (1- (expt b p)))
                               (= (sigc x p b) (1- (expt b p))))))
  :rule-classes())

(defrule fpr+2
    (implies (and (> x 0)
		  (> y x)
		  (exactrp x p b)
		  (exactrp y p b))
	     (>= y (fpr+ x p b)))
  :enable (exactrp-forward-p<1
           sigc-lower-bound sigc-upper-bound
           fpr+-rep-qc fpr+1-rep-qc)
  :disable fpr+
  :cases ((and (rationalp x) (posp p)))
  :hints (
    ("subgoal 1" :in-theory (enable exactrp radixp signum)
                 :use ((:instance compare-abs-qc (x x))
                       (:instance compare-abs-qc (x (fpr+ x p b))))
                 :cases ((< (sigc x p b) (1- (expt b p)))
                         (= (sigc x p b) (1- (expt b p))))))
  :rule-classes ())

(defrule fpr+expe
    (implies (and (> x 0)
                  (exactrp x p b)
                  (not (= (expe (fpr+ x p b) b) (expe x b))))
	     (equal (fpr+ x p b) (expt b (1+ (expe x b)))))
  :enable (exactrp-forward-p<1 sigc-upper-bound
           fpr+-rep-qc fpr+1-rep-qc)
  :disable fpr+
  :cases ((and (rationalp x) (posp p)))
  :hints (
    ("subgoal 1" :cases ((< (sigc x p b) (1- (expt b p)))
                         (= (sigc x p b) (1- (expt b p)))))
    ("subgoal 1.3" :in-theory(enable exactrp))
    ("subgoal 1.2" :cases ((equal (expq (fpr+ x p b) p b) (expq x p b))))
    ("subgoal 1.2.1" :in-theory (enable expq))
    ("subgoal 1.1" :cases ((equal (expq (fpr+ x p b) p b) (1+ (expq x p b))))
                   :use (:instance fp-rep-qc
                          (x (fpr+ x p b))))
    ("subgoal 1.1.1" :in-theory (enable signum expq)))
  :rule-classes ())

(defrule fpr+expq
    (implies (and (> x 0)
                  (exactrp x p b)
                  (not (= (expq (fpr+ x p b) p b) (expq x p b))))
	     (equal (fpr+ x p b) (expt b (+ p (expq x p b)))))
  :enable expq
  :disable fpr+
  :use fpr+expe
  :rule-classes ())

(defrule expe-diff-min
    (implies (and (exactrp x p b)
		  (exactrp y p b)
		  (not (= y x)))
	     (>= (expe (- y x) b)
                 (- (1+ (min (expe x b) (expe y b))) p)))
  :prep-lemmas (
    (defrule lemma0
      (implies (and (integerp x)
                    (integerp y)
                    (not (= y x))
                    (real/rationalp r)
                    (> r 0))
               (>= (abs (* r (- y x))) r))
      :cases ((>= y (1+ x))
              (<= y (1- x)))
      :rule-classes ())
    (defrule lemma
      (implies (and (real/rationalp x)
                    (real/rationalp y)
                    (integerp (/ x (expt b n)))
                    (integerp (/ y (expt b n)))
                    (not (= y x))
                    (integerp n)
                    (radixp b))
               (>= (expe (- y x) b) n))
      :use ((:instance lemma0
              (x (/ x (expt b n)))
              (y (/ y (expt b n)))
              (r (expt b n)))
            (:instance expe-monotone
              (x (expt b n))
              (y (- y x))))
      :rule-classes ()))
  :enable (exactrp-forward-p<1 expq exactrp-<=)
  :use (
    (:instance lemma (n (min (expq x p b) (expq y p b))))
    (:instance exact-digits-1 (x x) (k (min (expq x p b) (expq y p b))))
    (:instance exact-digits-1 (x y) (k (min (expq x p b) (expq y p b)))))
  :rule-classes ())

; (defun fpr- (x p b) ... )

(defrule fpr--non-negative
   (implies (and (rationalp x)
                 (> x 0)
                 (posp p)
                 (radixp b))
            (and (rationalp (fpr- x p b))
                 (< 0 (fpr- x p b))))
  :prep-lemmas (
    (defrule lemma
      (implies (and (posp p)
                    (integerp n)
                    (radixp b))
               (<= (expt b (+ 1 (- p) n)) (expt b n)))
      :rule-classes :linear))
  :enable (sigc expq sigm expe-lower-bound)
  :rule-classes :type-prescription)

(local (defruled fpr--rep-qc
  (implies (and (real/rationalp x)
                (> x 0)
                (posp p)
                (radixp b)
                (>= (sigc x p b) (1+ (expt b (1- p)))))
           (and
             (equal (expq (fpr- x p b) p b) (expq x p b))
             (equal (sigc (fpr- x p b) p b) (1- (sigc x p b)))))
  :prep-lemmas (
    (defrule lemma
      (implies (and (>= (sigc x p b) (1+ (expt b (1- p))))
                    (integerp p)
                    (radixp b))
               (not (equal x (expt b (expe x b)))))
      :enable (sigc sigm)))
  :enable (signum sigc-upper-bound)
  :use (fp-rep-qc
        (:instance fp-rep-qc-unique
          (x (fpr- x p b))
          (q (expq x p b))
          (c (1- (sigc x p b)))))))

(local (defruled fpr-1-rep-qc
  (implies (and (real/rationalp x)
                (> x 0)
                (posp p)
                (radixp b)
                (= (sigc x p b) (expt b (1- p))))
           (and
             (equal (expq (fpr- x p b) p b) (1- (expq x p b)))
             (equal (sigc (fpr- x p b) p b) (1- (expt b p)))))
  :prep-lemmas (
    (acl2::with-arith5-nonlinear-help (defrule lemma
      (implies (and (posp p)
                    (radixp b))
               (<= (1+ (expt b (1- p))) (expt b p))))))
  :enable signum
  :use (fp-rep-qc
        (:instance fp-rep-qc-unique
          (x (fpr- x p b))
          (q (1- (expq x p b)))
          (c (1- (expt b p)))))))

(defrule exactrp-fpr-
    (implies (and (> x 0)
                  (exactrp x p b))
             (exactrp (fpr- x p b) p b))
  :enable (exactrp-forward-p<1 sigc-lower-bound
           fpr--rep-qc fpr-1-rep-qc)
  :disable fpr-
  :cases ((and (rationalp x) (posp p)))
  :hints (("subgoal 1" :in-theory (enable exactrp)
                       :cases ((>= (sigc x p b) (1+ (expt b (1- p))))
                               (= (sigc x p b) (expt b (1- p))))))
  :rule-classes())

(defrule fpr+-
  (implies (and (> x 0)
                (exactrp x p b))
           (equal (fpr+ (fpr- x p b) p b)
                  x))
  :enable (signum exactrp-forward-p<1
           sigc-lower-bound sigc-upper-bound
           fpr--rep-qc fpr-1-rep-qc
           fpr+-rep-qc fpr+1-rep-qc)
  :disable (fpr+ fpr-)
  :use ((:instance fp-rep-qc (x x))
        (:instance fp-rep-qc (x (fpr+ (fpr- x p b) p b))))
  :cases ((posp p))
  :hints (
    ("subgoal 1" :cases ((>= (sigc x p b) (1+ (expt b (1- p))))
                         (= (sigc x p b) (expt b (1- p)))))
    ("subgoal 1.3" :in-theory (enable exactrp))))

(defrule fpr-+
  (implies (and (> x 0)
                (exactrp x p b))
           (equal (fpr- (fpr+ x p b) p b)
                  x))
  :enable (signum exactrp-forward-p<1
           sigc-lower-bound sigc-upper-bound
           fpr--rep-qc fpr-1-rep-qc
           fpr+-rep-qc fpr+1-rep-qc
           acl2::scatter-exponents-theory)
  :disable (fpr+ fpr- acl2::gather-exponents-theory)
  :use ((:instance fp-rep-qc (x x))
        (:instance fp-rep-qc (x (fpr- (fpr+ x p b) p b))))
  :cases ((posp p))
  :hints (
    ("subgoal 1" :cases ((< (sigc x p b) (1- (expt b p)))
                         (= (sigc x p b) (1- (expt b p)))))
    ("subgoal 1.3" :in-theory (enable exactrp))))

(defrule fpr-2
  (implies (and (> y 0)
                (> x y)
                (exactrp x p b)
                (exactrp y p b))
           (<= y (fpr- x p b)))
  :enable (exactrp-forward-p<1
           sigc-lower-bound sigc-upper-bound
           fpr--rep-qc fpr-1-rep-qc)
  :disable fpr-
  :cases ((and (rationalp x) (posp p)))
  :hints (
    ("subgoal 1" :in-theory (enable exactrp signum)
                 :use ((:instance compare-abs-qc (x x))
                       (:instance compare-abs-qc (x (fpr- x p b))))
                 :cases ((>= (sigc x p b) (1+ (expt b (1- p))))
                         (= (sigc x p b) (expt b (1- p))))))
  :rule-classes ())

(defruled expq-fpr-
   (implies (and (> x 0)
                 (not (= x (expt b (expe x b))))
                 (exactrp x p b))
            (equal (expq (fpr- x p b) p b) (expq x p b)))
  :prep-lemmas (
    (acl2::with-arith5-nonlinear++-help (defrule lemma
      (implies (and (equal (* x (expt b (- n))) 1)
                    (integerp n)
                    (radixp b))
               (equal (expt b n) x)))))
  :enable (exactrp exactrp-forward-p<1 sigc-lower-bound
           fpr--rep-qc fpr-1-rep-qc)
  :disable fpr-
  :cases ((posp p))
  :hints (
    ("subgoal 1" :cases ((>= (sigc x p b) (1+ (expt b (1- p))))
                         (= (sigc x p b) (expt b (1- p)))))
    ("subgoal 1.1" :in-theory (enable sigc sigm))))

(defruled expe-fpr-
   (implies (and (> x 0)
                 (not (= x (expt b (expe x b))))
                 (exactrp x p b))
            (equal (expe (fpr- x p b) b) (expe x b)))
  :enable expq
  :disable fpr-
  :use expq-fpr-)

;;;**********************************************************************
;;;                          Exactness
;;;**********************************************************************

; (defund exactp (x n) ... )

(local (defrule exactp-as-exactrp
  (implies (integerp p)
           (equal (exactp x p)
                  (or (not (rationalp x)) (exactrp x p 2))))
  :enable (exactp exactrp sigc)))

(defruled exactp2
    (implies (and (rationalp x)
		  (integerp n))
	     (equal (exactp x n)
		    (integerp (* x (expt 2 (- (1- n) (expo x)))))))
  :enable (exactrp sigc sigm))

(defrule exactp-sig
  (equal (exactp (sig x) n)
         (exactp x n))
  :enable exactp)

(defrule minus-exactp
  (equal (exactp (- x) n)
         (exactp x n))
  :enable exactp)

(defthm exactp-abs
  (equal (exactp (abs x) n)
         (exactp x n)))

(defruled exactp-shift
  (implies (and (rationalp x)
                (integerp k)
                (integerp n))
           (equal (exactp (* (expt 2 k) x) n)
                  (exactp x n)))
  :use (:instance exactrp-shift (p n) (b 2)))

(defruled exactp-<=
    (implies (and (exactp x m)
                  (<= m n)
                  (rationalp x)
		  (integerp n)
		  (integerp m))
	     (exactp x n))
  :enable exactrp-<=)

(defruled exactp-2**n
  (implies  (and (case-split (integerp m))
                 (case-split (> m 0)))
            (exactp (expt 2 n) m))
  :use (:instance exactrp-b**n (n (ifix n)) (p m) (b 2)))

(defrule bvecp-exactp
  (implies (bvecp x n)
           (exactp x n))
  :enable (bvecp dvecp)
  :cases ((natp n))
  :hints (("subgoal 2" :in-theory (enable exactp))))

(defrule exactp-prod
    (implies (and (rationalp x)
		  (rationalp y)
		  (integerp m)
		  (integerp n)
		  (exactp x m)
		  (exactp y n))
	     (exactp (* x y) (+ m n)))
  :use (:instance exactrp-prod (px m) (py n) (b 2))
  :rule-classes ())

(defrule exactp-x2
    (implies (and (rationalp x)
		  (integerp n)
		  (exactp (* x x) (* 2 n)))
	     (exactp x n))
  :use (:instance exactrp-x2 (p n) (b 2))
  :rule-classes ())

#|
Lemma(exactp-factors): Assume that x and y are k-exact for some k.  If xy is non-zero and p-exact, then so are x and y.

Proof: Let m and n be the smallest integers such that x' = 2^n*x and y' = 2^m*y are integers.  Thus, x' and y' are odd.
Since x, y, or x*y, respectively, is p-exact iff x', y', or x'*y' is p-exact, we may replace x and y with
x' and y'.  That is, we may assume without loss of generality that x and y are odd integers.

An odd integer z is p-exact iff |z| < 2^p.  Thus, since xy is p-exact, xy < 2^p, which implies x < 2^p and
y < 2^p, and hence x and y are p-exact.
|#
(defrule exactp-factors
  (implies (and (rationalp x)
                (rationalp y)
                (integerp k)
                (integerp n)
                (not (zerop x))
                (not (zerop y))
                (exactp x k)
                (exactp y k)
                (exactp (* x y) n))
           (exactp x n))
  :prep-lemmas (
    (defun pow2 (n)
      (if (or (zp n) (oddp n))
          0
        (1+ (pow2 (/ n 2)))))

    (defruled pow2-oddp-1
      (implies (integerp n)
               (equal (expt 2 (1- n))
                      (* 1/2 (expt 2 n))))
      :use ((:instance expt (r 2) (i n))
            (:instance expt (r 2) (i (1- n)))))

    (defrule pow2-oddp
      (implies (not (zp n))
               (and (integerp (/ n (expt 2 (pow2 n))))
                    (oddp (/ n (expt 2 (pow2 n))))))
      :rule-classes ()
      :hints (("Subgoal *1/3" :use ((:instance pow2-oddp-1 (n (- (pow2 (/ n 2)))))))
              ("Subgoal *1/2" :use ((:instance pow2-oddp-1 (n (- (pow2 (/ n 2)))))))))

    (defrule lemma-1
      (implies (and (integerp x) (integerp y))
               (integerp (* x y)))
      :rule-classes ())

    (defrule lemma-2
      (implies (and (integerp n)
                    (oddp n)
                    (not (zp k)))
               (not (integerp (/ n (expt 2 k)))))
      :rule-classes ()
      :use ((:instance pow2-oddp-1 (n k))
            (:instance lemma-1 (x (/ n (expt 2 k))) (y (expt 2 (1- k))))))

    (defrule lemma-3
      (implies (and (integerp n)
                    (integerp k)
                    (oddp n))
               (iff (integerp (* (expt 2 k) n))
                    (>= k 0)))
      :rule-classes ()
      :use (:instance lemma-2 (k (- k))))

    (defrule lemma-4
      (implies (and (integerp n)
                    (integerp k)
                    (oddp n))
               (iff (exactp n k)
                    (> k (expo n))))
      :rule-classes ()
      :enable exactp2
      :use (:instance lemma-3 (k (- (1- k) (expo n)))))

    (defrule lemma-5
      (implies (and (integerp x)
                    (integerp y)
                    (oddp x)
                    (oddp y))
               (>= (expo (* x y)) (expo x)))
      :rule-classes ()
      :use (:instance expo-monotone (y (* x y))))

    (defrule lemma-6
      (implies (integerp x)
               (iff (oddp x) (= (mod x 2) 1)))
      :rule-classes ()
      :disable fl-integerp
      :use ((:instance fl-integerp (x (/ x 2)))
            (:instance mod-def (y 2))
            (:instance mod012 (m x))))

    (defrule lemma-7
      (implies (and (integerp x)
                    (integerp y)
                    (oddp x)
                    (oddp y))
               (oddp (* x y)))
      :use (lemma-6
            (:instance lemma-6 (x y))
            (:instance lemma-6 (x (* x y)))
            (:instance mod-mod-times (n 2) (a x) (b y))))

    (defrule lemma-8
      (implies (and (integerp x)
                    (integerp y)
                    (oddp x)
                    (oddp y)
                    (integerp k)
                    (exactp (* x y) k))
               (exactp x k))
      :rule-classes ()
      :use (lemma-5
            lemma-7
            (:instance lemma-4 (n (* x y)))
            (:instance lemma-4 (n x))))

    (defrule lemma-9
      (implies (and (rationalp x)
                    (rationalp y)
                    (integerp k)
                    (integerp n)
                    (not (zerop x))
                    (not (zerop y))
                    (exactp x k)
                    (exactp y k))
               (let ((xp (/ (abs (* (expt 2 (- (1- k) (expo x))) x))
                            (expt 2 (pow2 (abs (* (expt 2 (- (1- k) (expo x))) x))))))
                     (yp (/ (abs (* (expt 2 (- (1- k) (expo y))) y))
                            (expt 2 (pow2 (abs (* (expt 2 (- (1- k) (expo y))) y)))))))
                 (and (integerp xp)
                      (oddp xp)
                      (iff (exactp x n) (exactp xp n))
                      (integerp yp)
                      (oddp yp)
                      (iff (exactp x n) (exactp xp n))
                      (iff (exactp y n) (exactp yp n))
                      (iff (exactp (* x y) n) (exactp (* xp yp) n)))))
      :rule-classes ()
      :enable exactp2
      :use (minus-exactp
            (:instance minus-exactp (x y))
            (:instance minus-exactp (x (* x y)))
            (:instance exactp-shift (x (abs x)) (k (- (1- k) (+ (expo x) (pow2 (abs (* (expt 2 (- (1- k) (expo x))) x)))))))
            (:instance exactp-shift (x (abs y)) (k (- (1- k) (+ (expo y) (pow2 (abs (* (expt 2 (- (1- k) (expo y))) y)))))))
            (:instance exactp-shift (x (abs (* x y)))
                       (k (+ (- (1- k) (+ (expo x) (pow2 (abs (* (expt 2 (- (1- k) (expo x))) x)))))
                             (- (1- k) (+ (expo y) (pow2 (abs (* (expt 2 (- (1- k) (expo y))) y))))))))
            (:instance pow2-oddp (n (abs (* (expt 2 (- (1- k) (expo x))) x))))
            (:instance pow2-oddp (n (abs (* (expt 2 (- (1- k) (expo y))) y))))))
  )
  :use (lemma-9
        (:instance lemma-8 (k n)
                   (x (/ (abs (* (expt 2 (- (1- k) (expo x))) x))
                         (expt 2 (pow2 (abs (* (expt 2 (- (1- k) (expo x))) x))))))
                   (y (/ (abs (* (expt 2 (- (1- k) (expo y))) y))
                         (expt 2 (pow2 (abs (* (expt 2 (- (1- k) (expo y))) y))))))))
  :rule-classes ())

(defrule exact-bits-1
  (implies (and (equal (expo x) (1- n))
                (rationalp x)
                (integerp k))
           (equal (integerp (/ x (expt 2 k)))
		  (exactp x (- n k))))
  :use (:instance exact-digits-1 (b 2))
  :rule-classes ())

(defrule exact-bits-2
  (implies (and (equal (expo x) (1- n))
                (rationalp x)
                (<= 0 x)
                (integerp k)
                )
           (equal (integerp (/ x (expt 2 k)))
		  (equal (bits x (1- n) k)
                         (/ x (expt 2 k)))))
  :enable (bits digits)
  :use (:instance exact-digits-2 (b 2))
  :rule-classes ())

(defrule exact-bits-3
  (implies (integerp x)
           (equal (integerp (/ x (expt 2 k)))
		  (equal (bits x (1- k) 0)
                         0)))
  :enable (bits digits)
  :use (:instance exact-digits-3 (b 2))
  :rule-classes ())

(defrule exact-k+1
    (implies (and (natp n)
		  (natp x)
		  (= (expo x) (1- n))
		  (natp k)
		  (< k (1- n))
		  (exactp x (- n k)))
	     (iff (exactp x (1- (- n k)))
		  (= (bitn x k) 0)))
  :enable (bitn bits digitn digits)
  :use (:instance exact-digit-k+1 (b 2))
  :rule-classes ())

(defrule exactp-diff
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
  :use (:instance exactrp-diff (p n) (b 2))
  :rule-classes ())

(defrule exactp-diff-cor
    (implies (and (rationalp x)
		  (rationalp y)
		  (integerp n)
		  (> n 0)
		  (exactp x n)
		  (exactp y n)
		  (<= (abs (- x y)) (abs x))
		  (<= (abs (- x y)) (abs y)))
	     (exactp (- x y) n))
  :use (:instance exactrp-diff-cor (p n) (b 2))
  :rule-classes ())

; (defun fp+ (x n) ... )

(defthm fp+-positive
  (implies (<= 0 x)
           (< 0 (fp+ x n)))
  :rule-classes :type-prescription)

(local (defrule fp+-as-fpr+
  (implies (and (rationalp x)
                (integerp n))
           (equal (fp+ x n) (fpr+ x n 2)))
  :enable expq))

(defrule fp+1
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0)
		  (exactp x n))
	     (exactp (fp+ x n) n))
  :use (:instance fpr+1 (p n) (b 2))
  :rule-classes ())

(defrule fp+2
    (implies (and (rationalp x)
		  (> x 0)
		  (rationalp y)
		  (> y x)
		  (integerp n)
		  (> n 0)
		  (exactp x n)
		  (exactp y n))
	     (>= y (fp+ x n)))
  :use (:instance fpr+2 (p n) (b 2))
  :rule-classes ())

(defrule fp+expo
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0)
		  (exactp x n)
  		  (not (= (expo (fp+ x n)) (expo x))))
	     (equal (fp+ x n) (expt 2 (1+ (expo x)))))
  :use (:instance fpr+expe (p n) (b 2))
  :rule-classes ())

(defrule expo-diff-min
    (implies (and (rationalp x)
		  (rationalp y)
		  (integerp n)
		  (> n 0)
		  (exactp x n)
		  (exactp y n)
		  (not (= y x)))
	     (>= (expo (- y x)) (- (1+ (min (expo x) (expo y))) n)))
  :use (:instance expe-diff-min (p n) (b 2))
  :rule-classes ())

; (defun fp- (x n) ... )

(local (defrule fp--as-fpr-
  (implies (and (rationalp x)
                (integerp n))
           (equal (fp- x n) (fpr- x n 2)))
  :enable expq))

(defrule fp--non-negative
   (implies (and (rationalp x)
                 (integerp n)
                 (> n 0)
                 (> x 0))
            (and (rationalp (fp- x n))
                 (< 0 (fp- x n))))
   :use (:instance fpr--non-negative (p n) (b 2))
   :rule-classes :type-prescription)

(defrule exactp-fp-
  (implies (and (rationalp x)
                (> x 0)
                (integerp n)
                (> n 0)
                (exactp x n))
           (exactp (fp- x n) n))
  :use (:instance exactrp-fpr- (p n) (b 2)))

(defrule fp+-
  (implies (and (rationalp x)
                (> x 0)
                (integerp n)
                (> n 0)
                (exactp x n))
           (equal (fp+ (fp- x n) n)
                  x))
  :use (:instance fpr+- (p n) (b 2)))

(defrule fp-+
  (implies (and (rationalp x)
                (> x 0)
                (integerp n)
                (> n 0)
                (exactp x n))
           (equal (fp- (fp+ x n) n)
                  x))
  :use (:instance fpr-+ (p n) (b 2)))

(defrule fp-2
  (implies (and (rationalp x)
                (rationalp y)
                (> y 0)
                (> x y)
                (integerp n)
                (> n 0)
                (exactp x n)
                (exactp y n))
           (<= y (fp- x n)))
  :use (:instance fpr-2 (p n) (b 2))
  :rule-classes ())

(defruled expo-fp-
   (implies (and (rationalp x)
                 (> x 0)
                 (not (= x (expt 2 (expo x))))
                 (integerp n)
                 (> n 0)
                 (exactp x n))
            (equal (expo (fp- x n)) (expo x)))
  :use (:instance expe-fpr- (p n) (b 2)))

