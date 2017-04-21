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

(in-package "RTL")

(set-enforce-redundancy t)

(include-book "log-new")

(local (include-book "float-new-proofs"))

(set-inhibit-warnings "theory") ; avoid warning in the next event
(local (in-theory nil))


;;;**********************************************************************
;;;                 Sign, Significand, and Exponent
;;;**********************************************************************


(defund sgn (x)
  (declare (xargs :guard t))
  (if (or (not (rationalp x)) (equal x 0))
      0
    (if (< x 0) -1 +1)))


(defnd expo (x)
  (declare (xargs :measure (:? x)
                  :verify-guards nil))
  (mbe
   :logic
   (cond ((or (not (rationalp x)) (equal x 0)) 0)
         ((< x 0) (expo (- x)))
         ((< x 1) (1- (expo (* 2 x))))
         ((< x 2) 0)
         (t (1+ (expo (/ x 2)))))
   :exec
   (if (rationalp x)
       (let* ((n (abs (numerator x)))
              (d (denominator x))
              (ln (integer-length n))
              (ld (integer-length d))
              (l (- ln ld)))
         (if (>= ln ld)
             (if (>= (ash n (- l)) d) l (1- l))
           (if (> ln 1)
               (if (> n (ash d l)) l (1- l))
             (- (integer-length (1- d))))))
     0)))


(defund sig (x)
  (declare (xargs :guard t
                  :verify-guards nil))
  (if (rationalp x)
      (if (< x 0)
          (- (* x (expt 2 (- (expo x)))))
        (* x (expt 2 (- (expo x)))))
    0))

(defthmd expo-lower-bound
    (implies (and (rationalp x)
		  (not (equal x 0)))
	     (<= (expt 2 (expo x)) (abs x)))
  :rule-classes :linear)

(defthmd expo-upper-bound
    (implies (and (rationalp x))
	     (< (abs x) (expt 2 (1+ (expo x)))))
  :rule-classes :linear)

(defthm expo-unique
  (implies (and (<= (expt 2 n) (abs x))
                (< (abs x) (expt 2 (1+ n)))
                (rationalp x)
                (integerp n))
           (equal n (expo x)))
  :rule-classes ())


(defthm fp-rep
    (implies (rationalp x)
	     (equal x (* (sgn x) (sig x) (expt 2 (expo x)))))
  :rule-classes ())


(defthm fp-abs
    (implies (rationalp x)
	     (equal (abs x) (* (sig x) (expt 2 (expo x)))))
  :rule-classes ())


(defthmd expo>=
    (implies (and (<= (expt 2 n) x)
                  (rationalp x)
		  (integerp n))
	     (<= n (expo x)))
  :rule-classes :linear)


(defthmd expo<=
    (implies (and (< x (* 2 (expt 2 n)))
                  (< 0 x)
                  (rationalp x)
		  (integerp n))
	     (<= (expo x) n))
  :rule-classes :linear)


(defthm expo-2**n
    (implies (integerp n)
	     (equal (expo (expt 2 n))
		    n)))


(defthmd expo-monotone
  (implies (and (<= (abs x) (abs y))
                (case-split (rationalp x))
                (case-split (not (equal x 0)))
                (case-split (rationalp y)))
           (<= (expo x) (expo y)))
  :rule-classes :linear)


(defthmd bvecp-expo
    (implies (case-split (natp x))
	     (bvecp x (1+ (expo x)))))


(defthmd mod-expo
  (implies (and (< 0 x)
                (rationalp x))
           (equal (mod x (expt 2 (expo x)))
                  (- x (expt 2 (expo x))))))


(defthmd sig-lower-bound
  (implies (and (rationalp x)
                (not (equal x 0)))
           (<= 1 (sig x)))
  :rule-classes (:rewrite :linear))


(defthmd sig-upper-bound
  (< (sig x) 2)
  :rule-classes (:rewrite :linear))


(defthm already-sig
  (implies (and (rationalp x)
                (<= 1 x)
                (< x 2))
           (= (sig x) x)))


(defthm sig-sig
    (equal (sig (sig x))
	   (sig x)))


(defthm fp-rep-unique
    (implies (and (rationalp x)
		  (rationalp m)
		  (<= 1 m)
		  (< m 2)
		  (integerp e)
		  (= (abs x) (* m (expt 2 e))))
	     (and (= m (sig x))
		  (= e (expo x))))
  :rule-classes ())


(defthmd sgn-minus
  (equal (sgn (* -1 x))
         (* -1 (sgn x))))


(defthmd expo-minus
  (equal (expo (* -1 x))
         (expo x)))


(defthmd sig-minus
  (equal (sig (* -1 x))
         (sig x)))


(defthmd sgn-shift
  (equal (sgn (* x (expt 2 k)))
         (sgn x)))


(defthmd expo-shift
  (implies (and (rationalp x)
                (not (equal x 0))
                (integerp n))
           (equal (expo (* (expt 2 n) x))
                  (+ n (expo x)))))


(defthmd sig-shift
  (equal (sig (* (expt 2 n) x))
         (sig x)))


(defthmd sgn-prod
  (implies (and (case-split (rationalp x))
                (case-split (rationalp y)))
           (equal (sgn (* x y))
                  (* (sgn x) (sgn y)))))


(defthmd expo-prod
    (implies (and (rationalp x)
		  (not (= x 0))
		  (rationalp y)
		  (not (= y 0)))
	     (equal (expo (* x y))
		    (if (< (* (sig x) (sig y)) 2)
			(+ (expo x) (expo y))
		      (+ 1 (expo x) (expo y))))))

(defthmd expo-prod-lower
    (implies (and (rationalp x)
		  (not (= x 0))
		  (rationalp y)
		  (not (= y 0)))
	     (<= (+ (expo x) (expo y)) (expo (* x y))))
  :rule-classes :linear)

(defthmd expo-prod-upper
    (implies (and (rationalp x)
		  (not (= x 0))
		  (rationalp y)
		  (not (= y 0)))
	     (>= (+ (expo x) (expo y) 1) (expo (* x y))))
  :rule-classes :linear)


(defthmd sig-prod
    (implies (and (rationalp x)
		  (not (= x 0))
		  (rationalp y)
		  (not (= y 0)))
	     (equal (sig (* x y))
		    (if (< (* (sig x) (sig y)) 2)
			(* (sig x) (sig y))
		      (* 1/2 (sig x) (sig y))))))

;;;**********************************************************************
;;;                          Exactness
;;;**********************************************************************


(defund exactp (x n)
  (integerp (* (sig x) (expt 2 (1- n)))))


(defthmd exactp2
    (implies (and (rationalp x)
		  (integerp n))
	     (equal (exactp x n)
		    (integerp (* x (expt 2 (- (1- n) (expo x))))))))


(defthm exactp-sig
  (equal (exactp (sig x) n)
         (exactp x n)))


(defthm exactp-minus
  (equal (exactp (* -1 x) n)
         (exactp x n)))

(defthm exact-neg
    (equal (exactp x n) (exactp (abs x) n))
  :rule-classes ())


(defthmd exactp-shift
  (implies (and (rationalp x)
                (integerp k)
                (integerp n))
           (equal (exactp (* (expt 2 k) x) n)
                  (exactp x n))))


(defthmd exactp-<=
    (implies (and (exactp x m)
                  (<= m n)
                  (rationalp x)
		  (integerp n)
		  (integerp m))
	     (exactp x n)))


(defthmd exactp-2**n
  (implies  (and (case-split (integerp m))
                 (case-split (> m 0)))
            (exactp (expt 2 n) m)))


(defthm bvecp-exactp
  (implies (bvecp x n)
           (exactp x n)))


(defthm exactp-prod
    (implies (and (rationalp x)
		  (rationalp y)
		  (integerp m)
		  (integerp n)
		  (exactp x m)
		  (exactp y n))
	     (exactp (* x y) (+ m n)))
  :rule-classes ())


(defthm exactp-x2
    (implies (and (rationalp x)
		  (integerp n)
		  (exactp (* x x) (* 2 n)))
	     (exactp x n))
  :rule-classes ())


;;;
;;; the only different part.  Fri Feb 13 12:24:43 2009
;;;


(defthm exact-bits_alt-1
  (implies (and (equal (expo x) (1- n))
                (rationalp x)
                (integerp k))
           (equal (integerp (/ x (expt 2 k)))
		  (exactp x (- n k))))
  :rule-classes ()
  :hints (("Goal" :in-theory (e/d (bits_alt-is-bits) ())
           :use ((:instance exact-bits-1)))))





(defthm exact-bits_alt-2
  (implies (and (equal (expo x) (1- n))
                (rationalp x)
                (<= 0 x)
                (integerp k)
                )
           (equal (integerp (/ x (expt 2 k)))
		  (equal (bits_alt x (1- n) k)
                         (/ x (expt 2 k)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (e/d (bits_alt-is-bits) ())
           :use ((:instance exact-bits-2)))))


(defthm exact-bits_alt-3
  (implies (integerp x)
           (equal (integerp (/ x (expt 2 k)))
		  (equal (bits_alt x (1- k) 0)
                         0)))
  :rule-classes ()
  :hints (("Goal" :in-theory (e/d (bits_alt-is-bits) ())
           :use ((:instance exact-bits-3)))))


(defthm exact-k+1_alt
    (implies (and (natp n)
		  (natp x)
		  (= (expo x) (1- n))
		  (natp k)
		  (< k (1- n))
		  (exactp x (- n k)))
	     (iff (exactp x (1- (- n k)))
		  (= (bitn_alt x k) 0)))
  :rule-classes ()
  :hints (("Goal" :in-theory (e/d (bitn_alt-is-bitn) ())
           :use ((:instance exact-k+1)))))


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
  :rule-classes ())


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
  :rule-classes ())


(defun fp+ (x n)
  (+ x (expt 2 (- (1+ (expo x)) n))))

(defthm fp+-positive
  (implies (<= 0 x)
           (< 0 (fp+ x n)))
  :rule-classes :type-prescription)


(defthm fp+1
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0)
		  (exactp x n))
	     (exactp (fp+ x n) n))
  :rule-classes ())


(defthm fp+2
    (implies (and (rationalp x)
		  (> x 0)
		  (rationalp y)
		  (> y x)
		  (integerp n)
		  (> n 0)
		  (exactp x n)
		  (exactp y n))
	     (>= y (fp+ x n)))
  :rule-classes ())


(defthm fp+expo
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0)
		  (exactp x n)
  		  (not (= (expo (fp+ x n)) (expo x))))
	     (equal (fp+ x n) (expt 2 (1+ (expo x)))))
  :rule-classes ())


(defthm expo-diff-min
    (implies (and (rationalp x)
		  (rationalp y)
		  (integerp n)
		  (> n 0)
		  (exactp x n)
		  (exactp y n)
		  (not (= y x)))
	     (>= (expo (- y x)) (- (1+ (min (expo x) (expo y))) n)))
  :rule-classes ())


(defun fp- (x n)
  (if (= x (expt 2 (expo x)))
      (- x (expt 2 (- (expo x) n)))
    (- x (expt 2 (- (1+ (expo x)) n)))))

(defthm fp--non-negative
   (implies (and (rationalp x)
                 (integerp n)
                 (> n 0)
                 (> x 0))
            (and (rationalp (fp- x n))
                 (< 0 (fp- x n))))
   :rule-classes :type-prescription)


(defthm fp-1
  (implies (and (rationalp x)
                (> x 0)
                (integerp n)
                (> n 0)
                (exactp x n))
           (exactp (fp- x n) n))
  :rule-classes ())


(defthm fp+-
  (implies (and (rationalp x)
                (> x 0)
                (integerp n)
                (> n 0)
                (exactp x n))
           (equal (fp+ (fp- x n) n)
                  x)))


(defthm fp-+
  (implies (and (rationalp x)
                (> x 0)
                (integerp n)
                (> n 0)
                (exactp x n))
           (equal (fp- (fp+ x n) n)
                  x)))


(defthm fp-2
  (implies (and (rationalp x)
                (rationalp y)
                (> y 0)
                (> x y)
                (integerp n)
                (> n 0)
                (exactp x n)
                (exactp y n))
           (<= y (fp- x n)))
  :rule-classes ())

;;;***************************************************************
;;;                 Floating-Point formats
;;;***************************************************************


(defund esgnf_alt  (x p q) (bitn_alt x (+ p q)))
(defund eexpof_alt (x p q) (bits_alt x (1- (+ p q)) p))
(defund esigf_alt  (x p)   (bits_alt x (1- p) 0))

(defund bias (q) (- (expt 2 (- q 1)) 1) )

(defthm bias-non-negative-integerp-type-prescription
  (implies (and (case-split (integerp q))
                (case-split (< 0 q)))
           (and (integerp (bias q))
                (>= (bias q) 0)))
  :rule-classes :type-prescription)


(defund edecode_alt (x p q)
  (* (if (= (esgnf_alt x p q) 0) 1 -1)
     (esigf_alt x p)
     (expt 2 (+ 1 (- p) (eexpof_alt x p q) (- (bias q))))))



(defun isgnf_alt (x p q) (bitn_alt x (1- (+ p q))))
(defun iexpof_alt (x p q) (bits_alt x (- (+ p q) 2) (1- p)))
(defun isigf_alt (x p) (bits_alt x (- p 2) 0))




(defund nencodingp_alt (x p q)
  (and (bvecp x (+ p q))
       (< 0 (iexpof_alt x p q))
       (< (iexpof_alt x p q) (- (expt 2 q) 1))))



(defund ndecode_alt (x p q)
  (* (if (= (isgnf_alt x p q) 0) 1 -1)
     (+ (expt 2 (- (iexpof_alt x p q) (bias q)))
        (* (isigf_alt x p)
           (expt 2 (+ 1 (iexpof_alt x p q) (- (bias q)) (- p)))))))


(defthmd sgn-ndecode_alt
    (implies (and (rationalp x)
		  (>= x 0)
		  (integerp p)
		  (> p 1)
		  (integerp q)
		  (> q 0))
	     (equal (sgn (ndecode_alt x p q))
		    (if (= (isgnf_alt x p q) 0) 1 -1)))
    :hints (("Goal" :in-theory (enable sgn-ndecode))))


(defthmd expo-ndecode_alt
    (implies (and (nencodingp_alt x p q)
		  (integerp p)
		  (> p 1)
		  (integerp q)
		  (> q 0))
	     (equal (expo (ndecode_alt x p q))
		    (- (iexpof_alt x p q) (bias q))))
    :hints (("Goal" :in-theory (enable expo-ndecode))))


(defthmd sig-ndecode_alt
    (implies (and (nencodingp_alt x p q)
		  (integerp p)
		  (> p 1)
		  (integerp q)
		  (> q 0))
	     (equal (sig (ndecode_alt x p q))
		    (+ 1 (/ (isigf_alt x p) (expt 2 (- p 1))))))
    :hints (("Goal" :in-theory (enable sig-ndecode))))



(defund nrepp (x p q)
  (and (rationalp x)
       (not (= x 0))
       (< 0 (+ (expo x) (bias q)))
       (< (+ (expo x) (bias q)) (- (expt 2 q) 1))
       (exactp x p)))


(defund nencode_alt (x p q)
  (cat_alt (cat_alt (if (= (sgn x) 1) 0 1)
	    1
            (+ (expo x) (bias q))
            q)
       (1+ q)
       (* (- (sig x) 1) (expt 2 (- p 1)))
       (- p 1)))



(defthm bvecp-nencode_alt
  (implies (and (equal k (+ p q))
                (natp p)
                (natp q))
           (bvecp (nencode_alt x p q) k)))

(defthmd nrepp-ndecode_alt
    (implies (and (nencodingp_alt x p q)
		  (integerp p)
		  (> p 1)
		  (integerp q)
		  (> q 0))
	     (nrepp (ndecode_alt x p q) p q))
    :hints (("Goal" :in-theory (enable nrepp-ndecode))))


(defthmd nencode_alt-ndecode_alt
    (implies (and (nencodingp_alt x p q)
		  (integerp p)
		  (> p 1)
		  (integerp q)
		  (> q 0))
	     (equal (nencode_alt (ndecode_alt x p q) p q)
		    x))
    :hints (("Goal" :in-theory (enable nencode-ndecode))))


(defthmd nencodingp_alt-nencode_alt
    (implies (and (nrepp x p q)
                  (integerp p)
                  (> p 1)
                  (integerp q)
                  (> q 0))
             (nencodingp_alt (nencode_alt x p q) p q))
    :hints (("Goal" :in-theory (enable nencodingp-nencode))))


(defthmd ndecode_alt-nencode_alt
    (implies (and (nrepp x p q)
		  (integerp p)
		  (> p 1)
		  (integerp q)
		  (> q 0))
	     (equal (ndecode_alt (nencode_alt x p q) p q)
		    x))
    :hints (("Goal" :in-theory (enable ndecode-nencode))))


(defund spn (q)
  (expt 2 (- 1 (bias q))))


(defthmd positive-spn
  (> (spn q) 0)
  :rule-classes ( :linear))


(defthmd nrepp-spn
  (implies (and (integerp p)
                (> p 0)
                (integerp q)
                (> q 1))
           (nrepp (spn q) p q)))


(defthmd smallest-spn
  (implies (and (nrepp x p q)
                (integerp p)
                (> p 0)
                (integerp q)
                (> q 1))
           (>= (abs x) (spn q)))
  :rule-classes
  ((:rewrite :match-free :once)))


(defund dencodingp_alt (x p q)
  (and (bvecp x (+ p q))
       (= (iexpof_alt x p q) 0)
       (not (= (isigf_alt x p) 0))))


(defund ddecode_alt (x p q)
  (* (if (= (isgnf_alt x p q) 0) 1 -1)
     (isigf_alt x p)
     (expt 2 (+ 2 (- (bias q)) (- p)))))



(defthmd sgn-ddecode_alt
    (implies (and (dencodingp_alt x p q)
		  (integerp p)
		  (> p 1)
		  (integerp q)
		  (> q 0))
	     (equal (sgn (ddecode_alt x p q))
		    (if (= (isgnf_alt x p q) 0) 1 -1)))
    :hints (("Goal" :in-theory (e/d (sgn-ddecode) ()))))


(defthmd expo-ddecode_alt
    (implies (and (dencodingp_alt x p q)
		  (integerp p)
		  (> p 1)
		  (integerp q)
		  (> q 0))
	     (equal (expo (ddecode_alt x p q))
		    (+ 2 (- p) (- (bias q)) (expo (isigf_alt x p)))))
    :hints (("Goal" :in-theory (e/d (expo-ddecode) ()))))


(defthmd sig-ddecode_alt
    (implies (and (dencodingp_alt x p q)
		  (integerp p)
		  (> p 1)
		  (integerp q)
		  (> q 0))
	     (equal (sig (ddecode_alt x p q))
		    (sig (isigf_alt x p))))
    :hints (("Goal" :in-theory (e/d (sig-ddecode) ()))))


(defund drepp (x p q)
  (and (rationalp x)
       (not (= x 0))
       (<= (- 2 p) (+ (expo x) (bias q)))
       (<= (+ (expo x) (bias q)) 0)
       ;number of bits_alt available in the sig field = p - 1 - ( - bias - expo(r))
       (exactp x (+ -2 p (expt 2 (- q 1)) (expo x)))))


(defund dencode_alt (x p q)
  (cat_alt (cat_alt (if (= (sgn x) 1) 0 1)
	    1
            0
            q)
       (1+ q)
       (* (sig x) (expt 2 (+ -2 p (expo x) (bias q))))
       (- p 1)))


(defthmd drepp-ddecode_alt
    (implies (and (dencodingp_alt x p q)
		  (integerp p)
		  (> p 1)
		  (integerp q)
		  (> q 0))
	     (drepp (ddecode_alt x p q) p q))
    :hints (("Goal" :in-theory (e/d (drepp-ddecode) ()))))


(defthmd dencode_alt-ddecode_alt
    (implies (and (dencodingp_alt x p q)
		  (integerp p)
		  (> p 1)
		  (integerp q)
		  (> q 0))
	     (equal (dencode_alt (ddecode_alt x p q) p q)
		    x))
    :hints (("Goal" :in-theory (e/d (dencode-ddecode) ()))))


(defthmd dencodingp_alt-dencode_alt
    (implies (and (drepp x p q)
		  (integerp p)
		  (integerp q)
		  (> q 0))
	     (dencodingp_alt (dencode_alt x p q) p q))
    :hints (("Goal" :in-theory (e/d (dencodingp-dencode) ()))))


(defthmd ddecode_alt-dencode_alt
    (implies (and (drepp x p q)
		  (integerp p)
		  (> p 1)
		  (integerp q)
		  (> q 0))
	     (equal (ddecode_alt (dencode_alt x p q) p q)
		    x))
    :hints (("Goal" :in-theory (e/d (ddecode-dencode) ()))))


(defund spd (p q)
     (expt 2 (+ 2 (- (bias q)) (- p))))


(defthm positive-spd
  (implies (and (integerp p)
                (> p 1)
                (> q 0))
           (> (spd p q) 0))
  :rule-classes :linear)


(defthmd drepp-spd
  (implies (and (integerp p)
                (> p 1)
                (integerp q)
                (> q 0))
           (drepp (spd p q) p q)))

(defthmd smallest-spd
  (implies (and (integerp p)
                (> p 1)
                (integerp q)
                (> q 0)
                (drepp r p q))
           (>= (abs r) (spd p q))))
