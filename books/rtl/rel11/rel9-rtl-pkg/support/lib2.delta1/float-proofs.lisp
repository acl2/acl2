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

(include-book "log")

(local (include-book "float-new"))


(local
 (defthm bits-is-bits_alt
   (equal (bits x i j)
          (bits_alt x i j))
   :hints (("Goal" :in-theory (e/d (bits_alt bits) ())))))

(local
 (defthm bitn-is-bitn_alt
   (equal (bitn x n)
          (bitn_alt x n))
   :hints (("Goal" :in-theory (e/d (bitn_alt bitn) ())))))

(local
 (defthm binary-cat_alt-is-binary-cat
   (equal (binary-cat x m y n)
          (binary-cat_alt x m y n))
   :hints (("Goal" :in-theory (e/d (binary-cat_alt binary-cat) ())))))

(local
 (defthm mulcat_alt-is-mulcat
   (equal (mulcat l n x)
          (mulcat_alt l n x))
   :hints (("Goal" :in-theory (e/d (mulcat_alt mulcat) ())))))


;;;;


;;;**********************************************************************
;;;                 Sign, Significand, and Exponent
;;;**********************************************************************


(defund sgn (x)
  (declare (xargs :guard t))
  (if (or (not (rationalp x)) (equal x 0))
      0
    (if (< x 0) -1 +1)))


(defund expo (x)
  (declare (xargs :guard t
                  :measure (:? x)))
  (cond ((or (not (rationalp x)) (equal x 0)) 0)
	((< x 0) (expo (- x)))
	((< x 1) (1- (expo (* 2 x))))
	((< x 2) 0)
	(t (1+ (expo (/ x 2))))))


(defund sig (x)
  (declare (xargs :guard t))
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




(defthm exact-bits-1
  (implies (and (equal (expo x) (1- n))
                (rationalp x)
                (integerp k))
           (equal (integerp (/ x (expt 2 k)))
		  (exactp x (- n k))))
  :rule-classes ()
  :hints (("Goal" :use exact-bits_alt-1)))


(defthm exact-bits-2
  (implies (and (equal (expo x) (1- n))
                (rationalp x)
                (<= 0 x)
                (integerp k)
                )
           (equal (integerp (/ x (expt 2 k)))
		  (equal (bits x (1- n) k)
                         (/ x (expt 2 k)))))
  :rule-classes ()
  :hints (("Goal" :use exact-bits_alt-2)))


(defthm exact-bits-3
  (implies (integerp x)
           (equal (integerp (/ x (expt 2 k)))
		  (equal (bits x (1- k) 0)
                         0)))
  :rule-classes ()
  :hints (("Goal" :use exact-bits_alt-3)))



(defthm exact-k+1
    (implies (and (natp n)
		  (natp x)
		  (= (expo x) (1- n))
		  (natp k)
		  (< k (1- n))
		  (exactp x (- n k)))
	     (iff (exactp x (1- (- n k)))
		  (= (bitn x k) 0)))
  :rule-classes ()
  :hints (("Goal" :use exact-k+1_alt)))


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


(defund esgnf  (x p q) (bitn x (+ p q)))

(local
 (defthm esgnf-is-esgnf_alt
   (equal (esgnf x p q)
          (esgnf_alt x p q))
   :hints (("Goal" :in-theory (e/d (esgnf esgnf_alt) ())))))


(defund eexpof (x p q) (bits x (1- (+ p q)) p))


(local
 (defthm eexpof-is-eexpof_alt
   (equal (eexpof x p q)
          (eexpof_alt x p q))
   :hints (("Goal" :in-theory (e/d (eexpof eexpof_alt) ())))))



(defund esigf  (x p)   (bits x (1- p) 0))


(local
 (defthm esigf-is-esigf_alt
   (equal (esigf x p)
          (esigf_alt x p))
   :hints (("Goal" :in-theory (e/d (esigf esigf_alt) ())))))



(defund bias (q) (- (expt 2 (- q 1)) 1) )

(defthm bias-non-negative-integerp-type-prescription
  (implies (and (case-split (integerp q))
                (case-split (< 0 q)))
           (and (integerp (bias q))
                (>= (bias q) 0)))
  :rule-classes :type-prescription)


(defund edecode (x p q)
  (* (if (= (esgnf x p q) 0) 1 -1)
     (esigf x p)
     (expt 2 (+ 1 (- p) (eexpof x p q) (- (bias q))))))


(local
 (defthm edecode-is-edecode_alt
   (equal (edecode x p q)
          (edecode_alt x p q))
   :hints (("Goal" :in-theory (e/d (edecode
                                    edecode_alt) ())))))


(defun isgnf (x p q) (bitn x (1- (+ p q))))

(local
 (defthm isgnf-is-isgn_alt
   (equal (isgnf x p q)
          (isgnf_alt x p q))
   :hints (("Goal" :in-theory (e/d (isgnf_alt isgnf) ())))))



(defun iexpof (x p q) (bits x (- (+ p q) 2) (1- p)))


(local
 (defthm iexpof-is-iexpo_alt
   (equal (iexpof x p q)
          (iexpof_alt x p q))
   :hints (("Goal" :in-theory (e/d (iexpof_alt iexpof) ())))))



(defun isigf (x p) (bits x (- p 2) 0))

(local
 (defthm isigf-is-isigf_alt
   (equal (isigf x p)
          (isigf_alt x p))
   :hints (("Goal" :in-theory (e/d (isigf_alt isigf) ())))))



(defund nencodingp (x p q)
  (and (bvecp x (+ p q))
       (< 0 (iexpof x p q))
       (< (iexpof x p q) (- (expt 2 q) 1))))


(local
 (defthm nencodingp-is-nencoding_alt
   (equal (nencodingp x p q)
          (nencodingp_alt x p q))
   :hints (("Goal" :in-theory (e/d (nencodingp_alt nencodingp) ())))))



(defund ndecode (x p q)
  (* (if (= (isgnf x p q) 0) 1 -1)
     (+ (expt 2 (- (iexpof x p q) (bias q)))
        (* (isigf x p)
           (expt 2 (+ 1 (iexpof x p q) (- (bias q)) (- p)))))))


(local
 (defthm ndecode-is-ndecode_alt
   (equal (ndecode x p q)
          (ndecode_alt x p q))
   :hints (("Goal" :in-theory (e/d (ndecode_alt ndecode) ())))))

(defthmd sgn-ndecode
    (implies (and (rationalp x)
		  (>= x 0)
		  (integerp p)
		  (> p 1)
		  (integerp q)
		  (> q 0))
	     (equal (sgn (ndecode x p q))
		    (if (= (isgnf x p q) 0) 1 -1)))
    :hints (("Goal" :use sgn-ndecode_alt)))


(defthmd expo-ndecode
    (implies (and (nencodingp x p q)
		  (integerp p)
		  (> p 1)
		  (integerp q)
		  (> q 0))
	     (equal (expo (ndecode x p q))
		    (- (iexpof x p q) (bias q))))
    :hints (("Goal" :use expo-ndecode_alt)))


(defthmd sig-ndecode
    (implies (and (nencodingp x p q)
		  (integerp p)
		  (> p 1)
		  (integerp q)
		  (> q 0))
	     (equal (sig (ndecode x p q))
		    (+ 1 (/ (isigf x p) (expt 2 (- p 1))))))
    :hints (("Goal" :use sig-ndecode_alt)))



(defund nrepp (x p q)
  (and (rationalp x)
       (not (= x 0))
       (< 0 (+ (expo x) (bias q)))
       (< (+ (expo x) (bias q)) (- (expt 2 q) 1))
       (exactp x p)))



(defund nencode (x p q)
  (cat (cat (if (= (sgn x) 1) 0 1)
	    1
            (+ (expo x) (bias q))
            q)
       (1+ q)
       (* (- (sig x) 1) (expt 2 (- p 1)))
       (- p 1)))

(local
 (defthm nencode-is-nencode_alt
   (equal (nencode x p q)
          (nencode_alt x p q))
   :hints (("Goal" :in-theory (e/d (nencode_alt nencode) ())))))


(defthm bvecp-nencode
  (implies (and (equal k (+ p q))
                (natp p)
                (natp q))
           (bvecp (nencode x p q) k))
   :hints (("Goal" :use bvecp-nencode_alt)))

(defthmd nrepp-ndecode
    (implies (and (nencodingp x p q)
		  (integerp p)
		  (> p 1)
		  (integerp q)
		  (> q 0))
	     (nrepp (ndecode x p q) p q))
   :hints (("Goal" :use nrepp-ndecode_alt)))



(defthmd nencode-ndecode
    (implies (and (nencodingp x p q)
		  (integerp p)
		  (> p 1)
		  (integerp q)
		  (> q 0))
	     (equal (nencode (ndecode x p q) p q)
		    x))
   :hints (("Goal" :use nencode_alt-ndecode_alt)))


(defthmd nencodingp-nencode
    (implies (and (nrepp x p q)
                  (integerp p)
                  (> p 1)
                  (integerp q)
                  (> q 0))
             (nencodingp (nencode x p q) p q))
   :hints (("Goal" :use nencodingp_alt-nencode_alt)))


(defthmd ndecode-nencode
    (implies (and (nrepp x p q)
		  (integerp p)
		  (> p 1)
		  (integerp q)
		  (> q 0))
	     (equal (ndecode (nencode x p q) p q)
		    x))
   :hints (("Goal" :use ndecode_alt-nencode_alt)))


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


(defund dencodingp (x p q)
  (and (bvecp x (+ p q))
       (= (iexpof x p q) 0)
       (not (= (isigf x p) 0))))

(local
 (defthm dencodingp-is-dencodingp_alt
   (equal (dencodingp x p q)
          (dencodingp_alt x p q))
   :hints (("Goal" :in-theory (e/d (dencodingp
                                    dencodingp_alt) ())))))



(defund ddecode (x p q)
  (* (if (= (isgnf x p q) 0) 1 -1)
     (isigf x p)
     (expt 2 (+ 2 (- (bias q)) (- p)))))

(local
 (defthm ddecode-is-ddecode_alt
   (equal (ddecode x p q)
          (ddecode_alt x p q))
   :hints (("Goal" :in-theory (e/d (ddecode_alt
                                    ddecode) ())))))



(defthmd sgn-ddecode
    (implies (and (dencodingp x p q)
		  (integerp p)
		  (> p 1)
		  (integerp q)
		  (> q 0))
	     (equal (sgn (ddecode x p q))
		    (if (= (isgnf x p q) 0) 1 -1)))
    :hints (("Goal" :use sgn-ddecode_alt)))



(defthmd expo-ddecode
    (implies (and (dencodingp x p q)
		  (integerp p)
		  (> p 1)
		  (integerp q)
		  (> q 0))
	     (equal (expo (ddecode x p q))
		    (+ 2 (- p) (- (bias q)) (expo (isigf x p)))))
    :hints (("Goal" :use expo-ddecode_alt)))


(defthmd sig-ddecode
    (implies (and (dencodingp x p q)
		  (integerp p)
		  (> p 1)
		  (integerp q)
		  (> q 0))
	     (equal (sig (ddecode x p q))
		    (sig (isigf x p))))
    :hints (("Goal" :use sig-ddecode_alt)))


(defund drepp (x p q)
  (and (rationalp x)
       (not (= x 0))
       (<= (- 2 p) (+ (expo x) (bias q)))
       (<= (+ (expo x) (bias q)) 0)
       ;number of bits available in the sig field = p - 1 - ( - bias - expo(r))
       (exactp x (+ -2 p (expt 2 (- q 1)) (expo x)))))


(defund dencode (x p q)
  (cat (cat (if (= (sgn x) 1) 0 1)
	    1
            0
            q)
       (1+ q)
       (* (sig x) (expt 2 (+ -2 p (expo x) (bias q))))
       (- p 1)))


(local
 (defthm dencode-is-dencode_alt
   (equal (dencode x p q)
          (dencode_alt x p q))
   :hints (("Goal" :in-theory (e/d (dencode_alt dencode) ())))))


(defthmd drepp-ddecode
    (implies (and (dencodingp x p q)
		  (integerp p)
		  (> p 1)
		  (integerp q)
		  (> q 0))
	     (drepp (ddecode x p q) p q))
    :hints (("Goal" :use drepp-ddecode_alt)))


(defthmd dencode-ddecode
    (implies (and (dencodingp x p q)
		  (integerp p)
		  (> p 1)
		  (integerp q)
		  (> q 0))
	     (equal (dencode (ddecode x p q) p q)
		    x))
    :hints (("Goal" :use dencode_alt-ddecode_alt)))


(defthmd dencodingp-dencode
    (implies (and (drepp x p q)
		  (integerp p)
		  (integerp q)
		  (> q 0))
	     (dencodingp (dencode x p q) p q))
    :hints (("Goal" :use dencodingp_alt-dencode_alt)))


(defthmd ddecode-dencode
    (implies (and (drepp x p q)
		  (integerp p)
		  (> p 1)
		  (integerp q)
		  (> q 0))
	     (equal (ddecode (dencode x p q) p q)
		    x))
    :hints (("Goal" :use ddecode_alt-dencode_alt)))


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
