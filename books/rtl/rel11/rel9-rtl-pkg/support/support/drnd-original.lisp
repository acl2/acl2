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

(local (include-book "merge"))
;(include-book "ireps") ;make local?
(local (include-book "rnd"))
(local (include-book "bias"))
(local (include-book "sgn"))
(local (include-book "bits"))
(local (include-book "trunc"))
(local (include-book "away"))
(local (include-book "near"))
(local (include-book "near+"))
(local (include-book "sticky"))
(local (include-book "../../arithmetic/top"))

(local (in-theory (enable evenp))) ;yuck
(local (in-theory (disable EXPT-2-TYPE-LINEAR))) ;yuck!

;; Necessary functions:

(local ; ACL2 primitive
 (defun natp (x)
   (declare (xargs :guard t))
   (and (integerp x)
        (<= 0 x))))

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

(defnd expo (x)
  (declare (xargs :measure (expo-measure x)
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

;could redefine to divide by the power of 2 (instead of making it a negative power of 2)...
(defund sig (x)
  (declare (xargs :guard t
                  :verify-guards nil))
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

(defund exactp (x n)
;  (declare (xargs :guard (and (real/rationalp x) (integerp n))))
  (integerp (* (sig x) (expt 2 (1- n)))))

(defun fp+ (x n)
  (+ x (expt 2 (- (1+ (expo x)) n))))

(defund trunc (x n)
  (declare (xargs :guard (integerp n)
                  :verify-guards nil))
  (* (sgn x) (fl (* (expt 2 (1- n)) (sig x))) (expt 2 (- (1+ (expo x)) n))))

(defund away (x n)
  (* (sgn x) (cg (* (expt 2 (1- n)) (sig x))) (expt 2 (- (1+ (expo x)) n))))


(defund re (x)
  (- x (fl x)))

(defund near (x n)
  (let ((z (fl (* (expt 2 (1- n)) (sig x))))
	(f (re (* (expt 2 (1- n)) (sig x)))))
    (if (< f 1/2)
	(trunc x n)
      (if (> f 1/2)
	  (away x n)
	(if (evenp z)
	    (trunc x n)
	  (away x n))))))

(defund near+ (x n)
  (if (< (re (* (expt 2 (1- n)) (sig x)))
	 1/2)
      (trunc x n)
    (away x n)))

(defund sticky (x n)
  (cond ((exactp x (1- n)) x)
	(t (+ (trunc x (1- n))
              (* (sgn x) (expt 2 (1+ (- (expo x) n))))))))

(defund inf (x n)
  (if (>= x 0)
      (away x n)
    (trunc x n)))

(defund minf (x n)
  (if (>= x 0)
      (trunc x n)
    (away x n)))

(defund rnd (x mode n)
  (case mode
    (away (away x n)) ;added by eric in august, 2001
    (near+ (near+ x n))
    (trunc (trunc x n))
    (inf (inf x n))
    (minf (minf x n))
    (near (near x n))
    (otherwise 0)))

(defund IEEE-MODE-P (mode)
  (member mode '(trunc inf minf near)))

(defund common-rounding-mode-p (mode)
  (or (IEEE-mode-p mode) (equal mode 'away) (equal mode 'near+)))

(defund flip (m)
  (case m
    (inf 'minf)
    (minf 'inf)
    (t m)))

; bias of a q bit exponent field is 2^(q-1)-1
(defund bias (q) (- (expt 2 (- q 1)) 1) )



;;
;; New stuff:
;;
;; ------------------------------------------------------------------------





















;-------------------------------------------------------------------------

(defund drnd-original (x mode n k)
  (- (rnd (+ x (* (sgn x) (expt 2 (- 2 (expt 2 (1- k)))))) mode n)
     (* (sgn x) (expt 2 (- 2 (expt 2 (1- k)))))))

(defthmd drnd-original-minus
  (equal (drnd-original (* -1 x) mode n k)
         (* -1 (drnd-original x (flip mode) n k)))
  :hints (("Goal" :in-theory
           (enable drnd-original)
           :use ((:instance rnd-minus
                            (x (+ x (* (sgn x) (expt 2 (- 2 (expt 2 (1- k))))))))))))

(defthm drnd-original-0
  (equal (drnd-original 0 mode n k)
         0)
  :hints (("Goal" :in-theory (enable drnd-original))))


(local (defthm drnd-original-sticky-pos
    (implies (and (common-rounding-mode-p mode)
		  (natp n)
		  (> n 0)
		  (natp m)
		  (> m 1)
		  (natp k)
		  (> k 0)
		  (rationalp x)
		  (> x 0)
		  (<= (expo x) (- 1 (expt 2 (1- k))))
		  (<= (expo x) (- m (+ n (expt 2 (1- k))))))
	     (equal (drnd-original (sticky x m) mode n k)
		    (drnd-original x mode n k)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable sgn drnd-original rnd-sticky)
		  :use (expo-upper-bound
			expo-lower-bound
			(:instance sticky-pos (n m))
			(:instance sticky-plus-original
				   (x (expt 2 (- 2 (expt 2 (1- k)))))
				   (y x)
				   (k m)
				   (k1 (- (+ m 2) (+ (expt 2 (1- k)) (expo x))))
				   (k2 (- (+ m 2) (+ (expt 2 (1- k)) (expo x)))))
			(:instance exactp-2**n
				   (n (- 2 (expt 2 (1- k))))
				   (m (- (+ m 1) (+ (expt 2 (1- k)) (expo x))))))))))

(defthm drnd-original-sticky
  (implies (and (common-rounding-mode-p mode)
                (natp n)
                (> n 0)
                (natp m)
                (> m 1)
                (natp k)
                (> k 0)
                (rationalp x)
                (<= (expo x) (- 1 (expt 2 (1- k))))
                (<= (expo x) (- m (+ n (expt 2 (1- k))))))
           (equal (drnd-original (sticky x m) mode n k)
                  (drnd-original x mode n k)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable drnd-original-minus)
           :use (drnd-original-sticky-pos
                 (:instance drnd-original-sticky-pos (mode (flip mode)) (x (- x)))
                 ))))

(local (defthm drnd-original-bnd-1
    (implies (and (natp n)
		  (> n 0)
		  (natp k)
		  (> k 0)
		  (rationalp x)
		  (>= x (expt 2 (- 2 (expt 2 (1- k)))))
		  (< x (+ (expt 2 (- 2 (expt 2 (1- k))))
			  (expt 2 (- 3 (+ n (expt 2 (1- k))))))))
	     (equal (trunc x n)
		    (expt 2 (- 2 (expt 2 (1- k))))))
  :hints (("Goal" :in-theory (disable trunc-exactp-a trunc-exactp-c)
		  :use (trunc-exactp-a
			trunc-upper-pos
			(:instance expt-split (r 2) (j (- 1 n)) (i (- 2 (expt 2 (1- k)))))
			(:instance trunc-exactp-c (a (expt 2 (- 2 (expt 2 (1- k))))))
			(:instance exactp-2**n (n (- 2 (expt 2 (1- k)))) (m n))
			(:instance fp+2
				   (y (trunc x n))
				   (x (expt 2 (- 2 (expt 2 (1- k)))))))))))



(local (defthm drnd-original-bnd-2
    (implies (and (natp n)
		  (> n 0)
		  (natp k)
		  (> k 0)
		  (rationalp x)
		  (>= x 0)
		  (< x (expt 2 (- 3 (+ n (expt 2 (1- k)))))))
	     (equal (drnd-original x 'trunc n k)
		    0))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable sgn rnd drnd-original)
           :use trunc-0))))



(local (defthm drnd-original-bnd-3
    (implies (and (natp n)
		  (> n 0)
		  (natp k)
		  (> k 0)
		  (rationalp x)
		  (> x (expt 2 (- 2 (expt 2 (1- k)))))
		  (<= x (+ (expt 2 (- 2 (expt 2 (1- k))))
			   (expt 2 (- 3 (+ n (expt 2 (1- k))))))))
	     (equal (away x n)
		    (+ (expt 2 (- 2 (expt 2 (1- k))))
		       (expt 2 (- 3 (+ n (expt 2 (1- k))))))))
  :hints (("Goal" :in-theory (disable away-exactp-a away-exactp-c)
		  :use (away-exactp-a
			away-lower-pos
			(:instance expt-split (r 2) (j (- 1 n)) (i (- 2 (expt 2 (1- k)))))
			(:instance away-exactp-c
				   (a (+ (expt 2 (- 2 (expt 2 (1- k))))
					 (expt 2 (- 3 (+ n (expt 2 (1- k))))))))
			(:instance exactp-2**n (n (- 2 (expt 2 (1- k)))) (m n))
			(:instance fp+1
				   (x (expt 2 (- 2 (expt 2 (1- k))))))
			(:instance fp+2
				   (y (away x n))
				   (x (expt 2 (- 2 (expt 2 (1- k)))))))))))

(local (defthm drnd-original-bnd-4
    (implies (and (natp n)
		  (> n 0)
		  (natp k)
		  (> k 0)
		  (rationalp x)
		  (> x 0)
		  (<= x (expt 2 (- 3 (+ n (expt 2 (1- k)))))))
	     (equal (drnd-original x 'inf n k)
		    (expt 2 (- 3 (+ n (expt 2 (1- k)))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable sgn rnd drnd-original inf)))))

(local (defthm drnd-original-bnd-5
    (implies (and (natp n)
		  (> n 0)
		  (natp k)
		  (> k 0)
		  (rationalp x)
		  (> x (expt 2 (- 2 (expt 2 (1- k)))))
		  (< x (+ (expt 2 (- 2 (expt 2 (1- k))))
			  (expt 2 (- 3 (+ n (expt 2 (1- k)))))))
		  (< x (+ (expt 2 (- 2 (expt 2 (1- k))))
			  (expt 2 (- 2 (+ n (expt 2 (1- k))))))))
	     (equal (near x n)
		    (expt 2 (- 2 (expt 2 (1- k))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable expt-split)
           :use (near1-a)))))

(local (defthm drnd-original-bnd-6
    (implies (and (natp n)
		  (> n 0)
		  (natp k)
		  (> k 0)
		  (rationalp x)
		  (> x (expt 2 (- 2 (expt 2 (1- k)))))
		  (< x (+ (expt 2 (- 2 (expt 2 (1- k))))
			  (expt 2 (- 2 (+ n (expt 2 (1- k))))))))
	     (equal (near x n)
		    (expt 2 (- 2 (expt 2 (1- k))))))
  :hints (("Goal" :in-theory (disable expt-compare)
           :use (drnd-original-bnd-5
			(:instance expt-weak-monotone
				   (n (- 2 (+ n (expt 2 (1- k)))))
				   (m (- 3 (+ n (expt 2 (1- k)))))))))))

(local (defthm drnd-original-bnd-7
    (implies (and (natp n)
		  (> n 0)
		  (natp k)
		  (> k 0)
		  (rationalp x)
		  (> x 0)
		  (< x (expt 2 (- 2 (+ n (expt 2 (1- k)))))))
	     (equal (drnd-original x 'near n k)
		    0))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable sgn rnd drnd-original)))))

(local (defthm drnd-original-bnd-8
    (implies (and (ieee-mode-p m)
		  (natp n)
		  (> n 0)
		  (natp k)
		  (> k 0)
		  (rationalp x)
		  (> x 0)
		  (< x (expt 2 (- 2 (+ n (expt 2 (1- k)))))))
	     (equal (drnd-original x m n k)
		    (if (eql m 'inf)
			(expt 2 (- 3 (+ n (expt 2 (1- k)))))
		      0)))
  :rule-classes ()
  :hints (("Goal" :in-theory (e/d (ieee-mode-p sgn rnd drnd-original minf inf) (expt-compare))
		  :use (drnd-original-bnd-2
			drnd-original-bnd-4
			drnd-original-bnd-7
			(:instance expt-weak-monotone
				   (n (- 2 (+ n (expt 2 (1- k)))))
				   (m (- 3 (+ n (expt 2 (1- k)))))))))))

(local (defthm drnd-original-bnd-9
    (implies (and (ieee-mode-p m)
		  (natp n)
		  (> n 0)
		  (natp k)
		  (> k 0)
		  (rationalp x)
		  (> x 0)
		  (< x (expt 2 (- 2 (+ n (expt 2 (1- k))))))
		  (rationalp y)
		  (> y 0)
		  (< y (expt 2 (- 2 (+ n (expt 2 (1- k)))))))
	     (equal (drnd-original x m n k)
		    (drnd-original y m n k)))
  :rule-classes ()
  :hints (("Goal" :use (drnd-original-bnd-8
			(:instance drnd-original-bnd-8 (x y)))))))

(defthm drnd-original-tiny-equal
    (implies (and (ieee-mode-p m)
		  (natp n)
		  (> n 0)
		  (natp k)
		  (> k 0)
		  (rationalp x)
		  (< (abs x) (expt 2 (- 2 (+ n (expt 2 (1- k))))))
		  (rationalp y)
		  (< (abs y) (expt 2 (- 2 (+ n (expt 2 (1- k))))))
		  (equal (sgn x) (sgn y)))
	     (equal (drnd-original x m n k)
		    (drnd-original y m n k)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable sgn  DRND-ORIGINAL-minus)
		  :use ((:instance drnd-original-bnd-9 (m (if (< x 0) (flip m) m)) (x (abs x)) (y (abs y)))))))



;beginning of Eric's drnd-original lemmas.  Throughout, n is the number of significand bits
;(counting the implicit leading zero), and k is the number of exponent bits.

;it doesn't make sense for n to be 0 (no bits of significand).  Since n counts the
;implicit 0, n=1 is also questionable.

;It doesn't make sense for k to be 0 (no bits of exponent).  Having k=1 is also
;questionable, since that would allow only 2 possible exponent values, both
;reserved (one reserved for denormals).

(defund spn (q)
  (expt 2 (- 1 (bias q))))

(defund spd (p q)
     (expt 2 (+ 2 (- (bias q)) (- p))))


(defthm expo-spn
  (implies (and (case-split (acl2-numberp k))
                (case-split (< 0 k)))
           (equal (expo (spn k))
                  (+ 1 (* -1 (bias k)))))
  :hints (("Goal" :in-theory (enable  spn))))

(defthm expo-spd
  (implies (and (case-split (acl2-numberp k))
                (case-split (integerp n))
                (case-split (< 0 k)))
           (equal (expo (spd n k))
                  (+ 2 (- (bias k)) (- n))))
  :hints (("Goal" :in-theory (enable spd))))

(defthm spn-positive-rational-type
  (and (rationalp (spn k))
       (> (spn k) 0))
  :rule-classes (:type-prescription ))

(defthm positive-spn
  (> (spn q) 0)
  :rule-classes (:linear))

(defund nrepp (x p q)
  (and (rationalp x)
       (not (= x 0))
       (< 0 (+ (expo x) (bias q)))
       (< (+ (expo x) (bias q)) (- (expt 2 q) 1))
       (exactp x p)))

(defund drepp (x p q)
  (and (rationalp x)
       (not (= x 0))
       (<= (- 2 p) (+ (expo x) (bias q)))
       (<= (+ (expo x) (bias q)) 0)
       (exactp x (+ -2 p (expt 2 (- q 1)) (expo x)))))

(defund irepp (x p q)
  (or (nrepp x p q)
      (drepp x p q)))

(local (defthm nrepp-spn-support
  (implies (and (integerp n)
                (> n 0)
                (integerp k)
                (> k 1))
           (nrepp (spn k) n k))
  :hints (("goal" :in-theory (enable nrepp SPN)
           :use ((:instance exactp-2**n
                            (n (+ 1 (* -1 (bias k))))
                            (m n))
                 (:instance expt-strong-monotone
                            (n 1)
                            (m k)))))))

(defthmd nrepp-spn
  (implies (and (integerp p)
                (> p 0)
                (integerp q)
                (> q 1))
           (nrepp (spn q) p q))
  :hints (("Goal" :by nrepp-spn-support)))


(local (defthm smallest-spn-support
  (implies (and (nrepp x n k) ;n is a free var
                (integerp n)
                (> n 0)
                (integerp k)
                (> k 1)
                )
           (>= (abs x) (spn k)))
  :rule-classes ((:rewrite :match-free :once))
  :hints (("goal" :in-theory (enable nrepp; bias
                                     SPN
                                     )
           :use (fp-abs
                 sig-lower-bound
                 (:instance expt-weak-monotone
                            (n (- 1 (bias k)))
                            (m (expo x))))))))


(defthmd smallest-spn
  (implies (and (nrepp r p q)
                (integerp p)
                (> p 0)
                (integerp q)
                (> q 1))
           (>= (abs r) (spn q)))
  :rule-classes
  ((:rewrite :match-free :once))
  :hints (("Goal" :by smallest-spn-support)))


;uses bias to avoid having to open bias in proofs below
(defthmd drnd-original-def
  (equal (drnd-original x mode n k)
         (- (rnd (+ x
                    (* (sgn x)
                       (expt 2 (- 1 (bias k)))))
                 mode n)
            (* (sgn x)
               (expt 2 (- 1 (bias k))))))
  :hints (("goal" :in-theory (enable drnd-original bias))))

(defthmd drnd-original-spn
  (implies (and (common-rounding-mode-p mode)
                (integerp n)
                (> n 0)
                (integerp k)
                (> k 0))
           (equal (drnd-original (spn k) mode n k)
                  (rnd (spn k)
                       mode
                       (+ n
                          (- (expo (spn k)))
                          (+ 1 (* -1 (BIAS K)))))))
  :hints (("goal" :in-theory (set-difference-theories
                              (enable drnd-original-def ;sgn
                                      SPN
;      expt-split
;     expt-minus
                                      )
                              '(a15
                                EXPT-COMPARE-EQUAL))
           :use ((:instance rnd-exactp-b (x (expt 2 (+ 2 (* -1 (bias k))))))
                 (:instance rnd-exactp-b (x (expt 2 (+ 1 (* -1 (bias k))))))
                 (:instance a15
                            (i 2)
                            (j1 (+ 1 (- (bias k))))
                            (j2 1))
                 ))))

(local (defthmd drnd-original-rewrite-1
         (implies (and (rationalp x)
                       (<= 0 x)
                       (< x (spn k))
                       (common-rounding-mode-p mode)
                       (integerp n)
                       (> n 1)
                       (integerp k)
                       (> k 0))
                  (equal (drnd-original x mode n k)
                         (rnd x
                              mode
                              (+ n (- (expo (spn k))) (expo x)))))
         :hints (("goal" :in-theory (set-difference-theories
                                     (enable drnd-original-def sgn ;common-rounding-mode-p ;ieee-mode-p
                                             expt ;expt-split ;why?
                                             ;bias
                                             SPN
                                             )
                                     '(                                       ;SPN
                                       common-rounding-mode-p
                                       expo-x+2**k))
                  :use ((:instance plus-rnd
                                   (y x)
                                   (x (spn k))
                                   (k (+ n (expo x) (- (expo
                                                        (spn k))))))
                        (:instance expo-x+2**k
                                   (k (+ 1 (* -1 (bias k)))))
                        (:instance expo<=
                                   (n (* -1 (bias k)))))))
         :otf-flg t))

(local
 (defthmd drnd-original-rewrite-pos
  (implies (and (rationalp x)
                (<= 0 x)
                (<= x (spn k))
                (common-rounding-mode-p mode)
                (integerp n)
                (> n 1)
                (integerp k)
                (> k 0))
           (equal (drnd-original x mode n k)
                  (rnd x
                       mode
                       (+ n (- (expo (spn k))) (expo x)))))
  :hints (("goal" :in-theory (disable spn COMMON-ROUNDING-MODE-P)
           :use (drnd-original-rewrite-1 drnd-original-spn )))))

(local
 (defthmd drnd-original-rewrite-neg
   (implies (and (rationalp x)
                 (<= (- (spn k)) x)
                 (<= x 0)
                 (common-rounding-mode-p mode)
                 (integerp n)
                 (> n 1)
                 (integerp k)
                 (> k 0))
            (equal (drnd-original x mode n k)
                   (rnd x
                        mode
                        (+ n (- (expo (spn k))) (expo x)))))
   :hints (("goal" :in-theory (enable drnd-original-rewrite-pos )
            :use ((:instance drnd-original-minus (mode (flip mode)))
                  (:instance
                   rnd-minus (x (- x)) (mode mode)
                   (n (+ -1 n (expo x) (bias k)))))))))

;why enable so much?
(defthmd drnd-original-rewrite
  (implies (and (rationalp x)
                (<= (abs x) (spn k))
                (common-rounding-mode-p mode)
                (integerp n)
                (> n 1)
                (integerp k)
                (> k 0))
           (equal (drnd-original x mode n k)
                  (rnd x
                       mode
                       (+ n
                          (- (expo (spn k)))
                          (expo x)))))
  :hints (("Goal" :in-theory (enable drnd-original-rewrite-pos drnd-original-rewrite-neg))))

(defthm drepp-range
  (implies (and (drepp x n k)
                (integerp n)
                (>= n 0)
                (integerp k)
                (> k 0)
                )
           (<= (abs x)
               (spn k)))
  :hints (("Goal" :in-theory (enable bias drepp SPN)
           :use ((:instance expo>= (x (- x))
                        (n (+ 1 (- (bias k)))))
                 (:instance expo>= (n (+ 1 (- (bias k)))))))))

(defthmd drepp-def
  (equal (drepp x p q)
         (and (rationalp x)
              (not (= x 0))
              (<= (- 2 p) (+ (expo x) (bias q)))
              (<= (+ (expo x) (bias q)) 0)
              (exactp x (+ -1 p (bias q) (expo x)))))
  :hints (("Goal" :in-theory (enable drepp bias))))

(defthm drnd-original-of-drepp-is-NOP
  (implies (and (drepp x n k)
                (integerp n)
                (> n 1)
                (integerp k)
                (> k 0)
                (common-rounding-mode-p mode))
           (equal (drnd-original x mode n k)
                  x))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable drepp-def
                                      )
                              '( SPN))
           :use (drnd-original-rewrite
                 drepp-range
                 (:instance rnd-exactp-b
                            (n (+ n
                                  (- (expo (spn k)))
                                  (expo x))))))))
;move up?
(defthm spn-1-exact
  (implies (and (case-split (integerp k))
                (case-split (> k 0)))
           (exactp (spn k) 1))
  :hints (("Goal" :in-theory (enable spn))))

(defthm spd-1-exact
  (implies (and (case-split (integerp k))
                (case-split (integerp n))
                (case-split (> k 0)))
           (exactp (spd n k) 1))
  :hints (("Goal" :in-theory (enable spd)))
  )

;(in-theory (enable drnd-original-spn))

(defthm drnd-original-spn-is-spn
  (implies (and (common-rounding-mode-p mode)
                (integerp n)
                (>= n 1)
                (integerp k)
                (> k 0))
           (= (drnd-original (spn k) mode n k)
              (spn k))
           )
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable IEEE-MODE-P)
                              '( spn-1-exact
                                 SPN
                                      drnd-original-spn
                                      ))
           :use ( drnd-original-spn
                  (:instance exactp-<= (m 1)
                             (x (spn k)))
                  (:instance spn-1-exact)
                  (:instance rnd-exactp-b
                             (x (spn k))
;                             (m mode)
                             (n n))))))

;can be expensive..
(defthmd drnd-original-spn-is-spn-general
  (implies (and (= (abs x) (spn k))
                (common-rounding-mode-p mode)
                (integerp n)
                (>= n 1)
                (integerp k)
                (> k 0)
                (rationalp x)
                )
           (= (drnd-original x mode n k)
              x)
           )
  :hints (("Goal" :in-theory (disable spn drnd-original-rewrite drnd-original-spn)
           :use (:instance drnd-original-minus (mode (flip mode))))))

;(in-theory (disable drnd-original-spn))

;(in-theory (enable drnd-original-rewrite)) ;BOZO yuck!

(defthm drnd-original-trunc-never-goes-away-from-zero
  (implies (and (integerp n)
                (> n 1)
                (integerp k)
                (> k 0)
                (rationalp x)
                (<= (abs x) (spn k)))
           (<= (abs (drnd-original x 'trunc n k))
               (abs x)))
  :hints (("Goal" :in-theory (enable rnd drnd-original-rewrite)
           :use (:instance trunc-upper-bound
                           (n (+ -1 N (EXPO X) (bias k)))))))

(defthm drnd-original-away-never-goes-toward-zero
  (implies (and (integerp n)
                (> n 1)
                (integerp k)
                (> k 0)
                (rationalp x)
                (<= (abs x) (spn k)))
           (>= (abs (drnd-original x 'away n k))
               (abs x)))
  :hints (("Goal" :in-theory (enable rnd drnd-original-rewrite)
           :use (:instance away-lower-bound
                (n (+ -1 N (EXPO X) (bias k)))))))

(defthm drnd-original-inf-never-goes-down
  (implies (and (integerp n)
                (> n 1)
                (integerp k)
                (> k 0)
                (rationalp x)
                (<= (abs x) (spn k)))
           (>= (drnd-original x 'inf n k)
               x))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable rnd drnd-original-rewrite)
                              '(expo-2**n abs-pos)))))

(defthm drnd-original-minf-never-goes-up
  (implies (and (integerp n)
                (> n 1)
                (integerp k)
                (> k 0)
                (rationalp x)
                (<= (abs x) (spn k)))
           (<= (drnd-original x 'minf n k)
               x))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable rnd drnd-original-rewrite)
                              '(expo-2**n abs-pos)))))

;t-p?
(defthm fl-not-0
  (implies (and (rationalp x)
                (>= x 1))
           (not (= (fl x)
                   0))))
;t-p?
(defthm cg-not-0
  (implies (and (rationalp x)
                (> x 0))
           (not (= (cg x)
                   0))))

(defthm drnd-original-trunc-skips-no-denormals
  (implies (and (integerp n)
                (> n 1)
                (integerp k)
                (> k 0)
                (rationalp x)
                (<= (abs x) (spn k))
                (drepp a n k)
                (<= (abs a) (abs x))
                )
           (<= (abs a)
               (abs (drnd-original x 'trunc n k))))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable rnd drepp-def drnd-original-rewrite
                                      )
                              '(trunc-exactp-c-eric
                                 EXPO-COMPARISON-REWRITE-TO-BOUND-2
                                  EXPO-COMPARISON-REWRITE-TO-BOUND
                                spn))
           :use (
                 (:instance exactp-<=
                            (x a)
                            (m (+ -1 N (EXPO A) (bias k)))
                            (n (+ -1 N (EXPO x) (bias k))))
                 (:instance trunc-exactp-c-eric (n (+ -1 N (EXPO X) (bias k))))
                 (:instance expo-monotone (x a) (y x))))))


(defthm drnd-original-trunc-skips-no-rep-numbers
  (implies (and (integerp n)
                (> n 1)
                (integerp k)
                (> k 1)
                (rationalp x)
                (<= (abs x) (spn k))
                (irepp a n k)
                (<= (abs a) (abs x))
                )
           (<= (abs a)
               (abs (drnd-original x 'trunc n k))))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable irepp DRND-ORIGINAL-SPN-IS-SPN-GENERAL )
                              '(drnd-original-trunc-skips-no-denormals

                                  DRND-ORIGINAL-SPN-IS-SPN
                                smallest-spn-support
                                spn drnd-original-rewrite))
           :use (drnd-original-trunc-skips-no-denormals
                 (:instance smallest-spn-support (x a))))
          ("goal'"
           :cases ((and (nrepp a n k) (< (abs x) (spn k)))
                   (and (drepp a n k) (< (abs x) (spn k)))))))

(local (defthm positive-spd-support
  (implies (and (integerp n)
                (> k 1)
                (integerp k)
                (> k 0))
           (> (spd n k) 0))))

(defthm positive-spd
  (implies (and (integerp p)
                (> p 1)
                (> q 0))
           (> (spd p q) 0))
  :rule-classes :linear)


(local (defthm drepp-spd-support
  (implies (and (integerp n)
                (> n 1)
                (integerp k)
                (> k 0))
           (drepp (spd n k) n k))
  :hints (("goal" :in-theory (enable drepp-DEF ;bias
                                     )))))


(defthmd drepp-spd
  (implies (and (integerp p)
                (> p 1)
                (integerp q)
                (> q 0))
           (drepp (spd p q) p q))
  :hints (("Goal" :by drepp-spd-support)))


(local (defthm smallest-spd-support
  (implies (and (integerp n)
                (> n 1)
                (integerp k)
                (> k 0)
                (drepp x n k))
           (>= (abs x) (spd n k)))
  :hints (("goal" :in-theory (enable drepp SPD)
           :use (sig-lower-bound
                 fp-abs
                 (:instance expt-weak-monotone
                            (n (+ 2 (* -1 n) (* -1 (bias k))))
                            (m (expo x))))))))


(defthmd smallest-spd
  (implies (and (integerp p)
                (> p 1)
                (integerp q)
                (> q 0)
                (drepp r p q))
           (>= (abs r) (spd p q)))
  :hints (("Goal" :by smallest-spd-support)))



;BOZO.  if we try to scatter exponents here, we don't gather the constants...
(defthm drnd-original-trunc-of-low-range
  (implies (and (rationalp x)
                (< (abs x) (abs (spd n k)))
                (integerp n)
                (> n 1)
                (integerp k)
                (> k 0))
           (= (drnd-original x 'trunc n k)
              0))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable drnd-original-rewrite rnd sgn
                                      SPD
                                      SPN
                                      bias ;drop?
;                                      EXPT-COMPARE-EQUAL
;expt-split expt-minus
                                      )
                              '(a15 ;spn
;spd
                                EXPT-COMPARE-EQUAL
                                EXPT-COMPARE
                                ))
           :use ((:instance expt-strong-monotone
                            (n (expo (spd n k)))
                            (m (expo (spn k))))
                 (:instance trunc-to-0-or-fewer-bits
                            (n (+ -1 N (EXPO X) (bias k))))
                 (:instance a15 (i 2) (j1 1) (j2 (+ 1 (* -1 N)
                                                    (* -1 (bias k)))))
                 (:instance expo<= (n (+ 1 (* -1 N)
                                         (* -1 (bias k)))))
                 (:instance expo<= (x (- x))
                            (n (+ 1 (* -1 N)
                                  (* -1 (bias k)))))))))

(defthm drnd-original-away-of-low-range
  (implies (and (rationalp x)
                (< (abs x) (abs (spd n k)))
                (integerp n)
                (> n 1)
                (integerp k)
                (> k 0))
           (= (drnd-original x 'away n k)
              (* (sgn x) (spd n k))))
  :hints (("Goal"  :in-theory (set-difference-theories
                               (enable drnd-original-rewrite rnd sgn bias
                                       spn
                                       spd)
                               '(a15 ;
                                                                 EXPT-COMPARE-EQUAL
                                EXPT-COMPARE
                                     ))
           :use ((:instance expt-strong-monotone
                            (n (expo (spd n k)))
                            (m (expo (spn k))))
;                 (:instance away-to-0-or-fewer-bits
 ;                           (n (+ -2 N (EXPO X) (EXPT 2 (+ -1 K)))))
                 (:instance a15 (i 2) (j1 1) (j2 (+ 2 (* -1 N)
                                                    (* -1 (EXPT 2 (+ -1 K))))))
                 (:instance expo<= (n (+ 2 (* -1 N)
                                         (* -1 (EXPT 2 (+ -1 K))))))
                 (:instance expo<= (x (- x))
                            (n (+ 2 (* -1 N)
                                  (* -1 (EXPT 2 (+ -1 K))))))))))


(defthm spd-<-spn
  (implies (and (integerp n)
                (> n 1)
                (> k 0)
                (integerp k))
  (< (spd n k)
     (spn k)))
;  :rule-classes :linear
  :hints (("Goal" :in-theory (enable spd
                                     spn)
           :use (:instance expt-strong-monotone
                                  (n (+ 2 (* -1 N) (* -1 (bias k))))
                                  (m (+ 1          (* -1 (bias k))))))))

#|
(defthm abs-spd-<-abs-spn
  (implies (and (integerp n)
                (> n 1)
                (> k 0)
                (integerp k))
  (< (abs (spd n k))
     (abs (spn k))))
 ; :rule-classes :linear
  :hints (("Goal" :in-theory (disable spd spn))))
|#

;move or drop?
(defthm abs-prod
  (implies (and (rationalp x)
                (rationalp y))
           (= (abs (* x y))
              (* (abs x) (abs y))))
  :hints (("Goal" :in-theory (enable sgn))))

(defthm drnd-original-of-low-range
  (implies (and (rationalp x)
                (< (abs x) (abs (spd n k)))
                (integerp n)
                (> n 1)
                (integerp k)
                (> k 0)
                (common-rounding-mode-p mode))
           (or (= (drnd-original x mode n k) 0)
               (= (abs (drnd-original x mode n k)) (spd n k))))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable rnd inf minf near near+ ieee-mode-p common-rounding-mode-p sgn drnd-original-rewrite
                                      )
                              '(spd
                                spn
                                abs
                                abs-away
                                drnd-original-away-of-low-range
                                drnd-original-trunc-of-low-range
                                spd-<-spn
;                                drnd-original-rewrite
                                rearrange-negative-coefs-equal))
           :use (;drnd-original-rewrite
                 spd-<-spn
                 drnd-original-away-of-low-range drnd-original-trunc-of-low-range)))
  :rule-classes nil)

(defthm drnd-original-spd-is-spd
  (implies (and (common-rounding-mode-p mode)
                (integerp n)
                (> n 1)
                (integerp k)
                (> k 0))
           (= (drnd-original (spd n k) mode n k)
              (spd n k))
           )
  :hints (("Goal" :in-theory (disable spd))))

(defthm drepp-minus
  (implies (and (rationalp x)
                (integerp n)
                (> n 1)
                (integerp k)
                (> k 0))
           (= (drepp (* -1 x) n k) (drepp x n k)))
  :hints (("Goal" :in-theory (enable drepp))))

;can be expensive
(defthmd drnd-original-spd-is-spd-general
  (implies (and (= (abs x) (spd n k))
                (common-rounding-mode-p mode)
                (integerp n)
                (> n 1)
                (integerp k)
                (> k 0)
                (rationalp x)
                )
           (= (drnd-original x mode n k)
              x)
           )
  :hints (("Goal" :in-theory (disable spd drnd-original-rewrite
                                      DRND-ORIGINAL-OF-DREPP-IS-NOP
                                      drepp-spd-support)
           :use ((:instance drepp-spd-support)
                 (:instance DRND-ORIGINAL-OF-DREPP-IS-NOP (x (- x)))
                 (:instance DRND-ORIGINAL-OF-DREPP-IS-NOP )))))



(defund largest-positive-denormal (n k)
  (- (spn k)
     (spd n k)))


(defthm positive-lpd
  (implies (and (integerp n)
                (> n 1)
                (integerp k)
                (> k 0))
           (> (largest-positive-denormal n k) 0))
  :hints (("goal" :in-theory (enable drepp bias; SPN
;                                     spd
                                     largest-positive-denormal)
           :use
           (:instance expt-strong-monotone
                      (n (+ 2 (* -1 n) (* -1 (bias k))))
                      (m (+ 1 (* -1 (bias k)))))))
  :rule-classes (:rewrite :linear))

(defthm expo-2**k-x
  (implies (and (integerp k)
                (rationalp x)
                (> x 0)
                (<= x (expt 2 (- k 1))))
           (equal (expo (+ (expt 2 k) (* -1 x)))
                  (- k 1)))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable expt-split)
                              '())
           :use (
                 (:instance expo-unique (x (- (expt 2 k) x)) (n (- k 1)))
                 )))
  :otf-flg t)

(defthm expo-lpd
  (implies (and (integerp n)
                (> n 1)
                (integerp k)
                (> k 0))
           (= (expo (largest-positive-denormal n k))
              (1- (expo (spn k)))))
  :hints (("Goal" :in-theory (enable largest-positive-denormal
                                     SPN
                                     spd))))

;move
(defthm exactp-diff-of-powers-of-2
  (implies (and (integerp m)
                (integerp n)
                (> m n) ; remove?
                )
           (exactp (+ (expt 2 m) (* -1 (expt 2 n)))
                   (- m n)))
  :hints (("Goal" :in-theory (disable  expo-2**k-x)
           :use ((:instance expt-strong-monotone (n m) (m n))
                 (:instance exactp2 (x (- (expt 2 m) (expt 2 n)))
                               (n (- m n)))
                 (:instance  expo-2**k-x (k m)
                             (x (EXPT 2 N)))))))


(defthm exactness-of-lpd
  (implies (and (integerp n)
                (> n 1)
                (integerp k)
                (> k 0))
           (exactp (largest-positive-denormal n k)
                   (1- n)))
  :hints (("Goal" :in-theory (e/d (largest-positive-denormal
                                   SPN
                                   spd) ( exactp-diff-of-powers-of-2))
           :use (:instance
                        exactp-diff-of-powers-of-2
                        (m (expo (spn k)))
                        (n (expo (spd n k)))))))

(defthm drepp-lpd
  (implies (and (integerp n)
                (> n 1)
                (integerp k)
                (> k 0))
           (drepp (largest-positive-denormal n k) n k))
  :hints (("goal" :in-theory (set-difference-theories
                              (enable drepp-def)
                              '(expo-lpd exactness-of-lpd))
           :use ( (:instance expo-lpd)
                  (:instance exactness-of-lpd)
                  (:instance expt-strong-monotone
                             (n (+ 3 (* -1 n) (* -1 (EXPT 2 (1- k)))))
                             (m (+ 2 (* -1 (EXPT 2 (1- k))))))))))

;BOZO move these
;nice rules to have in lib?
(defthmd expo<=-2
  (implies (and (<= (expo x) (- n 1))
                (rationalp x)
                (> x 0) ;gen?
                (integerp n)
                )
           (<= x (expt 2 n)))
  :hints (("Goal" :in-theory (disable EXPT-COMPARE)
           :use (expo-upper-bound
                 (:instance expt-weak-monotone-linear (m n) (n (+ 1 (expo x)))))))
  :rule-classes (:rewrite :linear))

;shouldn't be a linear rule?
(defthmd expo>=-2
  (implies (and (>= (expo x) n)
                (rationalp x)
                (> x 0) ;gen?
                (integerp n)
                )
           (>= x (expt 2 n)))
  :hints (("Goal" :in-theory (disable EXPT-COMPARE)
           :use (expo-lower-bound
                 (:instance expt-weak-monotone-linear (m (expo x))))))
  :rule-classes (:rewrite :linear))


;are these 2 duplicated elsewhere?
;shouldn't be a linear rule?
(defthmd expo>
  (implies (and (> x (expt 2 (+ 1 n)))
                (rationalp x)
                (integerp n)
                )
           (> (expo x) n))
  :rule-classes :linear
  :otf-flg t
  :hints (("goal" :in-theory (set-difference-theories
                              (enable expt-split)
                              '( EXPT-COMPARE))
           :use (expo-upper-bound
                 expo>=))))

(defthmd expo<
  (implies (and (< x (expt 2 n))
                (> x 0)
                (rationalp x)
                (integerp n)
                )
           (< (expo x) n))
  :rule-classes :linear
  :hints (("goal" :use (expo-lower-bound
			(:instance expt-split (r 2) (i 1) (j n))
			(:instance expt-weak-monotone (n (1+ n)) (m (expo x)))))))

(defthm largest-lpd
  (implies (and (drepp x n k)
                (> x 0) ;drop?
                (integerp n)
                (> n 1)
                (integerp k)
                (> k 0)
                )
           (<= x (largest-positive-denormal n k)))
  :hints (("goal" :in-theory (set-difference-theories
                              (enable drepp-def largest-positive-denormal
                                      SPN
                                      spd)
                              '(expo<=-2))
           :use ((:instance expo<=-2 (n (+ 1 (* -1 (bias k)))))
                 (:instance fp+2
                            (y (EXPT 2 (+ 1 (* -1 (bias k)))))
                            (n (+ -1 n (EXPO X) (bias k)))
                            )))))

;why? :
(local (in-theory (disable expo-monotone)))
(local (in-theory (disable expt-weak-monotone-linear)))

;rephrase using bias?
(defthm drepp-drnd-original-exactness
  (implies (and (rationalp x)
                (< (spd n k) x)
                (< x (spn k))
                (integerp n)
                (> n 1)
                (integerp k)
                (> k 0)
                (common-rounding-mode-p m))
           (exactp (drnd-original x m n k) (+ -2 n (expt 2 (- k 1)) (expo (drnd-original x m n k)))))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable bias
                                      drnd-original-rewrite
                                      spn
                                      spd
                                      ) ;drop?
                              '(expo>))
           :use ((:instance expo-rnd (mode m) (n (+ -1 N (EXPO X)
                                                    (bias k))))
                 (:instance expo> (n (+ 1 (- n ) (- (bias k)))))))))


(defthm drepp-drnd-original-expo-1
  (implies (and (rationalp x)
                (< (spd n k) x)
                (< x (spn k))
                (integerp n)
                (> n 1)
                (integerp k)
                (> k 0)
                (common-rounding-mode-p m))
           (<= (- 2 n) (+ (expo (drnd-original x m n k)) (bias k))))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable spn
                                      drnd-original-rewrite
                                      spd)
                              '(expo>=))
           :use ((:instance expo-rnd (mode m) (n (+ -1 N (EXPO X)
                                                    (bias k))))
                 (:instance expo>= (n (+ 2 (- n) (- (bias k)))))))))

(local
 (defthm hack3
   (implies (and (equal (expo x) (- 1 (expt 2 (1- k))))
                 (rationalp x)
                 (integerp n)
                 (< 1 n)
                 (integerp k)
                 (< 0 k))
            (> (+ (expt 2 (+ 1 (expo x)))
                  (expt 2
                        (+ 3 (* -1 n)
                           (* -1 (expt 2 (1- k))))))
               (expt 2 (+ 2 (* -1 (expt 2 (1- k)))))))
   :rule-classes nil
   :hints (("Goal" :in-theory (disable   REARRANGE-NEGATIVE-COEFS-EQUAL)))))


(defthm drepp-drnd-original-expo-2
  (implies (and (rationalp x)
                (< (spd n k) x)
                (< x (largest-positive-denormal n k))
                (integerp n)
                (> n 1)
                (integerp k)
                (> k 0)
                (common-rounding-mode-p m))
           (<= (+ (expo (drnd-original x m n k)) (bias k)) 0))
  :hints (("goal" :in-theory (set-difference-theories
                              (enable ;expt-split
                               bias ;drop
                               largest-positive-denormal
                               spn
                               spd
                               drnd-original-rewrite
                               )
                              '(expo>= expo>=-2 ; expo-2**k-x
                                       rnd-exactp-c ; expt-compare
                                       exactp-diff-of-powers-of-2
                                       ))
           :use ((:instance expo-rnd (mode m)
                            (n (+ -1 n (expo x) (bias k))))
                 (:instance expo< (n (+ 2 (- n ) (- (bias k)))))
                 (:instance expo< (n (+ 1 (* -1 (bias k)))))
                 (:instance expo>= (n (+ 2 (- n ) (- (bias k)))))
                 (:instance exactp-diff-of-powers-of-2
                            (m (+ 1 (* -1 (bias k))))
                            (n (+ 2 (* -1 n)
                                  (* -1 (bias k)))))
                 (:instance rnd-exactp-c (a (largest-positive-denormal n k))
                            (mode m)
                            (n (1- n)))
                 hack3 ;hack3-bias

                 ))
          )
  :otf-flg t
  )


#|
(defthm drepp-drnd-original-expo-2
  (implies (and (rationalp x)
                (< (spd n k) x)
                (< x (largest-positive-denormal n k))
                (integerp n)
                (> n 1)
                (integerp k)
                (> k 0)
                (common-rounding-mode-p m))
           (<= (+ (expo (drnd-original x m n k)) (bias k)) 0))
  :hints (("goal" :cases (< x 0)
           :in-theory (set-difference-theories
                              (enable ;expt-split
;                               bias ;drop
                               expt-split
                               drnd-original-rewrite
                               )
                              '(expo>= expo>=-2 ; expo-2**k-x
                                       rnd-exactp-c ; expt-compare
                                       exactp-diff-of-powers-of-2
                                       ))
           )
          )
  :otf-flg t
  )


|#


(defthm drepp-drnd-original-not-0
  (implies (and (rationalp x)
                (< (spd n k) x)
                (< x (largest-positive-denormal n k))
                (integerp n)
                (> n 1)
                (integerp k)
                (> k 0)
                (common-rounding-mode-p m))
           (not (equal (drnd-original x m n k) 0)))
  :hints (("goal" :in-theory (set-difference-theories
                              (enable rnd inf minf near near+
                                      drnd-original-rewrite
                                      common-rounding-mode-p ieee-mode-p
                                      spd
                                      spn
                                      LARGEST-POSITIVE-DENORMAL
;                                      bias
                                      )
                              '(drepp-spd drnd-original-trunc-skips-no-denormals))
           :use ((:instance drepp-spd-support)
                 (:instance drnd-original-trunc-skips-no-denormals
                             (a (expt 2
                                      (+ 2 (* -1 n) (* -1 (bias k))))))))))


(defthm drepp-drnd-original-mid-range-1
  (implies (and (rationalp x)
                (< (spd n k) x)
                (< x (largest-positive-denormal n k))
                (integerp n)
                (> n 1)
                (integerp k)
                (> k 0)
                (common-rounding-mode-p m))
           (drepp (drnd-original x m n k) n k))
  :hints (("goal" :in-theory (set-difference-theories
                              (enable drepp bias
                                      spd
                                      spn
                                      LARGEST-POSITIVE-DENORMAL)
                              '(drnd-original-rewrite
                                drepp-drnd-original-expo-2  drepp-drnd-original-expo-1))
           :use ( drepp-drnd-original-expo-2  drepp-drnd-original-expo-1))))

(defthm drepp-drnd-original-mid-range
  (implies (and (rationalp x)
                (< (spd n k) (abs x))
                (< (abs x) (largest-positive-denormal n k))
                (integerp n)
                (> n 1)
                (integerp k)
                (> k 0)
                (common-rounding-mode-p m))
           (drepp (drnd-original x m n k) n k))
  :hints (("goal" :in-theory (e/d (drnd-original-minus)
                                  ( drnd-original-rewrite DREPP-DRND-ORIGINAL-MID-RANGE-1 flip  DREPP-DEF
                                      SPN SPD))
           :use (drepp-drnd-original-mid-range-1
                 (:instance drepp-drnd-original-mid-range-1 (m (flip m)) (x (- x)))))))

(defthm expo-of-high-range-1
  (implies (and (rationalp x)
                (< (largest-positive-denormal n k) x)
                (< x (spn k))
                (integerp n)
                (> n 1)
                (integerp k)
                (> k 0))
           (> x 0))
  :hints (("goal" :in-theory (disable largest-positive-denormal positive-lpd)
           :use (:instance positive-lpd))))

(defthm expo-of-high-range-2-2
  (implies (and
                (integerp n)
                (> n 1)
                (integerp k)
                (> k 0))
           (<= (* 2
                   (expt 2
                         (+ 3 (* -1 n)
                            (* -1 (expt 2 (1- k))))))
               (expt 2 (+ 2 (* -1 (expt 2 (1- k)))))))
  :hints (("goal" :in-theory (disable expo>=-2)
           :use ((:instance a15 (i 2) (j1 1) (j2 (+ 3 (* -1 n) (* -1 (expt 2 (1- k))))))
                 (:instance expt-weak-monotone (n (+ 4 (* -1 n)
                         (* -1 (expt 2 (1- k)))))

                       (m (+ 2 (* -1 (expt 2 (1- k))))))))))
#|
;BOZO kill move
(defthm expo-shift-3-alt
    (implies (and (rationalp (* x y))
		  (not (= (* x y) 0))
		  (integerp n))
	     (= (expo (* y (expt 2 n) x))
		(+ n (expo (* x y)))))
  :hints (("Goal" :use (:instance sig-expo-shift (x (* x y ))))))
|#

;finish trying to keep bias disabled in proofs below here
(defthm expo-of-high-range-2-1
  (implies (and (integerp n)
                (> n 1)
                (integerp k)
                (> k 0))
           (<= (expt 2 (- (expo (spn k)) 1))
               (largest-positive-denormal n k)))
  :hints (("goal" :in-theory (set-difference-theories
                              (enable expt-split
                                      expo-shift-2
                                      bias
                                      LARGEST-POSITIVE-DENORMAL
                                      spn
                                      spd
                                      )
                              '()))))

(defthm expo-of-high-range-2
  (implies (and (rationalp x)
                (< (largest-positive-denormal n k) x)
                (< x (spn k))
                (integerp n)
                (> n 1)
                (integerp k)
                (> k 0))
           (< (expt 2 (- (expo (spn k)) 1)) x))
  :hints (("goal" :in-theory (set-difference-theories
                              (enable largest-positive-denormal
                                      )
                              '( expo>=-2
                                      expo-of-high-range-2-1
                                      spn
                                      ))
           :use  expo-of-high-range-2-1)))


(defthm expo-of-high-range
    (implies (and (rationalp x)
                  (< (largest-positive-denormal n k) x)
                  (< x (spn k))
                  (integerp n)
                  (> n 1)
                  (integerp k)
                  (> k 0))
             (= (expo x)
                (- (expo (spn k)) 1)))
    :hints (("goal" :in-theory (e/d (spn
                                     spd)
                                    (
                                 expo-of-high-range-2
                                positive-lpd))
             :use ( expo-of-high-range-2
                    (:instance positive-lpd)
                   (:instance expo-unique (n (- (expo (spn k)) 1)))))))

(defthm drnd-original-trunc-of-high-range-3
  (implies (and (integerp n)
                (> n 1)
                (integerp k)
                (> k 0))
           (equal (fp+ (largest-positive-denormal n k) (- n 1))
                  (spn k)))
  :hints (("Goal" :in-theory (enable expo>=-2 largest-positive-denormal spn
                                     SPD))))

(defthm drnd-original-trunc-of-high-range-1
  (implies (and (rationalp x)
                (< (largest-positive-denormal n k) x)
                (< x (spn k))
                (integerp n)
                (> n 1)
                (integerp k)
                (> k 0))
           (>= (drnd-original x 'trunc n k)
               (largest-positive-denormal n k)))
  :hints (("goal" :in-theory (set-difference-theories
                              (enable rnd drnd-original-rewrite)
                              '(drnd-original-trunc-skips-no-denormals
                                spn
                                largest-positive-denormal
                                rnd-exactp-d
                                ))
           :use ((:instance drnd-original-trunc-skips-no-denormals
                            (a (largest-positive-denormal n k))
                            )))))

(defthm drnd-original-trunc-of-high-range-2
  (implies (and (rationalp x)
                (< (largest-positive-denormal n k) x)
                (< x (spn k))
                (integerp n)
                (> n 1)
                (integerp k)
                (> k 0))
           (<= (drnd-original x 'trunc n k)
               (largest-positive-denormal n k)))
  :hints (("goal" :in-theory (set-difference-theories
                              (enable rnd drnd-original-rewrite)
                              '(
                                spn
                                largest-positive-denormal
                                rnd-exactp-d
                                ;; expo-of-high-range
                                ))
           :use ((:instance fp+2
                            (y (trunc x (+ n
                                                (- (expo (spn k)))
                                                (expo x))))
                            (x (largest-positive-denormal n k))
                            (n (- n 1)))))))

(defthm drnd-original-trunc-of-high-range-pos
  (implies (and (rationalp x)
                (< (largest-positive-denormal n k) x)
                (< x (spn k))
                (integerp n)
                (> n 1)
                (integerp k)
                (> k 0))
           (= (drnd-original x 'trunc n k)
               (largest-positive-denormal n k)))
  :hints (("goal" :in-theory (disable spn
                                      drnd-original-rewrite
                                      largest-positive-denormal
                                      drnd-original-trunc-of-high-range-2
                                      drnd-original-trunc-of-high-range-1
                                      )
           :use (drnd-original-trunc-of-high-range-2 drnd-original-trunc-of-high-range-1))))


(defthm drnd-original-trunc-of-high-range
  (implies (and (rationalp x)
                (< (largest-positive-denormal n k) (abs x))
                (< (abs x) (spn k))
                (integerp n)
                (> n 1)
                (integerp k)
                (> k 0))
           (= (drnd-original x 'trunc n k)
               (* (sgn x) (largest-positive-denormal n k))))
  :hints (("goal" :in-theory (set-difference-theories
                              (enable sgn drnd-original-minus)
                              '(spn
                                drnd-original-rewrite
                                largest-positive-denormal
                                drnd-original-trunc-of-high-range-pos))
           :use (drnd-original-trunc-of-high-range-pos
                 (:instance drnd-original-trunc-of-high-range-pos (x (- x)))))))

(defthm drnd-original-away-of-high-range-1
  (implies (and (rationalp x)
                (< (largest-positive-denormal n k) x)
                (< x (spn k))
                (integerp n)
                (> n 1)
                (integerp k)
                (> k 0))
           (<= (drnd-original x 'away n k)
               (spn k)))
  :hints (("goal" :in-theory (set-difference-theories
                              (enable rnd drnd-original-rewrite)
                              '(spn-1-exact
                                spn
                                largest-positive-denormal
                                rnd-exactp-d))
           :use ( spn-1-exact
                  (:instance exactp-<= (x (spn k)) (m 1) (n (- n 1)))
                  (:instance away-exactp-c (a (spn k))
                             (n (+ n
                                   (- (expo (spn k)))
                                   (expo x))))))))

(defthm drnd-original-away-of-high-range-2
  (implies (and (rationalp x)
                (< (largest-positive-denormal n k) x)
                (< x (spn k))
                (integerp n)
                (> n 1)
                (integerp k)
                (> k 0))
           (>= (drnd-original x 'away n k)
               (spn k)))
  :hints (("goal" :in-theory (set-difference-theories
                              (enable rnd drnd-original-rewrite)
                              '(spn
                                largest-positive-denormal
                                rnd-exactp-d))
           :use ((:instance exactp-<= (x (spn k)) (m 1) (n
                                                                              (- n 1)))
                 (:instance fp+2
                            (y (away x (+ n
                                          (- (expo (spn k)))
                                          (expo x))))
                            (x (largest-positive-denormal n k))
                            (n (- n 1)))))))

(defthm drnd-original-away-of-high-range-pos
  (implies (and (rationalp x)
                (< (largest-positive-denormal n k) x)
                (< x (spn k))
                (integerp n)
                (> n 1)
                (integerp k)
                (> k 0))
           (= (drnd-original x 'away n k)
               (spn k)))
  :hints (("goal" :in-theory (disable
                              drnd-original-rewrite
                              spn
                              largest-positive-denormal
                               DRND-ORIGINAL-AWAY-OF-HIGH-RANGE-1
                                DRND-ORIGINAL-AWAY-OF-HIGH-RANGE-2)
           :use (drnd-original-away-of-high-range-2 drnd-original-away-of-high-range-1))))


(defthm drnd-original-away-of-high-range
  (implies (and (rationalp x)
                (< (largest-positive-denormal n k) (abs x))
                (< (abs x) (spn k))
                (integerp n)
                (> n 1)
                (integerp k)
                (> k 0))
           (= (drnd-original x 'away n k)
               (* (sgn x) (spn k))))
  :hints (("goal" :in-theory (set-difference-theories
                              (enable sgn drnd-original-minus)
                              '(spn
                                drnd-original-rewrite
                                largest-positive-denormal
                                drnd-original-away-of-high-range-pos))
           :use (drnd-original-away-of-high-range-pos
                 (:instance drnd-original-away-of-high-range-pos (x (- x)))
                 ))))

(defthm drnd-original-choice
  (implies (common-rounding-mode-p mode)
           (or (equal (drnd-original x mode n k) (drnd-original x 'away n k))
               (equal (drnd-original x mode n k) (drnd-original x 'trunc n k))))
  :hints (("Goal" :use (:instance rnd-choice (x (+ X
                        (* (SGN X)
                           (EXPT 2 (+ 2 (* -1 (EXPT 2 (1- K)))))))))
           :in-theory (set-difference-theories
                       (enable drnd-original)
                       '(re evenp))))
  :rule-classes nil)


(defthm drnd-original-of-high-range
  (implies (and (< (largest-positive-denormal n k) (abs x))
                (< (abs x) (spn k))
                (rationalp x)
                (integerp n)
                (> n 1)
                (integerp k)
                (> k 0)
                (common-rounding-mode-p mode))
           (or (= (drnd-original x mode n k) (* (sgn x) (largest-positive-denormal n k)))
               (= (drnd-original x mode n k) (* (sgn x) (spn k)))))
  :hints (("goal" :in-theory (set-difference-theories
                              (enable rnd inf minf near ieee-mode-p common-rounding-mode-p sgn)
                              '(spd
                                drnd-original-rewrite
                                spn
                                abs-away
                                common-rounding-mode-p
                                rearrange-negative-coefs-equal))
           :use (drnd-original-choice)))
  :rule-classes nil)

;add?
;gen?
(defthm drnd-original-non-neg
  (implies (and (<= 0 x)
                (rationalp x)
                (<= x (spn k)) ;drop?
                (integerp n)
                (> n 1)
                (integerp k)
                (> k 0)
                (common-rounding-mode-p mode))
           (<= 0 (drnd-original x mode n k)))
  :hints (("Goal" :in-theory (enable drnd-original-rewrite)))
  :rule-classes (:rewrite :type-prescription))

;add?
;gen?
(defthm drnd-original-non-pos
  (implies (and (<= x 0)
                (rationalp x)
                (<= (abs x) (spn k)) ;drop?
                (integerp n)
                (> n 1)
                (integerp k)
                (> k 0)
                (common-rounding-mode-p mode))
           (<= (drnd-original x mode n k) 0))
  :hints (("Goal" :in-theory (enable drnd-original-rewrite)))
  :rule-classes (:rewrite :type-prescription))

;bad name?
(defthm drnd-original-type-pos
  (implies (and (rationalp x)
                (<= 0 x)
                (<= x (spn k)) ;drop?
                (integerp n)
                (> n 1)
                (integerp k)
                (> k 0)
                (common-rounding-mode-p mode))
           (or (drepp (drnd-original x mode n k) n k)
               (= (drnd-original x mode n k) 0)
               (= (drnd-original x mode n k) (spn k))))
           :otf-flg t
           :hints (("goal" :in-theory (set-difference-theories
                              (enable sgn DRND-ORIGINAL-SPN-IS-SPN-GENERAL)
                              '(drnd-original-rewrite
                                drepp-drnd-original-mid-range
                                drnd-original-spd-is-spd-general
                                spd
                                largest-positive-denormal
                                spn
                                drepp-drnd-original-mid-range-1
                                drepp-spd-support
                                ))
           :use (drnd-original-of-high-range
                 drnd-original-of-low-range
                 (:instance  DREPP-MINUS (x  (DRND-ORIGINAL X MODE N K)))
                 (:instance  drepp-spd-support)
                 (:instance drepp-drnd-original-mid-range (m mode)))))
  :rule-classes nil)

;bad name?
(defthm drnd-original-type
  (implies (and (rationalp x)
                (<= (abs x) (spn k)) ;drop?
                (integerp n)
                (> n 1)
                (integerp k)
                (> k 0)
                (common-rounding-mode-p mode))
           (or (drepp (drnd-original x mode n k) n k)
               (= (drnd-original x mode n k) 0)
               (= (drnd-original x mode n k) (* (sgn x) (spn k)))))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable sgn drnd-original-minus)
                              '(drnd-original-rewrite
;                                DRND-ORIGINAL-SPD-IS-SPD-GENERAL ; for efficiency
                                spn))
           :use (drnd-original-type-pos
                 (:instance drnd-original-type-pos (mode (flip mode)) (x (- x))))))
  :rule-classes nil)


;drop?
;(in-theory (disable SPN))



;better proof?
(defthm drnd-original-diff
  (implies (and (rationalp x)
                (<= (ABS X) (SPN K))
                (integerp n)
                (> n 1)
                (integerp k)
                (> k 0)
                (common-rounding-mode-p mode))
           (< (abs (- x (drnd-original x mode n k))) (spd n k)))
  :hints (("Goal'"
           :cases ((> (+ n
                         (- (expo (spn k)))
                         (expo x)) 0)))
          ("goal" :in-theory (set-difference-theories
                              (enable rnd
                                      drnd-original-rewrite
                                      SPD
                                      ;bias
                                     ; SPN
                                      common-rounding-mode-p
                                      inf minf near near+ sgn)
                              '( ;BIAS
                                ;sgn
                                SPN
                                ;spd
                                re evenp EXPO<=-2 EXPO>=-2 expt-compare
                                rnd-diff))
           :use ((:instance rnd-diff (n (+ N (EXPO X)
                                           (* -1 (EXPO (SPN
                                                        K))))))
                 (:instance expo-upper-bound (x (- x)))
                 (:instance expo-upper-bound)
                 (:instance expt-weak-monotone (n (+ 1 (expo x)))
                            (M (+ 2 (* -1 N)
                                  (* -1 (bias k)))))))))


(defthm drepp-rationalp
  (implies (drepp x n k)
           (rationalp x))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable drepp))))

;just an intermediate step in the proofs
(defund next-denormal-2 (x n k)
  (fp+ x (+ -1 n (expo x) (bias k))))

(defund next-denormal (x n k)
  (+ x (spd n k)))

(defthmd denormals-same
  (equal (next-denormal-2 x n k)
         (next-denormal x n k))
  :hints (("Goal" :in-theory (enable next-denormal next-denormal-2
                                     SPD)))
  )

;move
(defthmd fp+-expo
  (implies (and (rationalp x)
                (< 0 x)
                (< x y)
                (rationalp y)
                (exactp x n)
                (integerp n)
                (> n 0)
                (< y (fp+ x n)))
           (= (expo y)
              (expo x)))
  :hints (("Goal" :use ((:instance expo-unique (x y) (n (expo x)))
           (:instance fp+1-1)))))

;remove x>=0 hyp?
(defthm denormal-spacing-1
  (implies (and (integerp n)
                (integerp k)
                (> k 0)
                (> n 1)
                (drepp x n k)
                (drepp x+ n k)
                (>= x 0)
                (> x+ x))
           (>= x+ (next-denormal-2 x n k)))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable drepp bias NEXT-DENORMAL-2)
                              '(fp+ fp+-expo))
           :use ((:instance fp+-expo (y x+)
                            (n (+ -2 N (EXPO X) (EXPT 2 (1- K)))))
                 (:instance fp+2
                            (y x+)
                            (n (+ -1 n (expo x) (bias k))))))))

(defthm denormal-spacing
  (implies (and (integerp n)
                (integerp k)
                (> k 0)
                (> n 1)
                (drepp x n k)
                (drepp x+ n k)
                (>= x 0)
                (> x+ x))
           (>= x+ (next-denormal x n k)))
  :hints (("Goal" :in-theory (disable denormal-spacing-1)
           :use (denormal-spacing-1
                 (:instance denormals-same)))))

(defthm drnd-original-away-skips-no-denormals-pos
  (implies (and (integerp n)
                (> n 1)
                (integerp k)
                (> k 0)
                (rationalp x)
                (<= 0 x)
                (<= x (spn k))
                (drepp a n k)
                (>= a x)
                )
           (>= a (drnd-original x 'away n k)))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable sgn spn
                                      SPD
                                      LARGEST-POSITIVE-DENORMAL
                                      NEXT-DENORMAL)
                              '(drnd-original-diff
                                drnd-original-rewrite
                                largest-lpd
                                denormal-spacing

;                                DRND-ORIGINAL-SPD-IS-SPD-GENERAL ;these two for efficiency
 ;                               DRND-ORIGINAL-SPN-IS-SPN-GENERAL ;
                                 ))
           :use ((:instance largest-lpd (x a))
                 (:instance drnd-original-diff (mode 'away))
                 (:instance drnd-original-type (mode 'away))
                 (:instance denormal-spacing
                            (x a)
                            (x+ (drnd-original x 'away n k)))))))

; all 4 :use hints seem necessary
(defthm drnd-original-away-skips-no-denormals
  (implies (and (integerp n)
                (> n 1)
                (integerp k)
                (> k 0)
                (rationalp x)
                (<= (abs x) (spn k))
                (drepp a n k)
                (>= (abs a) (abs x))
                )
           (>= (abs a) (abs (drnd-original x 'away n k))))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable sgn drnd-original-minus)
                              '(drnd-original-diff
                                DRND-ORIGINAL-AWAY-OF-HIGH-RANGE
                                DRND-ORIGINAL-AWAY-OF-HIGH-RANGE-POS
                                DRND-ORIGINAL-AWAY-OF-LOW-RANGE
                                DREPP-DRND-ORIGINAL-MID-RANGE
                                drnd-original-non-pos
                                drnd-original-rewrite
                                spn
                                DRND-ORIGINAL-AWAY-SKIPS-NO-DENORMALS-pos
;                                DRND-ORIGINAL-SPD-IS-SPD-GENERAL ;these two for efficiency
 ;                               DRND-ORIGINAL-SPN-IS-SPN-GENERAL
                                ))

           :use ((:instance drnd-original-non-pos (mode 'away))
                 (:instance drnd-original-away-skips-no-denormals-pos)
                 (:instance drnd-original-away-skips-no-denormals-pos (a (- a)) (x (- x)))
                 (:instance drnd-original-away-skips-no-denormals-pos (x (- x)))
                 (:instance drnd-original-away-skips-no-denormals-pos (a (- a)))))))

;BOZO
;(in-theory (disable SPN BIAS DREPP))

(defthm drnd-original-inf-skips-no-denormals
  (implies (and (integerp n)
                (> n 1)
                (integerp k)
                (> k 0)
                (rationalp x)
                (<= (abs x) (spn k))
                (drepp a n k)
                (>= a x))
           (>= a (drnd-original x 'inf n k)))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable rnd ;drepp
                                      inf
                                      drnd-original-rewrite)
                              '(;drnd-original-rewrite
                                drnd-original-away-skips-no-denormals
                                 drnd-original-trunc-skips-no-denormals))
          :use ((:instance drnd-original-away-skips-no-denormals)
                (:instance drnd-original-trunc-skips-no-denormals (x (- x)))))))

(defthm drnd-original-minf-skips-no-denormals
  (implies (and (integerp n)
                (> n 1)
                (integerp k)
                (> k 0)
                (rationalp x)
                (<= (abs x) (spn k))
                (drepp a n k)
                (<= a x))
           (<= a (drnd-original x 'minf n k)))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable rnd ;drepp
                                      drnd-original-rewrite
                                      minf)
                              '(
                                drnd-original-away-skips-no-denormals
                                 drnd-original-trunc-skips-no-denormals))
          :use ((:instance drnd-original-away-skips-no-denormals (x (- x)))
                (:instance drnd-original-trunc-skips-no-denormals)))))



(local
 (defthm hack1
   (implies (and (< n 0)
                 (>= x 0)
                 (rationalp x)
                 (integerp n)
                 )
            (>= (EXPT 2 (+ (EXPO X) (* -1 N)))
                X))
   :hints (("Goal" :use (:instance expo<=-2 (n (+ (EXPO X) (* -1 N))))))))

;BOZO this hack shouldn't be needed
(local
 (defthm hack2
   (implies (and (rationalp x)
                 (integerp n)
                 (< n 0)
                 (>= x 0))
            (>= (EXPT 2 (+ 1 (EXPO X) (* -1 N)))
                (* 2 X)))
   :hints (("Goal" :in-theory (set-difference-theories
                               (enable expt-split)
                               '( hack1 expo<=-2))
            :use (hack1
                  (:instance a15 (i 2) (j1 1) (j2 (+ (EXPO X) (* -1 N)))))))))

;BOZO in trying to improve this I enabled sig, which caused a loop
;try
(local
 (defthm near1-b-negative-n
   (implies (and (rationalp x)
                 (>= x 0)
                 (integerp n)
                 (<= n 0)
                 (> (- x (trunc x n)) (- (away x n) x)))
            (= (near x n) (away x n)))
   :rule-classes ()
   :hints (("Goal" :in-theory (set-difference-theories
                               (enable sgn near expt-split re)
                               '(                                     ;FL-EQUAL-0
                                 EXPT-COMPARE
                                 FL-EQUAL-0
                                 hack2 EXPO-BOUND-ERIC
                                 expo>=-2 expo<=-2
                                 ;; MattK: The following disable is needed by
                                 ;; v2-8-alpha-12-30-03 (and somewhat before,
                                 ;; but not in June 03).  I haven't
                                 ;; investigated why exactly, but from the
                                 ;; transcript it seems that the new use of
                                 ;; linear arithmetic for type-set is the
                                 ;; culprit.  I don't have any reason to
                                 ;; believe that this exposes a problem with
                                 ;; that new use; I'm happy to assume that it's
                                 ;; just an artifact of this particular proof
                                 ;; approach, at least for now.
                                 expt-2-positive-rational-type
                                 ))
            :use (expo-upper-bound
                  hack2
                  (:instance expt-strong-monotone (m (+ (EXPO X) (* -1 N))) (n (EXPO X)))
                  (:instance expt-weak-monotone (n n) (m 0))
                  (:instance expt-weak-monotone (n n) (m -1))
                  (:instance fl-unique (x (* 1/2 (SIG X) (EXPT 2 N)))
                             (n 0))
                  )))))


;BOZO could replace the version in near.lisp
(defthm near1-b-eric
    (implies (and (rationalp x)
		  (>= x 0)
		  (integerp n)
		  (> (- x (trunc x n)) (- (away x n) x)))
	     (= (near x n) (away x n)))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable near away trunc)
		  :use (near1-b
                        near1-b-negative-n))))



(defthm drnd-original-near-2-1
  (implies (and (rationalp x)
                (<= x (spn k))
                (rationalp a)
                (integerp n)
                (> n 1)
                (integerp k)
                (> k 0)
                (> x 0)
                (drepp a n k)
                (= (drnd-original x 'near n k) (drnd-original x 'trunc n k)))
           (>= (abs (- x a)) (abs (- x (drnd-original x 'trunc n k)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable rnd bias drnd-original-rewrite)
                              '(  away-exactp-c
				      near trunc-exactp-c
                                      drnd-original-away-skips-no-denormals
                                      drnd-original-trunc-skips-no-denormals
                                      ))
           :use ((:instance near1-b-eric (n (+ -2 N (EXPO X) (EXPT 2 (1- K)))))
                 (:instance away-lower-pos (n (+ -2 N (EXPO X) (EXPT 2 (1- K)))))
                 (:instance trunc-upper-pos (n (+ -2 N (EXPO X) (EXPT 2 (1- K)))))
                 (:instance drnd-original-away-skips-no-denormals )
                 (:instance drnd-original-trunc-skips-no-denormals)))))

(defthm drnd-original-near-2-2
  (implies (and (rationalp x)
                (<= x (spn k))
                (rationalp a)
                (integerp n)
                (> n 1)
                (integerp k)
                (> k 0)
                (> x 0)
                (drepp a n k)
                (= (drnd-original x 'near n k) (drnd-original x 'away n k)))
           (>= (abs (- x a)) (abs (- x (drnd-original x 'away n k)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable rnd bias drnd-original-rewrite)
                              '( drnd-original-away-skips-no-denormals
                                 drnd-original-trunc-skips-no-denormals
                                 away-exactp-c
                                 trunc-exactp-c
                                 ))
           :use ((:instance near1-a (n (+ -2 N (EXPO X) (EXPT 2 (1- K)))))
                 (:instance away-lower-pos (n (+ -2 N (EXPO X) (EXPT 2 (1- K)))))
                 (:instance trunc-upper-pos (n (+ -2 N (EXPO X) (EXPT 2 (1- K)))))
                 (:instance drnd-original-away-skips-no-denormals )
                 (:instance drnd-original-trunc-skips-no-denormals)))))

(defthm drnd-original-near-choice
  (implies (and (rationalp x)
                (integerp n)
                (> n 1)
                (integerp k)
                (> k 0)
                (<= (abs x) (spn k)))
           (or (= (drnd-original x 'near n k) (drnd-original x 'trunc n k))
               (= (drnd-original x 'near n k) (drnd-original x 'away n k))))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable rnd near drnd-original-rewrite)
                              '(re evenp))))
  :rule-classes ())

;BOZO
;(in-theory (disable SPD))

(defthm no-denormal-is-closer-than-what-drnd-original-near-returns-pos
  (implies (and (rationalp x)
                (>= x 0)
                (<= x (spn k))
                (integerp n)
                (> n 1)
                (integerp k)
                (> k 0)
                (drepp a n k))
           (>= (abs (- x a)) (abs (- x (drnd-original x 'near n k)))))
  :hints (("Goal" :in-theory (disable

                              drnd-original-rewrite
                              drnd-original-non-neg
                              DRND-ORIGINAL-AWAY-SKIPS-NO-DENORMALS-POS)
           :use ((:instance drnd-original-near-2-1)
                 (:instance drnd-original-near-2-2)
                 (:instance drnd-original-near-choice)))))

(defthm no-denormal-is-closer-than-what-drnd-original-near-returns-neg
  (implies (and (rationalp x)
                (<= x 0)
                (<= (abs x) (spn k))
                (integerp n)
                (> n 1)
                (integerp k)
                (> k 0)
                (drepp a n k))
           (>= (abs (- x a)) (abs (- x (drnd-original x 'near n k)))))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable drnd-original-minus)
                              '(drnd-original-rewrite
                                drnd-original-non-pos
                                drnd-original-non-neg
                                spn
                                no-denormal-is-closer-than-what-drnd-original-near-returns-pos
                                DRND-ORIGINAL-AWAY-SKIPS-NO-DENORMALS-POS))
           :use ((:instance no-denormal-is-closer-than-what-drnd-original-near-returns-pos
                            (x (- x)) (a (- a)))))))


(defthm no-denormal-is-closer-than-what-drnd-original-near-returns
  (implies (and (rationalp x)
                (<= (abs x) (spn k))
                (integerp n)
                (> n 1)
                (integerp k)
                (> k 0)
                (drepp a n k))
           (>= (abs (- x a)) (abs (- x (drnd-original x 'near n k)))))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable)
                              '(drnd-original-rewrite
                                drnd-original-non-pos
                                drnd-original-non-neg
                                spn
                                DRND-ORIGINAL-AWAY-SKIPS-NO-DENORMALS-POS
                                no-denormal-is-closer-than-what-drnd-original-near-returns-pos
                                no-denormal-is-closer-than-what-drnd-original-near-returns-neg))
           :use (no-denormal-is-closer-than-what-drnd-original-near-returns-pos
                 no-denormal-is-closer-than-what-drnd-original-near-returns-neg))))

;could speed up the above with a :cases hint instead of :use hints?




#|
;remove these?
(defthm drnd-original-trunc-never-goes-up-for-pos-args
  (implies (and (integerp n)
                (> n 1)
                (integerp k)
                (> k 0)
                (rationalp x)
                (<= 0 x)
                (<= x (spn k)))
           (<= (drnd-original x 'trunc n k)
               x))
  :hints (("Goal" :in-theory (enable rnd)
           :use (:instance trunc-upper-bound
                                  (n (+ -2 N (EXPO X) (EXPT 2 (1- K))))))))


(defthm drnd-original-away-never-goes-down-for-pos-args
  (implies (and (integerp n)
                (> n 1)
                (integerp k)
                (> k 0)
                (rationalp x)
                (<= 0 x)
                (<= x (spn k)))
           (>= (drnd-original x 'away n k)
               x))
  :hints (("Goal" :in-theory (enable rnd)
           :use (:instance away-lower-bound
                                  (n (+ -2 N (EXPO X) (EXPT 2 (1- K))))))))
|#

;why?
(in-theory (disable expo< expo>))





