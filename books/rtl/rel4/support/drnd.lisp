(in-package "ACL2")

(local (include-book "merge"))
(include-book "ireps") ;make local?
(local (include-book "rnd"))
(local (include-book "bias"))
(local (include-book "sgn"))
(local (include-book "bits"))
(local (include-book "trunc"))
(local (include-book "away"))
(local (include-book "near"))
(local (include-book "near+"))
(local (include-book "sticky"))
(local (include-book "../arithmetic/top"))

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

(defund exactp (x n)
;  (declare (xargs :guard (and (real/rationalp x) (integerp n))))
  (integerp (* (sig x) (expt 2 (1- n)))))

(defun fp+ (x n)
  (+ x (expt 2 (- (1+ (expo x)) n))))

(defund trunc (x n)
  (declare (xargs :guard (integerp n)))
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

(defund rounding-mode-p (mode)
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

(defund drnd (x mode n k)
  (- (rnd (+ x (* (sgn x) (expt 2 (- 2 (expt 2 (1- k)))))) mode n)
     (* (sgn x) (expt 2 (- 2 (expt 2 (1- k)))))))

(defthmd drnd-minus
  (equal (drnd (* -1 x) mode n k)
         (* -1 (drnd x (flip mode) n k)))
  :hints (("Goal" :in-theory
           (enable drnd)
           :use ((:instance rnd-minus
                            (x (+ x (* (sgn x) (expt 2 (- 2 (expt 2 (1- k))))))))))))

(defthm drnd-0
  (equal (drnd 0 mode n k)
         0)
  :hints (("Goal" :in-theory (enable drnd))))


(local (defthm drnd-sticky-pos
    (implies (and (rounding-mode-p mode)
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
	     (equal (drnd (sticky x m) mode n k)
		    (drnd x mode n k)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable sgn drnd rnd-sticky)
		  :use (expo-upper-bound
			expo-lower-bound
			(:instance sticky-pos (n m))
			(:instance sticky-plus
				   (x (expt 2 (- 2 (expt 2 (1- k)))))
				   (y x)
				   (k m)
				   (k1 (- (+ m 2) (+ (expt 2 (1- k)) (expo x))))
				   (k2 (- (+ m 2) (+ (expt 2 (1- k)) (expo x)))))
			(:instance exactp-2**n
				   (n (- 2 (expt 2 (1- k))))
				   (m (- (+ m 1) (+ (expt 2 (1- k)) (expo x))))))))))

(defthm drnd-sticky
  (implies (and (rounding-mode-p mode)
                (natp n)
                (> n 0)
                (natp m)
                (> m 1)
                (natp k)
                (> k 0)
                (rationalp x)
                (<= (expo x) (- 1 (expt 2 (1- k))))
                (<= (expo x) (- m (+ n (expt 2 (1- k))))))
           (equal (drnd (sticky x m) mode n k)
                  (drnd x mode n k)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable drnd-minus)
           :use (drnd-sticky-pos
                 (:instance drnd-sticky-pos (mode (flip mode)) (x (- x)))
                 ))))

(local (defthm drnd-bnd-1
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
  :hints (("Goal" :in-theory (disable trunc-exactp-b trunc-exactp-c)
		  :use (trunc-exactp-b
			trunc-upper-pos
			(:instance expt-split (r 2) (j (- 1 n)) (i (- 2 (expt 2 (1- k)))))
			(:instance trunc-exactp-c (a (expt 2 (- 2 (expt 2 (1- k))))))
			(:instance exactp-2**n (n (- 2 (expt 2 (1- k)))) (m n))
			(:instance fp+1
				   (y (trunc x n))
				   (x (expt 2 (- 2 (expt 2 (1- k)))))))))))



(local (defthm drnd-bnd-2
    (implies (and (natp n)
		  (> n 0)
		  (natp k)
		  (> k 0)
		  (rationalp x)
		  (>= x 0)
		  (< x (expt 2 (- 3 (+ n (expt 2 (1- k)))))))
	     (equal (drnd x 'trunc n k)
		    0))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable sgn rnd drnd)
           :use trunc-0))))



(local (defthm drnd-bnd-3
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
  :hints (("Goal" :in-theory (disable away-exactp-b away-exactp-c)
		  :use (away-exactp-b
			away-lower-pos
			(:instance expt-split (r 2) (j (- 1 n)) (i (- 2 (expt 2 (1- k)))))
			(:instance away-exactp-c
				   (a (+ (expt 2 (- 2 (expt 2 (1- k))))
					 (expt 2 (- 3 (+ n (expt 2 (1- k))))))))
			(:instance exactp-2**n (n (- 2 (expt 2 (1- k)))) (m n))
			(:instance fp+2
				   (x (expt 2 (- 2 (expt 2 (1- k))))))
			(:instance fp+1
				   (y (away x n))
				   (x (expt 2 (- 2 (expt 2 (1- k)))))))))))

(local (defthm drnd-bnd-4
    (implies (and (natp n)
		  (> n 0)
		  (natp k)
		  (> k 0)
		  (rationalp x)
		  (> x 0)
		  (<= x (expt 2 (- 3 (+ n (expt 2 (1- k)))))))
	     (equal (drnd x 'inf n k)
		    (expt 2 (- 3 (+ n (expt 2 (1- k)))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable sgn rnd drnd inf)))))

(local (defthm drnd-bnd-5
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

(local (defthm drnd-bnd-6
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
           :use (drnd-bnd-5
			(:instance expt-weak-monotone
				   (n (- 2 (+ n (expt 2 (1- k)))))
				   (m (- 3 (+ n (expt 2 (1- k)))))))))))

(local (defthm drnd-bnd-7
    (implies (and (natp n)
		  (> n 0)
		  (natp k)
		  (> k 0)
		  (rationalp x)
		  (> x 0)
		  (< x (expt 2 (- 2 (+ n (expt 2 (1- k)))))))
	     (equal (drnd x 'near n k)
		    0))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable sgn rnd drnd)))))

(local (defthm drnd-bnd-8
    (implies (and (ieee-mode-p m)
		  (natp n)
		  (> n 0)
		  (natp k)
		  (> k 0)
		  (rationalp x)
		  (> x 0)
		  (< x (expt 2 (- 2 (+ n (expt 2 (1- k)))))))
	     (equal (drnd x m n k)
		    (if (eql m 'inf)
			(expt 2 (- 3 (+ n (expt 2 (1- k)))))
		      0)))
  :rule-classes ()
  :hints (("Goal" :in-theory (e/d (ieee-mode-p sgn rnd drnd minf inf) (expt-compare))
		  :use (drnd-bnd-2
			drnd-bnd-4
			drnd-bnd-7
			(:instance expt-weak-monotone
				   (n (- 2 (+ n (expt 2 (1- k)))))
				   (m (- 3 (+ n (expt 2 (1- k)))))))))))

(local (defthm drnd-bnd-9
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
	     (equal (drnd x m n k)
		    (drnd y m n k)))
  :rule-classes ()
  :hints (("Goal" :use (drnd-bnd-8
			(:instance drnd-bnd-8 (x y)))))))

(defthm drnd-tiny-equal
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
	     (equal (drnd x m n k)
		    (drnd y m n k)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable sgn  DRND-minus)
		  :use ((:instance drnd-bnd-9 (m (if (< x 0) (flip m) m)) (x (abs x)) (y (abs y)))))))



;beginning of Eric's drnd lemmas.  Throughout, n is the number of significand bits
;(counting the implicit leading zero), and k is the number of exponent bits.

;it doesn't make sense for n to be 0 (no bits of significand).  Since n counts the
;implicit 0, n=1 is also questionable.

;It doesn't make sense for k to be 0 (no bits of exponent).  Having k=1 is also
;questionable, since that would allow only 2 possible exponent values, both
;reserved (one reserved for denormals).

(defund smallest-positive-normal (k)
  (expt 2 (- 1 (bias k))))

(defund smallest-positive-denormal (n k)
     (expt 2 (+ 2 (- (bias k)) (- n))))


(defthm expo-spn
  (implies (and (case-split (acl2-numberp k))
                (case-split (< 0 k)))
           (equal (expo (smallest-positive-normal k))
                  (+ 1 (* -1 (bias k)))))
  :hints (("Goal" :in-theory (enable  smallest-positive-normal))))

(defthm expo-spd
  (implies (and (case-split (acl2-numberp k))
                (case-split (integerp n))
                (case-split (< 0 k)))
           (equal (expo (smallest-positive-denormal n k))
                  (+ 2 (- (bias k)) (- n))))
  :hints (("Goal" :in-theory (enable smallest-positive-denormal))))

(defthm spn-positive-rational-type
  (and (rationalp (smallest-positive-normal k))
       (> (smallest-positive-normal k) 0))
  :rule-classes (:type-prescription ))

(defthm positive-spn
  (> (smallest-positive-normal k) 0)
  :rule-classes (:linear))

(defthm nrepp-spn
  (implies (and (integerp n)
                (> n 0)
                (integerp k)
                (> k 1))
           (nrepp (smallest-positive-normal k) n k))
  :hints (("goal" :in-theory (enable nrepp SMALLEST-POSITIVE-NORMAL)
           :use ((:instance exactp-2**n
                            (n (+ 1 (* -1 (bias k))))
                            (m n))
                 (:instance expt-strong-monotone
                            (n 1)
                            (m k))))))

(defthm smallest-spn
  (implies (and (nrepp x n k) ;n is a free var
                (integerp n)
                (> n 0)
                (integerp k)
                (> k 1)
                )
           (>= (abs x) (smallest-positive-normal k)))
  :rule-classes ((:rewrite :match-free :once))
  :hints (("goal" :in-theory (enable nrepp; bias
                                     SMALLEST-POSITIVE-NORMAL
                                     )
           :use (fp-abs
                 sig-lower-bound
                 (:instance expt-weak-monotone
                            (n (- 1 (bias k)))
                            (m (expo x)))))))

;uses bias to avoid having to open bias in proofs below
(defthmd drnd-def
  (equal (drnd x mode n k)
         (- (rnd (+ x
                    (* (sgn x)
                       (expt 2 (- 1 (bias k)))))
                 mode n)
            (* (sgn x)
               (expt 2 (- 1 (bias k))))))
  :hints (("goal" :in-theory (enable drnd bias))))

(defthmd drnd-spn
  (implies (and (rounding-mode-p mode)
                (integerp n)
                (> n 0)
                (integerp k)
                (> k 0))
           (equal (drnd (smallest-positive-normal k) mode n k)
                  (rnd (smallest-positive-normal k)
                       mode
                       (+ n
                          (- (expo (smallest-positive-normal k)))
                          (+ 1 (* -1 (BIAS K)))))))
  :hints (("goal" :in-theory (set-difference-theories
                              (enable drnd-def ;sgn
                                      SMALLEST-POSITIVE-NORMAL
;      expt-split
;     expt-minus
                                      )
                              '(a15
                                EXPT-COMPARE-EQUAL))
           :use ((:instance rnd-exactp-a (x (expt 2 (+ 2 (* -1 (bias k))))))
                 (:instance rnd-exactp-a (x (expt 2 (+ 1 (* -1 (bias k))))))
                 (:instance a15
                            (i 2)
                            (j1 (+ 1 (- (bias k))))
                            (j2 1))
                 ))))

(local (defthmd drnd-rewrite-1
         (implies (and (rationalp x)
                       (<= 0 x)
                       (< x (smallest-positive-normal k))
                       (rounding-mode-p mode)
                       (integerp n)
                       (> n 1)
                       (integerp k)
                       (> k 0))
                  (equal (drnd x mode n k)
                         (rnd x
                              mode
                              (+ n (- (expo (smallest-positive-normal k))) (expo x)))))
         :hints (("goal" :in-theory (set-difference-theories
                                     (enable drnd-def sgn ;rounding-mode-p ;ieee-mode-p
                                             expt ;expt-split ;why?
                                             ;bias
                                             SMALLEST-POSITIVE-NORMAL
                                             )
                                     '(                                       ;SMALLEST-POSITIVE-NORMAL
                                       rounding-mode-p
                                       expo-x+2**k))
                  :use ((:instance plus-rnd
                                   (y x)
                                   (x (smallest-positive-normal k))
                                   (k (+ n (expo x) (- (expo
                                                        (smallest-positive-normal k))))))
                        (:instance expo-x+2**k
                                   (k (+ 1 (* -1 (bias k)))))
                        (:instance expo<=
                                   (n (* -1 (bias k)))))))
         :otf-flg t))

(local
 (defthmd drnd-rewrite-pos
  (implies (and (rationalp x)
                (<= 0 x)
                (<= x (smallest-positive-normal k))
                (rounding-mode-p mode)
                (integerp n)
                (> n 1)
                (integerp k)
                (> k 0))
           (equal (drnd x mode n k)
                  (rnd x
                       mode
                       (+ n (- (expo (smallest-positive-normal k))) (expo x)))))
  :hints (("goal" :in-theory (disable smallest-positive-normal ROUNDING-MODE-P)
           :use (drnd-rewrite-1 drnd-spn )))))

(local
 (defthmd drnd-rewrite-neg
   (implies (and (rationalp x)
                 (<= (- (smallest-positive-normal k)) x)
                 (<= x 0)
                 (rounding-mode-p mode)
                 (integerp n)
                 (> n 1)
                 (integerp k)
                 (> k 0))
            (equal (drnd x mode n k)
                   (rnd x
                        mode
                        (+ n (- (expo (smallest-positive-normal k))) (expo x)))))
   :hints (("goal" :in-theory (enable drnd-rewrite-pos )
            :use ((:instance drnd-minus (mode (flip mode)))
                  (:instance
                   rnd-minus (x (- x)) (mode mode)
                   (n (+ -1 n (expo x) (bias k)))))))))

;why enable so much?
(defthmd drnd-rewrite
  (implies (and (rationalp x)
                (<= (abs x) (smallest-positive-normal k))
                (rounding-mode-p mode)
                (integerp n)
                (> n 1)
                (integerp k)
                (> k 0))
           (equal (drnd x mode n k)
                  (rnd x
                       mode
                       (+ n
                          (- (expo (smallest-positive-normal k)))
                          (expo x)))))
  :hints (("Goal" :in-theory (enable drnd-rewrite-pos drnd-rewrite-neg))))

(defthm drepp-range
  (implies (and (drepp x n k)
                (integerp n)
                (>= n 0)
                (integerp k)
                (> k 0)
                )
           (<= (abs x)
               (smallest-positive-normal k)))
  :hints (("Goal" :in-theory (enable bias drepp SMALLEST-POSITIVE-NORMAL)
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

(defthm drnd-of-drepp-is-NOP
  (implies (and (drepp x n k)
                (integerp n)
                (> n 1)
                (integerp k)
                (> k 0)
                (rounding-mode-p mode))
           (equal (drnd x mode n k)
                  x))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable drepp-def
                                      )
                              '( SMALLEST-POSITIVE-NORMAL))
           :use (drnd-rewrite
                 drepp-range
                 (:instance rnd-exactp-a
                            (n (+ n
                                  (- (expo (smallest-positive-normal k)))
                                  (expo x))))))))
;move up?
(defthm spn-1-exact
  (implies (and (case-split (integerp k))
                (case-split (> k 0)))
           (exactp (smallest-positive-normal k) 1))
  :hints (("Goal" :in-theory (enable smallest-positive-normal))))

(defthm spd-1-exact
  (implies (and (case-split (integerp k))
                (case-split (integerp n))
                (case-split (> k 0)))
           (exactp (smallest-positive-denormal n k) 1))
  :hints (("Goal" :in-theory (enable smallest-positive-denormal)))
  )

;(in-theory (enable drnd-spn))

(defthm drnd-spn-is-spn
  (implies (and (rounding-mode-p mode)
                (integerp n)
                (>= n 1)
                (integerp k)
                (> k 0))
           (= (drnd (smallest-positive-normal k) mode n k)
              (smallest-positive-normal k))
           )
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable IEEE-MODE-P)
                              '( spn-1-exact
                                 SMALLEST-POSITIVE-NORMAL
                                      drnd-spn
                                      ))
           :use ( drnd-spn
                  (:instance exactp-<= (m 1)
                             (x (smallest-positive-normal k)))
                  (:instance spn-1-exact)
                  (:instance rnd-exactp-a
                             (x (smallest-positive-normal k))
;                             (m mode)
                             (n n))))))

;can be expensive..
(defthmd drnd-spn-is-spn-general
  (implies (and (= (abs x) (smallest-positive-normal k))
                (rounding-mode-p mode)
                (integerp n)
                (>= n 1)
                (integerp k)
                (> k 0)
                (rationalp x)
                )
           (= (drnd x mode n k)
              x)
           )
  :hints (("Goal" :in-theory (disable smallest-positive-normal drnd-rewrite drnd-spn)
           :use (:instance drnd-minus (mode (flip mode))))))

;(in-theory (disable drnd-spn))

;(in-theory (enable drnd-rewrite)) ;BOZO yuck!

(defthm drnd-trunc-never-goes-away-from-zero
  (implies (and (integerp n)
                (> n 1)
                (integerp k)
                (> k 0)
                (rationalp x)
                (<= (abs x) (smallest-positive-normal k)))
           (<= (abs (drnd x 'trunc n k))
               (abs x)))
  :hints (("Goal" :in-theory (enable rnd drnd-rewrite)
           :use (:instance trunc-upper-bound
                           (n (+ -1 N (EXPO X) (bias k)))))))

(defthm drnd-away-never-goes-toward-zero
  (implies (and (integerp n)
                (> n 1)
                (integerp k)
                (> k 0)
                (rationalp x)
                (<= (abs x) (smallest-positive-normal k)))
           (>= (abs (drnd x 'away n k))
               (abs x)))
  :hints (("Goal" :in-theory (enable rnd drnd-rewrite)
           :use (:instance away-lower-bound
                (n (+ -1 N (EXPO X) (bias k)))))))

(defthm drnd-inf-never-goes-down
  (implies (and (integerp n)
                (> n 1)
                (integerp k)
                (> k 0)
                (rationalp x)
                (<= (abs x) (smallest-positive-normal k)))
           (>= (drnd x 'inf n k)
               x))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable rnd drnd-rewrite)
                              '(expo-2**n abs-pos)))))

(defthm drnd-minf-never-goes-up
  (implies (and (integerp n)
                (> n 1)
                (integerp k)
                (> k 0)
                (rationalp x)
                (<= (abs x) (smallest-positive-normal k)))
           (<= (drnd x 'minf n k)
               x))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable rnd drnd-rewrite)
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

(defthm drnd-trunc-skips-no-denormals
  (implies (and (integerp n)
                (> n 1)
                (integerp k)
                (> k 0)
                (rationalp x)
                (<= (abs x) (smallest-positive-normal k))
                (drepp a n k)
                (<= (abs a) (abs x))
                )
           (<= (abs a)
               (abs (drnd x 'trunc n k))))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable rnd drepp-def drnd-rewrite
                                      )
                              '(trunc-exactp-c-eric
                                 EXPO-COMPARISON-REWRITE-TO-BOUND-2
                                  EXPO-COMPARISON-REWRITE-TO-BOUND
                                smallest-positive-normal))
           :use (
                 (:instance exactp-<=
                            (x a)
                            (m (+ -1 N (EXPO A) (bias k)))
                            (n (+ -1 N (EXPO x) (bias k))))
                 (:instance trunc-exactp-c-eric (n (+ -1 N (EXPO X) (bias k))))
                 (:instance expo-monotone (x a) (y x))))))


(defthm drnd-trunc-skips-no-rep-numbers
  (implies (and (integerp n)
                (> n 1)
                (integerp k)
                (> k 1)
                (rationalp x)
                (<= (abs x) (smallest-positive-normal k))
                (irepp a n k)
                (<= (abs a) (abs x))
                )
           (<= (abs a)
               (abs (drnd x 'trunc n k))))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable irepp DRND-SPN-IS-SPN-GENERAL )
                              '(drnd-trunc-skips-no-denormals

                                  DRND-SPN-IS-SPN
                                smallest-spn
                                smallest-positive-normal drnd-rewrite))
           :use (drnd-trunc-skips-no-denormals
                 (:instance smallest-spn (x a))))
          ("goal'"
           :cases ((and (nrepp a n k) (< (abs x) (smallest-positive-normal k)))
                   (and (drepp a n k) (< (abs x) (smallest-positive-normal k)))))))

(defthm positive-spd
  (implies (and (integerp n)
                (> n 1)
                (integerp k)
                (> k 0))
           (> (smallest-positive-denormal n k) 0)))

(defthm drepp-spd
  (implies (and (integerp n)
                (> n 1)
                (integerp k)
                (> k 0))
           (drepp (smallest-positive-denormal n k) n k))
  :hints (("goal" :in-theory (enable drepp-DEF ;bias
                                     ))))


(defthm smallest-spd
  (implies (and (integerp n)
                (> n 1)
                (integerp k)
                (> k 0)
                (drepp x n k))
           (>= (abs x) (smallest-positive-denormal n k)))
  :hints (("goal" :in-theory (enable drepp SMALLEST-POSITIVE-DENORMAL)
           :use (sig-lower-bound
                 fp-abs
                 (:instance expt-weak-monotone
                            (n (+ 2 (* -1 n) (* -1 (bias k))))
                            (m (expo x)))))))


;BOZO.  if we try to scatter exponents here, we don't gather the constants...
(defthm drnd-trunc-of-low-range
  (implies (and (rationalp x)
                (< (abs x) (abs (smallest-positive-denormal n k)))
                (integerp n)
                (> n 1)
                (integerp k)
                (> k 0))
           (= (drnd x 'trunc n k)
              0))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable drnd-rewrite rnd sgn
                                      SMALLEST-POSITIVE-DENORMAL
                                      SMALLEST-POSITIVE-NORMAL
                                      bias ;drop?
;                                      EXPT-COMPARE-EQUAL
;expt-split expt-minus
                                      )
                              '(a15 ;smallest-positive-normal
;smallest-positive-denormal
                                EXPT-COMPARE-EQUAL
                                EXPT-COMPARE
                                ))
           :use ((:instance expt-strong-monotone
                            (n (expo (smallest-positive-denormal n k)))
                            (m (expo (smallest-positive-normal k))))
                 (:instance trunc-to-0-or-fewer-bits
                            (n (+ -1 N (EXPO X) (bias k))))
                 (:instance a15 (i 2) (j1 1) (j2 (+ 1 (* -1 N)
                                                    (* -1 (bias k)))))
                 (:instance expo<= (n (+ 1 (* -1 N)
                                         (* -1 (bias k)))))
                 (:instance expo<= (x (- x))
                            (n (+ 1 (* -1 N)
                                  (* -1 (bias k)))))))))

(defthm drnd-away-of-low-range
  (implies (and (rationalp x)
                (< (abs x) (abs (smallest-positive-denormal n k)))
                (integerp n)
                (> n 1)
                (integerp k)
                (> k 0))
           (= (drnd x 'away n k)
              (* (sgn x) (smallest-positive-denormal n k))))
  :hints (("Goal"  :in-theory (set-difference-theories
                               (enable drnd-rewrite rnd sgn bias
                                       smallest-positive-normal
                                       smallest-positive-denormal)
                               '(a15 ;
                                                                 EXPT-COMPARE-EQUAL
                                EXPT-COMPARE
                                     ))
           :use ((:instance expt-strong-monotone
                            (n (expo (smallest-positive-denormal n k)))
                            (m (expo (smallest-positive-normal k))))
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
  (< (smallest-positive-denormal n k)
     (smallest-positive-normal k)))
;  :rule-classes :linear
  :hints (("Goal" :in-theory (enable smallest-positive-denormal
                                     smallest-positive-normal)
           :use (:instance expt-strong-monotone
                                  (n (+ 2 (* -1 N) (* -1 (bias k))))
                                  (m (+ 1          (* -1 (bias k))))))))

#|
(defthm abs-spd-<-abs-spn
  (implies (and (integerp n)
                (> n 1)
                (> k 0)
                (integerp k))
  (< (abs (smallest-positive-denormal n k))
     (abs (smallest-positive-normal k))))
 ; :rule-classes :linear
  :hints (("Goal" :in-theory (disable smallest-positive-denormal smallest-positive-normal))))
|#

;move or drop?
(defthm abs-prod
  (implies (and (rationalp x)
                (rationalp y))
           (= (abs (* x y))
              (* (abs x) (abs y))))
  :hints (("Goal" :in-theory (enable sgn))))

(defthm drnd-of-low-range
  (implies (and (rationalp x)
                (< (abs x) (abs (smallest-positive-denormal n k)))
                (integerp n)
                (> n 1)
                (integerp k)
                (> k 0)
                (rounding-mode-p mode))
           (or (= (drnd x mode n k) 0)
               (= (abs (drnd x mode n k)) (smallest-positive-denormal n k))))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable rnd inf minf near near+ ieee-mode-p rounding-mode-p sgn drnd-rewrite
                                      )
                              '(smallest-positive-denormal
                                smallest-positive-normal
                                abs
                                abs-away
                                drnd-away-of-low-range
                                drnd-trunc-of-low-range
                                spd-<-spn
;                                drnd-rewrite
                                rearrange-negative-coefs-equal))
           :use (;drnd-rewrite
                 spd-<-spn
                 drnd-away-of-low-range drnd-trunc-of-low-range)))
  :rule-classes nil)

(defthm drnd-spd-is-spd
  (implies (and (rounding-mode-p mode)
                (integerp n)
                (> n 1)
                (integerp k)
                (> k 0))
           (= (drnd (smallest-positive-denormal n k) mode n k)
              (smallest-positive-denormal n k))
           )
  :hints (("Goal" :in-theory (disable smallest-positive-denormal))))

(defthm drepp-minus
  (implies (and (rationalp x)
                (integerp n)
                (> n 1)
                (integerp k)
                (> k 0))
           (= (drepp (* -1 x) n k) (drepp x n k)))
  :hints (("Goal" :in-theory (enable drepp))))

;can be expensive
(defthmd drnd-spd-is-spd-general
  (implies (and (= (abs x) (smallest-positive-denormal n k))
                (rounding-mode-p mode)
                (integerp n)
                (> n 1)
                (integerp k)
                (> k 0)
                (rationalp x)
                )
           (= (drnd x mode n k)
              x)
           )
  :hints (("Goal" :in-theory (disable smallest-positive-denormal drnd-rewrite
                                      DRND-OF-DREPP-IS-NOP
                                      drepp-spd)
           :use ((:instance drepp-spd)
                 (:instance DRND-OF-DREPP-IS-NOP (x (- x)))
                 (:instance DRND-OF-DREPP-IS-NOP )))))




(defund largest-positive-denormal (n k)
  (- (smallest-positive-normal k)
     (smallest-positive-denormal n k)))


(defthm positive-lpd
  (implies (and (integerp n)
                (> n 1)
                (integerp k)
                (> k 0))
           (> (largest-positive-denormal n k) 0))
  :hints (("goal" :in-theory (enable drepp bias; SMALLEST-POSITIVE-NORMAL
;                                     SMALLEST-POSITIVE-deNORMAL
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
              (1- (expo (smallest-positive-normal k)))))
  :hints (("Goal" :in-theory (enable largest-positive-denormal
                                     SMALLEST-POSITIVE-NORMAL
                                     SMALLEST-POSITIVE-deNORMAL))))

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
                                   SMALLEST-POSITIVE-NORMAL
                                   SMALLEST-POSITIVE-deNORMAL) ( exactp-diff-of-powers-of-2))
           :use (:instance
                        exactp-diff-of-powers-of-2
                        (m (expo (smallest-positive-normal k)))
                        (n (expo (smallest-positive-denormal n k)))))))

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
                                      SMALLEST-POSITIVE-NORMAL
                                      SMALLEST-POSITIVE-deNORMAL)
                              '(expo<=-2))
           :use ((:instance expo<=-2 (n (+ 1 (* -1 (bias k)))))
                 (:instance fp+1
                            (y (EXPT 2 (+ 1 (* -1 (bias k)))))
                            (n (+ -1 n (EXPO X) (bias k)))
                            )))))

;why? :
(local (in-theory (disable expo-monotone)))
(local (in-theory (disable expt-weak-monotone-linear)))

;rephrase using bias?
(defthm drepp-drnd-exactness
  (implies (and (rationalp x)
                (< (smallest-positive-denormal n k) x)
                (< x (smallest-positive-normal k))
                (integerp n)
                (> n 1)
                (integerp k)
                (> k 0)
                (rounding-mode-p m))
           (exactp (drnd x m n k) (+ -2 n (expt 2 (- k 1)) (expo (drnd x m n k)))))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable bias
                                      drnd-rewrite
                                      smallest-positive-normal
                                      smallest-positive-denormal
                                      ) ;drop?
                              '(expo>))
           :use ((:instance expo-rnd (mode m) (n (+ -1 N (EXPO X)
                                                    (bias k))))
                 (:instance expo> (n (+ 1 (- n ) (- (bias k)))))))))


(defthm drepp-drnd-expo-1
  (implies (and (rationalp x)
                (< (smallest-positive-denormal n k) x)
                (< x (smallest-positive-normal k))
                (integerp n)
                (> n 1)
                (integerp k)
                (> k 0)
                (rounding-mode-p m))
           (<= (- 2 n) (+ (expo (drnd x m n k)) (bias k))))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable smallest-positive-normal
                                      drnd-rewrite
                                      smallest-positive-denormal)
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


(defthm drepp-drnd-expo-2
  (implies (and (rationalp x)
                (< (smallest-positive-denormal n k) x)
                (< x (largest-positive-denormal n k))
                (integerp n)
                (> n 1)
                (integerp k)
                (> k 0)
                (rounding-mode-p m))
           (<= (+ (expo (drnd x m n k)) (bias k)) 0))
  :hints (("goal" :in-theory (set-difference-theories
                              (enable ;expt-split
                               bias ;drop
                               largest-positive-denormal
                               smallest-positive-normal
                               smallest-positive-denormal
                               drnd-rewrite
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
(defthm drepp-drnd-expo-2
  (implies (and (rationalp x)
                (< (smallest-positive-denormal n k) x)
                (< x (largest-positive-denormal n k))
                (integerp n)
                (> n 1)
                (integerp k)
                (> k 0)
                (rounding-mode-p m))
           (<= (+ (expo (drnd x m n k)) (bias k)) 0))
  :hints (("goal" :cases (< x 0)
           :in-theory (set-difference-theories
                              (enable ;expt-split
;                               bias ;drop
                               expt-split
                               drnd-rewrite
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


(defthm drepp-drnd-not-0
  (implies (and (rationalp x)
                (< (smallest-positive-denormal n k) x)
                (< x (largest-positive-denormal n k))
                (integerp n)
                (> n 1)
                (integerp k)
                (> k 0)
                (rounding-mode-p m))
           (not (equal (drnd x m n k) 0)))
  :hints (("goal" :in-theory (set-difference-theories
                              (enable rnd inf minf near near+
                                      drnd-rewrite
                                      rounding-mode-p ieee-mode-p
                                      smallest-positive-denormal
                                      smallest-positive-normal
                                      LARGEST-POSITIVE-DENORMAL
;                                      bias
                                      )
                              '(drepp-spd drnd-trunc-skips-no-denormals))
           :use ((:instance drepp-spd)
                 (:instance drnd-trunc-skips-no-denormals
                             (a (expt 2
                                      (+ 2 (* -1 n) (* -1 (bias k))))))))))


(defthm drepp-drnd-mid-range-1
  (implies (and (rationalp x)
                (< (smallest-positive-denormal n k) x)
                (< x (largest-positive-denormal n k))
                (integerp n)
                (> n 1)
                (integerp k)
                (> k 0)
                (rounding-mode-p m))
           (drepp (drnd x m n k) n k))
  :hints (("goal" :in-theory (set-difference-theories
                              (enable drepp bias
                                      smallest-positive-denormal
                                      smallest-positive-normal
                                      LARGEST-POSITIVE-DENORMAL)
                              '(drnd-rewrite
                                drepp-drnd-expo-2  drepp-drnd-expo-1))
           :use ( drepp-drnd-expo-2  drepp-drnd-expo-1))))

(defthm drepp-drnd-mid-range
  (implies (and (rationalp x)
                (< (smallest-positive-denormal n k) (abs x))
                (< (abs x) (largest-positive-denormal n k))
                (integerp n)
                (> n 1)
                (integerp k)
                (> k 0)
                (rounding-mode-p m))
           (drepp (drnd x m n k) n k))
  :hints (("goal" :in-theory (e/d (drnd-minus)
                                  ( drnd-rewrite DREPP-DRND-MID-RANGE-1 flip  DREPP-DEF
                                      SMALLEST-POSITIVE-NORMAL SMALLEST-POSITIVE-DENORMAL))
           :use (drepp-drnd-mid-range-1
                 (:instance drepp-drnd-mid-range-1 (m (flip m)) (x (- x)))))))

(defthm expo-of-high-range-1
  (implies (and (rationalp x)
                (< (largest-positive-denormal n k) x)
                (< x (smallest-positive-normal k))
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
           (<= (expt 2 (- (expo (smallest-positive-normal k)) 1))
               (largest-positive-denormal n k)))
  :hints (("goal" :in-theory (set-difference-theories
                              (enable expt-split
                                      expo-shift-2
                                      bias
                                      LARGEST-POSITIVE-DENORMAL
                                      smallest-positive-normal
                                      smallest-positive-denormal
                                      )
                              '()))))

(defthm expo-of-high-range-2
  (implies (and (rationalp x)
                (< (largest-positive-denormal n k) x)
                (< x (smallest-positive-normal k))
                (integerp n)
                (> n 1)
                (integerp k)
                (> k 0))
           (< (expt 2 (- (expo (smallest-positive-normal k)) 1)) x))
  :hints (("goal" :in-theory (set-difference-theories
                              (enable largest-positive-denormal
                                      )
                              '( expo>=-2
                                      expo-of-high-range-2-1
                                      smallest-positive-normal
                                      ))
           :use  expo-of-high-range-2-1)))


(defthm expo-of-high-range
    (implies (and (rationalp x)
                  (< (largest-positive-denormal n k) x)
                  (< x (smallest-positive-normal k))
                  (integerp n)
                  (> n 1)
                  (integerp k)
                  (> k 0))
             (= (expo x)
                (- (expo (smallest-positive-normal k)) 1)))
    :hints (("goal" :in-theory (e/d (smallest-positive-normal
                                     smallest-positive-denormal)
                                    (
                                 expo-of-high-range-2
                                positive-lpd))
             :use ( expo-of-high-range-2
                    (:instance positive-lpd)
                   (:instance expo-unique (n (- (expo (smallest-positive-normal k)) 1)))))))

(defthm drnd-trunc-of-high-range-3
  (implies (and (integerp n)
                (> n 1)
                (integerp k)
                (> k 0))
           (equal (fp+ (largest-positive-denormal n k) (- n 1))
                  (smallest-positive-normal k)))
  :hints (("Goal" :in-theory (enable expo>=-2 largest-positive-denormal smallest-positive-normal
                                     SMALLEST-POSITIVE-DENORMAL))))

(defthm drnd-trunc-of-high-range-1
  (implies (and (rationalp x)
                (< (largest-positive-denormal n k) x)
                (< x (smallest-positive-normal k))
                (integerp n)
                (> n 1)
                (integerp k)
                (> k 0))
           (>= (drnd x 'trunc n k)
               (largest-positive-denormal n k)))
  :hints (("goal" :in-theory (set-difference-theories
                              (enable rnd drnd-rewrite)
                              '(drnd-trunc-skips-no-denormals
                                smallest-positive-normal
                                largest-positive-denormal
                                rnd-exactp-d
                                ))
           :use ((:instance drnd-trunc-skips-no-denormals
                            (a (largest-positive-denormal n k))
                            )))))

(defthm drnd-trunc-of-high-range-2
  (implies (and (rationalp x)
                (< (largest-positive-denormal n k) x)
                (< x (smallest-positive-normal k))
                (integerp n)
                (> n 1)
                (integerp k)
                (> k 0))
           (<= (drnd x 'trunc n k)
               (largest-positive-denormal n k)))
  :hints (("goal" :in-theory (set-difference-theories
                              (enable rnd drnd-rewrite)
                              '(
                                smallest-positive-normal
                                largest-positive-denormal
                                rnd-exactp-d
                                ;; expo-of-high-range
                                ))
           :use ((:instance fp+1
                            (y (trunc x (+ n
                                                (- (expo (smallest-positive-normal k)))
                                                (expo x))))
                            (x (largest-positive-denormal n k))
                            (n (- n 1)))))))

(defthm drnd-trunc-of-high-range-pos
  (implies (and (rationalp x)
                (< (largest-positive-denormal n k) x)
                (< x (smallest-positive-normal k))
                (integerp n)
                (> n 1)
                (integerp k)
                (> k 0))
           (= (drnd x 'trunc n k)
               (largest-positive-denormal n k)))
  :hints (("goal" :in-theory (disable smallest-positive-normal
                                      drnd-rewrite
                                      largest-positive-denormal
                                      drnd-trunc-of-high-range-2
                                      drnd-trunc-of-high-range-1
                                      )
           :use (drnd-trunc-of-high-range-2 drnd-trunc-of-high-range-1))))


(defthm drnd-trunc-of-high-range
  (implies (and (rationalp x)
                (< (largest-positive-denormal n k) (abs x))
                (< (abs x) (smallest-positive-normal k))
                (integerp n)
                (> n 1)
                (integerp k)
                (> k 0))
           (= (drnd x 'trunc n k)
               (* (sgn x) (largest-positive-denormal n k))))
  :hints (("goal" :in-theory (set-difference-theories
                              (enable sgn drnd-minus)
                              '(smallest-positive-normal
                                drnd-rewrite
                                largest-positive-denormal
                                drnd-trunc-of-high-range-pos))
           :use (drnd-trunc-of-high-range-pos
                 (:instance drnd-trunc-of-high-range-pos (x (- x)))))))

(defthm drnd-away-of-high-range-1
  (implies (and (rationalp x)
                (< (largest-positive-denormal n k) x)
                (< x (smallest-positive-normal k))
                (integerp n)
                (> n 1)
                (integerp k)
                (> k 0))
           (<= (drnd x 'away n k)
               (smallest-positive-normal k)))
  :hints (("goal" :in-theory (set-difference-theories
                              (enable rnd drnd-rewrite)
                              '(spn-1-exact
                                smallest-positive-normal
                                largest-positive-denormal
                                rnd-exactp-d))
           :use ( spn-1-exact
                  (:instance exactp-<= (x (smallest-positive-normal k)) (m 1) (n (- n 1)))
                  (:instance away-exactp-c (a (smallest-positive-normal k))
                             (n (+ n
                                   (- (expo (smallest-positive-normal k)))
                                   (expo x))))))))

(defthm drnd-away-of-high-range-2
  (implies (and (rationalp x)
                (< (largest-positive-denormal n k) x)
                (< x (smallest-positive-normal k))
                (integerp n)
                (> n 1)
                (integerp k)
                (> k 0))
           (>= (drnd x 'away n k)
               (smallest-positive-normal k)))
  :hints (("goal" :in-theory (set-difference-theories
                              (enable rnd drnd-rewrite)
                              '(smallest-positive-normal
                                largest-positive-denormal
                                rnd-exactp-d))
           :use ((:instance exactp-<= (x (smallest-positive-normal k)) (m 1) (n
                                                                              (- n 1)))
                 (:instance fp+1
                            (y (away x (+ n
                                          (- (expo (smallest-positive-normal k)))
                                          (expo x))))
                            (x (largest-positive-denormal n k))
                            (n (- n 1)))))))

(defthm drnd-away-of-high-range-pos
  (implies (and (rationalp x)
                (< (largest-positive-denormal n k) x)
                (< x (smallest-positive-normal k))
                (integerp n)
                (> n 1)
                (integerp k)
                (> k 0))
           (= (drnd x 'away n k)
               (smallest-positive-normal k)))
  :hints (("goal" :in-theory (disable
                              drnd-rewrite
                              smallest-positive-normal
                              largest-positive-denormal
                               DRND-AWAY-OF-HIGH-RANGE-1
                                DRND-AWAY-OF-HIGH-RANGE-2)
           :use (drnd-away-of-high-range-2 drnd-away-of-high-range-1))))


(defthm drnd-away-of-high-range
  (implies (and (rationalp x)
                (< (largest-positive-denormal n k) (abs x))
                (< (abs x) (smallest-positive-normal k))
                (integerp n)
                (> n 1)
                (integerp k)
                (> k 0))
           (= (drnd x 'away n k)
               (* (sgn x) (smallest-positive-normal k))))
  :hints (("goal" :in-theory (set-difference-theories
                              (enable sgn drnd-minus)
                              '(smallest-positive-normal
                                drnd-rewrite
                                largest-positive-denormal
                                drnd-away-of-high-range-pos))
           :use (drnd-away-of-high-range-pos
                 (:instance drnd-away-of-high-range-pos (x (- x)))
                 ))))

(defthm drnd-choice
  (implies (rounding-mode-p mode)
           (or (equal (drnd x mode n k) (drnd x 'away n k))
               (equal (drnd x mode n k) (drnd x 'trunc n k))))
  :hints (("Goal" :use (:instance rnd-choice (x (+ X
                        (* (SGN X)
                           (EXPT 2 (+ 2 (* -1 (EXPT 2 (1- K)))))))))
           :in-theory (set-difference-theories
                       (enable drnd)
                       '(re evenp))))
  :rule-classes nil)


(defthm drnd-of-high-range
  (implies (and (< (largest-positive-denormal n k) (abs x))
                (< (abs x) (smallest-positive-normal k))
                (rationalp x)
                (integerp n)
                (> n 1)
                (integerp k)
                (> k 0)
                (rounding-mode-p mode))
           (or (= (drnd x mode n k) (* (sgn x) (largest-positive-denormal n k)))
               (= (drnd x mode n k) (* (sgn x) (smallest-positive-normal k)))))
  :hints (("goal" :in-theory (set-difference-theories
                              (enable rnd inf minf near ieee-mode-p rounding-mode-p sgn)
                              '(smallest-positive-denormal
                                drnd-rewrite
                                smallest-positive-normal
                                abs-away
                                rounding-mode-p
                                rearrange-negative-coefs-equal))
           :use (drnd-choice)))
  :rule-classes nil)

;add?
;gen?
(defthm drnd-non-neg
  (implies (and (<= 0 x)
                (rationalp x)
                (<= x (smallest-positive-normal k)) ;drop?
                (integerp n)
                (> n 1)
                (integerp k)
                (> k 0)
                (rounding-mode-p mode))
           (<= 0 (drnd x mode n k)))
  :hints (("Goal" :in-theory (enable drnd-rewrite)))
  :rule-classes (:rewrite :type-prescription))

;add?
;gen?
(defthm drnd-non-pos
  (implies (and (<= x 0)
                (rationalp x)
                (<= (abs x) (smallest-positive-normal k)) ;drop?
                (integerp n)
                (> n 1)
                (integerp k)
                (> k 0)
                (rounding-mode-p mode))
           (<= (drnd x mode n k) 0))
  :hints (("Goal" :in-theory (enable drnd-rewrite)))
  :rule-classes (:rewrite :type-prescription))

;bad name?
(defthm drnd-type-pos
  (implies (and (rationalp x)
                (<= 0 x)
                (<= x (smallest-positive-normal k)) ;drop?
                (integerp n)
                (> n 1)
                (integerp k)
                (> k 0)
                (rounding-mode-p mode))
           (or (drepp (drnd x mode n k) n k)
               (= (drnd x mode n k) 0)
               (= (drnd x mode n k) (smallest-positive-normal k))))
           :otf-flg t
           :hints (("goal" :in-theory (set-difference-theories
                              (enable sgn DRND-SPN-IS-SPN-GENERAL)
                              '(drnd-rewrite
                                drepp-drnd-mid-range
                                drnd-spd-is-spd-general
                                smallest-positive-denormal
                                largest-positive-denormal
                                smallest-positive-normal
                                drepp-drnd-mid-range-1
                                drepp-spd
                                ))
           :use (drnd-of-high-range
                 drnd-of-low-range
                 (:instance  DREPP-MINUS (x  (DRND X MODE N K)))
                 (:instance  drepp-spd)
                 (:instance drepp-drnd-mid-range (m mode)))))
  :rule-classes nil)

;bad name?
(defthm drnd-type
  (implies (and (rationalp x)
                (<= (abs x) (smallest-positive-normal k)) ;drop?
                (integerp n)
                (> n 1)
                (integerp k)
                (> k 0)
                (rounding-mode-p mode))
           (or (drepp (drnd x mode n k) n k)
               (= (drnd x mode n k) 0)
               (= (drnd x mode n k) (* (sgn x) (smallest-positive-normal k)))))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable sgn drnd-minus)
                              '(drnd-rewrite
;                                DRND-SPD-IS-SPD-GENERAL ; for efficiency
                                smallest-positive-normal))
           :use (drnd-type-pos
                 (:instance drnd-type-pos (mode (flip mode)) (x (- x))))))
  :rule-classes nil)


;drop?
;(in-theory (disable SMALLEST-POSITIVE-NORMAL))



;better proof?
(defthm drnd-diff
  (implies (and (rationalp x)
                (<= (ABS X) (SMALLEST-POSITIVE-NORMAL K))
                (integerp n)
                (> n 1)
                (integerp k)
                (> k 0)
                (rounding-mode-p mode))
           (< (abs (- x (drnd x mode n k))) (smallest-positive-denormal n k)))
  :hints (("Goal'"
           :cases ((> (+ n
                         (- (expo (smallest-positive-normal k)))
                         (expo x)) 0)))
          ("goal" :in-theory (set-difference-theories
                              (enable rnd
                                      drnd-rewrite
                                      SMALLEST-POSITIVE-DENORMAL
                                      ;bias
                                     ; SMALLEST-POSITIVE-NORMAL
                                      rounding-mode-p
                                      inf minf near near+ sgn)
                              '( ;BIAS
                                ;sgn
                                SMALLEST-POSITIVE-NORMAL
                                ;SMALLEST-POSITIVE-deNORMAL
                                re evenp EXPO<=-2 EXPO>=-2 expt-compare
                                rnd-diff))
           :use ((:instance rnd-diff (n (+ N (EXPO X)
                                           (* -1 (EXPO (SMALLEST-POSITIVE-NORMAL
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
  (+ x (smallest-positive-denormal n k)))

(defthmd denormals-same
  (equal (next-denormal-2 x n k)
         (next-denormal x n k))
  :hints (("Goal" :in-theory (enable next-denormal next-denormal-2
                                     SMALLEST-POSITIVE-DENORMAL)))
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
           (:instance fp+2-1)))))

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
                 (:instance fp+1
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

(defthm drnd-away-skips-no-denormals-pos
  (implies (and (integerp n)
                (> n 1)
                (integerp k)
                (> k 0)
                (rationalp x)
                (<= 0 x)
                (<= x (smallest-positive-normal k))
                (drepp a n k)
                (>= a x)
                )
           (>= a (drnd x 'away n k)))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable sgn smallest-positive-normal
                                      SMALLEST-POSITIVE-DENORMAL
                                      LARGEST-POSITIVE-DENORMAL
                                      NEXT-DENORMAL)
                              '(drnd-diff
                                drnd-rewrite
                                largest-lpd
                                denormal-spacing

;                                DRND-SPD-IS-SPD-GENERAL ;these two for efficiency
 ;                               DRND-SPN-IS-SPN-GENERAL ;
                                 ))
           :use ((:instance largest-lpd (x a))
                 (:instance drnd-diff (mode 'away))
                 (:instance drnd-type (mode 'away))
                 (:instance denormal-spacing
                            (x a)
                            (x+ (drnd x 'away n k)))))))

; all 4 :use hints seem necessary
(defthm drnd-away-skips-no-denormals
  (implies (and (integerp n)
                (> n 1)
                (integerp k)
                (> k 0)
                (rationalp x)
                (<= (abs x) (smallest-positive-normal k))
                (drepp a n k)
                (>= (abs a) (abs x))
                )
           (>= (abs a) (abs (drnd x 'away n k))))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable sgn drnd-minus)
                              '(drnd-diff
                                DRND-AWAY-OF-HIGH-RANGE
                                DRND-AWAY-OF-HIGH-RANGE-POS
                                DRND-AWAY-OF-LOW-RANGE
                                DREPP-DRND-MID-RANGE
                                drnd-non-pos
                                drnd-rewrite
                                smallest-positive-normal
                                DRND-AWAY-SKIPS-NO-DENORMALS-pos
;                                DRND-SPD-IS-SPD-GENERAL ;these two for efficiency
 ;                               DRND-SPN-IS-SPN-GENERAL
                                ))

           :use ((:instance drnd-non-pos (mode 'away))
                 (:instance drnd-away-skips-no-denormals-pos)
                 (:instance drnd-away-skips-no-denormals-pos (a (- a)) (x (- x)))
                 (:instance drnd-away-skips-no-denormals-pos (x (- x)))
                 (:instance drnd-away-skips-no-denormals-pos (a (- a)))))))

;BOZO
;(in-theory (disable SMALLEST-POSITIVE-NORMAL BIAS DREPP))

(defthm drnd-inf-skips-no-denormals
  (implies (and (integerp n)
                (> n 1)
                (integerp k)
                (> k 0)
                (rationalp x)
                (<= (abs x) (smallest-positive-normal k))
                (drepp a n k)
                (>= a x))
           (>= a (drnd x 'inf n k)))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable rnd ;drepp
                                      inf
                                      drnd-rewrite)
                              '(;drnd-rewrite
                                drnd-away-skips-no-denormals
                                 drnd-trunc-skips-no-denormals))
          :use ((:instance drnd-away-skips-no-denormals)
                (:instance drnd-trunc-skips-no-denormals (x (- x)))))))

(defthm drnd-minf-skips-no-denormals
  (implies (and (integerp n)
                (> n 1)
                (integerp k)
                (> k 0)
                (rationalp x)
                (<= (abs x) (smallest-positive-normal k))
                (drepp a n k)
                (<= a x))
           (<= a (drnd x 'minf n k)))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable rnd ;drepp
                                      drnd-rewrite
                                      minf)
                              '(
                                drnd-away-skips-no-denormals
                                 drnd-trunc-skips-no-denormals))
          :use ((:instance drnd-away-skips-no-denormals (x (- x)))
                (:instance drnd-trunc-skips-no-denormals)))))



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



(defthm drnd-near-2-1
  (implies (and (rationalp x)
                (<= x (smallest-positive-normal k))
                (rationalp a)
                (integerp n)
                (> n 1)
                (integerp k)
                (> k 0)
                (> x 0)
                (drepp a n k)
                (= (drnd x 'near n k) (drnd x 'trunc n k)))
           (>= (abs (- x a)) (abs (- x (drnd x 'trunc n k)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable rnd bias drnd-rewrite)
                              '(  away-exactp-c
				      near trunc-exactp-c
                                      drnd-away-skips-no-denormals
                                      drnd-trunc-skips-no-denormals
                                      ))
           :use ((:instance near1-b-eric (n (+ -2 N (EXPO X) (EXPT 2 (1- K)))))
                 (:instance away-lower-pos (n (+ -2 N (EXPO X) (EXPT 2 (1- K)))))
                 (:instance trunc-upper-pos (n (+ -2 N (EXPO X) (EXPT 2 (1- K)))))
                 (:instance drnd-away-skips-no-denormals )
                 (:instance drnd-trunc-skips-no-denormals)))))

(defthm drnd-near-2-2
  (implies (and (rationalp x)
                (<= x (smallest-positive-normal k))
                (rationalp a)
                (integerp n)
                (> n 1)
                (integerp k)
                (> k 0)
                (> x 0)
                (drepp a n k)
                (= (drnd x 'near n k) (drnd x 'away n k)))
           (>= (abs (- x a)) (abs (- x (drnd x 'away n k)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable rnd bias drnd-rewrite)
                              '( drnd-away-skips-no-denormals
                                 drnd-trunc-skips-no-denormals
                                 away-exactp-c
                                 trunc-exactp-c
                                 ))
           :use ((:instance near1-a (n (+ -2 N (EXPO X) (EXPT 2 (1- K)))))
                 (:instance away-lower-pos (n (+ -2 N (EXPO X) (EXPT 2 (1- K)))))
                 (:instance trunc-upper-pos (n (+ -2 N (EXPO X) (EXPT 2 (1- K)))))
                 (:instance drnd-away-skips-no-denormals )
                 (:instance drnd-trunc-skips-no-denormals)))))

(defthm drnd-near-choice
  (implies (and (rationalp x)
                (integerp n)
                (> n 1)
                (integerp k)
                (> k 0)
                (<= (abs x) (smallest-positive-normal k)))
           (or (= (drnd x 'near n k) (drnd x 'trunc n k))
               (= (drnd x 'near n k) (drnd x 'away n k))))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable rnd near drnd-rewrite)
                              '(re evenp))))
  :rule-classes ())

;BOZO
;(in-theory (disable SMALLEST-POSITIVE-DENORMAL))

(defthm no-denormal-is-closer-than-what-drnd-near-returns-pos
  (implies (and (rationalp x)
                (>= x 0)
                (<= x (smallest-positive-normal k))
                (integerp n)
                (> n 1)
                (integerp k)
                (> k 0)
                (drepp a n k))
           (>= (abs (- x a)) (abs (- x (drnd x 'near n k)))))
  :hints (("Goal" :in-theory (disable

                              drnd-rewrite
                              drnd-non-neg
                              DRND-AWAY-SKIPS-NO-DENORMALS-POS)
           :use ((:instance drnd-near-2-1)
                 (:instance drnd-near-2-2)
                 (:instance drnd-near-choice)))))

(defthm no-denormal-is-closer-than-what-drnd-near-returns-neg
  (implies (and (rationalp x)
                (<= x 0)
                (<= (abs x) (smallest-positive-normal k))
                (integerp n)
                (> n 1)
                (integerp k)
                (> k 0)
                (drepp a n k))
           (>= (abs (- x a)) (abs (- x (drnd x 'near n k)))))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable drnd-minus)
                              '(drnd-rewrite
                                drnd-non-pos
                                drnd-non-neg
                                smallest-positive-normal
                                no-denormal-is-closer-than-what-drnd-near-returns-pos
                                DRND-AWAY-SKIPS-NO-DENORMALS-POS))
           :use ((:instance no-denormal-is-closer-than-what-drnd-near-returns-pos
                            (x (- x)) (a (- a)))))))


(defthm no-denormal-is-closer-than-what-drnd-near-returns
  (implies (and (rationalp x)
                (<= (abs x) (smallest-positive-normal k))
                (integerp n)
                (> n 1)
                (integerp k)
                (> k 0)
                (drepp a n k))
           (>= (abs (- x a)) (abs (- x (drnd x 'near n k)))))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable)
                              '(drnd-rewrite
                                drnd-non-pos
                                drnd-non-neg
                                smallest-positive-normal
                                DRND-AWAY-SKIPS-NO-DENORMALS-POS
                                no-denormal-is-closer-than-what-drnd-near-returns-pos
                                no-denormal-is-closer-than-what-drnd-near-returns-neg))
           :use (no-denormal-is-closer-than-what-drnd-near-returns-pos
                 no-denormal-is-closer-than-what-drnd-near-returns-neg))))

;could speed up the above with a :cases hint instead of :use hints?




#|
;remove these?
(defthm drnd-trunc-never-goes-up-for-pos-args
  (implies (and (integerp n)
                (> n 1)
                (integerp k)
                (> k 0)
                (rationalp x)
                (<= 0 x)
                (<= x (smallest-positive-normal k)))
           (<= (drnd x 'trunc n k)
               x))
  :hints (("Goal" :in-theory (enable rnd)
           :use (:instance trunc-upper-bound
                                  (n (+ -2 N (EXPO X) (EXPT 2 (1- K))))))))


(defthm drnd-away-never-goes-down-for-pos-args
  (implies (and (integerp n)
                (> n 1)
                (integerp k)
                (> k 0)
                (rationalp x)
                (<= 0 x)
                (<= x (smallest-positive-normal k)))
           (>= (drnd x 'away n k)
               x))
  :hints (("Goal" :in-theory (enable rnd)
           :use (:instance away-lower-bound
                                  (n (+ -2 N (EXPO X) (EXPT 2 (1- K))))))))
|#

;why?
(in-theory (disable expo< expo>))




