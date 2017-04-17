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

;;;***************************************************************
;;;An ACL2 Library of Floating Point Arithmetic

;;;David M. Russinoff
;;;Advanced Micro Devices, Inc.
;;;February, 1998
;;;***************************************************************

;there may be some cruft to be deleted from this file...

;(include-book "trunc") ;BOZO drop
(local (include-book "away-proofs"))

;; Necessary defuns


(defund fl (x)
  (declare (xargs :guard (real/rationalp x)))
  (floor x 1))

(defund power2p-measure (x)
  (declare (xargs :guard (and (rationalp x) (not (equal x 0)))))
  (cond ((or (not (rationalp x))
             (<= x 0)) 0)
	((< x 1) (cons 1 (fl (/ x))))
	(t (fl x))))

(defund power2p (x)
  (declare (xargs :guard t
                  :measure (power2p-measure x)
                  :hints (("goal" :in-theory (enable power2p-measure)))))
  (cond ((or (not (rationalp x))
             (<= x 0))
         nil)
        ((< x 1) (power2p (* 2 x)))
        ((<= 2 x) (power2p (* 1/2 x)))
        ((equal x 1) t)
        (t nil) ;got a number in the doubly-open interval (1,2)
        ))

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

(defun fp+ (x n)
  (+ x (expt 2 (- (1+ (expo x)) n))))

(defund exactp (x n)
;  (declare (xargs :guard (and (real/rationalp x) (integerp n))))
  (integerp (* (sig x) (expt 2 (1- n)))))

(defund trunc (x n)
  (declare (xargs :guard (integerp n)
                  :verify-guards nil))
  (* (sgn x) (fl (* (expt 2 (1- n)) (sig x))) (expt 2 (- (1+ (expo x)) n))))

;; Start of new stuff

(defund away (x n)
  (* (sgn x) (cg (* (expt 2 (1- n)) (sig x))) (expt 2 (- (1+ (expo x)) n))))

;generated automatically by ACL2 when we define away, but included here just to be safe
;could disable (:type-prescription away) for slight efficiency gain at the cost of making the output of :pe a
;little deceptive
(defthm away-rational-type-prescription
  (rationalp (away x n))
  :rule-classes :type-prescription)

(defthm away-of-non-rationalp-is-0
  (implies (not (rationalp x))
           (equal (away x n)
                  0)))

;make alt version? use negative-syntaxp?
(defthm away-minus
  (= (away (* -1 x) n)
     (* -1 (away x n))))

(defthm away-positive
  (implies (and (< 0 x)
                (case-split (rationalp x))
                )
           (< 0 (away x n)))
  :rule-classes (:rewrite :linear))

(defthm away-positive-rational-type-prescription
  (implies (and (< 0 x)
                (case-split (rationalp x))
                )
           (and (< 0 (away x n))
                (rationalp (away x n))))
  :rule-classes :type-prescription)

(defthm away-negative
    (implies (and (< x 0)
                  (case-split (rationalp x))
                  )
	     (< (away x n) 0))
    :rule-classes (:rewrite :linear))

(defthm away-negative-rational-type-prescription
  (implies (and (< x 0)
                (case-split (rationalp x))
                )
           (< (away x n) 0))
  :rule-classes :type-prescription)

(defthm away-0
  (equal (away 0 n)
         0))

(defthm away-non-negative-rational-type-prescription
  (implies (<= 0 x)
           (and (<= 0 (away x n))
                (rationalp (away x n))))
  :rule-classes :type-prescription)

(defthm away-non-positive-rational-type-prescription
  (implies (<= x 0)
           (and (<= (away x n) 0)
                (rationalp (away x n))))
  :rule-classes :type-prescription)

(defthm away-equal-0-rewrite
  (implies (rationalp x)
           (equal (equal (away x n) 0)
                  (equal x 0))))

(defthm sgn-away
  (equal (sgn (away x n))
         (sgn x)))

;keep this disabled, since it basically opens up AWAY
(defthmd abs-away
  (implies (and (rationalp x)
                (integerp n))
           (equal (abs (away x n))
                  (* (cg (* (expt 2 (1- n)) (sig x))) (expt 2 (- (1+ (expo x)) n))))))

;kind of gross...
(defthm away-to-0-or-fewer-bits
  (implies (and (<= n 0)
                (rationalp x)
                (integerp n)
                )
           (equal (away x n)
                  (* (sgn x) (expt 2 (+ 1 (expo x) (- n)))))))

(defthm away-lower-bound
    (implies (and (case-split (rationalp x))
		  (case-split (integerp n))
                  )
	     (>= (abs (away x n)) (abs x)))
  :rule-classes :linear)

(defthm away-lower-pos
    (implies (and (>= x 0)
                  (case-split (rationalp x))
		  (case-split (integerp n))
                  )
	     (>= (away x n) x))
  :rule-classes :linear)

;elim?
;; (defthm expo-away-lower-bound
;;   (implies (and (rationalp x)
;;                 (integerp n)
;;                 (> n 0))
;;            (>= (expo (away x n)) (expo x)))
;;   :rule-classes :linear)

(defthm expo-away-lower-bound
  (implies (and (rationalp x)
                (natp n))
           (>= (expo (away x n)) (expo x)))
  :rule-classes :linear)

(defthm away-upper-1
  (implies (and (rationalp x)
                (integerp n)
                (> n 0))
           (< (abs (away x n)) (+ (abs x) (expt 2 (- (1+ (expo x)) n)))))
  :rule-classes :linear)

(defthm away-upper-2
  (implies (and (rationalp x)
                (not (= x 0))
                (integerp n)
                (> n 0))
           (< (abs (away x n)) (* (abs x) (+ 1 (expt 2 (- 1 n))))))
  :rule-classes :linear)

(defthm away-upper-pos
    (implies (and (> x 0)
                  (rationalp x)
		  (integerp n)
		  (> n 0))
	     (< (away x n) (* x (+ 1 (expt 2 (- 1 n))))))
  :rule-classes :linear)

(defthm away-upper-3
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (<= (abs (away x n)) (* (abs x) (+ 1 (expt 2 (- 1 n))))))
  :rule-classes :linear)

(defthm away-diff
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (< (abs (- (away x n) x)) (expt 2 (- (1+ (expo x)) n))))
  :rule-classes :linear)

(defthm away-diff-pos
    (implies (and (rationalp x)
		  (>= x 0)
		  (integerp n)
		  (> n 0))
	     (< (- (away x n) x) (expt 2 (- (1+ (expo x)) n))))
  :rule-classes :linear)


(defthm away-diff-expo-1
    (implies (and (rationalp x)
		  (not (= x (away x n)))
		  (integerp n)
		  (> n 0))
	     (<= (expo (- (away x n) x)) (- (expo x) n)))
  :rule-classes :linear)
;slow
(defthmd away-rewrite
  (implies (and (rationalp x)
                (integerp n)
                (> n 0))
           (equal (away x n)
                  (* (sgn x)
                     (cg (* (expt 2 (- (1- n) (expo x))) (abs x)))
                     (expt 2 (- (1+ (expo x)) n))))))

(defthm away-exactp-b
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (iff (= x (away x n))
		  (exactp x n)))
  :rule-classes ())

(defthm away-diff-expo
    (implies (and (rationalp x)
		  (not (exactp x n))
		  (integerp n)
		  (> n 0))
	     (<= (expo (- (away x n) x)) (- (expo x) n)))
  :rule-classes :linear)

(defthm away-exactp-a
    (implies (case-split (< 0 n))
	     (exactp (away x n) n)))



;trying disabled?
(defthmd away-monotone
  (implies (and (rationalp x)
                (rationalp y)
                (integerp n)
                (<= x y))
           (<= (away x n) (away y n)))
  :rule-classes :linear)

(defthm away-exactp-d
    (implies (and (rationalp x)
		  (not (= x 0))
		  (integerp n)
		  (> n 0))
	     (<= (abs (away x n)) (expt 2 (1+ (expo x)))))
  :rule-classes ())

(defthmd away-pos-rewrite
  (implies (and (rationalp x)
                (>= x 0)
                (integerp n))
           (equal (away x n)
                  (* (cg (* (expt 2 (- (1- n) (expo x))) x))
                     (expt 2 (- (1+ (expo x)) n))))))

(defthm expo-away
  (implies (and (rationalp x)
                (natp n)
                (not (= (abs (away x n)) (expt 2 (1+ (expo x))))))
           (equal (expo (away x n))
                  (expo x))))


;handle the case where n<m?
(defthm away-away
    (implies (and (rationalp x)
		  (>= x 0)
		  (integerp n)
		  (integerp m)
		  (> m 0)
		  (>= n m))
	     (equal (away (away x n) m)
		    (away x m))))

(defthm away-shift
  (implies (integerp n)
           (= (away (* x (expt 2 k)) n)
              (* (away x n) (expt 2 k)))))

;BOZO move to trunc! ?
(defthm trunc-away-a
    (implies (and (integerp n) (> n 0)
		  (rationalp x) (> x 0)
		  (exactp x (1+ n))
		  (not (exactp x n)))
	     (= (- x (expt 2 (- (expo x) n)))
		(trunc x n)))
  :rule-classes ())

;rename! doesn't mention trunc
(defthm trunc-away-b
  (implies (and (integerp n) (> n 0)
                (rationalp x) (> x 0)
                (exactp x (1+ n))
                (not (exactp x n)))
           (= (away x n)
              (+ x (expt 2 (- (expo x) n)))))
  :rule-classes ())

(defthmd away-exactp-c
    (implies (and (exactp a n)
		  (>= a x)
                  (rationalp x)
		  (integerp n)
		  (> n 0)
		  (rationalp a))
	     (>= a (away x n))))

(defthm away-imp
  (implies (and (rationalp x)
                (> x 0)
                (integerp n)
                (> n 0)
                (integerp m)
                (>= m n)
                (exactp x m))
           (= (away x n)
              (trunc (+ x
                        (expt 2 (- (1+ (expo x)) n))
                        (- (expt 2 (- (1+ (expo x)) m))))
                     n)))
  :rule-classes ())

(defthm plus-away-2
  (implies (and (exactp x (+ k (- (expo x) (expo y))))
                (rationalp x)
                (>= x 0)
                (rationalp y)
                (>= y 0)
                (integerp k)
                )
           (equal (+ x (away y k))
                  (* (cg (* (+ x y) (expt 2 (- (1- k) (expo y)))))
                     (expt 2 (- (1+ (expo y)) k)))))
  :rule-classes ())

(defthm plus-away
  (implies (and (exactp x (+ k (- (expo x) (expo y))))
                (rationalp x)
                (>= x 0)
                (rationalp y)
                (>= y 0)
                (integerp k)
                )
           (= (+ x (away y k))
              (away (+ x y) (+ k (- (expo (+ x y)) (expo y))))))
  :rule-classes ())

;add to lib? alternate form of the above
(defthm plus-away-alt
  (implies (and (exactp x (+ j (expo x) (- (expo (+ x y)))))
                (rationalp x)
                (>= x 0)
                (rationalp y)
                (>= y 0)
                (integerp j)
                )
           (= (away (+ x y) j)
              (+ x (away y (+ j (- (expo (+ x y))) (expo y))))))
  :rule-classes ())

; isn't nice for y=0
;prove corollaries like this for inf, minf, rnd?
(defthm plus-away-corollary
  (implies (and (< y (expt 2 (- (1+ (expo x)) n)))
                (rationalp x)
                (> x 0)
                (rationalp y)
                (> y 0)
                (integerp n)
                (exactp x n)
                )
           (= (away (+ x y) n)
              (fp+ x n))))


;gross.  keep disabled? don't put in user/ ?
(defthmd away-with-n-not-an-integer
  (implies (not (integerp n))
           (equal (away x n)
                  (if (not (rationalp x))
                      0
                    (if (acl2-numberp n)
                        (if (power2p (abs x))
                            (sgn x)
                        (* 2 (sgn x)))
                      (* (sgn x) (expt 2 (+ 1 (expo x)))))))))
