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

;;;***************************************************************
;;;An ACL2 Library of Floating Point Arithmetic

;;;David M. Russinoff
;;;Advanced Micro Devices, Inc.
;;;February, 1998
;;;***************************************************************

(in-package "RTL")

(local (include-book "trunc"))
(local (include-book "../../arithmetic/top"))
(local (include-book "float"))

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
;could disabled (:type-prescription away) for slight efficiency gain at the cost of making the output of :pe a
;little deceptive
(defthm away-rational-type-prescription
  (rationalp (away x n))
  :rule-classes :type-prescription)

(defthm away-of-non-rationalp-is-0
  (implies (not (rationalp x))
           (equal (away x n)
                  0))
  :hints (("goal" :in-theory (enable away sig))))

;make alt version? use negative-syntaxp?
(defthm away-minus
  (= (away (* -1 x) n)
     (* -1 (away x n)))
  :hints (("Goal" :in-theory (enable away))))

(defthm away-positive
  (implies (and (< 0 x)
                (case-split (rationalp x))
                )
           (< 0 (away x n)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable away cg)
           :use (;(:instance sig-lower-bound)
                 ))))

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
    :rule-classes (:rewrite :linear)
    :hints (("Goal" :in-theory (e/d (away) (sig-lower-bound SIG-LESS-THAN-1-MEANS-X-0))
             :use ((:instance sig-lower-bound)))))

(defthm away-negative-rational-type-prescription
  (implies (and (< x 0)
                (case-split (rationalp x))
                )
           (< (away x n) 0))
  :rule-classes :type-prescription)

(defthm away-0
  (equal (away 0 n)
         0)
  :hints (("Goal" :in-theory (enable away))))

(defthm away-non-negative-rational-type-prescription
  (implies (<= 0 x)
           (and (<= 0 (away x n))
                (rationalp (away x n))))
  :hints (("Goal" :cases ((or (not (rationalp x)) (equal x 0)))))
  :rule-classes :type-prescription)

(defthm away-non-positive-rational-type-prescription
  (implies (<= x 0)
           (and (<= (away x n) 0)
                (rationalp (away x n))))
  :hints (("Goal" :cases ((or (not (rationalp x)) (equal x 0)))))
  :rule-classes :type-prescription)

(defthm away-equal-0-rewrite
  (implies (rationalp x)
           (equal (equal (away x n) 0)
                  (equal x 0)))
  :hints (("Goal" :cases ((< x 0) (equal x 0) (< 0 x)))))

(defthm sgn-away
  (equal (sgn (away x n))
         (sgn x)))

;keep this disabled, since it basically opens up AWAY
(defthmd abs-away
  (implies (and (rationalp x)
                (integerp n))
           (equal (abs (away x n))
                  (* (cg (* (expt 2 (1- n)) (sig x))) (expt 2 (- (1+ (expo x)) n)))))
  :hints (("Goal" :in-theory (enable away sig)))) ;why enable sig?

;kind of gross...
(defthm away-to-0-or-fewer-bits
  (implies (and (<= n 0)
                (rationalp x)
                (integerp n)
                )
           (equal (away x n)
                  (* (sgn x) (expt 2 (+ 1 (expo x) (- n))))))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable away expt-split
;                                     expt ;yuck
                                     )
                              '())
           :use ((:instance cg-unique
                            (x (* 1/2 (SIG X) (EXPT 2 N)))
                            (n 1))
;                 sig-upper-bound
                 sig-lower-bound
                 (:instance expt-weak-monotone
                            (n n)
                            (m 0))
                 (:instance expt-strong-monotone
                            (n 0)
                            (m n))))))

(defthm away-lower-bound
    (implies (and (case-split (rationalp x))
		  (case-split (integerp n))
                  )
	     (>= (abs (away x n)) (abs x)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable away sig
                                     expt-split
                                     expt-minus
                                     )
		  :use (away-to-0-or-fewer-bits
                        (:instance cg-def-linear (x (* (expt 2 (1- n)) (sig x))))
;			(:instance fp-abs)
                        ))))
(defthm away-lower-pos
    (implies (and (>= x 0)
                  (case-split (rationalp x))
		  (case-split (integerp n))
                  )
	     (>= (away x n) x))
  :rule-classes :linear
  :hints (("Goal" :use ((:instance away-lower-bound)))))

;elim?

(defthm expo-away-lower-bound
  (implies (and (rationalp x)
                (natp n))
           (>= (expo (away x n)) (expo x)))
  :rule-classes :linear
  :hints (("Goal"
           :use ((:instance away-lower-bound)
;                 (:instance away-0-0)
                 (:instance expo-monotone (y (away x n)))))))


;; (defthm expo-away-lower-bound
;;   (implies (and (rationalp x)
;;                 (integerp n)
;;                 (> n 0))
;;            (>= (expo (away x n)) (expo x)))
;;   :rule-classes :linear
;;   :hints (("Goal"
;;            :use ((:instance away-lower-bound)
;; ;                 (:instance away-0-0)
;;                  (:instance expo-monotone (y (away x n)))))))

(local
   (defthm trunc-lower-1-2
     (implies (and (rationalp u)
                   (rationalp v)
                   (rationalp r)
                   (> r 0)
                   (< u (1+ v)))
              (< (* r u) (* r (1+ v))))
     :rule-classes ()))

;gross..
(defthm trunc-lower-1-3
    (implies (and (rationalp u)
                  (rationalp v)
                  (rationalp r)
                  (> r 0)
                  (< u (1+ v)))
             (< (* r u) (+ r (* r v))))
    :rule-classes ()
    :hints (("goal" :in-theory (disable *-strongly-monotonic)
             :use ((:instance trunc-lower-1-2)))))

(defthm away-upper-1
  (implies (and (rationalp x)
                (integerp n)
                (> n 0))
           (< (abs (away x n)) (+ (abs x) (expt 2 (- (1+ (expo x)) n)))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable abs-away
                                      expt-split
                                      expt-minus
                                      sig)
           :use (;(:instance trunc-lower-1-1)
                 (:instance fp-abs)
                 (:instance trunc-lower-1-3
                            (u (* (sig x) (expt 2 (1- n))))
                            (v (fl (* (sig x) (expt 2 (1- n)))))
                            (r (expt 2 (- (1+ (expo x)) n))))
                 (:instance cg-def-linear (x (* (expt 2 (1- n)) (sig x))))))))

(defthm away-upper-2
  (implies (and (rationalp x)
                (not (= x 0))
                (integerp n)
                (> n 0))
           (< (abs (away x n)) (* (abs x) (+ 1 (expt 2 (- 1 n))))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (disable abs)
           :use ((:instance away-upper-1)
                 (:instance trunc-lower-2-1)))))

(defthm away-upper-pos
    (implies (and (> x 0)
                  (rationalp x)
		  (integerp n)
		  (> n 0))
	     (< (away x n) (* x (+ 1 (expt 2 (- 1 n))))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (disable abs-pos)
		  :use ((:instance away-upper-2)
;			(:instance away-positive)
                        ))))

(defthm away-upper-3
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (<= (abs (away x n)) (* (abs x) (+ 1 (expt 2 (- 1 n))))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (disable abs)
		  :use ((:instance away-upper-1)
;			(:instance away-0-0)
			(:instance trunc-lower-2-1)))))

(defthm away-diff
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (< (abs (- (away x n) x)) (expt 2 (- (1+ (expo x)) n))))
  :rule-classes :linear
  :hints (("Goal" :use (;(:instance trunc-diff-1 (y (away x n)))
;			(:instance away-negative)
	;		(:instance away-positive)
			;(:instance away-0-0)
			(:instance away-lower-bound)
			(:instance away-upper-1)
                        ))))

(defthm away-diff-pos
    (implies (and (rationalp x)
		  (>= x 0)
		  (integerp n)
		  (> n 0))
	     (< (- (away x n) x) (expt 2 (- (1+ (expo x)) n))))
  :rule-classes :linear
  :hints (("Goal" :use ((:instance away-diff)
;			(:instance away-pos)
			(:instance away-lower-bound)))))


(defthm away-diff-expo-1
    (implies (and (rationalp x)
		  (not (= x (away x n)))
		  (integerp n)
		  (> n 0))
	     (<= (expo (- (away x n) x)) (- (expo x) n)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (disable abs)
		  :use ((:instance away-diff)
			(:instance expo-lower-bound (x (- (away x n) x)))
			(:instance expt-strong-monotone
				   (n (expo (- (away x n) x)))
				   (m (- (1+ (expo x)) n)))))))
;slow
(defthmd away-rewrite
  (implies (and (rationalp x)
                (integerp n)
                (> n 0))
           (equal (away x n)
                  (* (sgn x)
                     (cg (* (expt 2 (- (1- n) (expo x))) (abs x)))
                     (expt 2 (- (1+ (expo x)) n)))))
  :hints (("Goal" :in-theory (enable away sig expt-split))))


(local
 (defthm away-exactp-1
    (implies (and (rationalp x)
		  (integerp n))
	     (= x (* (sgn x) (* (expt 2 (- (1- n) (expo x))) (abs x)) (expt 2 (- (1+ (expo x)) n)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance expt-split (r 2) (j (- (1- n) (expo x))) (i (- (1+ (expo x)) n))))))))

(local
 (defthm away-exactp-2
    (implies (and (rationalp x)
		  (rationalp y)
		  (rationalp z)
		  (not (= x 0))
		  (not (= z 0)))
	     (iff (= (* x y z) (* x (cg y) z))
		  (integerp y)))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable cg-int cg-integerp)
		  :use ((:instance cg-integerp (x y))
			(:instance *cancell (x (cg y)) (z (* x z))))))))

(defthm away-exactp-b
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (iff (= x (away x n))
		  (exactp x n)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable exactp2 away-rewrite expt-split expt-minus)
		  :use ((:instance away-exactp-1)
;			(:instance away-exactp-6)
			(:instance away-exactp-2
				   (x (sgn x))
				   (y (* (expt 2 (- (1- n) (expo x))) (abs x)))
				   (z (expt 2 (- (1+ (expo x)) n))))))))

(defthm away-diff-expo
    (implies (and (rationalp x)
		  (not (exactp x n))
		  (integerp n)
		  (> n 0))
	     (<= (expo (- (away x n) x)) (- (expo x) n)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (disable abs)
		  :use ((:instance away-diff-expo-1)
			(:instance away-exactp-b)))))
(local
 (defthm away-exactp-b-1
    (implies (and (rationalp x)
		  (rationalp y)
		  (integerp n)
		  (> n 0))
	     (integerp (* (* (sgn x) (cg y) (expt 2 (- (1- n) (expo x)))) (expt 2 (- (1+ (expo x)) n)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance integerp-x-y
				   (x (sgn x))
				   (y (cg (* (expt 2 (- (1- n) (expo x))) (abs x)))))
			(:instance expt-split (r 2) (j (- (1- n) (expo x))) (i (- (1+ (expo x)) n))))))))

(local
 (defthm away-exactp-b-2
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (integerp (* (away x n) (expt 2 (- (1- n) (expo x))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable away-rewrite)
                              '( sgn))
		  :use ((:instance away-exactp-b-1 (y (* (expt 2 (- (1- n) (expo x))) (abs x)))))))))

(local
 (defthm away-exactp-b-3
    (implies (and (rationalp x)
		  (not (= x 0))
		  (integerp n)
		  (> n 0))
	     (<= (* (expt 2 (1- n)) (sig x)) (expt 2 n)))
  :rule-classes ()
  :hints (("Goal" :in-theory (e/d (expt-split) (SIG-UPPER-BOUND
                                               ))
		  :use ((:instance sig-upper-bound)
			(:instance expt-split (r 2) (j (1- n)) (i 1)))))))
(local
 (defthm away-exactp-b-4
    (implies (and (rationalp c)
		  (integerp n)
		  (integerp m)
		  (<= c (expt 2 n)))
	     (<= (* c (expt 2 (- m n))) (expt 2 m)))
    :hints (("Goal" :in-theory (enable expt-split expt-minus)))
  :rule-classes ()))

(local
 (defthm away-exactp-b-5
    (implies (and (rationalp x)
		  (not (= x 0))
		  (integerp n)
		  (> n 0))
	     (<= (abs (away x n)) (expt 2 (1+ (expo x)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable abs-away)
                              '( abs))
		  :use ((:instance away-exactp-b-3)
			(:instance away-exactp-b-4 (c (cg (* (sig x) (expt 2 (1- n))))) (m (1+ (expo x))))
			(:instance n>=cg-linear (n (expt 2 n)) (x (* (expt 2 (1- n)) (sig x)))))))))

(local
 (defthm away-exactp-b-6
    (implies (and (rationalp x)
		  (not (= x 0))
		  (integerp n)
		  (> n 0)
		  (not (= (abs (away x n)) (expt 2 (1+ (expo x))))))
	     (<= (expo (away x n)) (expo x)))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable abs)
		  :use ((:instance away-exactp-b-5)
			(:instance expo-lower-bound (x (away x n)))
;			(:instance away-0-0)
			(:instance expt-strong-monotone (n (expo (away x n))) (m (1+ (expo x)))))))))

(local
 (defthm away-exactp-b-7
   (implies (and (rationalp x)
                 (not (= x 0))
                 (integerp n)
                 (> n 0)
                 (not (= (abs (away x n)) (expt 2 (1+ (expo x))))))
            (exactp (away x n) n))
   :rule-classes ()
   :hints (("Goal" :in-theory (disable abs)
            :use ((:instance away-exactp-b-2)
                  (:instance away-exactp-b-6)
;                  (:instance away-0-0)
                  (:instance exactp->=-expo (x (away x n)) (e (expo x))))))))

(local
 (defthm away-exactp-b-9
   (implies (and (rationalp x)
                 (integerp n)
                 (integerp m)
                 (> m 0)
                 (= (abs x) (expt 2 n)))
            (exactp x m))
   :rule-classes ()
   :hints (("Goal" :in-theory (enable exactp2)
            :use (;(:instance away-exactp-b-8)
                  (:instance exactp-2**n))))))

(local
 (defthm away-exactp-b-10
    (implies (and (rationalp x)
		  (not (= x 0))
		  (integerp n)
		  (> n 0))
	     (exactp (away x n) n))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable abs)
		  :use ((:instance away-exactp-b-7)
			(:instance away-exactp-b-9 (x (away x n)) (m n) (n (1+ (expo x))))
                        )))))


;gross.  keep disabled
(defthmd away-with-n-not-an-integer
  (implies (not (integerp n))
           (equal (away x n)
                  (if (not (rationalp x))
                      0
                    (if (acl2-numberp n)
                        (if (power2p (abs x))
                            (sgn x)
                        (* 2 (sgn x)))
                      (* (sgn x) (expt 2 (+ 1 (expo x))))))))
  :otf-flg t
  :hints (("Goal" :in-theory (enable away)))
  )

(defthm away-exactp-a
    (implies (case-split (< 0 n)) ;can't drop this hyp
	     (exactp (away x n) n))
  :hints (("Goal" :in-theory (enable  away-with-n-not-an-integer)
           :use ((:instance away-exactp-b-10)
;			(:instance away-0-0)
                        ))))

(local
 (defthm away-exactp-c-1
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0)
		  (rationalp a)
		  (exactp a n)
		  (>= a x)
		  (< a (away x n)))
	     (>= (away x n) (+ x (expt 2 (- (1+ (expo x)) n)))))
    :rule-classes ((:rewrite :match-free :all))
  :hints (("Goal" :in-theory (disable EXPT-COMPARE)
		  :use ((:instance away-exactp-b)
			(:instance fp+2 (x a) (y (away x n)))
			(:instance expo-monotone (y a))
			(:instance expt-weak-monotone (n (- (1+ (expo x)) n)) (m (- (1+ (expo a)) n))))))))




(local
 (defthm away-exactp-c-support
    (implies (and (exactp a n)
		  (>= a x)
                  (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0)
		  (rationalp a)
		  )
	     (>= a (away x n)))
  :hints (("Goal" :in-theory (disable)
		  :use ((:instance away-exactp-c-1)
			(:instance away-upper-1)
			;(:instance away-positive)
                        )))))

(defthmd away-exactp-c
    (implies (and (exactp a n)
		  (>= a x)
                  (rationalp x)
		  (integerp n)
		  (> n 0)
		  (rationalp a))
	     (>= a (away x n)))
    :hints (("Goal" :cases ((equal x 0)
                            (< 0 x)
                            (< x 0))
             :in-theory (e/d (away-minus) ()))
            ("Subgoal 2" :use ((:instance away-exactp-c-support)))
            ("Subgoal 1" :use ((:instance away-lower-bound)))))


(encapsulate
 ()
 (local (defthm away-monotone-old
   (implies (and (rationalp x)
                 (rationalp y)
                 (integerp n)
                 (> x 0)
                 (> n 0)
                 (<= x y))
            (<= (away x n) (away y n)))
   :hints (("Goal" :in-theory (disable)
            :use ((:instance away-exactp-b (x y))
                  (:instance away-lower-pos (x y))
                  (:instance away-exactp-c (a (away y n))))))))

;trying disabled?
 (defthmd away-monotone
   (implies (and (rationalp x)
                 (rationalp y)
                 (integerp n)
                 (<= x y))
            (<= (away x n) (away y n)))
   :hints (("Goal" :in-theory (disable away-upper-pos
;                                      away-positive away-negative
;away-to-0-or-fewer-bits
                                       expo-monotone
                                       away-monotone-old)
            :cases ((> n 0)))
           ("subgoal 2"
            :use ((:instance expt-weak-monotone
                             (n (+ 1 (EXPO X) (* -1 N)))
                             (m (+ 1 (EXPO y) (* -1 N))))
;                 away-to-0-or-fewer-bits
                  expo-monotone
                  (:instance expo-monotone (x y) (y x))
;                (:instance away-to-0-or-fewer-bits (x y))
                  ))
           ("subgoal 1"
            :use (away-monotone-old
                  (:instance away-monotone-old (x (- y))
                             (y (- x))))))
   :rule-classes :linear)
 )



(defthm away-exactp-d
    (implies (and (rationalp x)
		  (not (= x 0))
		  (integerp n)
		  (> n 0))
	     (<= (abs (away x n)) (expt 2 (1+ (expo x)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable abs)
		  :use ((:instance away-exactp-b-5)))))

(defthmd away-pos-rewrite
  (implies (and (rationalp x)
                (>= x 0)
                (integerp n))
           (equal (away x n)
                  (* (cg (* (expt 2 (- (1- n) (expo x))) x))
                     (expt 2 (- (1+ (expo x)) n)))))
  :hints (("goal" :in-theory (enable away sgn expt-split expt-minus)
           :use fp-abs)))


(local (defthm expo-away-support
  (implies (and (rationalp x)
                (not (= x 0))
                (integerp n)
                (> n 0)
                (not (= (abs (away x n)) (expt 2 (1+ (expo x))))))
           (equal (expo (away x n))
                  (expo x)))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable abs)
           :use ((:instance away-exactp-b-6)
                 (:instance expo-monotone (y (away x n)))
                 (:instance away-lower-bound))))))

(defthm expo-away
  (implies (and (rationalp x)
                (natp n)
                (not (= (abs (away x n)) (expt 2 (1+ (expo x))))))
           (equal (expo (away x n))
                  (expo x)))
  :hints (("Goal" :cases ((equal x 0) (< x 0) (> x 0)))
             ("Subgoal 2" :in-theory (enable sgn)
              :use ((:instance expo-away-support)))
             ("Subgoal 1" :in-theory (enable sgn)
              :use ((:instance expo-away-support)))))



(local
 (defthm away-away-1
    (implies (and (rationalp x)
		  (>= x 0)
		  (integerp n)
		  (not (= (away x n) (expt 2 (1+ (expo x)))))
		  (integerp m)
		  (> m 0)
		  (>= n m))
	     (= (away (away x n) m)
		(* (cg (* (expt 2 (- (1- m) (expo x)))
			  (* (cg (* (expt 2 (- (1- n) (expo x))) x))
			     (expt 2 (- (1+ (expo x)) n)))))
		   (expt 2 (- (1+ (expo x)) m)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (e/d (away-pos-rewrite expt-split expt-minus)
                              ())
		  :use (;(:instance away-positive)
			(:instance expo-away))))))

(local
 (defthm away-away-2
    (implies (and (rationalp x)
		  (>= x 0)
		  (integerp n)
		  (not (= (away x n) (expt 2 (1+ (expo x)))))
		  (integerp m)
		  (> m 0)
		  (>= n m))
	     (= (away (away x n) m)
		(* (cg (* (cg (* (expt 2 (- (1- n) (expo x))) x)) (expt 2 (- m n))))
		   (expt 2 (- (1+ (expo x)) m)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable expt-compare-equal)
		  :use ((:instance away-away-1)
			(:instance expt-split (r 2) (j (- (1- m) (expo x))) (i (- (1+
                                                                        (expo
                                                                         x))
                                                                       n))))))))


(local
 (defthm away-away-3
    (implies (and (rationalp x)
		  (>= x 0)
		  (integerp n)
		  (not (= (away x n) (expt 2 (1+ (expo x)))))
		  (integerp m)
		  (> m 0)
		  (>= n m))
	     (= (away (away x n) m)
		(* (cg (/ (cg (* (expt 2 (- (1- n) (expo x))) x)) (expt 2 (- n m))))
		   (expt 2 (- (1+ (expo x)) m)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable expt-split expt-minus)
		  :use ((:instance away-away-2))))))

(local
 (defthm away-away-4
    (implies (and (rationalp x)
		  (>= x 0)
		  (integerp n)
		  (not (= (away x n) (expt 2 (1+ (expo x)))))
		  (integerp m)
		  (> m 0)
		  (>= n m))
	     (= (away (away x n) m)
		(* (cg (/ (* (expt 2 (- (1- n) (expo x))) x) (expt 2 (- n m))))
		   (expt 2 (- (1+ (expo x)) m)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable cg/int-rewrite)
		  :use ((:instance away-away-3)
			(:instance cg/int-rewrite
				   (x (* (expt 2 (- (1- n) (expo x))) x))
				   (n (expt 2 (- n m)))))))))

(local
 (defthm away-away-5
    (implies (and (rationalp x)
		  (>= x 0)
		  (integerp n)
		  (not (= (away x n) (expt 2 (1+ (expo x)))))
		  (integerp m)
		  (> m 0)
		  (>= n m))
	     (= (away (away x n) m)
		(* (cg (* (expt 2 (- (1- m) (expo x))) x))
		   (expt 2 (- (1+ (expo x)) m)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (e/d (expt-split expt-minus) ())
		  :use ((:instance away-away-4))))))

(local
 (defthm away-away-6
    (implies (and (rationalp x)
		  (>= x 0)
		  (integerp n)
		  (not (= (away x n) (expt 2 (1+ (expo x)))))
		  (integerp m)
		  (> m 0)
		  (>= n m))
	     (equal (away (away x n) m)
		    (away x m)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable away-pos-rewrite)
		  :use ((:instance away-away-5))))))

(local
 (defthm away-away-7
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (integerp m)
		  (> m 0)
		  (>= n m))
	     (>= (away x m) (away x n)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance away-exactp-c (a (away x m)))
			(:instance away-exactp-b (n m))
			(:instance away-lower-pos (n m))
			(:instance exactp-<= (x (away x m))))))))
(local
 (defthm away-away-8
    (implies (and (rationalp x)
		  (>= x 0)
		  (integerp n)
		  (integerp m)
		  (> m 0)
		  (>= n m))
	     (>= (away x m) (away x n)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance away-away-7)
;			(:instance away-0-0)
	;		(:instance away-0-0 (n m))
                        )))))

(local
 (defthm away-away-9
    (implies (and (rationalp x)
		  (>= x 0)
		  (integerp n)
		  (= (away x n) (expt 2 (1+ (expo x))))
		  (integerp m)
		  (> m 0)
		  (>= n m))
	     (equal (away (away x n) m)
		    (away x m)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable away-pos-rewrite)
		  :use ((:instance away-away-8)
			(:instance exactp-2**n (n (1+ (expo x))))
			(:instance away-exactp-a (x (expt 2 (1+ (expo x)))) (n m))
			(:instance away-exactp-d (n m)))))))

;handle the case where n<m?
(defthm away-away
    (implies (and (rationalp x)
		  (>= x 0)
		  (integerp n)
		  (integerp m)
		  (> m 0)
		  (>= n m))
	     (equal (away (away x n) m)
		    (away x m)))
  :hints (("Goal" :use ((:instance away-away-9)
			(:instance away-away-6)))))

(defthm away-shift
  (implies (integerp n)
           (= (away (* x (expt 2 k)) n)
              (* (away x n) (expt 2 k))))
  :hints (("Goal" :in-theory (set-difference-theories
                              (enable away
                                      sig
                                      expt-split
                                      )
                              '()))))

(local
 (defthm trunc-away-1
   (implies (and (integerp n) (> n 0)
                 (rationalp x) (> x 0)
                 (not (exactp x n)))
            (> x (expt 2 (expo x))))
   :rule-classes ()
   :hints (("goal" :use ((:instance expo-lower-bound)
                  (:instance exactp-2**n (n (expo x)) (m n)))))))


(local
(defthm trunc-away-2
    (implies (and (integerp n) (> n 0)
		  (rationalp x) (> x 0)
		  (exactp x (1+ n))
		  (not (exactp x n)))
	     (>= (- x (expt 2 (- (expo x) n)))
		 (expt 2 (expo x))))
  :rule-classes ()
  :hints (("goal" :use ((:instance trunc-away-1)
			(:instance exactp-2**n (n (expo x)) (m (1+ n)))
			(:instance fp+2 (x (expt 2 (expo x))) (n (1+ n)) (y x)))))))

(local
(defthm trunc-away-3
    (implies (and (integerp n) (> n 0)
		  (rationalp x) (> x 0)
		  (exactp x (1+ n))
		  (not (exactp x n)))
	     (= (expo (- x (expt 2 (- (expo x) n))))
		(expo x)))
  :rule-classes ()
  :hints (("goal" :use ((:instance trunc-away-2)
			(:instance expo-unique (x (- x (expt 2 (- (expo x) n)))) (n (expo x)))
			(:instance exactp-2**n (n (- (expo x) n)) (m n))
;			(:instance expt-pos (x (- (expo x) n)))
			(:instance expo-lower-bound)
			(:instance expt-weak-monotone (n (- (expo x) n)) (m (expo x)))
			(:instance expo-upper-bound))))))

#|
zz
;yuck
(local
 (defthm hack-83
   (implies (and (integerp n)
                 (< 0 n))
            (= (* 1/2 (expt 2 (+ n (* -1 (expo x)))))
               (expt 2 (1- n (* -1 (expo x))))))
   :rule-classes ()
   :hints (("goal" :use ((:instance expt-split (r 2) (i (- n (expo x))) (j -1)))))))

;yuck
(local
 (defthm hack-84
   (implies (and (rationalp x)
                 (rationalp a)
                 (rationalp b)
                 (= a b))
            (= (* x a) (* x b)))
   :rule-classes ()))

;yuck
(local
 (defthm hack-85
   (implies (and (integerp n)
                 (< 0 n)
                 (rationalp x))
            (equal (* 1/2 x (expt 2 (+ n (* -1 (expo x)))))
                   (* x (expt 2 (1- n (* -1 (expo x)))))))
   :hints (("goal" :use ((:instance hack-83)
                         (:instance hack-84
                                    (a (* 1/2 (expt 2 (+ n (* -1 (expo x))))))
                                    (b (expt 2 (1- n (* -1 (expo x)))))))))))
|#

(local
 (defthm trunc-away-4
   (implies (and (integerp n) (> n 0)
                 (rationalp x) (> x 0)
                 (exactp x (1+ n))
                 (not (exactp x n)))
            (= (* x (expt 2 (- n (expo x))))
               (1+ (* 2 (fl-half (* x (expt 2 (- n (expo x)))))))))
   :rule-classes ()
   :hints (("goal" :in-theory (enable exactp2 expt-split)
            :use ((:instance fl-half-lemma (x (* x (expt 2 (- n (expo x)))))))))))

#|
;yuck
(local
 (defthm hack-86
   (implies (integerp k)
            (= (- (/ (1+ (* 2 k)) 2) 1/2) k))
   :rule-classes ()))
|#

(local
 (defthm trunc-away-5
   (implies (and (integerp n) (> n 0)
                 (rationalp x) (> x 0)
                 (exactp x (1+ n))
                 (not (exactp x n)))
            (= (* (- x (expt 2 (- (expo x) n)))
                  (expt 2 (- (1- n) (expo x))))
               (fl-half (* x (expt 2 (- n (expo x)))))))
   :rule-classes ()
   :hints (("goal" :in-theory (disable expt-compare-equal)
            :use ((:instance trunc-away-4)
;                         (:instance hack-86 (k (fl-half (* x (expt 2 (- n (expo x)))))))
                         (:instance expt-split (r 2) (i (- (expo x) n)) (j (- (1- n) (expo x))))
                         (:instance expt-split (r 2) (i 1) (j (- (1- n) (expo x)))))))))

(local
 (defthm trunc-away-6
   (implies (and (integerp n) (> n 0)
                 (rationalp x) (> x 0)
                 (exactp x (1+ n))
                 (not (exactp x n)))
            (integerp (* (- x (expt 2 (- (expo x) n)))
                         (expt 2 (- (1- n) (expo x))))))
   :rule-classes ()
   :hints (("goal" :use ((:instance trunc-away-5))))))

(local
 (defthm trunc-away-7
   (implies (and (integerp n) (> n 0)
                 (rationalp x) (> x 0)
                 (exactp x (1+ n))
                 (not (exactp x n)))
            (integerp (* (- x (expt 2 (- (expo x) n)))
                         (expt 2 (- (1- n) (expo (- x (expt 2 (- (expo x) n)))))))))
   :rule-classes ()
   :hints (("goal" :use ((:instance trunc-away-6)
                         (:instance trunc-away-3))))))

(local
 (defthm trunc-away-8
   (implies (and (integerp n) (> n 0)
                 (rationalp x) (> x 0)
                 (exactp x (1+ n))
                 (>= (- x (expt 2 (- (expo x) n))) 0)
                 (not (exactp x n)))
            (exactp (- x (expt 2 (- (expo x) n)))
                    n))
   :rule-classes ()
   :hints (("goal" :in-theory (enable exactp2)
            :use ((:instance trunc-away-7))))))

(local
 (defthm trunc-away-9
   (implies (and (integerp n) (> n 0)
                 (rationalp x) (> x 0)
                 (exactp x (1+ n))
                 (not (exactp x n)))
            (exactp (- x (expt 2 (- (expo x) n)))
                    n))
   :rule-classes ()
   :hints (("goal" :in-theory (e/d (expt-split) (expt-compare
                                                 EXPO-COMPARISON-REWRITE-TO-BOUND
                                                 EXPO-COMPARISON-REWRITE-TO-BOUND-2
                                                 ))
            :use ((:instance trunc-away-8)
                  (:instance expo-lower-bound)
                  (:instance expt-weak-monotone (n (- (expo x) n)) (m (expo x))))))))

(local
 (defthm trunc-away-10
   (implies (and (integerp n) (> n 0)
                 (rationalp x) (> x 0)
                 (exactp x (1+ n))
                 (not (exactp x n)))
            (<= (- x (expt 2 (- (expo x) n)))
                (trunc x n)))
   :rule-classes ()
   :hints (("goal" :in-theory (disable; expt-pos
                               trunc-exactp-c)
            :use ((:instance trunc-away-9)
                  (:instance expo-lower-bound)
                  (:instance expt-weak-monotone (n (- (expo x) n)) (m (expo x)))
;                  (:instance expt-pos (x (- (expo x) n)))
                  (:instance trunc-exactp-c (a (- x (expt 2 (- (expo x) n))))))))))

(local
(defthm trunc-away-11
    (implies (and (integerp n) (> n 0)
		  (rationalp x) (> x 0)
		  (exactp x (1+ n))
		  (not (exactp x n))
		  (< (- x (expt 2 (- (expo x) n)))
		     (trunc x n)))
	     (<= x (trunc x n)))
  :rule-classes ()
  :hints (("goal" :in-theory (disable
                              expt-compare
                               EXPT-COMPARE-EQUAL
                               EXPO-COMPARISON-REWRITE-TO-BOUND
                              ;expt-pos
;exactp2
                               )
		  :use ((:instance trunc-away-8)
			(:instance trunc-away-3)
			(:instance expt-split (r 2) (i 1) (j (- n (expo x))))
;			(:instance expt-pos (x (- (expo x) n)))
			(:instance fp+2 (x (- x (expt 2 (- (expo x) n)))) (y (trunc x n)))
			(:instance expo-lower-bound)
			(:instance expt-strong-monotone (n (- (expo x) n)) (m (expo x)))
			(:instance expt-strong-monotone (n (- (expo x) n)) (m (- (1+ (expo x)) n))))))))



(defthm trunc-away-a
    (implies (and (integerp n) (> n 0)
		  (rationalp x) (> x 0)
		  (exactp x (1+ n))
		  (not (exactp x n)))
	     (= (- x (expt 2 (- (expo x) n)))
		(trunc x n)))
  :rule-classes ()
  :hints (("goal" :in-theory (disable trunc-exactp-a)
		  :use ((:instance trunc-away-10)
			(:instance trunc-away-11)
			(:instance trunc-upper-pos)
			(:instance trunc-exactp-a)))))

(local
(defthm hack-87
    (implies (and (rationalp x)
		  (integerp n)
		  (= (expo (- x (expt 2 (- (expo x) n))))
		     (expo x)))
	     (equal (+ x (* -1 (expt 2 (+ (expo x) (* -1 n))))
		       (expt 2
			 (+ 1 (* -1 n)
			    (expo (+ x
				     (* -1 (expt 2 (+ (expo x) (* -1 n)))))))))
		    (+ x (expt 2 (+ (expo x) (* -1 n))))))
  :rule-classes ()
  :hints (("goal" :use ((:instance expt-split (r 2) (i (- (expo x) n)) (j
                                                                        1)))))))

(local
 (defthm hack-88
   (implies (equal x y) (equal (exactp x n) (exactp y n)))
   :rule-classes ()))

(local
 (defthm hack-89
   (implies (and (rationalp x)
                 (integerp n)
                 (= (expo (- x (expt 2 (- (expo x) n))))
                    (expo x)))
            (equal (exactp (+ x (* -1 (expt 2 (+ (expo x) (* -1 n))))
                              (expt 2
                                    (+ 1 (* -1 n)
                                       (expo (+ x
                                                (* -1 (expt 2 (+ (expo x) (* -1 n)))))))))
                           n)
                   (exactp (+ x (expt 2 (+ (expo x) (* -1 n)))) n)))
   :rule-classes ()
   :hints (("goal" :use ((:instance hack-87)
                         (:instance hack-88
                                    (x (+ x (* -1 (expt 2 (+ (expo x) (* -1 n))))
                                          (expt 2
                                                (+ 1 (* -1 n)
                                                   (expo (+ x
                                                            (* -1 (expt 2 (+ (expo x) (* -1 n))))))))))
                                    (y (+ x (expt 2 (+ (expo x) (* -1 n)))))))))))

;(local (in-theory (disable expo-monotone))) ;drop?

;not about away...
(local
 (defthm trunc-away-12
   (implies (and (integerp n) (> n 0)
                 (rationalp x) (> x 0)
                 (exactp x (1+ n))
                 (not (exactp x n)))
            (exactp (+ x (expt 2 (- (expo x) n)))
                    n))
   :rule-classes ()
   :hints (("goal" :in-theory (disable EXPO-COMPARISON-REWRITE-TO-BOUND
                                       EXPO-COMPARISON-REWRITE-TO-BOUND-2
                                       EXPT-COMPARE-EQUAL
                                       EXPT-COMPARE)
            :use ((:instance trunc-away-9)
                  (:instance fp+1 (x (- x (expt 2 (- (expo x) n)))))
                  (:instance expo-lower-bound)
                  (:instance expt-strong-monotone (n (- (expo x) n)) (m (expo x)))
                  (:instance expt-split (r 2) (i (- (expo x) n)) (j 1))
                  (:instance hack-89)
                  (:instance trunc-away-3))))))

(local
(defthm trunc-away-13
    (implies (and (integerp n) (> n 0)
		  (rationalp x) (> x 0)
		  (exactp x (1+ n))
		  (not (exactp x n)))
	     (>= (+ x (expt 2 (- (expo x) n)))
		 (away x n)))
  :rule-classes ()
  :hints (("goal" :in-theory (disable ;expt-pos
                                      away-exactp-c)
		  :use ((:instance trunc-away-12)
			(:instance expo-lower-bound)
			(:instance expt-weak-monotone (n (- (expo x) n)) (m (expo x)))
;			(:instance expt-pos (x (- (expo x) n)))
			(:instance away-exactp-c (a (+ x (expt 2 (- (expo x) n))))))))))

(local
(defthm trunc-away-14
    (implies (and (integerp n) (> n 0)
		  (rationalp x) (> x 0)
		  (exactp x (1+ n))
		  (not (exactp x n)))
	     (> (away x n)
		(- x (expt 2 (- (expo x) n)))))
  :rule-classes ()
  :hints (("goal" :in-theory (disable ;expt-pos
                              )
		  :use ((:instance away-lower-pos)
;			(:instance expt-pos (x (- (expo x) n)))
                        )))))

(local
(defthm trunc-away-15
    (implies (and (integerp n) (> n 0)
		  (rationalp x) (> x 0)
		  (exactp x (1+ n))
		  (not (exactp x n)))
	     (>= (away x n)
		 (+ (- x (expt 2 (- (expo x) n)))
		    (expt 2 (- (1+ (expo x)) n)))))
  :rule-classes ()
  :hints (("goal" :in-theory (disable away-exactp-a EXPT-COMPARE EXPO-COMPARISON-REWRITE-TO-BOUND)
		  :use ((:instance trunc-away-8)
			(:instance trunc-away-3)
			(:instance expo-lower-bound)
			(:instance expt-strong-monotone (n (- (expo x) n)) (m (expo x)))
			(:instance trunc-away-14)
			(:instance away-exactp-a)
			(:instance fp+2 (x (- x (expt 2 (- (expo x) n)))) (y (away x n))))))))


(local
 (defthm trunc-away-16
   (implies (and (integerp n) (> n 0)
                 (rationalp x) (> x 0)
                 (exactp x (1+ n))
                 (not (exactp x n)))
            (>= (away x n)
                (+ x (expt 2 (- (expo x) n)))))
   :rule-classes ()
   :hints (("goal" :in-theory (enable expt-split)
            :use ((:instance trunc-away-15)
                  )))))

(defthm trunc-away-b
    (implies (and (integerp n) (> n 0)
		  (rationalp x) (> x 0)
		  (exactp x (1+ n))
		  (not (exactp x n)))
	     (= (away x n)
		(+ x (expt 2 (- (expo x) n)))))
  :rule-classes ()
  :hints (("goal" :use ((:instance trunc-away-16)
			(:instance trunc-away-13)))))





(local (defthm away-imp-1
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0)
		  (integerp m)
		  (>= m n)
		  (exactp x m))
	     (< (trunc (+ x
			  (expt 2 (- (1+ (expo x)) n))
			  (- (expt 2 (- (1+ (expo x)) m))))
		       n)
		(+ x (expt 2 (- (1+ (expo x)) n)))))
  :rule-classes ()
  :hints (("goal" :in-theory (disable ;expt-pos
                              )
		  :use ((:instance trunc-upper-pos
				   (x (+ x
					 (expt 2 (- (1+ (expo x)) n))
					 (- (expt 2 (- (1+ (expo x)) m))))))
;			(:instance expt-pos (x (- (1+ (expo x)) m)))
			(:instance expt-weak-monotone (n (- (1+ (expo x)) m)) (m (- (1+ (expo x)) n))))))))

(local (in-theory (disable abs-pos)))

(local (defthm away-imp-2
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0))
	     (<= (+ x (expt 2 (- (1+ (expo x)) n)))
		 (+ (away x n)
		    (expt 2 (- (1+ (expo (away x n))) n)))))
  :rule-classes ()
  :hints (("goal" :in-theory (disable  expt-compare
                                       EXPO-COMPARISON-REWRITE-TO-BOUND-2)
                              :use ((:instance away-lower-pos)
			(:instance expo-monotone (y (away x n)))
			(:instance expt-weak-monotone
				   (n (- (1+ (expo x)) n)) (m (- (1+ (expo (away x n))) n))))))))

(local (defthm away-imp-3
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0)
		  (integerp m)
		  (>= m n)
		  (exactp x m))
	     (< (trunc (+ x
			  (expt 2 (- (1+ (expo x)) n))
			  (- (expt 2 (- (1+ (expo x)) m))))
		       n)
		(+ (away x n)
		   (expt 2 (- (1+ (expo (away x n))) n)))))
  :rule-classes ()
  :hints (("goal" :use (away-imp-1 away-imp-2)))))

(local
 (defthm away-imp-4
   (implies (and (rationalp x)
                 (> x 0)
                 (integerp n)
                 (> n 0)
                 (integerp m)
                 (>= m n)
                 (exactp x m))
            (<= (trunc (+ x
                          (expt 2 (- (1+ (expo x)) n))
                          (- (expt 2 (- (1+ (expo x)) m))))
                       n)
                (away x n)))
   :rule-classes ()
   :hints (("goal" :in-theory (disable away-exactp-a trunc-exactp-a away-positive)
            :use (away-imp-3
                  (:instance fp+2
                             (x (away x n))
                             (y (trunc (+ x
                                          (expt 2 (- (1+ (expo x)) n))
                                          (- (expt 2 (- (1+ (expo x)) m))))
                                       n)))
                  (:instance away-positive)
                  (:instance away-exactp-a)
                  (:instance trunc-exactp-a
                             (x (+ x
                                   (expt 2 (- (1+ (expo x)) n))
                                   (- (expt 2 (- (1+ (expo x)) m)))))))))))

(local (defthm away-imp-5
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0)
		  (integerp m)
		  (>= m n)
		  (exactp x m)
		  (exactp x n))
	     (>= (trunc (+ x
			   (expt 2 (- (1+ (expo x)) n))
			   (- (expt 2 (- (1+ (expo x)) m))))
			n)
		 (away x n)))
  :rule-classes ()
  :hints (("goal" :use ((:instance trunc-monotone
				   (y (+ x
					 (expt 2 (- (1+ (expo x)) n))
					 (- (expt 2 (- (1+ (expo x)) m))))))
			(:instance expt-weak-monotone (n (- (1+ (expo x)) m)) (m (- (1+ (expo x)) n)))
			(:instance trunc-exactp-a)
			(:instance away-exactp-a))))))

(local (defthm away-imp-6
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0)
		  (integerp m)
		  (>= m n)
		  (exactp x m)
		  (not (exactp x n)))
	     (>= x
		 (+ (trunc x n)
		    (expt 2 (- (1+ (expo x)) m)))))
  :rule-classes ()
  :hints (("goal" :in-theory (disable trunc-exactp-a)
           :use (trunc-exactp-a
;			trunc-pos
			trunc-upper-pos
			trunc-exactp-b
			(:instance exactp-<= (x (trunc x n)) (n m) (m n))
			(:instance fp+2 (x (trunc x n)) (y x) (n m)))))))

(local (defthm away-imp-7
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0)
		  (integerp m)
		  (>= m n)
		  (exactp x m)
		  (not (exactp x n)))
	     (>= (+ x
		    (expt 2 (- (1+ (expo x)) n))
		    (- (expt 2 (- (1+ (expo x)) m))))
		 (+ (trunc x n)
		    (expt 2 (- (1+ (expo x)) n)))))
  :rule-classes ()
  :hints (("goal" :use (away-imp-6)))))

(local (defthm away-imp-8
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0)
		  (not (exactp x n)))
	     (> (+ (trunc x n)
		   (expt 2 (- (1+ (expo x)) n)))
		x))
  :rule-classes ()
  :hints (("goal" :in-theory (disable trunc-exactp-c trunc-exactp-a)

           :use ((:instance fp+1 (x (trunc x n)))
			(:instance trunc-exactp-a)
;			(:instance trunc-pos)
;			(:instance expt-pos (x (- (1+ (expo x)) n)))
			(:instance trunc-exactp-c
				   (a (+ (trunc x n) (expt 2 (- (1+ (expo x)) n))))))))))

(local (defthm away-imp-9
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0)
		  (not (exactp x n)))
	     (>= (+ (trunc x n)
		   (expt 2 (- (1+ (expo x)) n)))
		(away x n)))
  :rule-classes ()
  :hints (("goal"  :in-theory (disable trunc-exactp-a away-exactp-c)
           :use (away-imp-8
			(:instance fp+1 (x (trunc x n)))
			(:instance trunc-exactp-a)
;			(:instance trunc-pos)
			(:instance away-exactp-c
				   (a (+ (trunc x n) (expt 2 (- (1+ (expo x)) n))))))))))

(local (defthm away-imp-10
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0)
		  (integerp m)
		  (>= m n)
		  (exactp x m)
		  (not (exactp x n)))
	     (>= (+ x
		    (expt 2 (- (1+ (expo x)) n))
		    (- (expt 2 (- (1+ (expo x)) m))))
		 (away x n)))
  :rule-classes ()
  :hints (("goal" :use (away-imp-7 away-imp-9)))))

(local (defthm away-imp-11
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0)
		  (integerp m)
		  (>= m n)
		  (exactp x m)
		  (not (exactp x n)))
	     (>= (trunc (+ x
			   (expt 2 (- (1+ (expo x)) n))
			   (- (expt 2 (- (1+ (expo x)) m))))
			n)
		 (away x n)))
  :rule-classes ()
  :hints (("goal" :in-theory (disable away-exactp-a trunc-exactp-c)
           :use (away-imp-10
			away-exactp-a
			(:instance expt-weak-monotone (n (- (1+ (expo x)) m)) (m (- (1+ (expo x)) n)))
			(:instance trunc-exactp-c
				   (a (away x n))
				   (x (+ x
					 (expt 2 (- (1+ (expo x)) n))
					 (- (expt 2 (- (1+ (expo x)) m)))))))))))

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
  :rule-classes ()
  :hints (("goal" :in-theory (disable AWAY-EXACTP-C-support) ;consider disabling this globally...
           :use (away-imp-11 away-imp-5 away-imp-4))))

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
  :rule-classes ()
  :hints (("goal" :in-theory (e/d (away-pos-rewrite exactp2)
                                  (cg+int-rewrite ;int-fl-rules
                                     ))
           :use ((:instance cg+int-rewrite
                            (x (* y (expt 2 (- (1- k) (expo y)))))
                            (n (* x (expt 2 (- (1- k) (expo y))))))))))

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
  :rule-classes ()
  :hints (("goal" :in-theory (enable away-pos-rewrite)
           :use ((:instance plus-away-2)
                 (:instance expo-monotone (y (+ x y)))))))

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
  :rule-classes ()
  :hints (("goal"
           :use (:instance plus-away
                           (k (+ j (- (expo (+ x y))) (expo y)))))))

; isn't nice for y=0
;corollaries like this for inf, minf, rnd?
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
              (fp+ x n)))
  :hints (("goal"  :in-theory (set-difference-theories
                               (enable sgn
                                       expt-split expt-minus)
                               '(EXPT-COMPARE-EQUAL))
           :use (
                 (:instance only-0-is-0-or-negative-exact)
                 (:instance away-exactp-b)
                  expo-of-sum-of-disjoint
                 (:instance expo<=
                            (x y)
                            (n (+ (expo x) (* -1 n))))
                 (:instance plus-away-alt
                            (j n)))))
  :otf-flg t)
