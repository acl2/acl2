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
;;;an acl2 library of floating point arithmetic
;;;david m. russinoff
;;;advanced micro devices, inc.
;;;february, 1998
;;;***************************************************************

(in-package "RTL")

(local (include-book "../../arithmetic/arith"))
(local (include-book "float"))
(local (include-book "trunc"))
(local (include-book "away"))
(local (include-book "near"))
(local (include-book "near+"))

;; Necessary functions:

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


;;
;; New stuff:
;;


(defund sticky (x n)
  (cond ((exactp x (1- n)) x)
	(t (+ (trunc x (1- n))
              (* (sgn x) (expt 2 (1+ (- (expo x) n))))))))

(defthm sticky-1
  (implies (rationalp x)
           (equal (sticky x 1)
                  (* (sgn x) (expt 2 (expo x)))))
  :hints (("goal" :in-theory (enable sticky)
           :use ((:instance only-0-is-0-or-negative-exact (n 0))
                        (:instance trunc-to-0-or-fewer-bits (n 0))))))

;more rule-classes?
(defthm sticky-pos
    (implies (and (< 0 x) (rationalp x)
		  (integerp n) (> n 0))
	     (< 0 (sticky x n)))
  :rule-classes :linear
  :hints (("goal" :in-theory (enable sticky)
		  :use ((:instance trunc-to-0-or-fewer-bits (n 0))
                        ))))

(defthm sticky-shift
    (implies (and (rationalp x)
		  (integerp n) (> n 0)
		  (integerp k))
	     (= (sticky (* (expt 2 k) x) n)
		(* (expt 2 k) (sticky x n))))
  :rule-classes ()
  :hints (("goal" :in-theory (enable sticky a15)
		  :use (;(:instance expt-pos (x k))
			(:instance sig-expo-shift (n k))
			(:instance expt-split (r 2) (i k) (j (expo x)))
			(:instance trunc-shift (n  (1- n)))
			(:instance exactp-shift (n (1- n)) (k k))
			(:instance exactp-shift (n (1- n)) (k (- k)) (x (* x (expt 2 k))))))))

;BOZO why isn't a5 firing here? if i comment out the (integerp n) hyp but leave the rational hyp?
(defthm sticky-minus
  (equal (sticky (* -1 x) n)
         (* -1 (sticky x n)))
  :hints (("goal" :in-theory (e/d (sgn sticky) (TRUNC-NEGATIVE-RATIONAL-TYPE-PRESCRIPTION ;prevents bad-ass problem
                                                )))))

;; Fri Oct 13 13:35:15 2006
;; (i-am-here)

(encapsulate ()
  (local
   (defthm sticky-exactp-support
     (implies (and (rationalp x) (>= x 0)
                   (integerp n) (> n 0)
                   )
              (exactp (sticky x n) n))
     :rule-classes ()
     :hints (("goal" :in-theory (set-difference-theories
                                 (enable sticky exactp-<= exactp-2**n)
                                 '( trunc-exactp-a
                                    ))
              :use ((:instance fp+1 (x (trunc x (1- n))))
                    (:instance trunc-exactp-a (n  (1- n)))
                    (:instance expo-trunc (n (1- n)))
                    )
              )
             )))

  (defthm sticky-exactp
    (implies (and (rationalp x) ;; (>= x 0)
                  (integerp n) (> n 0)
                  )
              (exactp (sticky x n) n))
     :rule-classes ()
     :hints (("Goal" :cases ((not (>= x 0))))
             ("Subgoal 2" :by sticky-exactp-support)
             ("Subgoal 1" :in-theory (enable sticky exactp-minus)
              :use ((:instance sticky-exactp-support
                               (x (* -1 x))))))))



(encapsulate ()

  (local
   (defthm sticky-exactp-n-1-support
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1))
	     (iff (exactp (sticky x n) (1- n))
		  (exactp x (1- n))))
  :rule-classes ()
  :hints (("goal" :in-theory (set-difference-theories
                              (enable sticky)
                              '( trunc-exactp-a))
		  :use ((:instance trunc-exactp-a (n  (1- n)))
			(:instance expo-trunc (n (1- n)))
			(:instance expt-strong-monotone
				   (n (1+ (- (expo x) n)))
				   (m (+ 2 (- (expo x) n))))
;			(:instance trunc-pos (n (1- n)))
;			(:instance expt-pos (x (1+ (- (expo x) n))))
			(:instance fp+2
				   (y (sticky x n))
				   (n (1- n))
				   (x (trunc x (1- n))))
                        )))))

  (defthm sticky-exactp-n-1
    (implies (and (rationalp x) ;; (> x 0)
		  (integerp n) (> n 1))
	     (iff (exactp (sticky x n) (1- n))
		  (exactp x (1- n))))
  :rule-classes ()
  :hints (("Goal" :cases ((not (> x 0))))
          ("Subgoal 2" :by sticky-exactp-n-1-support)
          ("Subgoal 1" :in-theory (enable sticky exactp-minus)
           :use ((:instance sticky-exactp-n-1-support
                            (x (* -1 x))))))))



(local (defthm expo-sticky-1
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1))
	     (<= (expt 2 (expo x))
		 (sticky x n)))
  :rule-classes ()
  :hints (("goal"
           :in-theory (enable sticky)
           :use ((:instance expo-trunc (n (1- n)))
			(:instance expo-lower-bound (x (trunc x (1- n))))
;			(:instance trunc-pos (n (1- n)))
			(:instance trunc-upper-pos (n (1- n)))
;			(:instance expt-pos (x (1+ (- (expo x) n))))
                        )))))

(local (defthm expo-sticky-2
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1))
	     (<= (+ (trunc x (1- n))
		    (expt 2 (+ 2 (- (expo x) n))))
		(expt 2 (1+ (expo x)))))
  :rule-classes ()
  :hints (("goal" :in-theory (disable trunc-exactp-a abs-trunc)
		  :use ((:instance trunc-exactp-a (n  (1- n)))
			(:instance expo-trunc (n (1- n)))
			(:instance exactp-2**n (n (1+ (expo x))) (m (1- n)))
			(:instance expo-upper-bound (x (trunc x (1- n))))
			(:instance expo-upper-bound)
;			(:instance trunc-pos (n (1- n)))
;			(:instance expt-pos (x (1+ (- (expo x) n))))
			(:instance fp+2
				   (y (expt 2 (1+ (expo x))))
				   (n (1- n))
				   (x (trunc x (1- n)))))))))

(local (defthm expo-sticky-3
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1))
	     (< (sticky x n)
		(expt 2 (1+ (expo x)))))
  :rule-classes ()
  :hints (("goal" :in-theory (set-difference-theories
                              (enable sticky)
                              '(trunc-exactp-a))
		  :use ((:instance expo-sticky-2)
			(:instance expo-upper-bound)
			(:instance expt-strong-monotone
				   (n (1+ (- (expo x) n)))
				   (m (+ 2 (- (expo x) n)))))))))

(local (defthm expo-sticky-4
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1))
	     (= (expo (sticky x n))
		(expo x)))
  :rule-classes ()
  :hints (("goal" :use (expo-sticky-1
			expo-sticky-3
			sticky-pos
			(:instance expo-unique (x (sticky x n)) (n (expo x))))))))


(encapsulate ()
  (local
   (defthm expo-sticky-support
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 0))
	     (= (expo (sticky x n))
		(expo x)))
  :rule-classes ()
  :hints (("goal" :use (expo-sticky-4
			expo-upper-bound
			expo-lower-bound
			(:instance trunc-to-0-or-fewer-bits (n 0))
                        (:instance expo-unique (x (expt 2 (expo x))) (n (expo
                                                                         x))))))))


   (defthm expo-sticky
    (implies (and (rationalp x) ;; (> x 0)
		  (integerp n) (> n 0))
	     (= (expo (sticky x n))
		(expo x)))
  :rule-classes ()
  :hints (("Goal" :cases ((not (> x 0))))
          ("Subgoal 2" :by expo-sticky-support)
          ("Subgoal 1" :in-theory (enable sticky expo-minus)
           :use ((:instance expo-sticky-support
                            (x (* -1 x))))))))



(local (defthm trunc-sticky-1
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1))
	     (= (trunc (sticky x n) (1- n))
		(trunc x (1- n))))
  :rule-classes ()
  :hints (("goal" :in-theory (enable sticky)
           :use (sticky-exactp
			expo-sticky
			sticky-exactp-n-1
			sticky-pos
;			(:instance trunc-trunc (n (1- n)) (m (1- n)))
			(:instance trunc-away-a (x (sticky x n)) (n (1- n))))))))

(encapsulate ()
   (local
    (defthm trunc-sticky-support
      (implies (and (rationalp x) (> x 0)
                    (integerp m) (> m 0)
                    (integerp n) (> n m))
               (= (trunc (sticky x n) m)
                  (trunc x m)))
      :rule-classes ()
      :hints (("goal" :in-theory (disable sticky trunc-trunc)
               :use (trunc-sticky-1
                     sticky-pos
                     (:instance trunc-trunc (n (1- n)))
                     (:instance trunc-trunc (n (1- n)) (x (sticky x n)))
                     )))))

  (defthm trunc-sticky
    (implies (and (rationalp x) ;; (> x 0)
                  (integerp m) (> m 0)
                  (integerp n) (> n m))
             (= (trunc (sticky x n) m)
                (trunc x m)))
    :rule-classes ()
    :hints (("Goal" :cases ((not (> x 0))))
            ("Subgoal 2" :by trunc-sticky-support)
            ("Subgoal 1" :in-theory (enable sticky)
             :use ((:instance trunc-sticky-support
                              (x (* -1 x))))))))



(local (defthm away-sticky-1
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1)
		  (not (exactp x (1- n))))
	     (= (away (sticky x n) (1- n))
		(+ (trunc x (1- n))
		   (expt 2 (+ (expo x) 2 (- n))))))
  :rule-classes ()
  :hints (("goal" :in-theory (enable sticky)
           :use (sticky-exactp
			expo-sticky
			sticky-exactp-n-1
			sticky-pos
			(:instance expt-split (r 2) (i (1+ (- (expo x) n))) (j 1))
			(:instance trunc-away-b (x (sticky x n)) (n (1- n))))))))

(local (defthm away-sticky-2
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1)
		  (not (exactp x (1- n))))
	     (<= (+ (trunc x (1- n))
		    (expt 2 (+ (expo x) 2 (- n))))
		 (away x (1- n))))
  :rule-classes ()
  :hints (("goal" :use ((:instance fp+2 (x (trunc x (1- n))) (n (1- n)) (y (away x (1- n))))
			(:instance away-exactp-a (n (1- n)))
			(:instance trunc-exactp-a (n (1- n)))
			(:instance trunc-exactp-b (n (1- n)))
;			(:instance trunc-pos (n (1- n)))
			(:instance trunc-upper-pos (n (1- n)))
			(:instance away-lower-pos (n (1- n))))))))

(local (defthm away-sticky-3
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1)
		  (not (exactp x (1- n))))
	     (>= (+ (trunc x (1- n))
		    (expt 2 (+ (expo x) 2 (- n))))
		 (away x (1- n))))
  :rule-classes ()
  :hints (("goal" :use ((:instance fp+1 (x (trunc x (1- n))) (n (1- n)))
			(:instance trunc-exactp-a (n (1- n)))
;			(:instance trunc-pos (n (1- n)))
			(:instance trunc-diff-pos (n (1- n)))
			(:instance away-exactp-c
				   (n (1- n))
				   (a (+ (trunc x (1- n))
					 (expt 2 (+ (expo x) 2 (- n)))))))))))

(local (defthm away-sticky-4
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1))
	     (= (away (sticky x n) (1- n))
		(away x (1- n))))
  :rule-classes ()
  :hints (("goal" :in-theory (enable sticky)
           :use (away-sticky-1
			away-sticky-2
			away-sticky-3)))))

(encapsulate ()
   (local
    (defthm away-sticky-support
    (implies (and (rationalp x) (> x 0)
		  (integerp m) (> m 0)
		  (integerp n) (> n m))
	     (= (away (sticky x n) m)
		(away x m)))
  :rule-classes ()
  :hints (("goal" :in-theory (disable sticky)
		  :use (away-sticky-4
			sticky-pos
			(:instance away-away (n (1- n)))
			(:instance away-away (n (1- n)) (x (sticky x n))))))))

  (defthm away-sticky
    (implies (and (rationalp x) ;; (> x 0)
		  (integerp m) (> m 0)
		  (integerp n) (> n m))
	     (= (away (sticky x n) m)
		(away x m)))
  :rule-classes ()
  :hints (("Goal" :cases ((not (> x 0))))
          ("Subgoal 2" :by away-sticky-support)
          ("Subgoal 1" :in-theory (enable sticky)
           :use ((:instance away-sticky-support
                            (x (* -1 x))))))))


(local (defthm near-sticky-1
    (implies (and (rationalp x)
		  (rationalp y)
		  (< 0 x)
		  (<= x y)
		  (integerp m)
		  (> m 0)
		  (= (trunc x (1+ m)) (trunc y (1+ m)))
		  (not (= (near x m) (near y m))))
	     (= x (near-witness x y m)))
  :rule-classes ()
  :hints (("goal" :use ((:instance near-near-lemma (n m))
			(:instance trunc-upper-pos (n (1+ m)))
			(:instance trunc-exactp-c (x y) (n (1+ m)) (a (near-witness x y m))))))))

(local (defthm near-sticky-2
    (implies (and (rationalp x)
		  (rationalp y)
		  (< 0 x)
		  (<= x y)
		  (integerp m)
		  (> m 0)
		  (= (away x (1+ m)) (away y (1+ m)))
		  (not (= (near x m) (near y m))))
	     (= y (near-witness x y m)))
  :rule-classes ()
  :hints (("goal" :in-theory (disable away-exactp-c)
		  :use ((:instance near-near-lemma (n m))
			(:instance away-lower-pos (x y) (n (1+ m)))
			(:instance away-exactp-c (n (1+ m)) (a (near-witness x y m))))))))

(local (defthm near-sticky-3
    (implies (and (rationalp x)
		  (rationalp y)
		  (< 0 x)
		  (< 0 y)
		  (integerp m)
		  (> m 0)
		  (= (trunc x (1+ m)) (trunc y (1+ m)))
		  (= (away x (1+ m)) (away y (1+ m))))
	     (= (near x m) (near y m)))
  :rule-classes ()
  :hints (("goal" :use ((:instance near-sticky-1 (x y) (y x))
			(:instance near-sticky-2 (x y) (y x))
			(:instance near-sticky-1)
			(:instance near-sticky-2))))))


(encapsulate ()
  (local
   (defthm near-sticky-support
    (implies (and (rationalp x) (> x 0)
		  (integerp m) (> m 0)
		  (integerp n) (> n (1+ m)))
	     (= (near (sticky x n) m)
		(near x m)))
  :rule-classes ()
  :hints (("goal" :in-theory (disable sticky)
		  :use ((:instance near-sticky-3 (y (sticky x n)))
			(:instance trunc-sticky (m (1+ m)))
			(:instance away-sticky (m (1+ m)))
			sticky-pos)))))


   (defthm near-sticky
    (implies (and (rationalp x) ;; (> x 0)
		  (integerp m) (> m 0)
		  (integerp n) (> n (1+ m)))
	     (= (near (sticky x n) m)
		(near x m)))
  :rule-classes ()
  :hints (("Goal" :cases ((not (> x 0))))
          ("Subgoal 2" :by near-sticky-support)
          ("Subgoal 1" :in-theory (enable sticky near-minus)
           :use ((:instance near-sticky-support
                            (x (* -1 x))))))))



(local (defthm near+-sticky-1
    (implies (and (rationalp x)
		  (rationalp y)
		  (< 0 x)
		  (<= x y)
		  (integerp m)
		  (> m 0)
		  (= (trunc x (1+ m)) (trunc y (1+ m)))
		  (not (= (near+ x m) (near+ y m))))
	     (= x (near+-witness x y m)))
  :rule-classes ()
  :hints (("goal" :use ((:instance near+-near+-lemma (n m))
			(:instance trunc-upper-pos (n (1+ m)))
			(:instance trunc-exactp-c (x y) (n (1+ m)) (a (near+-witness x y m))))))))

(local (defthm near+-sticky-2
    (implies (and (rationalp x)
		  (rationalp y)
		  (< 0 x)
		  (<= x y)
		  (integerp m)
		  (> m 0)
		  (= (away x (1+ m)) (away y (1+ m)))
		  (not (= (near+ x m) (near+ y m))))
	     (= y (near+-witness x y m)))
  :rule-classes ()
  :hints (("goal" :in-theory (disable away-exactp-c)
		  :use ((:instance near+-near+-lemma (n m))
			(:instance away-lower-pos (x y) (n (1+ m)))
			(:instance away-exactp-c (n (1+ m)) (a (near+-witness x y m))))))))

(local (defthm near+-sticky-3
    (implies (and (rationalp x)
		  (rationalp y)
		  (< 0 x)
		  (< 0 y)
		  (integerp m)
		  (> m 0)
		  (= (trunc x (1+ m)) (trunc y (1+ m)))
		  (= (away x (1+ m)) (away y (1+ m))))
	     (= (near+ x m) (near+ y m)))
  :rule-classes ()
  :hints (("goal" :use ((:instance near+-sticky-1 (x y) (y x))
			(:instance near+-sticky-2 (x y) (y x))
			(:instance near+-sticky-1)
			(:instance near+-sticky-2))))))


(encapsulate ()
  (local
   (defthm near+-sticky-support
    (implies (and (rationalp x) (> x 0)
		  (integerp m) (> m 0)
		  (integerp n) (> n (1+ m)))
	     (= (near+ (sticky x n) m)
		(near+ x m)))
  :rule-classes ()
  :hints (("goal" :in-theory (disable sticky)
		  :use ((:instance near+-sticky-3 (y (sticky x n)))
			(:instance trunc-sticky (m (1+ m)))
			(:instance away-sticky (m (1+ m)))
			sticky-pos)))))



   (defthm near+-sticky
    (implies (and (rationalp x) ;; (> x 0)
		  (integerp m) (> m 0)
		  (integerp n) (> n (1+ m)))
	     (= (near+ (sticky x n) m)
		(near+ x m)))
  :rule-classes ()
  :hints (("Goal" :cases ((not (> x 0))))
          ("Subgoal 2" :by near+-sticky-support)
          ("Subgoal 1" :in-theory (enable sticky near+-minus)
           :use ((:instance near+-sticky-support
                            (x (* -1 x))))))))



(local (defthm minus-trunc-1
    (implies (and (rationalp x)
		  (> x 0)
		  (rationalp y)
		  (> y 0)
		  (integerp k)
		  (> k 0)
		  (= n (+ k (- (expo x) (expo y))))
		  (exactp x n))
	     (equal (- x (trunc y k))
		    (* (- (* x (expt 2 (- (1- k) (expo y))))
			  (fl (* y (expt 2 (- (1- k) (expo y))))))
		       (expt 2 (- (1+ (expo y)) k)))))
  :rule-classes ()
  :hints (("goal" :in-theory (enable trunc-rewrite)
           :use ((:instance expt-split (r 2) (i (- (1- k) (expo y))) (j (- (1+ (expo y)) k))))))))

(local (defthm minus-trunc-2
    (implies (and (rationalp x)
		  (> x 0)
		  (rationalp y)
		  (> y 0)
		  (integerp k)
		  (> k 0)
		  (= n (+ k (- (expo x) (expo y))))
		  (exactp x n))
	     (equal (- x (trunc y k))
		    (* (- (fl (* (- y x) (expt 2 (- (1- k) (expo y))))))
		       (expt 2 (- (1+ (expo y)) k)))))
  :rule-classes ()
  :hints (("goal" :in-theory (disable fl+int-rewrite expo trunc-rewrite)
		  :use ((:instance minus-trunc-1)
			exactp2
			(:instance fl+int-rewrite
				   (x (* y (expt 2 (- (1- k) (expo y)))))
				   (n (- (* x (expt 2 (- (1- k) (expo y))))))))))))

(local (defthm minus-trunc-3
    (implies (and (rationalp x)
		  (> x 0)
		  (rationalp y)
		  (> y 0)
		  (integerp k)
		  (> k 0)
		  (= n (+ k (- (expo x) (expo y))))
		  (exactp x n))
	     (equal (- x (trunc y k))
		    (* (cg (* (- x y) (expt 2 (- (1- k) (expo y)))))
		       (expt 2 (- (1+ (expo y)) k)))))
  :rule-classes ()
  :hints (("goal" :in-theory (enable cg)
		  :use ((:instance minus-trunc-2))))))

(defthm minus-trunc-4
    (implies (and (rationalp x)
		  (> x 0)
		  (rationalp y)
		  (> y 0)
		  (< y x)
		  (integerp k)
		  (> k 0)
		  (> (+ k (- (expo (- x y)) (expo y))) 0)
		  (= n (+ k (- (expo x) (expo y))))
		  (exactp x n))
	     (equal (- x (trunc y k))
		    (away (- x y) (+ k (- (expo (- x y)) (expo y))))))
  :rule-classes ()
  :hints (("goal" :in-theory (enable away-rewrite)
           :use ((:instance minus-trunc-3)))))

(defthm minus-trunc-5
    (implies (and (rationalp x)
		  (> x 0)
		  (rationalp y)
		  (> y 0)
		  (< x y)
		  (integerp k)
		  (> k 0)
		  (> (+ k (- (expo (- x y)) (expo y))) 0)
		  (= n (+ k (- (expo x) (expo y))))
		  (exactp x n))
	     (equal (- x (trunc y k))
		    (- (trunc (- y x) (+ k (- (expo (- x y)) (expo y)))))))
  :rule-classes ()
  :hints (("goal" :in-theory (set-difference-theories
                              (enable trunc-rewrite)
                              '( expo-minus))
           :use ((:instance minus-trunc-2)
                 (:instance expo-minus (x (- x y)))))))

(local (defthm sticky-plus-1
    (implies (and (rationalp x)
		  (rationalp y)
		  (integerp k)
		  (= k1 (+ k (- (expo x) (expo y))))
		  (= k2 (+ k (- (expo (+ x y)) (expo y))))
		  (> k 1)
		  (> k1 1)
		  (> k2 1)
		  (exactp x (1- k1)))
	     (iff (exactp y (1- k))
		  (exactp (+ x y) (1- k2))))
  :rule-classes ()
  :hints (("goal" :use ((:instance exactp2 (n (1- k1)))
			(:instance exactp2 (x y) (n (1- k)))
			(:instance exactp2 (x (+ x y)) (n (1- k2))))))))

(local (defthm sticky-plus-2
    (implies (and (rationalp x)
		  (> x 0)
		  (rationalp y)
		  (> y 0)
		  (exactp y (1- k))
		  (integerp k)
		  (= k1 (+ k (- (expo x) (expo y))))
		  (= k2 (+ k (- (expo (+ x y)) (expo y))))
		  (> k 1)
		  (> k1 1)
		  (> k2 1)
		  (exactp x (1- k1)))
	     (= (+ x (sticky y k))
		(sticky (+ x y) k2)))
  :rule-classes ()
  :hints (("goal" :in-theory (enable sticky)
           :use ((:instance sticky-plus-1))))))

(local (defthm sticky-plus-3
    (implies (and (rationalp x)
		  (> x 0)
		  (rationalp y)
		  (> y 0)
		  (not (exactp y (1- k)))
		  (integerp k)
		  (= k1 (+ k (- (expo x) (expo y))))
		  (= k2 (+ k (- (expo (+ x y)) (expo y))))
		  (> k 1)
		  (> k1 1)
		  (> k2 1)
		  (exactp x (1- k1)))
	     (= (+ x (sticky y k))
		(sticky (+ x y) k2)))
  :rule-classes ()
  :hints (("goal" :in-theory (enable sticky)
           :use (sticky-plus-1
			(:instance plus-trunc (k (1- k))))))))


(defthm sticky-plus-original
    (implies (and (rationalp x)
		  (> x 0)
		  (rationalp y)
		  (> y 0)
		  (integerp k)
		  (= k1 (+ k (- (expo x) (expo y))))
		  (= k2 (+ k (- (expo (+ x y)) (expo y))))
		  (> k 1)
		  (> k1 1)
		  (> k2 1)
		  (exactp x (1- k1)))
	     (= (+ x (sticky y k))
		(sticky (+ x y) k2)))
  :rule-classes ()
  :hints (("goal" :use (sticky-plus-2 sticky-plus-3))))








(local (defthm hack1
    (implies (and (integerp x)
		  (integerp y))
	     (integerp (- x y)))
  :rule-classes ()))

(local (defthm shack2
    (implies (and (rationalp x) (rationalp y))
	     (equal (+ x (* -1 (+ x (* -1 y))))
		    y))
  :rule-classes ()))

(local (defthm shack3
    (implies (and (integerp x)
		  (rationalp y)
		  (integerp (- x y)))
	     (integerp y))
  :rule-classes ()
  :hints (("goal" :use (shack2 (:instance hack1 (y (- x y))))))))

(local (defthm minus-sticky-1
    (implies (and (rationalp x)
		  (rationalp y)
		  (integerp k)
		  (= k1 (+ k (- (expo x) (expo y))))
		  (= k2 (+ k (- (expo (- x y)) (expo y))))
		  (> k 1)
		  (> k1 1)
		  (> k2 1)
		  (exactp x (1- k1)))
	     (iff (exactp y (1- k))
		  (exactp (- x y) (1- k2))))
  :rule-classes ()
  :hints (("goal" :in-theory (enable exactp2)
		  :use ((:instance expo-minus (x y))
			(:instance shack3
				   (x (* x (expt 2 (+ -2 k (* -1 (expo (* -1 y)))))))
				   (y (* y (expt 2 (+ -2 k (* -1 (expo (* -1 y)))))))))))))

(local (defthm minus-sticky-2
    (implies (and (rationalp x)
		  (> x 0)
		  (rationalp y)
		  (> y 0)
		  (exactp y (1- k))
		  (integerp k)
		  (= k1 (+ k (- (expo x) (expo y))))
		  (= k2 (+ k (- (expo (- x y)) (expo y))))
		  (> k 1)
		  (> k1 1)
		  (> k2 1)
		  (exactp x (1- k1)))
	     (= (- x (sticky y k))
		(sticky (- x y) k2)))
  :rule-classes ()
  :hints (("goal" :in-theory (enable sticky)
           :use ((:instance minus-sticky-1))))))

(local (defthm minus-sticky-3
    (implies (and (rationalp x)
		  (> x 0)
		  (rationalp y)
		  (> y 0)
		  (< x y)
		  (not (exactp y (1- k)))
		  (integerp k)
		  (= k1 (+ k (- (expo x) (expo y))))
		  (= k2 (+ k (- (expo (- x y)) (expo y))))
		  (> k 1)
		  (> k1 1)
		  (> k2 1)
		  (exactp x (1- k1)))
	     (= (- x (sticky y k))
		(- (sticky (- y x) k2))))
  :rule-classes ()
  :hints (("goal" :in-theory (set-difference-theories
                              (enable exactp2 sticky trunc-rewrite a15)
                              '(expo-minus))
		  :use ((:instance minus-sticky-1)
			(:instance expo-minus (x (- x y)))
			(:instance minus-trunc-5 (n (+ k (- (expo x) (expo y)))) (k (1- k))))))))

(local (defthm minus-sticky-4
    (implies (and (rationalp x)
		  (> x 0)
		  (rationalp y)
		  (> y 0)
		  (< y x)
		  (not (exactp y (1- k)))
		  (integerp k)
		  (= k1 (+ k (- (expo x) (expo y))))
		  (= k2 (+ k (- (expo (- x y)) (expo y))))
		  (> k 1)
		  (> k1 1)
		  (> k2 1)
		  (exactp x (1- k1)))
	     (= (- x (sticky y k))
		(- (away (- x y) (1- k2))
		   (expt 2 (1+ (- (expo (- x y)) k2))))))
  :rule-classes ()
  :hints (("goal" :in-theory (enable sticky)
           :use ((:instance minus-sticky-1)
			(:instance minus-trunc-4 (n (+ -1 k (- (expo x) (expo y)))) (k (1- k))))))))

(defthm trunc-away
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 0)
		  (not (exactp x n)))
	     (= (away x n)
		(+ (trunc x n)
		   (expt 2 (+ (expo x) 1 (- n))))))
  :rule-classes ()
  :hints (("goal" :use ((:instance away-sticky-2 (n (1+ n)))
			(:instance away-sticky-3 (n (1+ n)))))))

(local (defthm minus-sticky-5
    (implies (and (rationalp x)
		  (> x 0)
		  (rationalp y)
		  (> y 0)
		  (< y x)
		  (not (exactp y (1- k)))
		  (integerp k)
		  (= k1 (+ k (- (expo x) (expo y))))
		  (= k2 (+ k (- (expo (- x y)) (expo y))))
		  (> k 1)
		  (> k1 1)
		  (> k2 1)
		  (exactp x (1- k1)))
	     (= (- x (sticky y k))
		(sticky (- x y) k2)))
  :rule-classes ()
  :hints (("goal" :in-theory (enable sticky)
           :use ((:instance minus-sticky-4)
			(:instance minus-sticky-1)
			(:instance trunc-away (x (- x y)) (n (1- k2)))
			(:instance expt-split (r 2) (i (1+ (- (expo (- x y)) k2))) (j 1)))))))




(local (defthm minus-sticky-6
    (implies (and (rationalp x)
		  (> x 0)
		  (rationalp y)
		  (> y 0)
		  (not (= y x))
		  (integerp k)
		  (= k1 (+ k (- (expo x) (expo y))))
		  (= k2 (+ k (- (expo (- x y)) (expo y))))
		  (> k 1)
		  (> k1 1)
		  (> k2 1)
		  (exactp x (1- k1)))
	     (= (- x (sticky y k))
		(sticky (- x y) k2)))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable sticky sticky-minus)
		  :use ((:instance minus-sticky-2)
			(:instance minus-sticky-3)
			(:instance sticky-minus (x (- x y)) (n k2))
			(:instance minus-sticky-5))))))

(defthm sticky-0
  (equal (sticky 0 n) 0)
  :hints (("Goal" :in-theory (enable sticky trunc))))

(local (defthm minus-sticky-7
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp k)
		  (= k2 (+ k (- (expo (- x y)) (expo y))))
		  (> k 1)
		  (> k2 1)
		  (exactp x (1- k)))
	     (= (- x (sticky x k))
		(sticky 0 k2)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable sticky)
          :use ((:instance sticky-0 (n k2)))))))

(defthm minus-sticky
    (implies (and (rationalp x)
		  (> x 0)
		  (rationalp y)
		  (> y 0)
		  (integerp k)
		  (= k1 (+ k (- (expo x) (expo y))))
		  (= k2 (+ k (- (expo (- x y)) (expo y))))
		  (> k 1)
		  (> k1 1)
		  (> k2 1)
		  (exactp x (1- k1)))
	     (= (- x (sticky y k))
		(sticky (- x y) k2)))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable sticky)
		  :use ((:instance minus-sticky-7)
			(:instance minus-sticky-6)))))

(local (defthm sticky-lemma-1
    (implies (and (rationalp x)
		  (> x 0)
		  (rationalp y)
		  (< y 0)
		  (integerp k)
		  (= k1 (+ k (- (expo x) (expo y))))
		  (= k2 (+ k (- (expo (+ x y)) (expo y))))
		  (> k 1)
		  (> k1 1)
		  (> k2 1)
		  (exactp x (1- k1)))
	     (= (+ x (sticky y k))
		(sticky (+ x y) k2)))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable sticky)
		  :use ((:instance minus-sticky (y (- y)))
			(:instance expo-minus (x y))
			(:instance sticky-minus (x y) (n k)))))))

(local (defthm sticky-lemma-2
    (implies (and (rationalp x)
		  (> x 0)
		  (rationalp y)
		  (= y 0)
		  (integerp k)
		  (= k1 (+ k (- (expo x) (expo y))))
		  (= k2 (+ k (- (expo (+ x y)) (expo y))))
		  (> k 1)
		  (> k1 1)
		  (> k2 1)
		  (exactp x (1- k1)))
	     (= (+ x (sticky y k))
		(sticky (+ x y) k2)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable sticky)
           :use ((:instance sticky-0 (n k)))))))


(defthm STICKY-LEMMA
    (implies (and (rationalp x)
		  (> x 0)
		  (rationalp y)
		  (integerp k)
		  (= k1 (+ k (- (expo x) (expo y))))
		  (= k2 (+ k (- (expo (+ x y)) (expo y))))
		  (> k 1)
		  (> k1 1)
		  (> k2 1)
		  (exactp x (1- k1)))
	     (= (+ x (sticky y k))
		(sticky (+ x y) k2)))
  :rule-classes ()
  :hints (("Goal" :use (sticky-plus-original sticky-lemma-1 sticky-lemma-2
                                    (:instance
                                     trunc-0
                                     (n (+ -1 K (* -1 (EXPO Y)))))))))


;from add3
(local
 (defthm sticky-sticky-1
   (implies (and (rationalp x)
;                 (> x 0)
                 (integerp m)
                 (> m 1)
                 (integerp n)
                 (>= n m)
                 (exactp x (1- n)))
            (= (sticky (sticky x n) m)
               (sticky x m)))
   :rule-classes ()
   :hints (("goal" :use ((:instance sticky))))))

(local
 (defthm sticky-sticky-2
   (implies (and (rationalp x)
;                 (> x 0)
                 (integerp m)
                 (> m 1)
                 (integerp n)
                 (>= n m)
                 (not (exactp x (1- n))))
            (not (exactp x (1- m))))
   :rule-classes ()
   :hints (("goal" :use ((:instance exactp-<= (m (1- m)) (n (1- n))))))))

(local
 (defthm sticky-sticky-3
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp m)
		  (> m 1)
		  (integerp n)
		  (>= n m)
		  (not (exactp x (1- n))))
	     (not (exactp (sticky x n) (1- m))))
  :rule-classes ()
  :hints (("goal" :use (sticky-exactp-n-1
			(:instance exactp-<= (x (sticky x n)) (m (1- m)) (n (1- n))))))))

(local
 (defthm sticky-sticky-4
   (implies (and (rationalp x)
                 (> x 0)
                 (integerp m)
                 (> m 1)
                 (integerp n)
                 (>= n m)
                 (not (exactp x (1- n))))
            (= (sticky (sticky x n) m)
               (+ (trunc (sticky x n) (1- m))
                  (expt 2 (1+ (- (expo x) m))))))
   :rule-classes ()
   :hints (("goal" :in-theory (enable sgn)
            :use (expo-sticky
                  sticky-pos
                  sticky-sticky-3
                  (:instance sticky (x (sticky x n)) (n m)))))))

(local
 (defthm sticky-sticky-5
   (implies (and (rationalp x)
                 (> x 0)
                 (integerp m)
                 (> m 1)
                 (integerp n)
                 (>= n m)
                 (not (exactp x (1- n))))
            (= (sticky (sticky x n) m)
               (+ (trunc x (1- m))
                  (expt 2 (1+ (- (expo x) m))))))
   :rule-classes ()
   :hints (("goal" :in-theory (enable sgn)
            :use (sticky-sticky-4
                  (:instance trunc-sticky (m (1- m))))))))

(local
 (defthm sticky-sticky-6
   (implies (and (rationalp x)
                 (> x 0)
                 (integerp m)
                 (> m 1)
                 (integerp n)
                 (>= n m)
                 (not (exactp x (1- n))))
            (= (sticky (sticky x n) m)
               (sticky x m)))
   :rule-classes ()
   :hints (("goal" :in-theory (enable sgn)
            :use (sticky-sticky-5
                  sticky-sticky-2
                  (:instance trunc-0 (n (+ -1 m)))
                  (:instance sticky (n m)))))))

(local
 (defthm sticky-sticky-old
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp m)
		  (> m 1)
		  (integerp n)
		  (>= n m))
	     (= (sticky (sticky x n) m)
		(sticky x m)))
  :rule-classes ()
  :hints (("goal" :use (sticky-sticky-6
			sticky-sticky-1)))))

(defthm sticky-sticky
  (implies (and (rationalp x)
                (integerp m)
                (> m 1)
                (integerp n)
                (>= n m))
           (= (sticky (sticky x n) m)
              (sticky x m)))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable sticky)
           :use ((:instance sticky-sticky-old)
                 (:instance sticky-sticky-old (x (- x)))))))

(local (defthm sticky-exactp-m-1
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp m)
		  (integerp n)
		  (> n m)
		  (> m 0))
	     (iff (exactp (sticky x n) m)
		  (exactp x m)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable sticky-minus)
                  :use (sticky-exactp-n-1
			sticky
			(:instance exactp-<= (n (1- n)))
			(:instance exactp-<= (n (1- n)) (x (sticky x n))))))))

;;One for the library:

(defthm sticky-exactp-m
    (implies (and (rationalp x)
		  (integerp m)
		  (integerp n)
		  (> n m)
		  (> m 0))
	     (iff (exactp (sticky x n) m)
		  (exactp x m)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable sticky-minus)
                  :use (sticky-exactp-m-1
                        (:instance sticky-exactp-m-1 (x (- x)))
;                        (:instance exactp- (n m))
 ;                       (:instance exactp- (x (- x)) (n m))
  ;                      (:instance exactp- (x (sticky x n)) (n m))
   ;                     (:instance exactp- (x (- (sticky x n))) (n m))
                        ))))




