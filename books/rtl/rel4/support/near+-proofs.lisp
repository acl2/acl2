(in-package "ACL2")

(local (include-book "trunc"))
(local (include-book "away"))
(local (include-book "float"))
;BOZO include all of arithmetic?
;(local (include-book "../arithmetic/top"))
(local (include-book "../arithmetic/predicate"))
(local (include-book "../arithmetic/cg"))

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


;;
;; New stuff:
;;

(defund re (x)
  (- x (fl x)))

(defund near+ (x n)
  (if (< (re (* (expt 2 (1- n)) (sig x)))
	 1/2)
      (trunc x n)
    (away x n)))

(local
 (defthm near+trunc-1
   (implies (and (rationalp x)
                 (> x 0)
                 (integerp n)
                 (> n 0)
                 (< (re (* (expt 2 (1- n)) (sig x))) 1/2))
            (< (+ x (expt 2 (- (expo x) n)))
               (+ (trunc x n) (expt 2 (- (1+ (expo x)) n)))))
   :rule-classes ()
   :hints (("Goal" :in-theory (enable sgn trunc near+ re)
            :use (fp-rep
                  (:instance expt-split (r 2) (i (1- n)) (j (- (1+ (expo x)) n)))
                  (:instance expt-split (r 2) (i -1) (j (- (1+ (expo x)) n)))
                  (:instance *-strongly-monotonic
                             (x (expt 2 (- (1+ (expo x)) n)))
                             (y (re (* (expt 2 (1- n)) (sig x))))
                             (y+ 1/2)))))))

(local
 (defthm near+trunc-2
   (implies (and (rationalp x)
                 (> x 0)
                 (integerp n)
                 (> n 0)
                 (< (re (* (expt 2 (1- n)) (sig x))) 1/2))
            (< (trunc (+ x (expt 2 (- (expo x) n))) n)
               (+ (trunc x n) (expt 2 (- (1+ (expo x)) n)))))
   :rule-classes ()
   :hints (("Goal" :in-theory (disable re)
            :use (near+trunc-1
                  (:instance trunc-upper-pos (x (+ x (expt 2 (- (expo x) n)))))
;			(:instance expt-pos (x (- (expo x) n)))
                  )))))

(local
(defthm near+trunc-3
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0)
		  (< (re (* (expt 2 (1- n)) (sig x))) 1/2))
	     (<= (trunc (+ x (expt 2 (- (expo x) n))) n)
		(trunc x n)))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable re)
		  :use (near+trunc-2
			(:instance fp+1 (x (trunc x n)) (y (trunc (+ x (expt 2 (- (expo x) n))) n))))))))

(local
(defthm near+trunc-4
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0))
	     (>= (trunc (+ x (expt 2 (- (expo x) n))) n)
		(trunc x n)))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable re)
		  :use ((:instance trunc-monotone (y (+ x (expt 2 (- (expo x) n)))))
;			(:instance expt-pos (x (- (expo x) n)))
                        )))))

(local
 (defthm near+trunc-5
   (implies (and (rationalp x)
                 (> x 0)
                 (integerp n)
                 (> n 0)
                 (< (re (* (expt 2 (1- n)) (sig x))) 1/2))
            (= (near+ x n)
               (trunc (+ x (expt 2 (- (expo x) n))) n)))
   :rule-classes ()
   :hints (("Goal" :in-theory (enable trunc-rewrite near+)
            :use (near+trunc-3
                  near+trunc-4)))))

(local
 (defthm near+trunc-6
   (implies (and (rationalp x)
                 (> x 0)
                 (integerp n)
                 (> n 0)
                 (>= (re (* (expt 2 (1- n)) (sig x))) 1/2))
            (>= (+ x (expt 2 (- (expo x) n)))
                (+ (trunc x n) (expt 2 (- (1+ (expo x)) n)))))
   :rule-classes ()
   :hints (("Goal" :in-theory (enable sgn trunc near+ re)
            :use (fp-rep
                  (:instance expt-split (r 2) (i (1- n)) (j (- (1+ (expo x)) n)))
                  (:instance expt-split (r 2) (i -1) (j (- (1+ (expo x)) n)))
                  (:instance *-weakly-monotonic
                             (x (expt 2 (- (1+ (expo x)) n)))
                             (y+ (re (* (expt 2 (1- n)) (sig x))))
                             (y 1/2)))))))

(local
(defthm near+trunc-7
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0))
	     (>= (+ (trunc x n) (expt 2 (- (1+ (expo x)) n)))
		 (away x n)))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable trunc-exactp-c re)
		  :use ((:instance fp+2 (x (trunc x n)))
;			(:instance expt-pos (x (- (1+ (expo x)) n)))
			(:instance trunc-exactp-c (a (+ (trunc x n) (expt 2 (- (1+ (expo x)) n)))))
			(:instance away-exactp-c (a (+ (trunc x n) (expt 2 (- (1+ (expo x)) n))))))))))

(local
(defthm near+trunc-8
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0)
		  (>= (re (* (expt 2 (1- n)) (sig x))) 1/2))
	     (>= (+ x (expt 2 (- (expo x) n)))
		 (away x n)))
  :rule-classes ()
  :hints (("Goal" :use (near+trunc-7 near+trunc-6)))))

(local
(defthm near+trunc-9
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0)
		  (>= (re (* (expt 2 (1- n)) (sig x))) 1/2))
	     (>= (trunc (+ x (expt 2 (- (expo x) n))) n)
		 (away x n)))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable trunc-exactp-c re)
		  :use (near+trunc-8
			(:instance trunc-exactp-c (x (+ x (expt 2 (- (expo x) n)))) (a (away x n))))))))

(local
(defthm near+trunc-10
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0))
	     (< (trunc (+ x (expt 2 (- (expo x) n))) n)
		(fp+ (away x n) n)))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable trunc-exactp-c re)
		  :use (expo-away
;			(:instance expt-pos (x (- (expo x) n)))
			(:instance expt-strong-monotone (n (- (expo x) n)) (m (- (1+ (expo (away x n))) n))))))))

(local
(defthm near+trunc-11
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0))
	     (<= (trunc (+ x (expt 2 (- (expo x) n))) n)
		 (away x n)))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable trunc-exactp-c re)
		  :use (near+trunc-10
			(:instance fp+1 (x (away x n)) (y (trunc (+ x (expt 2 (- (expo x) n))) n))))))))

(local
 (defthm near+trunc-12
   (implies (and (rationalp x)
                 (> x 0)
                 (integerp n)
                 (> n 0)
                 (>= (re (* (expt 2 (1- n)) (sig x))) 1/2))
            (= (trunc (+ x (expt 2 (- (expo x) n))) n)
               (near+ x n)))
   :rule-classes ()
   :hints (("Goal" :in-theory (enable  near+)
            :use (near+trunc-11 near+trunc-9)))))

(defthm near+trunc
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0))
	     (= (near+ x n)
		(trunc (+ x (expt 2 (- (expo x) n))) n)))
  :rule-classes ()
  :hints (("Goal" :use (near+trunc-12 near+trunc-5))))

;why disabled?
(defthmd near+-minus
  (= (near+ (* -1 x) n)
     (* -1 (near+ x n)))
  :hints (("goal" :in-theory (enable near+)
           :use (trunc-minus
                 away-minus
                 sig-minus))))

;why disabled?
(defthmd near+-shift
    (implies (and (rationalp x)
		  (integerp n)
		  (integerp k))
	     (= (near+ (* x (expt 2 k)) n)
		(* (near+ x n) (expt 2 k))))
  :hints (("goal" :in-theory (enable near+)
		  :use (trunc-shift
			away-shift
			(:instance sig-expo-shift (n k))))))

(local
 (defthm sgn-near+-1
   (implies (and (rationalp x)
                 (integerp n)
                 (> n 0))
            (= (trunc x n)
               (* (sgn x) (trunc (abs x) n))))
   :rule-classes ()
   :hints (("goal" :in-theory (enable trunc sig)
            :use (sig-minus expo-minus)))))

(local
 (defthm sgn-near+-2-local
   (implies (and (rationalp x)
                 (integerp n)
                 (> n 0))
            (= (away x n)
               (* (sgn x) (away (abs x) n))))
   :rule-classes ()
   :hints (("goal" :in-theory (enable away sig)
            :use (sig-minus expo-minus)))))

;bad name!
(defthm sgn-near+
  (implies (and (rationalp x)
                (integerp n)
                (> n 0))
           (= (near+ x n)
              (* (sgn x) (near+ (abs x) n))))
  :rule-classes ()
  :hints (("goal" :in-theory (set-difference-theories
                              (enable near+)
                              '(sgn-away abs-pos  sig))
           :use (sgn-near+-2-local sgn-near+-1 sig-minus away-minus))))

(defthm near+-0
  (equal (near+ 0 n) 0)
  :hints (("Goal" :in-theory (enable near+)
           :use trunc-0)))

(defthm near+-1-1
  (implies (and (rationalp x)
                (>= x 0)
                (integerp n)
                (> n 0))
           (= (- x (trunc x n))
              (* (expt 2 (- (1+ (expo x)) n)) (re (* (expt 2 (1- n)) (sig x))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable re a15)
           :use ((:instance trunc)
                 (:instance fp-rep)))))

(defthm near+-1-2
  (implies (and (rationalp c)
                (rationalp f)
                (rationalp p)
                (= c (+ 1 f)))
           (= (* c p) (+ p (* f p))))
  :rule-classes ())

(defthm near+-1-3
  (implies (and (rationalp x)
                (>= x 0)
                (integerp n)
                (> n 0)
                (not (integerp (* (expt 2 (1- n)) (sig x)))))
           (= (- (away x n) x)
              (* (expt 2 (- (1+ (expo x)) n)) (- 1 (re (* (expt 2 (1- n)) (sig x)))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable re a15)
           :use ((:instance away)
                 (:instance fl-cg (x (* (expt 2 (1- n)) (sig x))))
                 (:instance fp-rep)
                 (:instance near+-1-2
                            (c (cg (* (expt 2 (1- n)) (sig x))))
                            (f (fl (* (expt 2 (1- n)) (sig x))))
                            (p (expt 2 (- (1+ (expo x)) n))))))))

(defthm near+-1-4
  (implies (and (rationalp x)
                (>= x 0)
                (integerp n)
                (> n 0)
                (integerp (* (expt 2 (1- n)) (sig x))))
           (= (trunc x n) x))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable a15)
           :use ((:instance trunc)
                 (:instance fl-int (x (* (expt 2 (1- n)) (sig x))))
                 (:instance fp-rep)))))

(defthm near+-1-5
  (implies (and (rationalp x)
                (>= x 0)
                (integerp n)
                (> n 0)
                (integerp (* (expt 2 (1- n)) (sig x))))
           (= (away x n) x))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable a15)
           :use ((:instance away)
                 (:instance cg-int (x (* (expt 2 (1- n)) (sig x))))
                 (:instance fp-rep)))))
;drop?
(defthm near+-1-6
  (implies (and (rationalp p)
                (> p 0)
                (rationalp f)
                (< (* p f) (* p (- 1 f))))
           (< f 1/2))
  :hints (("Goal" :in-theory (disable LESS-THAN-MULTIPLY-THROUGH-BY-inverted-factor-FROM-RIGHT-HAND-SIDE
                                      )))
  :rule-classes ())

(defthm near+-1-7
  (implies (and (rationalp x)
                (>= x 0)
                (integerp n)
                (> n 0)
                (not (integerp (* (expt 2 (1- n)) (sig x))))
                (< (- x (trunc x n)) (- (away x n) x)))
           (= (near+ x n) (trunc x n)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance near+-1-1)
			(:instance near+-1-3)
			(:instance near+-1-6
				   (p (expt 2 (- (1+ (expo x)) n)))
				   (f (re (* (expt 2 (1- n)) (sig x)))))
			(:instance near+)))))
;drop?
(defthm near+-1-8
  (implies (and (rationalp p)
                (> p 0)
                (rationalp f)
                (> (* p f) (* p (- 1 f))))
           (> f 1/2))
  :hints (("Goal" :in-theory (disable LESS-THAN-MULTIPLY-THROUGH-BY-inverted-factor-FROM-LEFT-HAND-SIDE
                                      )))
  :rule-classes ())

(defthm near+-1-9
    (implies (and (rationalp x)
		  (>= x 0)
		  (integerp n)
		  (> n 0)
		  (not (integerp (* (expt 2 (1- n)) (sig x))))
		  (> (- x (trunc x n)) (- (away x n) x)))
	     (= (near+ x n) (away x n)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance near+-1-1)
			(:instance near+-1-3)
			(:instance near+-1-8
				   (p (expt 2 (- (1+ (expo x)) n)))
				   (f (re (* (expt 2 (1- n)) (sig x)))))
			(:instance near+)))))

(defthm near+1-a
    (implies (and (rationalp x)
		  (>= x 0)
		  (integerp n)
		  (> n 0)
		  (< (- x (trunc x n)) (- (away x n) x)))
	     (= (near+ x n) (trunc x n)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance near+-1-7)
			(:instance near+-1-4)
			(:instance near+-1-5)))))

(defthm near+1-b
    (implies (and (rationalp x)
		  (>= x 0)
		  (integerp n)
		  (> n 0)
		  (> (- x (trunc x n)) (- (away x n) x)))
	     (= (near+ x n) (away x n)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance near+-1-9)
			(:instance near+-1-4)
			(:instance near+-1-5)))))

(defthm near+2-1
    (implies (and (rationalp x)
		  (rationalp y)
		  (> x 0)
		  (> y 0)
		  (integerp n)
		  (> n 0)
		  (exactp y n)
		  (= (near+ x n) (trunc x n)))
	     (>= (abs (- x y)) (- x (trunc x n))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable away-exactp-c
				      near+ trunc-exactp-c)
		  :use ((:instance near+1-b)
			(:instance away-lower-pos)
			(:instance trunc-upper-pos)
			(:instance trunc-exactp-c (a y))
			(:instance away-exactp-c (a y))))))

(defthm near+2-2
    (implies (and (rationalp x)
		  (rationalp y)
		  (> x 0)
		  (> y 0)
		  (integerp n)
		  (> n 0)
		  (exactp y n)
		  (= (near+ x n) (away x n)))
	     (>= (abs (- x y)) (- (away x n) x)))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable away-exactp-c
				      trunc-exactp-c)
		  :use ((:instance near+1-a)
			(:instance away-lower-pos)
			(:instance trunc-upper-pos)
			(:instance trunc-exactp-c (a y))
			(:instance away-exactp-c (a y))))))

(defthm near+-choice
  (or (= (near+ x n) (trunc x n))
      (= (near+ x n) (away x n)))
  :hints (("Goal" :in-theory (enable near+)))
  :rule-classes ())

(defthm near+2
    (implies (and (rationalp x)
		  (rationalp y)
		  (> x 0)
		  (> y 0)
		  (integerp n)
		  (> n 0)
		  (exactp y n))
	     (>= (abs (- x y)) (abs (- x (near+ x n)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable near+)
		  :use ((:instance near+2-1)
			(:instance near+2-2)
			(:instance near+-choice)
			(:instance away-lower-pos)
			(:instance trunc-upper-pos)))))

(defthm near+-exactp-b
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (exactp (near+ x n) n))
  :hints (("Goal" :in-theory (disable near+ trunc-exactp-b away-exactp-b)
		  :use ((:instance near+-choice)
			(:instance trunc-exactp-b)
			(:instance away-exactp-b)))))

(defthm sgn-near+-2
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (equal (sgn (near+ x n))
		    (sgn x)))
  :hints (("Goal" :use (near+-choice
			sgn-trunc
			sgn-away))))

(defthm near+-exactp-a
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (iff (= x (near+ x n))
		  (exactp x n)))
  :rule-classes ()
  :hints (("Goal" :use (near+-choice
			trunc-exactp-a
			away-exactp-a))))



(defthm near+-exactp-c
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0)
		  (rationalp a)
		  (exactp a n)
		  (>= a x))
	     (>= a (near+ x n)))
  :hints (("Goal" :use (near+-choice
			away-exactp-c
			trunc-upper-pos))))

(defthm near+-exactp-d
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0)
		  (rationalp a)
		  (exactp a n)
		  (<= a x))
	     (<= a (near+ x n)))
  :hints (("Goal" :use (near+-choice
			away-lower-pos
			trunc-exactp-c))))

(defthm near+-pos
  (implies (and (rationalp x)
                (> x 0)
                (integerp n)
                (> n 0))
           (> (near+ x n) 0))
  :rule-classes :linear
  :hints (("Goal" :in-theory (disable near+)
           :use ((:instance near+-choice)
))))

(defthmd near+-monotone
  (implies (and (<= x y)
                (rationalp x)
                (rationalp y)
                (< 0 x)
                (integerp n)
                (> n 0))
           (<= (near+ x n) (near+ y n)))
  :hints (("Goal" :in-theory (disable near+ trunc-exactp-b away-exactp-b)
           :use ((:instance near+-pos)
                 (:instance near+-pos (x y))
                 (:instance near+2 (y (near+ y n)))
                 (:instance near+2 (x y) (y (near+ x n)))))))

(defund near+-witness (x y n)
  (if (= (expo x) (expo y))
      (/ (+ (near+ x n) (near+ y n)) 2)
    (expt 2 (expo y))))

(local
 (defthm near+-near+-1
    (implies (and (rationalp x)
		  (rationalp y)
		  (< 0 x)
		  (< x y)
		  (integerp n)
		  (> n 0)
		  (not (= (expo x) (expo y))))
	     (and (<= x (near+-witness x y n))
		  (<= (near+-witness x y n) y)
		  (exactp (near+-witness x y n) (1+ n))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable near+-witness)
		  :use ((:instance exactp-2**n (n (expo y)) (m (1+ n)))
			(:instance expo-upper-bound)
			(:instance expo-monotone)
			(:instance expt-weak-monotone (n (1+ (expo x))) (m (expo y)))
			(:instance expo-lower-bound (x y)))))))

(local
 (defthm near+-near+-2
    (implies (and (rationalp x)
		  (rationalp y)
		  (< 0 x)
		  (< x y)
		  (integerp n)
		  (> n 0)
		  (< (near+ x n) (near+ y n))
		  (= (expo x) (expo y)))
	     (and (<= x (near+-witness x y n))
		  (<= (near+-witness x y n) y)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable near+-witness)
		  :use ((:instance near+2 (y (near+ y n)))
			(:instance near+2 (x y) (y (near+ x n)))
			(:instance near+-pos)
			(:instance near+-pos (x y)))))))

(local
 (defthm near+-near+-3
    (implies (and (rationalp x)
		  (rationalp y)
		  (< 0 x)
		  (< x y)
		  (integerp n)
		  (> n 0)
		  (not (= (near+ x n) (near+ y n)))
		  (= (expo x) (expo y)))
	     (and (<= x (near+-witness x y n))
		  (<= (near+-witness x y n) y)))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable near+-monotone)
		  :use ((:instance near+-near+-2)
			(:instance near+-monotone))))))

(defthm near+<=away
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0))
	     (<= (near+ x n) (away x n)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance near+-choice)
			(:instance trunc-upper-pos)
			(:instance away-lower-pos)))))

(defthm near+>=trunc
  (implies (and (rationalp x)
                (> x 0)
                (integerp n)
                (> n 0))
           (>= (near+ x n) (trunc x n)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance near+-choice)
			(:instance trunc-upper-pos)
			(:instance away-lower-pos)))))
(local
 (defthm near+-near+-4
    (implies (and (rationalp x)
		  (rationalp y)
		  (< 0 x)
		  (< x y)
		  (integerp n)
		  (> n 0)
		  (< (near+ x n) (near+ y n))
		  (= (expo x) (expo y)))
	     (<= (expo (near+-witness x y n)) (expo y)))
  :rule-classes ()
  :hints (("Goal" :in-theory (e/d (near+-witness) ( abs-away away-lower-pos))
		  :use ((:instance near+<=away (x y))
			(:instance away-exactp-d (x y))
			(:instance near+-pos)
;			(:instance away-pos (x y))
			(:instance expo-upper-2 (x (near+-witness x y n)) (n (1+ (expo y)))))))))

(defthm near+-neg
    (implies (and (< x 0)
                  (rationalp x)
		  (integerp n)
		  (> n 0))
	     (< (near+ x n) 0))
  :rule-classes :linear
  :hints (("Goal" :in-theory (disable near+)
		  :use ((:instance near+-choice)
	))))

(defthm near+-0-0
  (implies (and (case-split (< 0 n))
                (case-split (rationalp x))
                (case-split (integerp n))
                )
           (equal (equal (near+ x n) 0)
                  (equal x 0)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable near+))))

(local
 (defthm near+-near+-5
    (implies (and (rationalp x)
		  (rationalp y)
		  (< 0 x)
		  (< x y)
		  (integerp n)
		  (> n 0)
		  (< (near+ x n) (near+ y n))
		  (= (expo x) (expo y)))
	     (integerp (* (near+ x n) (expt 2 (- (1- n) (expo y))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable near+ expo-trunc abs-trunc abs-away)
		  :use ((:instance exactp-<=-expo (e (expo y)) (x (near+ x n)))
			(:instance expo-monotone (x (trunc x n)) (y (near+ x n)))
			(:instance near+-0-0)
;			(:instance trunc-pos)
			(:instance near+-pos)
			(:instance expo-trunc)
;			(:instance trunc-0-0)
			(:instance near+>=trunc))))))

(local
 (defthm near+-near+-6
    (implies (and (rationalp x)
		  (rationalp y)
		  (< 0 x)
		  (< x y)
		  (integerp n)
		  (> n 0)
		  (< (near+ x n) (near+ y n))
		  (= (expo x) (expo y)))
	     (integerp (* (near+ y n) (expt 2 (- (1- n) (expo y))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable near+ expo-trunc abs-trunc abs-away)
		  :use ((:instance exactp-<=-expo (e (expo y)) (x (near+ y n)))
			(:instance expo-monotone (x (trunc x n)) (y (near+ y n)))
			(:instance near+-0-0)
			(:instance near+-monotone)
;			(:instance trunc-pos)
			(:instance near+-pos)
			(:instance expo-trunc)
;			(:instance trunc-0-0)
			(:instance near+>=trunc))))))

(local
 (defthm near+-near+-7
    (implies (and (rationalp x)
		  (rationalp y)
		  (integerp k))
	     (= (+ (* x (expt 2 (1- k)))
		   (* y (expt 2 (1- k))))
		(* (/ (+ x y) 2) (expt 2 k))))
    :hints (("Goal" :in-theory (enable expt)))
  :rule-classes ()))

(local
 (defthm near+-near+-8
    (implies (and (rationalp x)
		  (rationalp y)
		  (integerp k)
	          (integerp (* x (expt 2 (1- k))))
	          (integerp (* y (expt 2 (1- k)))))
	     (integerp (* (/ (+ x y) 2) (expt 2 k))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance near+-near+-7))))))

(local
 (defthm near+-near+-9
    (implies (and (rationalp x)
		  (rationalp y)
		  (< 0 x)
		  (< x y)
		  (integerp n)
		  (> n 0)
		  (< (near+ x n) (near+ y n))
		  (= (expo x) (expo y)))
	     (exactp (near+-witness x y n) (1+ n)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable near+-witness)
           :use ((:instance near+-near+-5)
			(:instance near+-near+-6)
			(:instance near+-near+-4)
			(:instance near+-near+-8 (x (near+ x n)) (y (near+ y n)) (k (- n (expo y))))
			(:instance exactp->=-expo (n (1+ n)) (e (expo y)) (x (near+-witness x y n))))))))

(defthm near+-near+-lemma
    (implies (and (rationalp x)
		  (rationalp y)
		  (< 0 x)
		  (< x y)
		  (integerp n)
		  (> n 0)
		  (not (= (near+ x n) (near+ y n))))
	     (and (<= x (near+-witness x y n))
		  (<= (near+-witness x y n) y)
		  (exactp (near+-witness x y n) (1+ n))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable near+ near+-monotone)
		  :use ((:instance near+-near+-2)
			(:instance near+-near+-1)
			(:instance near+-near+-9)
			(:instance near+-monotone)))))

(local
 (defthm near+-near+-10
    (implies (and (rationalp x)
		  (rationalp y)
		  (rationalp a)
		  (integerp n)
		  (integerp k)
		  (> k 0)
		  (>= n k)
		  (< 0 a)
		  (< a x)
		  (< 0 y)
		  (< x y)
		  (< y (fp+ a (1+ n)))
		  (exactp a (1+ n)))
	     (= (near+ y k) (near+ x k)))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable near+ near+-monotone)
		  :use ((:instance near+-near+-lemma (n k))
			(:instance exactp-<= (x (near+-witness x y k)) (m (1+ k)) (n (1+ n)))
			(:instance fp+1 (x a) (y (near+-witness x y k)) (n (1+ n))))))))

(defthm near+-near+
    (implies (and (rationalp x)
		  (rationalp y)
		  (rationalp a)
		  (integerp n)
		  (integerp k)
		  (> k 0)
		  (>= n k)
		  (< 0 a)
		  (< a x)
		  (< 0 y)
		  (< y (fp+ a (1+ n)))
		  (exactp a (1+ n)))
	     (<= (near+ y k) (near+ x k)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance near+-near+-10)
			(:instance near+-monotone (n k) (x y) (y x))))))

(local
(defthm near+-a-a-1
    (implies (and (rationalp x) (> x 0)
		  (rationalp a) (> a 0)
		  (integerp n) (> n 0)
		  (exactp a n)
		  (> (near+ x n) a))
	     (>= (near+ x n) (+ a (expt 2 (- (1+ (expo a)) n)))))
  :rule-classes ()
  :hints (("goal" :use ((:instance fp+1 (x a) (y (near+ x n)))
			;(:instance exactp-near+)
                        )))))

(local
(defthm near+-a-a-2
    (implies (and (rationalp x) (> x 0)
		  (rationalp a) (> a 0)
		  (rationalp d) (> d 0)
		  (integerp n) (> n 0)
		  (<= (near+ x n) a)
		  (> x (+ a d)))
	     (> (abs (- (near+ x n) x))
		(abs (- (+ a d d)
			x))))
  :rule-classes ()))

(local
(defthm near+-a-a-3
    (implies (and (rationalp x) (> x 0)
		  (rationalp a) (> a 0)
		  (integerp n) (> n 0)
		  (<= (near+ x n) a)
		  (> x (+ a (expt 2 (- (expo a) n)))))
	     (> (abs (- (near+ x n) x))
		(abs (- (+ a
			   (expt 2 (- (expo a) n))
			   (expt 2 (- (expo a) n)))
			x))))
  :rule-classes ()
  :hints (("goal" :in-theory (disable ;expt-pos
                              )
		  :use ((:instance near+-a-a-2 (d (expt 2 (- (expo a) n))))
;			(:instance expt-pos (x (- (expo a) n)))
                        )))))

(local
(defthm near+-a-a-4
    (implies (and (rationalp x) (> x 0)
		  (rationalp a) (> a 0)
		  (integerp n) (> n 0)
		  (<= (near+ x n) a)
		  (> x (+ a (expt 2 (- (expo a) n)))))
	     (> (abs (- (near+ x n) x))
		(abs (- (+ a (expt 2 (- (1+ (expo a)) n)))
			x))))
  :rule-classes ()
  :hints (("goal" :use ((:instance near+-a-a-3)
			(:instance expt-split (r 2) (i (- (expo a) n)) (j 1)))))))

(defthm near+-a-a
    (implies (and (rationalp x) (> x 0)
		  (rationalp a) (> a 0)
		  (integerp n) (> n 0)
		  (exactp a n)
		  (> x (+ a (expt 2 (- (expo a) n)))))
	     (>= (near+ x n) (+ a (expt 2 (- (1+ (expo a)) n)))))
  :rule-classes ()
  :hints (("goal" :in-theory (disable ;expt-pos
                              )
		  :use ((:instance near+2 (y (+ a (expt 2 (- (1+ (expo a)) n)))))
			(:instance near+-a-a-4)
			(:instance near+-a-a-1)
			(:instance fp+2 (x a))
;			(:instance expt-pos (x (- (1+ (expo a)) n)))
                        ))))

(local
(defthm near+-a-b-1
    (implies (and (rationalp x) (> x 0)
		  (rationalp a) (> a 0)
		  (rationalp d) (> d 0)
		  (integerp n) (> n 0)
		  (>= (near+ x n) (+ a d d))
		  (< x (+ a d)))
	     (> (abs (- (near+ x n) x))
		(abs (- a x))))
  :rule-classes ()))

(local
(defthm near+-a-b-2
    (implies (and (rationalp x) (> x 0)
		  (rationalp a) (> a 0)
		  (integerp n) (> n 0)
		  (>= (near+ x n)
		      (+ a
			 (expt 2 (- (expo a) n))
			 (expt 2 (- (expo a) n))))
		  (< x (+ a (expt 2 (- (expo a) n)))))
	     (> (abs (- (near+ x n) x))
		(abs (- a x))))
  :rule-classes ()
  :hints (("goal" :in-theory (disable ;expt-pos
                              )
		  :use ((:instance near+-a-b-1 (d (expt 2 (- (expo a) n))))
;			(:instance expt-pos (x (- (expo a) n)))
                        )))))

(local
(defthm near+-a-b-3
    (implies (and (rationalp x) (> x 0)
		  (rationalp a) (> a 0)
		  (integerp n) (> n 0)
		  (>= (near+ x n)
		      (+ a (expt 2 (- (1+ (expo a)) n))))
		  (< x (+ a (expt 2 (- (expo a) n)))))
	     (> (abs (- (near+ x n) x))
		(abs (- a x))))
  :rule-classes ()
  :hints (("goal" :use ((:instance near+-a-b-2)
			(:instance expt-split (r 2) (i (- (expo a) n)) (j 1)))))))

(defthm near+-a-b
    (implies (and (rationalp x) (> x 0)
		  (rationalp a) (> a 0)
		  (integerp n) (> n 0)
		  (exactp a n)
		  (< x (+ a (expt 2 (- (expo a) n)))))
	     (<= (near+ x n) a))
  :rule-classes ()
  :hints (("goal" :use ((:instance near+2 (y a))
			(:instance near+-a-b-3)
			(:instance near+-a-a-1)))))

(local
(defthm near+-a-c-1
    (implies (and (rationalp x) (> x 0)
		  (rationalp a) (> a 0)
		  (integerp n) (> n 0)
		  (exactp a n)
		  (>= x a))
	     (>= (near+ x n) a))
  :rule-classes ()
  :hints (("goal" :use ((:instance near+-monotone (x a) (y x))
			(:instance near+-choice (x a))
			(:instance trunc-exactp-a (x a))
			(:instance away-exactp-a (x a)))))))

(local
(defthm near+-a-c-2
    (implies (and (rationalp x) (> x 0)
		  (rationalp a) (> a 0)
		  (integerp n) (> n 0)
		  (exactp a n)
		  (< x a))
	     (>= a
		 (+ (expt 2 (expo x))
		    (expt 2 (- (1+ (expo x)) n)))))
  :rule-classes ()
  :hints (("goal" :use ((:instance expo-lower-bound)
			(:instance fp+1 (x (expt 2 (expo x))) (y a))
			(:instance exactp-2**n (n (expo x)) (m n)))))))

(local
(defthm near+-a-c-3
    (implies (and (rationalp x) (> x 0)
		  (rationalp a) (> a 0)
		  (integerp n) (> n 0)
		  (> x (- a (expt 2 (- (expo x) n)))))
	     (> x (- a (expt 2 (- (1+ (expo x)) n)))))
  :rule-classes ()
  :hints (("goal" :use ((:instance expt-weak-monotone (n (- (expo x) n)) (m (- (1+ (expo x)) n))))))))

(local
(defthm near+-a-c-4
    (implies (and (rationalp x) (> x 0)
		  (rationalp a) (> a 0)
		  (integerp n) (> n 0)
		  (exactp a n)
		  (< x a)
		  (> x (- a (expt 2 (- (expo x) n)))))
	     (= (expo (- a (expt 2 (- (1+ (expo x)) n))))
		(expo x)))
  :rule-classes ()
  :hints (("goal" :in-theory (disable ;expt-pos
                              )
		  :use ((:instance near+-a-c-2)
			(:instance near+-a-c-3)
;			(:instance expt-pos (x (expo x)))
			(:instance expo-upper-bound)
			(:instance expo-unique
				   (x (- a (expt 2 (- (1+ (expo x)) n))))
				   (n (expo x))))))))

(local
(defthm near+-a-c-5
    (implies (and (rationalp x) (> x 0)
		  (rationalp a) (> a 0)
		  (integerp n) (> n 0)
		  (exactp a n)
		  (< x a)
		  (> x (- a (expt 2 (- (expo x) n)))))
	     (integerp (* (- a (expt 2 (- (1+ (expo x)) n)))
			  (expt 2 (- (1- n) (expo x))))))
  :rule-classes ()
  :hints (("goal" :use ((:instance expt-split (r 2) (i (- (1+ (expo x)) n)) (j (- (1- n) (expo x))))
			(:instance exactp-<=-expo (x a) (e (expo x)))
			(:instance near+-a-c-3)
			(:instance expo-monotone (x (- a (expt 2 (- (1+ (expo x)) n)))) (y a))
			(:instance expo-monotone (y a)))))))

(local
(defthm near+-a-c-6
    (implies (and (rationalp x) (> x 0)
		  (rationalp a) (> a 0)
		  (integerp n) (> n 0)
		  (exactp a n)
		  (< x a)
		  (> x (- a (expt 2 (- (expo x) n)))))
	     (exactp (- a (expt 2 (- (1+ (expo x)) n)))
		     n))
  :rule-classes ()
  :hints (("goal" :in-theory (enable; expt ;expt-pos
                              )
		  :use ((:instance exactp2 (x (- a (expt 2 (- (1+ (expo x)) n)))))
			(:instance near+-a-c-5)
			(:instance near+-a-c-2)
;			(:instance expt-pos (x (expo x)))
			(:instance near+-a-c-4))))))

(local
(defthm near+-a-c-7
    (implies (and (rationalp x)
		  (rationalp a)
		  (rationalp e)
		  (> x (- a e)))
	     (> x (+ (- a (* 2 e))
		     e)))
  :rule-classes ()))

(local
(defthm near+-a-c-8
    (implies (and (rationalp x)
		  (rationalp a)
		  (integerp n)
		  (> x (- a (expt 2 (- (expo x) n)))))
	     (> x (+ (- a (expt 2 (- (1+ (expo x)) n)))
		     (expt 2 (- (expo x) n)))))
  :rule-classes ()
  :hints (("goal" :use ((:instance expt-split (r 2) (i 1) (j (- (expo x) n)))
			(:instance near+-a-c-7 (e (expt 2 (- (expo x) n)))))))))

(local
(defthm near+-a-c-9
    (implies (and (rationalp x) (> x 0)
		  (rationalp a) (> a 0)
		  (integerp n) (> n 0)
		  (exactp a n)
		  (< x a)
		  (> x (- a (expt 2 (- (expo x) n)))))
	     (> (- a (expt 2 (- (1+ (expo x)) n)))
		0))
  :rule-classes ()
  :hints (("goal" :in-theory (disable ;expt-pos
                              )
		  :use ((:instance near+-a-c-2)
;			(:instance expt-pos (x (expo x)))
                        )))))

(defthm near+-a-c
    (implies (and (rationalp x) (> x 0)
		  (rationalp a) (> a 0)
		  (integerp n) (> n 0)
		  (exactp a n)
		  (< x a)
		  (> x (- a (expt 2 (- (expo x) n)))))
	     (>= (near+ x n) a))
  :rule-classes ()
  :hints (("goal" :use ((:instance near+-a-a (a (- a (expt 2 (- (1+ (expo x)) n)))))
			(:instance near+-a-c-8)
			(:instance near+-a-c-6)
			(:instance near+-a-c-4)
			(:instance near+-a-c-9)))))

(local
 (defthm near+-exact-1
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 0)
		  (not (exactp x n)))
	     (let ((f (re (* (expt 2 (1- n)) (sig x)))))
	       (and (< f 1) (< 0 f))))
  :rule-classes ()
  :hints (("goal" :in-theory (enable re)
           :use ((:instance fl-def-linear (x (* (expt 2 (1- n)) (sig x))))
			(:instance exactp))))))

(local
 (defthm near+-exact-2
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 0)
		  (exactp x (1+ n)))
	     (let ((f (re (* (expt 2 (1- n)) (sig x)))))
	       (integerp (* 2 f))))
  :rule-classes ()
  :hints (("goal" :in-theory (enable re expt)
           :use ((:instance exactp (n (1+ n))))))))

(local
 (defthm near+-exact-3
    (implies (and (integerp |2F|)
		  (< 0 |2F|)
		  (< |2F| 2))
	     (= |2F| 1))
  :rule-classes ()))

(local
 (defthm near+-exact-4
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 0)
		  (not (exactp x n))
		  (exactp x (1+ n)))
	     (= (re (* (expt 2 (1- n)) (sig x)))
		1/2))
  :rule-classes ()
  :hints (("goal" :use ((:instance near+-exact-1)
			(:instance near+-exact-2)
			(:instance near+-exact-3 (|2F| (* 2 (re (* (expt 2 (1- n)) (sig x)))))))))))

(local
 (defthm near+-exact-10
     (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 0)
		  (not (exactp x n))
		  (exactp x (1+ n)))
	     (= (near+ x n)
		(* (cg (* (expt 2 (1- n)) (sig x)))
		   (expt 2 (- (1+ (expo x)) n)))))
  :rule-classes ()
  :hints (("goal" :use ((:instance near+)
			(:instance near+-exact-4)
			(:instance away))))))

(local
 (defthm near+-exact-11
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 0)
		  (not (exactp x n))
		  (exactp x (1+ n)))
	     (= (near+ x n)
		(* (1+ (fl (* (expt 2 (1- n)) (sig x))))
		   (expt 2 (- (1+ (expo x)) n)))))
  :rule-classes ()
  :hints (("goal" :in-theory (enable near+ re)
           :use ((:instance near+-exact-10)
                 (:instance near+-exact-1)
                 (:instance fl-cg (x (* (expt 2 (1- n)) (sig x)))))))))

(local
 (defthm near+-exact-12
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 0)
		  (not (exactp x n))
		  (exactp x (1+ n)))
	     (= (* (expt 2 (- (- n 2) (expo x)))
		   (* (1+ (fl (* (expt 2 (1- n)) (sig x))))
		      (expt 2 (- (1+ (expo x)) n))))
		(/ (1+ (fl (* (expt 2 (1- n)) (sig x))))
		   2)))
  :rule-classes ()
  :hints (("goal" :in-theory (enable a15)
           :use ((:instance expt-split (r 2) (i (- (- n 2) (expo x))) (j (expt 2 (- (1+ (expo x)) n)))))))))

(local
 (defthm near+-exact-13
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 0)
		  (not (exactp x n))
		  (exactp x (1+ n)))
	     (= (* (expt 2 (- (- n 2) (expo x)))
		   (near+ x n))
		(/ (1+ (fl (* (expt 2 (1- n)) (sig x))))
		   2)))
  :rule-classes ()
  :hints (("goal" :use ((:instance near+-exact-11)
			(:instance near+-exact-12))))))

(local
(defthm near+-est-1
    (implies (and (integerp n) (> n 0)
		  (rationalp x) (> x 0)
		  (> (abs (- x (near+ x n)))
		     (expt 2 (- (expo x) n))))
	     (< (trunc x n)
		(- x (expt 2 (- (expo x) n)))))
  :rule-classes ()
  :hints (("goal" :use ((:instance near+2 (y (trunc x n)))
			(:instance trunc-exactp-b)
;			(:instance trunc-pos)
			(:instance trunc-upper-pos))))))

(local
(defthm near+-est-2
    (implies (and (integerp n) (> n 0)
		  (rationalp x) (> x 0)
		  (> (abs (- x (near+ x n)))
		     (expt 2 (- (expo x) n))))
	     (> (away x n)
		(+ x (expt 2 (- (expo x) n)))))
  :rule-classes ()
  :hints (("goal" :in-theory (disable near+-exactp-c)
           :use ((:instance near+2 (y (away x n)))
			(:instance away-exactp-b)
;			(:instance away-pos)
			(:instance away-lower-pos))))))

(local
(defthm near+-est-3
    (implies (and (integerp n) (> n 0)
		  (rationalp x) (> x 0)
		  (> (abs (- x (near+ x n)))
		     (expt 2 (- (expo x) n))))
	     (> (away x n)
		(+ (trunc x n) (expt 2 (- (1+ (expo x)) n)))))
  :rule-classes ()
  :hints (("goal" :in-theory (disable a15)
		  :use ((:instance near+-est-1)
			(:instance expt-split (r 2) (i (- (expo x) n)) (j 1))
			(:instance near+-est-2))))))

(local
(defthm near+-est-4
    (implies (and (integerp n) (> n 0)
		  (rationalp x) (> x 0)
		  (> (abs (- x (near+ x n)))
		     (expt 2 (- (expo x) n))))
	     (> x
		(+ (trunc x n) (expt 2 (- (1+ (expo x)) n)))))
  :rule-classes ()
  :hints (("goal" :use ((:instance near+-est-3)
			(:instance fp+2 (x (trunc x n)))
			(:instance trunc-exactp-b)
;			(:instance trunc-pos)
			(:instance expo-trunc)
			(:instance away-exactp-c (a (+ (trunc x n) (expt 2 (- (1+ (expo x)) n))))))))))


(defthm near+-est
    (implies (and (integerp n) (> n 0)
		  (rationalp x) (> x 0))
	     (<= (abs (- x (near+ x n)))
		 (expt 2 (- (expo x) n))))
  :rule-classes ()
  :hints (("goal" :use ((:instance near+-est-4)
			(:instance trunc-lower-1)
;			(:instance trunc-pos)
                        ))))

(local
(defthm near+-power-b-1
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1)
		  (>= (+ x (expt 2 (- (expo x) n)))
		      (expt 2 (1+ (expo x)))))
	     (>= (trunc (+ x (expt 2 (- (expo x) n))) n)
		 (expt 2 (1+ (expo x)))))
  :rule-classes ()
  :hints (("goal" :in-theory (disable ;expt-pos
                              )
		  :use ((:instance exactp-2**n (n (1+ (expo x))) (m n))
;			(:instance expt-pos (x (- (expo x) n)))
			(:instance trunc-exactp-c
				   (x (+ x (expt 2 (- (expo x) n))))
				   (a (expt 2 (1+ (expo x))))))))))

(local
(defthm near+-power-b-2
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1)
		  (>= (+ x (expt 2 (- (expo x) n)))
		      (expt 2 (1+ (expo x))))
		  (not (= (trunc (+ x (expt 2 (- (expo x) n))) n)
			  (expt 2 (1+ (expo x))))))
	     (> (trunc (+ x (expt 2 (- (expo x) n))) n)
		(expt 2 (1+ (expo x)))))
  :rule-classes ()
  :hints (("goal" :use ((:instance near+-power-b-1))))))

(local
(defthm near+-power-b-3
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1)
		  (>= (+ x (expt 2 (- (expo x) n)))
		      (expt 2 (1+ (expo x))))
		  (not (= (trunc (+ x (expt 2 (- (expo x) n))) n)
			  (expt 2 (1+ (expo x))))))
	     (>= (trunc (+ x (expt 2 (- (expo x) n))) n)
		 (+ (expt 2 (1+ (expo x)))
		    (expt 2 (- (+ 2 (expo x)) n)))))
  :rule-classes ()
  :hints (("goal" :in-theory (disable ;expt-pos
                              )
		  :use ((:instance near+-power-b-2)
			(:instance exactp-2**n (n (1+ (expo x))) (m n))
			(:instance trunc-exactp-b (x (+ x (expt 2 (- (expo x) n)))))
;			(:instance expt-pos (x (1+ (expo x))))
			(:instance expo-2**n (n (1+ (expo x))))
			(:instance fp+1
				   (x (expt 2 (1+ (expo x))))
				   (y (trunc (+ x (expt 2 (- (expo x) n))) n))))))))

(local
(defthm near+-power-b-4
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1)
		  (>= (+ x (expt 2 (- (expo x) n)))
		      (expt 2 (1+ (expo x))))
		  (not (= (trunc (+ x (expt 2 (- (expo x) n))) n)
			  (expt 2 (1+ (expo x))))))
	     (> (trunc (+ x (expt 2 (- (expo x) n))) n)
		(+ x (expt 2 (- (expo x) n)))))
  :rule-classes ()
  :hints (("goal" :use ((:instance near+-power-b-3)
			(:instance expo-upper-bound)
			(:instance expt-weak-monotone (n (- (expo x) n)) (m (- (+ 2 (expo x)) n))))))))

(defthm near+-power
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1)
		  (>= (+ x (expt 2 (- (expo x) n)))
		      (expt 2 (1+ (expo x)))))
	     (= (near+ x n)
		(expt 2 (1+ (expo x)))))
  :rule-classes ()
  :hints (("goal" :in-theory (disable ;expt-pos
                              )
		  :use (near+trunc
			(:instance near+-power-b-4)
			(:instance trunc-upper-pos (x (+ x (expt 2 (- (expo x) n)))))
;			(:instance expt-pos (x (- (expo x) n)))
                        ))))


(local (include-book "../arithmetic/top"))

; The next two lemmas are copied from near-proofs.lisp.

(defthm plus-near-1
  (implies (and (exactp x (+ k (- (expo x) (expo y))))
                (rationalp x)
                (>= x 0)
                (rationalp y)
                (>= y 0)
                (integerp k)
                )
           (= (re (* (expt 2 (1- k)) (sig y)))
              (re (* (expt 2 (1- (+ k (- (expo (+ x y)) (expo y)))))
                     (sig (+ x y))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable re sig exactp expt-split expt-minus))))

(defthm plus-near-2
  (implies (and (rationalp x)
                (>= x 0)
                (rationalp y)
                (>= y 0)
                (integerp k)
                (exactp x (+ -1 k (- (expo x) (expo y)))))
           (iff (evenp (fl (* (expt 2 (1- k)) (sig y))))
                (evenp (fl (* (expt 2
                                    (1- (+ k (- (expo (+ x y)) (expo y)))))
                              (sig (+ x y)))))))
  :otf-flg t
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (expt-split
                                   expt-minus
                                   exactp sig ; EXPT-SPLIT-leading-constant
                                   evenp ;this is sort of cheating...
                                   ) ())
           :use ((:instance exactp2 (n (+ k (expo x) (- (expo y)))))
                 (:instance exactp-<=
                            (m (+ -1 k (expo x) (- (expo y))))
                            (n (+ k (expo x) (- (expo y)))))))))

(defthm plus-near+
  (implies (and (rationalp x)
                (>= x 0)
                (rationalp y)
                (>= y 0)
                (integerp k)
                (exactp x (+ -1 k (- (expo x) (expo y)))))
           (= (+ x (near+ y k))
              (near+ (+ x y)
                     (+ k (- (expo (+ x y)) (expo y))))))
  :hints (("Goal" :in-theory (enable near+)
           :use (plus-trunc plus-away plus-near-1 plus-near-2
                            (:instance exactp-<=
                                       (m (+ -1 k (expo x) (* -1 (expo y))))
                                       (n (+ k (expo x) (* -1 (expo y))))))))
  :rule-classes nil)
