(in-package "ACL2")

(local (include-book "near+-proofs"))

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

(defthm near+trunc
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0))
	     (= (near+ x n)
		(trunc (+ x (expt 2 (- (expo x) n))) n)))
  :rule-classes ())

;why disabled?
(defthmd near+-minus
  (= (near+ (* -1 x) n)
     (* -1 (near+ x n))))

;why disabled?
(defthmd near+-shift
    (implies (and (rationalp x)
		  (integerp n)
		  (integerp k))
	     (= (near+ (* x (expt 2 k)) n)
		(* (near+ x n) (expt 2 k)))))


;bad name!
(defthm sgn-near+
  (implies (and (rationalp x)
                (integerp n)
                (> n 0))
           (= (near+ x n)
              (* (sgn x) (near+ (abs x) n))))
  :rule-classes ())

(defthm near+-0
  (equal (near+ 0 n)
         0))

;delete?
(defthm near+-1-1
  (implies (and (rationalp x)
                (>= x 0)
                (integerp n)
                (> n 0))
           (= (- x (trunc x n))
              (* (expt 2 (- (1+ (expo x)) n)) (re (* (expt 2 (1- n)) (sig x))))))
  :rule-classes ())

;delete?
(defthm near+-1-3
  (implies (and (rationalp x)
                (>= x 0)
                (integerp n)
                (> n 0)
                (not (integerp (* (expt 2 (1- n)) (sig x)))))
           (= (- (away x n) x)
              (* (expt 2 (- (1+ (expo x)) n)) (- 1 (re (* (expt 2 (1- n)) (sig x)))))))
  :rule-classes ())

(defthm near+1-a
    (implies (and (rationalp x)
		  (>= x 0)
		  (integerp n)
		  (> n 0)
		  (< (- x (trunc x n)) (- (away x n) x)))
	     (= (near+ x n) (trunc x n)))
  :rule-classes ())

(defthm near+1-b
    (implies (and (rationalp x)
		  (>= x 0)
		  (integerp n)
		  (> n 0)
		  (> (- x (trunc x n)) (- (away x n) x)))
	     (= (near+ x n) (away x n)))
  :rule-classes ())

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
  :rule-classes ())

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
  :rule-classes ())

(defthm near+-choice
  (or (= (near+ x n) (trunc x n))
      (= (near+ x n) (away x n)))
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
  :rule-classes ())

(defthm near+-exactp-b
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (exactp (near+ x n) n)))

(defthm sgn-near+-2
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (equal (sgn (near+ x n))
		    (sgn x))))

(defthm near+-exactp-a
    (implies (and (rationalp x)
		  (integerp n)
		  (> n 0))
	     (iff (= x (near+ x n))
		  (exactp x n)))
  :rule-classes ())



(defthm near+-exactp-c
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0)
		  (rationalp a)
		  (exactp a n)
		  (>= a x))
	     (>= a (near+ x n))))

(defthm near+-exactp-d
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0)
		  (rationalp a)
		  (exactp a n)
		  (<= a x))
	     (<= a (near+ x n))))

(defthm near+-pos
  (implies (and (rationalp x)
                (> x 0)
                (integerp n)
                (> n 0))
           (> (near+ x n) 0))
  :rule-classes :linear)

(defthm near+-monotone
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

(defthm near+<=away
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0))
	     (<= (near+ x n) (away x n)))
  :rule-classes ())

(defthm near+>=trunc
  (implies (and (rationalp x)
                (> x 0)
                (integerp n)
                (> n 0))
           (>= (near+ x n) (trunc x n)))
  :rule-classes ())


(defthm near+-neg
    (implies (and (< x 0)
                  (rationalp x)
		  (integerp n)
		  (> n 0))
	     (< (near+ x n) 0))
  :rule-classes :linear)

(defthm near+-0-0
  (implies (and (case-split (< 0 n))
                (case-split (rationalp x))
                (case-split (integerp n))
                )
           (equal (equal (near+ x n) 0)
                  (equal x 0)))
  :rule-classes ())

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
  :rule-classes ())

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
  :rule-classes ())

(defthm near+-a-a
    (implies (and (rationalp x) (> x 0)
		  (rationalp a) (> a 0)
		  (integerp n) (> n 0)
		  (exactp a n)
		  (> x (+ a (expt 2 (- (expo a) n)))))
	     (>= (near+ x n) (+ a (expt 2 (- (1+ (expo a)) n)))))
  :rule-classes ())



(defthm near+-a-b
    (implies (and (rationalp x) (> x 0)
		  (rationalp a) (> a 0)
		  (integerp n) (> n 0)
		  (exactp a n)
		  (< x (+ a (expt 2 (- (expo a) n)))))
	     (<= (near+ x n) a))
  :rule-classes ())

(defthm near+-a-c
    (implies (and (rationalp x) (> x 0)
		  (rationalp a) (> a 0)
		  (integerp n) (> n 0)
		  (exactp a n)
		  (< x a)
		  (> x (- a (expt 2 (- (expo x) n)))))
	     (>= (near+ x n) a))
  :rule-classes ())

(defthm near+-est
    (implies (and (integerp n) (> n 0)
		  (rationalp x) (> x 0))
	     (<= (abs (- x (near+ x n)))
		 (expt 2 (- (expo x) n))))
  :rule-classes ())

(defthm near+-power
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1)
		  (>= (+ x (expt 2 (- (expo x) n)))
		      (expt 2 (1+ (expo x)))))
	     (= (near+ x n)
		(expt 2 (1+ (expo x)))))
  :rule-classes ())


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
  :rule-classes nil)

;BOZO clean cruft from this book
