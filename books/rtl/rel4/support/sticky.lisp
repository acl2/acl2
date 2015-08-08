(in-package "ACL2")

;;;***************************************************************
;;;an acl2 library of floating point arithmetic
;;;david m. russinoff
;;;advanced micro devices, inc.
;;;february, 1998
;;;***************************************************************

(local (include-book "sticky-proofs"))

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
                  (* (sgn x) (expt 2 (expo x))))))

;more rule-classes?
(defthm sticky-pos
    (implies (and (< 0 x)
                  (rationalp x)
		  (integerp n) (> n 0))
	     (< 0 (sticky x n)))
  :rule-classes :linear)

(defthm sticky-shift
    (implies (and (rationalp x)
		  (integerp n) (> n 0)
		  (integerp k))
	     (= (sticky (* (expt 2 k) x) n)
		(* (expt 2 k) (sticky x n))))
  :rule-classes ())

(defthm sticky-minus
  (equal (sticky (* -1 x) n)
         (* -1 (sticky x n))))

;gen?
(defthm sticky-exactp
  (implies (and (rationalp x) (>= x 0)
                (integerp n) (> n 0)
                )
           (exactp (sticky x n) n))
  :rule-classes ())

(defthm sticky-exactp-n-1
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 1))
	     (iff (exactp (sticky x n) (1- n))
		  (exactp x (1- n))))
  :rule-classes ())

(defthm expo-sticky
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 0))
	     (= (expo (sticky x n))
		(expo x)))
  :rule-classes ())

(defthm trunc-sticky
    (implies (and (rationalp x) (> x 0)
		  (integerp m) (> m 0)
		  (integerp n) (> n m))
	     (= (trunc (sticky x n) m)
		(trunc x m)))
  :rule-classes ())

(defthm away-sticky
    (implies (and (rationalp x) (> x 0)
		  (integerp m) (> m 0)
		  (integerp n) (> n m))
	     (= (away (sticky x n) m)
		(away x m)))
  :rule-classes ())

(defthm near-sticky
    (implies (and (rationalp x) (> x 0)
		  (integerp m) (> m 0)
		  (integerp n) (> n (1+ m)))
	     (= (near (sticky x n) m)
		(near x m)))
  :rule-classes ())

(defthm near+-sticky
    (implies (and (rationalp x) (> x 0)
		  (integerp m) (> m 0)
		  (integerp n) (> n (1+ m)))
	     (= (near+ (sticky x n) m)
		(near+ x m)))
  :rule-classes ())

;make local?
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
  :rule-classes ())

;make local?
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
  :rule-classes ())

(defthm sticky-plus
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
  :rule-classes ())

;BOZO move?
(defthm trunc-away
    (implies (and (rationalp x) (> x 0)
		  (integerp n) (> n 0)
		  (not (exactp x n)))
	     (= (away x n)
		(+ (trunc x n)
		   (expt 2 (+ (expo x) 1 (- n))))))
  :rule-classes ())

(defthm sticky-0
  (equal (sticky 0 n)
         0))

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
  :rule-classes ())

(defthm sticky-lemma
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
  :rule-classes ())

(defthm sticky-sticky
  (implies (and (rationalp x)
                (integerp m)
                (> m 1)
                (integerp n)
                (>= n m))
           (= (sticky (sticky x n) m)
              (sticky x m)))
  :rule-classes ())

(defthm sticky-exactp-m
    (implies (and (rationalp x)
		  (integerp m)
		  (integerp n)
		  (> n m)
		  (> m 0))
	     (iff (exactp (sticky x n) m)
		  (exactp x m)))
  :rule-classes ())




