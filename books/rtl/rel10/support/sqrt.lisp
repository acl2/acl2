(in-package "ACL2")

(include-book "../../rel9/lib/util")

(local (encapsulate ()

(local (encapsulate ()

(local (include-book "../../rel9/lib/top"))
(local (include-book "../../rel9/lib/sqrt"))

;; From basic.lisp:

(defund fl (x)
  (declare (xargs :guard (real/rationalp x)))
  (floor x 1))

(defund cg (x)
  (declare (xargs :guard (real/rationalp x)))
  (- (fl (- x))))

;; From float.lisp:

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

(defund exactp (x n)
  (integerp (* (sig x) (expt 2 (1- n)))))

;; From round.lisp:

(defund rtz (x n)
  (declare (xargs :guard (integerp n)))
  (* (sgn x) 
     (fl (* (expt 2 (1- n)) (sig x))) 
     (expt 2 (- (1+ (expo x)) n))))

(defund raz (x n)
  (* (sgn x) 
     (cg (* (expt 2 (1- n)) (sig x))) 
     (expt 2 (- (1+ (expo x)) n))))

(defun re (x)
  (- x (fl x)))

(defund rne (x n)
  (let ((z (fl (* (expt 2 (1- n)) (sig x))))
	(f (re (* (expt 2 (1- n)) (sig x)))))
    (if (< f 1/2)
	(rtz x n)
      (if (> f 1/2)
	  (raz x n)
	(if (evenp z)
	    (rtz x n)
	  (raz x n))))))

(defund rto (x n)
  (if (exactp x (1- n))
      x
    (+ (rtz x (1- n))
       (* (sgn x) (expt 2 (1+ (- (expo x) n)))))))

(defund rup (x n)
  (if (>= x 0)
      (raz x n)
    (rtz x n)))

(defund rdn (x n)
  (if (>= x 0)
      (rtz x n)
    (raz x n)))

(defund rna (x n)
  (if (< (re (* (expt 2 (1- n)) (sig x)))
	 1/2)
      (rtz x n)
    (raz x n)))


(defund IEEE-rounding-mode-p (mode)
  (member mode '(rtz rup rdn rne)))

(defund common-mode-p (mode)
  (or (IEEE-rounding-mode-p mode) (equal mode 'raz) (equal mode 'rna)))

(defund fp-rnd (x mode n)
  (case mode
    (raz (raz x n))
    (rna (rna x n))
    (rtz (rtz x n))
    (rup (rup x n))
    (rdn (rdn x n))
    (rne (rne x n))
    (otherwise 0)))

;;-------------------------------------------------------------------------

(defund rtz (x n)
  (declare (xargs :guard (integerp n)))
  (* (sgn x) 
     (fl (* (expt 2 (1- n)) (sig x))) 
     (expt 2 (- (1+ (expo x)) n))))

(local-defthm rtz-trunc
  (equal (rtz x n) (trunc x n))
  :hints (("Goal" :in-theory (enable rtz trunc))))

(defund raz (x n)
  (* (sgn x) 
     (cg (* (expt 2 (1- n)) (sig x))) 
     (expt 2 (- (1+ (expo x)) n))))

(local-defthm raz-away
  (equal (raz x n) (away x n))
  :hints (("Goal" :in-theory (enable raz away))))

(defun re (x)
  (- x (fl x)))

(defund rne (x n)
  (let ((z (fl (* (expt 2 (1- n)) (sig x))))
	(f (re (* (expt 2 (1- n)) (sig x)))))
    (if (< f 1/2)
	(rtz x n)
      (if (> f 1/2)
	  (raz x n)
	(if (evenp z)
	    (rtz x n)
	  (raz x n))))))

(local-defthm rne-near
  (equal (rne x n) (near x n))
  :hints (("Goal" :in-theory (enable near rne))))

(defund rto (x n)
  (if (exactp x (1- n))
      x
    (+ (rtz x (1- n))
       (* (sgn x) (expt 2 (1+ (- (expo x) n)))))))

(local-defthm rto-sticky
  (equal (rto x n) (sticky x n))
  :hints (("Goal" :in-theory (enable rto sticky))))

(defun rup (x n)
  (if (>= x 0)
      (raz x n)
    (rtz x n)))

(local-defthm rup-inf
  (equal (rup x n) (inf x n))
  :hints (("Goal" :in-theory (enable rup inf))))

(defun rdn (x n)
  (if (>= x 0)
      (rtz x n)
    (raz x n)))

(local-defthm rdn-minf
  (equal (rdn x n) (minf x n))
  :hints (("Goal" :in-theory (enable rdn minf))))

(defund rna (x n)
  (if (< (re (* (expt 2 (1- n)) (sig x)))
	 1/2)
      (rtz x n)
    (raz x n)))

(local-defthm rna-near+
  (equal (rna x n) (near+ x n))
  :hints (("Goal" :in-theory (enable near+ rna))))

(defund IEEE-rounding-mode-p (mode)
  (member mode '(rtz rup rdn rne)))

(defun common-mode-p (mode)
  (or (IEEE-rounding-mode-p mode) (equal mode 'raz) (equal mode 'rna)))

(local-defund old-mode (mode)
  (case mode
    (raz 'away)
    (rna 'near+)
    (rtz 'trunc)
    (rup 'inf)
    (rdn 'minf)
    (rne 'near)
    (otherwise ())))

(local-defthm ieee-mode-rewrite
  (implies (ieee-rounding-mode-p mode)
           (ieee-mode-p (old-mode mode)))
  :hints (("Goal" :in-theory (enable IEEE-mode-p IEEE-rounding-mode-p old-mode))))

(local-defthm common-mode-rewrite
  (implies (common-mode-p mode)
           (common-rounding-mode-p (old-mode mode)))
  :hints (("Goal" :in-theory (enable IEEE-mode-p IEEE-rounding-mode-p common-mode-p common-rounding-mode-p old-mode))))

(defund fp-rnd (x mode n)
  (case mode
    (raz (raz x n))
    (rna (rna x n))
    (rtz (rtz x n))
    (rup (rup x n))
    (rdn (rdn x n))
    (rne (rne x n))
    (otherwise 0)))

(local-defthm fp-rnd-rnd
  (equal (fp-rnd x mode n) (rnd x (old-mode mode) n))
  :hints (("Goal" :in-theory (enable IEEE-rounding-mode-p common-mode-p fp-rnd old-mode rnd))))


;;;**********************************************************************
;;;		    	      RTZ-SQRT
;;;**********************************************************************

(defund rtz-sqrt (x n)
  (if (zp n)
      0
    (let* ((lower (rtz-sqrt x (1- n)))
           (upper (+ lower (expt 2 (- n)))))
      (if (<= (* upper upper) x)
          upper
        lower))))

(local-defthm rtz-trunc-sqrt
  (equal (rtz-sqrt x n) (trunc-sqrt x n))
  :hints (("Goal" :in-theory (enable trunc-sqrt rtz-sqrt))))

(defthm rtz-sqrt-bounds
  (implies (and (rationalp x)
                (<= 1/4 x)
                (not (zp n)))
           (and (<= 1/2 (rtz-sqrt x n))
                (<= (rtz-sqrt x n) (- 1 (expt 2 (- n))))))
  :rule-classes ()
  :hints (("Goal" :use trunc-sqrt-bounds)))
                                

(defthm expo-rtz-sqrt
  (implies (and (rationalp x)
                (<= 1/4 x)
                (not (zp n)))
           (equal (expo (rtz-sqrt x n))
                  -1))
  :hints (("Goal" :use expo-trunc-sqrt)))

(defthm exactp-rtz-sqrt
  (implies (and (rationalp x)
                (<= 1/4 x)
                (not (zp n)))
           (exactp (rtz-sqrt x n)
                   n))
  :rule-classes ()
  :hints (("Goal" :use exactp-trunc-sqrt)))

(defthmd rtz-rtz-sqrt
  (implies (and (rationalp x)
                (<= 1/4 x)
                (not (zp m))
                (natp n)
                (>= n m))
           (equal (rtz (rtz-sqrt x n) m)
                  (rtz-sqrt x m)))
  :hints (("Goal" :use trunc-trunc-sqrt)))

(defthm rtz-sqrt-square-bounds
  (implies (and (not (zp n))
                (rationalp x)
                (<= 1/4 x)
                (< x 1))                
           (and (<= (* (rtz-sqrt x n)
                       (rtz-sqrt x n))
                    x)
                (< x
                   (* (+ (rtz-sqrt x n) (expt 2 (- n)))
                      (+ (rtz-sqrt x n) (expt 2 (- n)))))))
  :rule-classes ()
  :hints (("Goal" :use trunc-sqrt-square-bounds)))

(defthm rtz-sqrt-unique
  (implies (and (not (zp n))
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (rationalp a)
                (exactp a n)
                (>= a 1/2)
                (<= (* a a) x)
                (< x (* (+ a (expt 2 (- n))) (+ a (expt 2 (- n))))))
           (= a (rtz-sqrt x n)))
  :rule-classes ()
  :hints (("Goal" :use trunc-sqrt-unique)))


;;;**********************************************************************
;;;		    	    RTO-SQRT-NORM
;;;**********************************************************************

(defund rto-sqrt-norm (x n)
  (let ((trunc (rtz-sqrt x (1- n))))
    (if (< (* trunc trunc) x)
        (+ trunc (expt 2 (- n)))
      trunc)))

(local-defthm rto-sticky-sqrt
  (equal (rto-sqrt-norm x n) (sticky-sqrt x n))
  :hints (("Goal" :in-theory (enable sticky-sqrt rto-sqrt-norm))))

(defthm rto-sqrt-norm-bounds
  (implies (and (rationalp x)
                (<= 1/4 x)
                (natp n)
                (>= n 2))
           (and (<= 1/2 (rto-sqrt-norm x n))
                (< (rto-sqrt-norm x n) 1)))
  :rule-classes ()
  :hints (("Goal" :use sticky-sqrt-bounds)))

(defthm expo-rto-sqrt-norm
  (implies (and (rationalp x)
                (<= 1/4 x)
                (natp n)
                (>= n 2))
           (equal (expo (rto-sqrt-norm x n))
                  -1))
  :hints (("Goal" :use expo-sticky-sqrt)))

(defthmd exactp-rto-sqrt-norm
  (implies (and (rationalp x)
                (<= 1/4 x)
                (natp n)
                (>= n 2))
           (exactp (rto-sqrt-norm x n) n))
  :hints (("Goal" :use exactp-sticky-sqrt)))

(defthm rto-sqrt-norm-lower
  (implies (and (natp n)
                (>= n 2)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (rationalp l)
                (<= (* l l) x))
           (<= (rto l n)
               (rto-sqrt-norm x n)))
  :rule-classes ()
  :hints (("Goal" :use sticky-sqrt-lower)))

#|
Proof: Let a = rtz-sqrt(n-2, x) and r = rto-sqrt-norm(x, n).
Suppose a^2 = x.  Then r = a, l^2 <= x = a^2 = r^2, and l <= r.  
By rto-monotone, rto-exactp-b, and exactp-rtz-sqrt,

  rto(l, n) <= rto(r, n) = r.

Thus, we may assume a^2 < x and r = a + 2^(1-n).  By rtz-sqrt-square-bounds, 
l^2 <= x < (a + 2^(2-n))^2, and hence l < a + 2^(2-n) = fp+(a, n-1).  
It follows from rtz-upper-pos, rtz-exactp-a, and fp+2 that 
rtz(l, n-1) <= a.  Thus,

  rto(l, n) <= rtz(l, n-1) + 2^(1+expo(l)-n)
            <= a + 2^(1-n)
             = r.
|#

(defthm rto-sqrt-norm-upper
  (implies (and (natp n)
                (>= n 2)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (rationalp h)
                (>= h 0)
                (>= (* h h) x))
           (>= (rto h n)
               (rto-sqrt-norm x n)))
  :rule-classes ()
  :hints (("Goal" :use sticky-sqrt-upper)))

#|
Proof: Let a = rtz-sqrt(x, n-1) and r = rto-sqrt-norm(x, n).
We may assume that h < r; otherwise, by rto-monotone, 
rto-exactp-b, and exactp-rtz-sqrt,

  rto(h, n) >= rto(r, n) = r.

If a^2 = x, then r = a, h^2 >= x = a^2 = r^2, and h >= r.  
Thus, by rtz-sqrt-square-bounds, a^2 < x and r = a + 2^(1-n) = fp+(a, n).
Since h^2 >= x > a^2, h > a.  It follows from trunc-exactp-c that 
trunc(h, n-1) >= a.  By fp+2, h is not n-exact, and hence

  rto(h, n) = rtz(h, n-1) + 2^(1-n)
           >= a + 2^(1-n)
            = r.
|#

(defthmd rto-rto-sqrt-norm
  (implies (and (natp n)
                (>= n 2)
                (natp m)
                (>= m n)
                (rationalp x)
                (<= 1/4 x)
                (< x 1))
           (equal (rto (rto-sqrt-norm x m) n)
                  (rto-sqrt-norm x n)))
  :hints (("Goal" :use sticky-sticky-sqrt)))

(defthm fp-rnd-rto-sqrt-norm
  (implies (and (not (zp k))
                (natp n)
                (>= n (+ k 2))
                (natp m)
                (>= m n)
                (common-mode-p mode)
                (rationalp x)
                (<= 1/4 x)
                (< x 1))
           (= (fp-rnd (rto-sqrt-norm x m) mode k)
              (fp-rnd (rto-sqrt-norm x n) mode k)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rnd-sticky-sqrt (mode (old-mode mode)))))))

(defthmd rtz-rto-sqrt-norm
  (implies (and (natp n)
                (>= n 2)
                (natp m)
                (> m n)
                (rationalp x)
                (<= 1/4 x)
                (< x 1))
           (equal (rtz (rto-sqrt-norm x m) n)
                  (rtz-sqrt x n)))
  :hints (("Goal" :use trunc-sticky-sqrt)))

(defthm rtz-rtz-rto
   (implies (and (natp n)
                (>= n 2)
                (natp m)
                (> m n)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)) 
           (iff (= (* (rtz-sqrt x n) (rtz-sqrt x n)) x)
                (= (rto-sqrt-norm x m) (rtz-sqrt x n))))
  :rule-classes ()
  :hints (("Goal" :use trunc-trunc-sticky)))

(defthm exactp-cmp-rto-sqrt-norm
  (implies (and (rationalp x) (>= x 1/4) (< x 1)
                (rationalp y) (> y 0)
                (integerp n) (> n 1)
                (exactp y (1- n)))
           (and (iff (< (* y y) x) (< y (rto-sqrt-norm x n)))
                (iff (> (* y y) x) (> y (rto-sqrt-norm x n)))))
  :rule-classes ()
  :hints (("Goal" :use exactp-cmp-sticky-sqrt)))


;;;**********************************************************************
;;;		    	      RTO-SQRT
;;;**********************************************************************

(defund rto-sqrt (x n)
  (let ((e (1+ (fl (/ (expo x) 2)))))
    (* (expt 2 e)
       (rto-sqrt-norm (/ x (expt 2 (* 2 e))) n))))

(local-defthm rto-sqrt-qsqrt
  (equal (rto-sqrt x n) (qsqrt x n))
  :hints (("Goal" :in-theory (enable rto-sqrt qsqrt))))

(defthmd sqrt-rto-sqrt
  (implies (and (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (integerp n)
                (> n 1))
           (equal (rto-sqrt x n)
                  (rto-sqrt-norm x n)))
  :hints (("Goal" :use sqrt-sticky-sqrt)))

(defthmd rto-sqrt-pos
  (implies (and (rationalp x)
                (> x 0))
           (> (rto-sqrt x n) 0))
  :hints (("Goal" :use qsqrt-pos)))

(defthmd rto-sqrt-shift
  (implies (and (rationalp x)
                (> x 0)
                (integerp k)
                (integerp n)
                (> n 1))
           (equal (rto-sqrt (* (expt 2 (* 2 k)) x) n)
                  (* (expt 2 k) (rto-sqrt x n))))
  :hints (("Goal" :use qsqrt-shift)))

(defthm exactp-cmp-rto-sqrt
  (implies (and (rationalp x) (> x 0)
                (rationalp y) (> y 0)
                (integerp n) (> n 1)
                (exactp y (1- n)))
           (and (iff (< (* y y) x) (< y (rto-sqrt x n)))
                (iff (> (* y y) x) (> y (rto-sqrt x n)))))
  :rule-classes ()
  :hints (("Goal" :use exactp-cmp-qsqrt)))

(defthm rto-sqrt-lower$
  (implies (and (rationalp x)
                (> x 0)
                (rationalp l)
                (<= (* l l) x)
                (common-mode-p mode)
                (not (zp k))
                (integerp n)
                (>= n (+ k 2)))
           (<= (fp-rnd l mode k)
               (fp-rnd (rto-sqrt x n) mode k)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance qsqrt-lower (mode (old-mode mode)))))))

#|
Proof: Let e = fl(expo(x)/2), x0 = x/2^(2*e), and l0 = l/2^e.
Then 1 <= x0 < 4 and l0^2 = l^2/2^(2*e) <= x/2^(2*e) = x0.
By rto-shift and rto-sqrt-norm-lower, 

  rto(l, 66) = 2^e * rto(l0, n) 
            <= 2^e * rto-sqrt-norm(x0, n)
             = sqrt(x, n).

By fp-rnd-rto and fp-rnd-monotone,

  fp-rnd(l, mode, k) = fp-rnd(rto(l, n), mode, k)
                    <= fp-rnd(rto-sqrt(x, n), mode, k)
|#

(defthm rto-sqrt-upper$
  (implies (and (rationalp x)
                (> x 0)
                (rationalp h)
                (>= h 0)
                (>= (* h h) x)
                (common-mode-p mode)
                (not (zp k))
                (integerp n)
                (>= n (+ k 2)))
           (>= (fp-rnd h mode k)
               (fp-rnd (rto-sqrt x n) mode k)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance qsqrt-upper (mode (old-mode mode)))))))



(defthm qe-1
  (implies (and (rationalp x)
                (> x 0))
           (let ((e (1+ (fl (/ (expo x) 2)))))
             (and (<= (expo x) (* 2 e))
                  (>= (expo x) (- (* 2 e) 2)))))
  :rule-classes ())

(local (include-book "arithmetic-5/top" :dir :system))

;; The following lemmas from arithmetic-5 have given me trouble:

(local-in-theory #!acl2(disable |(mod (+ x y) z) where (<= 0 z)| |(mod (+ x (- (mod a b))) y)| |(mod (mod x y) z)| |(mod (+ x (mod a b)) y)|
                    simplify-products-gather-exponents-equal mod-cancel-*-const cancel-mod-+ reduce-additive-constant-< 
                    |(floor x 2)| |(equal x (if a b c))| |(equal (if a b c) x)|))

(defthm qe-2
  (implies (and (rationalp x)
                (> x 0))
           (let* ((e (1+ (fl (/ (expo x) 2))))
                  (xp (/ x (expt 2 (* 2 e)))))
             (= (expo xp) (- (expo x) (* 2 e)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance expo-shift (n (- (* 2 (1+ (fl (/ (expo x) 2)))))))))))

(defthm qe-3
  (implies (and (rationalp x)
                (> x 0))
           (let* ((e (1+ (fl (/ (expo x) 2))))
                  (xp (/ x (expt 2 (* 2 e)))))
             (and (< (expo xp) 0)
                  (>= (expo xp) -2))))
  :rule-classes ()
  :hints (("Goal" :use (qe-1 qe-2))))

(defthm qsqrt-expo
  (implies (and (rationalp x)
                (> x 0))
           (let* ((e (1+ (fl (/ (expo x) 2))))
                  (xp (/ x (expt 2 (* 2 e)))))
             (and (<= 1/4 xp)
                  (< xp 1))))
  :rule-classes ()
  :hints (("Goal" :use (qe-1 qe-2
                        (:instance expo<= (n -3) (x (/ x (expt 2 (* 2 (1+ (fl (/ (expo x) 2))))))))
                        (:instance expo>= (n -0) (x (/ x (expt 2 (* 2 (1+ (fl (/ (expo x) 2))))))))))))

))

;;-----------------------------------------------------------------------------------------


;; From basic.lisp:

(defund fl (x)
  (declare (xargs :guard (real/rationalp x)))
  (floor x 1))

(defund cg (x)
  (declare (xargs :guard (real/rationalp x)))
  (- (fl (- x))))

;; From float.lisp:

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

(defund exactp (x n)
  (integerp (* (sig x) (expt 2 (1- n)))))

;; From round.lisp:

(defund rtz (x n)
  (declare (xargs :guard (integerp n)))
  (* (sgn x) 
     (fl (* (expt 2 (1- n)) (sig x))) 
     (expt 2 (- (1+ (expo x)) n))))

(defund raz (x n)
  (* (sgn x) 
     (cg (* (expt 2 (1- n)) (sig x))) 
     (expt 2 (- (1+ (expo x)) n))))

(defun re (x)
  (- x (fl x)))

(defund rne (x n)
  (let ((z (fl (* (expt 2 (1- n)) (sig x))))
	(f (re (* (expt 2 (1- n)) (sig x)))))
    (if (< f 1/2)
	(rtz x n)
      (if (> f 1/2)
	  (raz x n)
	(if (evenp z)
	    (rtz x n)
	  (raz x n))))))

(defund rto (x n)
  (if (exactp x (1- n))
      x
    (+ (rtz x (1- n))
       (* (sgn x) (expt 2 (1+ (- (expo x) n)))))))

(defund rup (x n)
  (if (>= x 0)
      (raz x n)
    (rtz x n)))

(defund rdn (x n)
  (if (>= x 0)
      (rtz x n)
    (raz x n)))

(defund rna (x n)
  (if (< (re (* (expt 2 (1- n)) (sig x)))
	 1/2)
      (rtz x n)
    (raz x n)))


(defund IEEE-rounding-mode-p (mode)
  (member mode '(rtz rup rdn rne)))

(defund common-mode-p (mode)
  (or (IEEE-rounding-mode-p mode) (equal mode 'raz) (equal mode 'rna)))

(defund rnd (x mode n)
  (case mode
    (raz (raz x n))
    (rna (rna x n))
    (rtz (rtz x n))
    (rup (rup x n))
    (rdn (rdn x n))
    (rne (rne x n))
    (otherwise 0)))

(local-defthm fp-rnd-rnd
  (equal (fp-rnd x mode n) (rnd x mode n))
  :hints (("Goal" :in-theory (enable fp-rnd rnd))))

;;;**********************************************************************
;;;		    	      RTZ-SQRT
;;;**********************************************************************

(defund rtz-sqrt (x n)
  (if (zp n)
      0
    (let* ((lower (rtz-sqrt x (1- n)))
           (upper (+ lower (expt 2 (- n)))))
      (if (<= (* upper upper) x)
          upper
        lower))))

(defthm rtz-sqrt-bounds
  (implies (and (rationalp x)
                (<= 1/4 x)
                (not (zp n)))
           (and (<= 1/2 (rtz-sqrt x n))
                (<= (rtz-sqrt x n) (- 1 (expt 2 (- n))))))
  :rule-classes ())
                                

(defthm expo-rtz-sqrt
  (implies (and (rationalp x)
                (<= 1/4 x)
                (not (zp n)))
           (equal (expo (rtz-sqrt x n))
                  -1)))

(defthm exactp-rtz-sqrt
  (implies (and (rationalp x)
                (<= 1/4 x)
                (not (zp n)))
           (exactp (rtz-sqrt x n)
                   n))
  :rule-classes ())

(defthmd rtz-rtz-sqrt
  (implies (and (rationalp x)
                (<= 1/4 x)
                (not (zp m))
                (natp n)
                (>= n m))
           (equal (rtz (rtz-sqrt x n) m)
                  (rtz-sqrt x m))))

(defthm rtz-sqrt-square-bounds
  (implies (and (not (zp n))
                (rationalp x)
                (<= 1/4 x)
                (< x 1))                
           (and (<= (* (rtz-sqrt x n)
                       (rtz-sqrt x n))
                    x)
                (< x
                   (* (+ (rtz-sqrt x n) (expt 2 (- n)))
                      (+ (rtz-sqrt x n) (expt 2 (- n)))))))
  :rule-classes ())

(defthm rtz-sqrt-unique
  (implies (and (not (zp n))
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (rationalp a)
                (exactp a n)
                (>= a 1/2)
                (<= (* a a) x)
                (< x (* (+ a (expt 2 (- n))) (+ a (expt 2 (- n))))))
           (= a (rtz-sqrt x n)))
  :rule-classes ())


;;;**********************************************************************
;;;		    	        RTO-SQRT
;;;**********************************************************************

(defund rto-sqrt-temp (x n)
  (let ((trunc (rtz-sqrt x (1- n))))
    (if (< (* trunc trunc) x)
        (+ trunc (expt 2 (- n)))
      trunc)))

(local-defthm rto-sqrt-norm-rewrite
  (equal (rto-sqrt-norm x n) (rto-sqrt-temp x n))
  :hints (("Goal" :in-theory (enable rto-sqrt-norm rto-sqrt-temp))))

(defthm rto-sqrt-temp-bounds
  (implies (and (rationalp x)
                (<= 1/4 x)
                (natp n)
                (>= n 2))
           (and (<= 1/2 (rto-sqrt-temp x n))
                (< (rto-sqrt-temp x n) 1)))
  :rule-classes ()
  :hints (("Goal" :use rto-sqrt-norm-bounds)))

(defthm expo-rto-sqrt-temp
  (implies (and (rationalp x)
                (<= 1/4 x)
                (natp n)
                (>= n 2))
           (equal (expo (rto-sqrt-temp x n))
                  -1))
  :hints (("Goal" :use expo-rto-sqrt-norm)))

(defthmd exactp-rto-sqrt-temp
  (implies (and (rationalp x)
                (<= 1/4 x)
                (natp n)
                (>= n 2))
           (exactp (rto-sqrt-temp x n) n))
  :hints (("Goal" :use exactp-rto-sqrt-norm)))

(defthm rto-sqrt-temp-lower
  (implies (and (natp n)
                (>= n 2)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (rationalp l)
                (<= (* l l) x))
           (<= (rto l n)
               (rto-sqrt-temp x n)))
  :rule-classes ()
  :hints (("Goal" :use rto-sqrt-norm-lower)))

(defthm rto-sqrt-temp-upper
  (implies (and (natp n)
                (>= n 2)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (rationalp h)
                (>= h 0)
                (>= (* h h) x))
           (>= (rto h n)
               (rto-sqrt-temp x n)))
  :rule-classes ()
  :hints (("Goal" :use rto-sqrt-norm-upper)))

(defthmd rto-rto-sqrt-temp
  (implies (and (natp n)
                (>= n 2)
                (natp m)
                (>= m n)
                (rationalp x)
                (<= 1/4 x)
                (< x 1))
           (equal (rto (rto-sqrt-temp x m) n)
                  (rto-sqrt-temp x n)))
  :hints (("Goal" :use rto-rto-sqrt-norm)))

(defthm rnd-rto-sqrt-temp
  (implies (and (not (zp k))
                (natp n)
                (>= n (+ k 2))
                (natp m)
                (>= m n)
                (common-mode-p mode)
                (rationalp x)
                (<= 1/4 x)
                (< x 1))
           (= (rnd (rto-sqrt-temp x m) mode k)
              (rnd (rto-sqrt-temp x n) mode k)))
  :rule-classes ()
  :hints (("Goal" :use fp-rnd-rto-sqrt-norm)))


(defthmd rtz-rto-sqrt-temp
  (implies (and (natp n)
                (>= n 2)
                (natp m)
                (> m n)
                (rationalp x)
                (<= 1/4 x)
                (< x 1))
           (equal (rtz (rto-sqrt-temp x m) n)
                  (rtz-sqrt x n)))
  :hints (("Goal" :use rtz-rto-sqrt-norm)))

(defthm rtz-rtz-rto-sqrt
   (implies (and (natp n)
                (>= n 2)
                (natp m)
                (> m n)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)) 
           (iff (= (* (rtz-sqrt x n) (rtz-sqrt x n)) x)
                (= (rto-sqrt-temp x m) (rtz-sqrt x n))))
  :rule-classes ()
  :hints (("Goal" :use rtz-rtz-rto)))

(defthm exactp-cmp-rto-sqrt-temp
  (implies (and (rationalp x) (>= x 1/4) (< x 1)
                (rationalp y) (> y 0)
                (integerp n) (> n 1)
                (exactp y (1- n)))
           (and (iff (< (* y y) x) (< y (rto-sqrt-temp x n)))
                (iff (> (* y y) x) (> y (rto-sqrt-temp x n)))))
  :rule-classes ()
  :hints (("Goal" :use exactp-cmp-rto-sqrt-norm)))


;;;**********************************************************************
;;;		    	        QSQRT
;;;**********************************************************************

(defund qsqrt-temp (x n)
  (let ((e (1+ (fl (/ (expo x) 2)))))
    (* (expt 2 e)
       (rto-sqrt-temp (/ x (expt 2 (* 2 e))) n))))

(defthm qsqrt-expo
  (implies (and (rationalp x)
                (> x 0))
           (let* ((e (1+ (fl (/ (expo x) 2))))
                  (xp (/ x (expt 2 (* 2 e)))))
             (and (<= 1/4 xp)
                  (< xp 1))))
  :rule-classes ()
  :hints (("Goal" :use (qe-1 qe-2
                        (:instance expo<= (n -3) (x (/ x (expt 2 (* 2 (1+ (fl (/ (expo x) 2))))))))
                        (:instance expo>= (n -0) (x (/ x (expt 2 (* 2 (1+ (fl (/ (expo x) 2))))))))))))

(local-defthm rto-sqrt-reqrite
  (equal (rto-sqrt x n) (qsqrt-temp x n))
  :hints (("Goal" :in-theory (enable qsqrt-temp rto-sqrt))))

(defthmd sqrt-qsqrt-temp
  (implies (and (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (integerp n)
                (> n 1))
           (equal (qsqrt-temp x n)
                  (rto-sqrt-temp x n)))
  :hints (("Goal" :use sqrt-rto-sqrt)))

(defthmd qsqrt-temp-pos
  (implies (and (rationalp x)
                (> x 0))
           (> (qsqrt-temp x n) 0))
  :hints (("Goal" :use rto-sqrt-pos)))

(defthmd qsqrt-temp-shift
  (implies (and (rationalp x)
                (> x 0)
                (integerp k)
                (integerp n)
                (> n 1))
           (equal (qsqrt-temp (* (expt 2 (* 2 k)) x) n)
                  (* (expt 2 k) (qsqrt-temp x n))))
  :hints (("Goal" :use rto-sqrt-shift)))

(defthm exactp-cmp-qsqrt-temp
  (implies (and (rationalp x) (> x 0)
                (rationalp y) (> y 0)
                (integerp n) (> n 1)
                (exactp y (1- n)))
           (and (iff (< (* y y) x) (< y (qsqrt-temp x n)))
                (iff (> (* y y) x) (> y (qsqrt-temp x n)))))
  :rule-classes ()
  :hints (("Goal" :use exactp-cmp-rto-sqrt)))

(defthm qsqrt-temp-lower
  (implies (and (rationalp x)
                (> x 0)
                (rationalp l)
                (<= (* l l) x)
                (common-mode-p mode)
                (not (zp k))
                (integerp n)
                (>= n (+ k 2)))
           (<= (rnd l mode k)
               (rnd (qsqrt-temp x n) mode k)))
  :rule-classes ()
  :hints (("Goal" :use (rto-sqrt-lower$))))

(defthm qsqrt-temp-upper
  (implies (and (rationalp x)
                (> x 0)
                (rationalp h)
                (>= h 0)
                (>= (* h h) x)
                (common-mode-p mode)
                (not (zp k))
                (integerp n)
                (>= n (+ k 2)))
           (>= (rnd h mode k)
               (rnd (qsqrt-temp x n) mode k)))
  :rule-classes ()
  :hints (("Goal" :use (rto-sqrt-upper$))))

))


;;-----------------------------------------------------------------------------------------


;; From basic.lisp:

(defund fl (x)
  (declare (xargs :guard (real/rationalp x)))
  (floor x 1))

(defund cg (x)
  (declare (xargs :guard (real/rationalp x)))
  (- (fl (- x))))

;; From float.lisp:

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

(defund exactp (x n)
  (integerp (* (sig x) (expt 2 (1- n)))))

;; From round.lisp:

(defund rtz (x n)
  (declare (xargs :guard (integerp n)))
  (* (sgn x) 
     (fl (* (expt 2 (1- n)) (sig x))) 
     (expt 2 (- (1+ (expo x)) n))))

(defund raz (x n)
  (* (sgn x) 
     (cg (* (expt 2 (1- n)) (sig x))) 
     (expt 2 (- (1+ (expo x)) n))))

(defun re (x)
  (- x (fl x)))

(defund rne (x n)
  (let ((z (fl (* (expt 2 (1- n)) (sig x))))
	(f (re (* (expt 2 (1- n)) (sig x)))))
    (if (< f 1/2)
	(rtz x n)
      (if (> f 1/2)
	  (raz x n)
	(if (evenp z)
	    (rtz x n)
	  (raz x n))))))

(defund rto (x n)
  (if (exactp x (1- n))
      x
    (+ (rtz x (1- n))
       (* (sgn x) (expt 2 (1+ (- (expo x) n)))))))

(defund rup (x n)
  (if (>= x 0)
      (raz x n)
    (rtz x n)))

(defund rdn (x n)
  (if (>= x 0)
      (rtz x n)
    (raz x n)))

(defund rna (x n)
  (if (< (re (* (expt 2 (1- n)) (sig x)))
	 1/2)
      (rtz x n)
    (raz x n)))


(defund IEEE-rounding-mode-p (mode)
  (member mode '(rtz rup rdn rne)))

(defund common-mode-p (mode)
  (or (IEEE-rounding-mode-p mode) (equal mode 'raz) (equal mode 'rna)))

(defund rnd (x mode n)
  (case mode
    (raz (raz x n))
    (rna (rna x n))
    (rtz (rtz x n))
    (rup (rup x n))
    (rdn (rdn x n))
    (rne (rne x n))
    (otherwise 0)))


;;;**********************************************************************
;;;		    	      RTZ-SQRT
;;;**********************************************************************

(defund rtz-sqrt (x n)
  (if (zp n)
      0
    (let* ((lower (rtz-sqrt x (1- n)))
           (upper (+ lower (expt 2 (- n)))))
      (if (<= (* upper upper) x)
          upper
        lower))))

(defthm rtz-sqrt-bounds
  (implies (and (rationalp x)
                (<= 1/4 x)
                (not (zp n)))
           (and (<= 1/2 (rtz-sqrt x n))
                (<= (rtz-sqrt x n) (- 1 (expt 2 (- n))))))
  :rule-classes ())
                                

(defthm expo-rtz-sqrt
  (implies (and (rationalp x)
                (<= 1/4 x)
                (not (zp n)))
           (equal (expo (rtz-sqrt x n))
                  -1)))

(defthm exactp-rtz-sqrt
  (implies (and (rationalp x)
                (<= 1/4 x)
                (not (zp n)))
           (exactp (rtz-sqrt x n)
                   n))
  :rule-classes ())

(defthmd rtz-rtz-sqrt
  (implies (and (rationalp x)
                (<= 1/4 x)
                (not (zp m))
                (natp n)
                (>= n m))
           (equal (rtz (rtz-sqrt x n) m)
                  (rtz-sqrt x m))))

(defthm rtz-sqrt-square-bounds
  (implies (and (not (zp n))
                (rationalp x)
                (<= 1/4 x)
                (< x 1))                
           (and (<= (* (rtz-sqrt x n)
                       (rtz-sqrt x n))
                    x)
                (< x
                   (* (+ (rtz-sqrt x n) (expt 2 (- n)))
                      (+ (rtz-sqrt x n) (expt 2 (- n)))))))
  :rule-classes ())

(defthm rtz-sqrt-unique
  (implies (and (not (zp n))
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (rationalp a)
                (exactp a n)
                (>= a 1/2)
                (<= (* a a) x)
                (< x (* (+ a (expt 2 (- n))) (+ a (expt 2 (- n))))))
           (= a (rtz-sqrt x n)))
  :rule-classes ())


;;;**********************************************************************
;;;		    	        RTO-SQRT
;;;**********************************************************************

(defund rto-sqrt (x n)
  (let ((trunc (rtz-sqrt x (1- n))))
    (if (< (* trunc trunc) x)
        (+ trunc (expt 2 (- n)))
      trunc)))

(local-defthm rto-sqrt-temp-rewrite
  (equal (rto-sqrt-temp x n) (rto-sqrt x n))
  :hints (("Goal" :in-theory (enable rto-sqrt rto-sqrt-temp))))

(defthm rto-sqrt-bounds
  (implies (and (rationalp x)
                (<= 1/4 x)
                (natp n)
                (>= n 2))
           (and (<= 1/2 (rto-sqrt x n))
                (< (rto-sqrt x n) 1)))
  :rule-classes ()
  :hints (("Goal" :use rto-sqrt-temp-bounds)))

(defthm expo-rto-sqrt
  (implies (and (rationalp x)
                (<= 1/4 x)
                (natp n)
                (>= n 2))
           (equal (expo (rto-sqrt x n))
                  -1))
  :hints (("Goal" :use expo-rto-sqrt-temp)))

(defthmd exactp-rto-sqrt
  (implies (and (rationalp x)
                (<= 1/4 x)
                (natp n)
                (>= n 2))
           (exactp (rto-sqrt x n) n))
  :hints (("Goal" :use exactp-rto-sqrt-temp)))

(defthm rto-sqrt-lower
  (implies (and (natp n)
                (>= n 2)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (rationalp l)
                (<= (* l l) x))
           (<= (rto l n)
               (rto-sqrt x n)))
  :rule-classes ()
  :hints (("Goal" :use rto-sqrt-temp-lower)))

(defthm rto-sqrt-upper
  (implies (and (natp n)
                (>= n 2)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (rationalp h)
                (>= h 0)
                (>= (* h h) x))
           (>= (rto h n)
               (rto-sqrt x n)))
  :rule-classes ()
  :hints (("Goal" :use rto-sqrt-temp-upper)))

(defthmd rto-rto-sqrt
  (implies (and (natp n)
                (>= n 2)
                (natp m)
                (>= m n)
                (rationalp x)
                (<= 1/4 x)
                (< x 1))
           (equal (rto (rto-sqrt x m) n)
                  (rto-sqrt x n)))
  :hints (("Goal" :use rto-rto-sqrt-temp)))

(defthm rnd-rto-sqrt
  (implies (and (not (zp k))
                (natp n)
                (>= n (+ k 2))
                (natp m)
                (>= m n)
                (common-mode-p mode)
                (rationalp x)
                (<= 1/4 x)
                (< x 1))
           (= (rnd (rto-sqrt x m) mode k)
              (rnd (rto-sqrt x n) mode k)))
  :rule-classes ()
  :hints (("Goal" :use rnd-rto-sqrt-temp)))


(defthmd rtz-rto-sqrt
  (implies (and (natp n)
                (>= n 2)
                (natp m)
                (> m n)
                (rationalp x)
                (<= 1/4 x)
                (< x 1))
           (equal (rtz (rto-sqrt x m) n)
                  (rtz-sqrt x n)))
  :hints (("Goal" :use rtz-rto-sqrt-temp)))

(defthm rtz-rtz-rto
   (implies (and (natp n)
                (>= n 2)
                (natp m)
                (> m n)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)) 
           (iff (= (* (rtz-sqrt x n) (rtz-sqrt x n)) x)
                (= (rto-sqrt x m) (rtz-sqrt x n))))
  :rule-classes ()
  :hints (("Goal" :use rtz-rtz-rto-sqrt)))

(defthm exactp-cmp-rto-sqrt
  (implies (and (rationalp x) (>= x 1/4) (< x 1)
                (rationalp q) (> q 0)
                (integerp n) (> n 1)
                (exactp q (1- n)))
           (and (iff (< (* q q) x) (< q (rto-sqrt x n)))
                (iff (> (* q q) x) (> q (rto-sqrt x n)))))
  :rule-classes ()
  :hints (("Goal" :use (:instance exactp-cmp-rto-sqrt-temp (y q)))))


;;;**********************************************************************
;;;		    	        QSQRT
;;;**********************************************************************

(defund qsqrt (x n)
  (let ((e (1+ (fl (/ (expo x) 2)))))
    (* (expt 2 e)
       (rto-sqrt (/ x (expt 2 (* 2 e))) n))))

(defthm qsqrt-expo
  (implies (and (rationalp x)
                (> x 0))
           (let* ((e (1+ (fl (/ (expo x) 2))))
                  (xp (/ x (expt 2 (* 2 e)))))
             (and (<= 1/4 xp)
                  (< xp 1))))
  :rule-classes ())

(local-defthm rto-sqrt-reqrite
  (equal (qsqrt-temp x n) (qsqrt x n))
  :hints (("Goal" :in-theory (enable qsqrt-temp qsqrt))))

(defthmd qsqrt-rto-sqrt
  (implies (and (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (integerp n)
                (> n 1))
           (equal (qsqrt x n)
                  (rto-sqrt x n)))
  :hints (("Goal" :use sqrt-qsqrt-temp)))

(defthmd qsqrt-pos
  (implies (and (rationalp x)
                (> x 0))
           (> (qsqrt x n) 0))
  :hints (("Goal" :use qsqrt-temp-pos)))

(defthmd qsqrt-shift
  (implies (and (rationalp x)
                (> x 0)
                (integerp k)
                (integerp n)
                (> n 1))
           (equal (qsqrt (* (expt 2 (* 2 k)) x) n)
                  (* (expt 2 k) (qsqrt x n))))
  :hints (("Goal" :use qsqrt-temp-shift)))

(defthm exactp-cmp-qsqrt
  (implies (and (rationalp x) (> x 0)
                (rationalp q) (> q 0)
                (integerp n) (> n 1)
                (exactp q (1- n)))
           (and (iff (< (* q q) x) (< q (qsqrt x n)))
                (iff (> (* q q) x) (> q (qsqrt x n)))))
  :rule-classes ()
  :hints (("Goal" :use (:instance exactp-cmp-qsqrt-temp (y q)))))

(defthm qsqrt-lower
  (implies (and (rationalp x)
                (> x 0)
                (rationalp l)
                (<= (* l l) x)
                (common-mode-p mode)
                (not (zp k))
                (integerp n)
                (>= n (+ k 2)))
           (<= (rnd l mode k)
               (rnd (qsqrt x n) mode k)))
  :rule-classes ()
  :hints (("Goal" :use (qsqrt-temp-lower))))

(defthm qsqrt-upper
  (implies (and (rationalp x)
                (> x 0)
                (rationalp h)
                (>= h 0)
                (>= (* h h) x)
                (common-mode-p mode)
                (not (zp k))
                (integerp n)
                (>= n (+ k 2)))
           (>= (rnd h mode k)
               (rnd (qsqrt x n) mode k)))
  :rule-classes ()
  :hints (("Goal" :use (qsqrt-temp-upper))))
