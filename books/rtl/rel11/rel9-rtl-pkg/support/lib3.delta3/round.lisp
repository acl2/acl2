(in-package "RTL")

(local (include-book "../lib3/top"))

(include-book "arithmetic-5/top" :dir :system)


;; From basic.lisp:

(defund fl (x)
  (declare (xargs :guard (real/rationalp x)))
  (floor x 1))

(defund cg (x)
  (declare (xargs :guard (real/rationalp x)))
  (- (fl (- x))))

;; From bits.lisp:

(defund bits (x i j)
  (declare (xargs :guard (and (integerp x)
                              (integerp i)
                              (integerp j))))
  (mbe :logic (if (or (not (integerp i))
                      (not (integerp j)))
                  0
                (fl (/ (mod x (expt 2 (1+ i))) (expt 2 j))))
       :exec  (if (< i j)
                  0
                (logand (ash x (- j)) (1- (ash 1 (1+ (- i j))))))))

(defund bitn (x n)
  (declare (xargs :guard (and (integerp x)
                              (integerp n))))
  (mbe :logic (bits x n n)
       :exec  (if (evenp (ash x (- n))) 0 1)))

;; From float.lisp:

(defund sgn (x)
  (declare (xargs :guard t))
  (if (or (not (rationalp x)) (equal x 0))
      0
    (if (< x 0) -1 +1)))

(defnd expo (x)
  (declare (xargs :measure (:? x)
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

(defund sig (x)
  (declare (xargs :guard t
                  :verify-guards nil))
  (if (rationalp x)
      (if (< x 0)
          (- (* x (expt 2 (- (expo x)))))
        (* x (expt 2 (- (expo x)))))
    0))

(defund exactp (x n)
  (integerp (* (sig x) (expt 2 (1- n)))))

(defun fp+ (x n)
  (+ x (expt 2 (- (1+ (expo x)) n))))


;; From round.lisp:

(defund away (x n)
  (* (sgn x)
     (cg (* (expt 2 (1- n)) (sig x)))
     (expt 2 (- (1+ (expo x)) n))))

(defund trunc (x n)
  (declare (xargs :guard (integerp n)
                  :verify-guards nil))
  (* (sgn x)
     (fl (* (expt 2 (1- n)) (sig x)))
     (expt 2 (- (1+ (expo x)) n))))

(defun re (x)
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

(defund near+ (x n)
  (if (< (re (* (expt 2 (1- n)) (sig x)))
	 1/2)
      (trunc x n)
    (away x n)))


(defund IEEE-mode-p (mode)
  (member mode '(trunc inf minf near)))

(defund common-rounding-mode-p (mode)
  (or (IEEE-mode-p mode) (equal mode 'away) (equal mode 'near+)))

(defund rnd (x mode n)
  (case mode
    (away (away x n))
    (near+ (near+ x n))
    (trunc (trunc x n))
    (inf (inf x n))
    (minf (minf x n))
    (near (near x n))
    (otherwise 0)))


;;;**********************************************************************

(defthm bits-trunc-bits
  (implies (and (rationalp x)
                (>= x 0)
                (integerp k)
                (integerp i)
                (integerp j)
                (> k 0)
                (>= (expo x) i)
                (>= j (- (1+ (expo x)) k)))
           (= (bits (trunc x k) i j)
              (bits x i j)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance bits-trunc (n (1+ (expo x))))
                        (:instance bits-shift-up-1 (k (- (1+ (expo x)) k)) (x (bits x (expo x) (- (1+ (expo x)) k))))))))


;;;**********************************************************************

(defun round-up (x sticky mode n)
  (case mode
    (near+ (= (bitn x (- (expo x) n)) 1))
    (near (and (= (bitn x (- (expo x) n)) 1)
               (or (not (= (bits x (- (expo x) (1+ n)) 0) 0))
                   (= sticky 1)
                   (= (bitn x (- (1+ (expo x)) n)) 1))))
    ((inf away) (or (not (= (bits x (- (expo x) n) 0) 0))
                    (= sticky 1)))
    (otherwise ())))

#|
(defthm round-up-thm
  (implies (and (common-rounding-mode-p mode)
                (rationalp r)
                (> r 0)
                (not (zp n))
                (natp k)
                (< n k)
                (<= k (1+ (expo r))))
           (let* ((x (trunc r k))
                  (sticky (if (< x r) 1 0)))
	     (= (rnd r mode n)
                (if (round-up x sticky mode n)
                    (fp+ (trunc r n) n)
                  (trunc r n)))))
  :rule-classes ())
|#

(defthm ru-0
  (implies (and (rationalp r)
                (> r 0)
                (not (zp n))
                (natp k)
                (< n k)
                (<= k (1+ (expo r))))
           (let* ((x (trunc r k))
                  (sticky (if (< x r) 1 0)))
	     (= (trunc r n)
                (if (round-up x sticky 'trunc n)
                    (fp+ (trunc r n) n)
                  (trunc r n)))))
  :rule-classes ())

#|

Let e = expo(r), 0 < n < k <= 1 + e, x = trunc(r, k), and s = 1 <=> x < r.

trunc(r, n) = trunc(trunc(r, k), n) = trunc(x, n) <= x <= r.

expo(x) = expo(r) = e.

x is (e+1)-exact.

By trunc-split (with n = e+1, m = e+1, k = n),

  x - trunc(x, n) = trunc(x, e+1) - trunc(x, n) = x[e-n:0].

By trunc-away (with x = r),

  away(r, n) = trunc(x, n)         if r = trunc(r, n)
               fp+(trunc(x, n), n) if r > trunc(r, n).

But r > trunc(r, n) <=> r > x or x > trunc(x, n)
                    <=> x[e-n:0] <> 0 or s = 1.

|#

(local (in-theory (enable trunc-trunc)))

(defthm ru-1
  (let ((e (expo r))
        (x (trunc r k)))
    (implies (and (not (zp n))
                  (natp k)
                  (< n k)
                  (<= k (1+ e)))
             (exactp x (1+ e))))
  :rule-classes ()
  :hints  (("Goal" :use ((:instance exactp-<= (x (trunc r k)) (m k) (n (1+ (expo r))))))))

(defthm ru-2
  (let ((e (expo r))
        (x (trunc r k)))
    (implies (and (not (zp n))
                  (natp k)
                  (< n k)
                  (<= k (1+ e)))
             (equal (trunc x (1+ e)) x)))
  :rule-classes ()
  :hints  (("Goal" :use (ru-1
                         (:instance trunc-exactp-b (x (trunc r k)) (n (1+ (expo r))))))))

(defthm ru-3
  (let ((e (expo r))
        (x (trunc r k)))
    (implies (and (rationalp r)
                  (> r 0)
                  (not (zp n))
                  (natp k)
                  (< n k)
                  (<= k (1+ e)))
             (equal (- x (trunc x n))
                    (bits x (- e n) 0))))
  :rule-classes ()
  :hints  (("Goal" :use (ru-2
                         (:instance trunc-split (x (trunc r k)) (n (1+ (expo r))) (m (1+ (expo r))) (k n))))))

(defthm ru-4
  (let ((e (expo r))
        (x (trunc r k)))
    (implies (and (rationalp r)
                  (> r 0)
                  (not (zp n))
                  (natp k)
                  (< n k)
                  (<= k (1+ e))
                  (= r (trunc r n)))
             (equal (away r n) (trunc x n))))
  :rule-classes ()
  :hints  (("Goal" :use ((:instance trunc-exactp-b (x r))
                         (:instance away-exactp-b (x r))))))

(defthm ru-5
  (let ((e (expo r))
        (x (trunc r k)))
    (implies (and (rationalp r)
                  (> r 0)
                  (not (zp n))
                  (natp k)
                  (< n k)
                  (<= k (1+ e))
                  (not (= r (trunc r n))))
             (equal (away r n) (fp+ (trunc x n) n))))
  :rule-classes ()
  :hints  (("Goal" :use ((:instance trunc-exactp-b (x r))
                         (:instance trunc-away (x r))))))

(defthm ru-6
  (let* ((e (expo r))
         (x (trunc r k))
         (s (if (< x r) 1 0)))
    (implies (and (rationalp r)
                  (> r 0)
                  (not (zp n))
                  (natp k)
                  (< n k)
                  (<= k (1+ e)))
             (iff (= r (trunc x n))
                  (and (= s 0) (= (bits x (- e n) 0) 0)))))
  :rule-classes ()
  :hints  (("Goal" :use (ru-3
                         (:instance trunc-upper-pos (x r) (n k))
                         (:instance trunc-upper-pos (x (trunc r k)))))))

(defthm ru-7
  (let* ((e (expo r))
         (x (trunc r k))
         (s (if (< x r) 1 0)))
    (implies (and (rationalp r)
                  (> r 0)
                  (not (zp n))
                  (natp k)
                  (< n k)
                  (<= k (1+ e)))
             (equal (away r n)
                    (if (and (= s 0) (= (bits x (- e n) 0) 0))
                        (trunc x n)
                      (fp+ (trunc x n) n)))))
  :rule-classes ()
  :hints  (("Goal" :use (ru-4 ru-5 ru-6))))

(defthm ru-8
  (implies (and (rationalp r)
                (> r 0)
                (not (zp n))
                (natp k)
                (< n k)
                (<= k (1+ (expo r))))
           (let* ((x (trunc r k))
                  (sticky (if (< x r) 1 0)))
	     (= (away r n)
                (if (round-up x sticky 'away n)
                    (fp+ (trunc r n) n)
                  (trunc r n)))))
  :rule-classes ()
  :hints (("Goal" :use (ru-7))))

#|

Let z = fl(2^(n-1) * sig(r)) and f = 2^(n-1) * sig(r) - z.

Then 2^(1+e-n) * z = trunc(r, n) and 2^(1+e-n) * f = r - trunc(r, n).

By bits-trunc (with n = 1+e and k = n),

  trunc(x, n) = 2^(1+e-n) * x[e:1+e-n]

and z = x[e:1+e-n], which implies that z is even <=> x[1+e-n] = 0.

|#

(defthm ru-9
  (let ((e (expo r))
        (z (fl (* (expt 2 (1- n)) (sig r)))))
    (implies (and (rationalp r)
                  (> r 0)
                  (not (zp n))
                  (natp k)
                  (< n k)
                  (<= k (1+ e)))
             (equal (* (expt 2 (- (1+ e) n))
                       z)
                    (trunc r n))))
  :rule-classes ()
  :hints  (("Goal" :in-theory (enable sgn trunc))))

(defthm ru-10
  (let ((e (expo r))
        (f (re (* (expt 2 (1- n)) (sig r)))))
    (implies (and (rationalp r)
                  (> r 0)
                  (not (zp n))
                  (natp k)
                  (< n k)
                  (<= k (1+ e)))
             (equal (* (expt 2 (- (1+ e) n))
                       f)
                    (- r (trunc r n)))))
  :rule-classes ()
  :hints  (("Goal" :use ((:instance fp-rep (x r)))
                   :in-theory (enable sgn trunc))))

(defthm ru-11
  (let ((e (expo r))
        (x (trunc r k)))
    (implies (and (rationalp r)
                  (> r 0)
                  (not (zp n))
                  (natp k)
                  (< n k)
                  (<= k (1+ e)))
             (equal (* (expt 2 (- (1+ e) n))
                       (bits x e (- (1+ e) n)))
                    (trunc x n))))
  :rule-classes ()
  :hints  (("Goal" :use ((:instance bits-trunc (x (trunc r k)) (n (1+ (expo r))) (k n))))))

(defthm ru-12
  (let ((e (expo r))
        (x (trunc r k))
        (z (fl (* (expt 2 (1- n)) (sig r)))))
    (implies (and (rationalp r)
                  (> r 0)
                  (not (zp n))
                  (natp k)
                  (< n k)
                  (<= k (1+ e)))
             (equal z (bits x e (- (1+ e) n)))))
  :rule-classes ()
  :hints  (("Goal" :use (ru-11 ru-9 (:instance sgn-trunc (x r)))
                   :in-theory (enable sgn))))

(defthm ru-13
  (implies (integerp m)
           (and (evenp (* 2 m))
                (not (evenp (1+ (* 2 m))))))
  :rule-classes ())

(defthm ru-14
  (let ((e (expo r))
        (x (trunc r k))
        (z (fl (* (expt 2 (1- n)) (sig r)))))
    (implies (and (rationalp r)
                  (> r 0)
                  (not (zp n))
                  (natp k)
                  (< n k)
                  (<= k (1+ e)))
             (iff (evenp z)
                  (= (bitn x (- (1+ e) n)) 0))))
  :rule-classes ()
  :hints  (("Goal" :in-theory (disable evenp)
                   :use (ru-12
                         (:instance ru-13 (m (bits (trunc r k) (expo r) (- (+ 2 (expo r)) n))))
                         (:instance bitn-0-1 (x (trunc r k)) (n (- (1+ (expo r)) n)))
                         (:instance bits-plus-bitn (x (trunc r k)) (n (expo r)) (m (- (1+ (expo r)) n)))))))

#|

By trunc-split (with n = e+1, m = 1+n, k = n),

  r - trunc(r, n) = (trunc(x, n+1) - trunc(x, n)) + (r - trunc(r, n+1))

                  = 2^(e-n) * x[e-n] + (r - trunc(r, n+1)).

Therefore,

  f = 2^(n-e-1) *(r -  trunc(r, n)) = 1/2 * x[e-n] + 2^(n-e-1) * (r - trunc(r, n+1)).

By trunc-diff (with x = r and n = n+1),

  2^(n-e-1) * (r - trunc(r, n+1)) < 2^(n-e-1) * 2^(e-n) = 1/2.

Thus,

  f >= 1/2 <=>  x[e-n] = 1

and

  f > 1/2 <=>  x[e-n] = 1 and r - trunc(r, n+1) > 0.

But by trunc-split (with n = 1+e, m = 1+e, k = n+1),

  r - trunc(r, n+1) = (r - x) + (x - trunc(r, n+1))

                    = (r - x) + (trunc(x, e+1) - trunc(x, n+1))

                    = (r - x) + x[e-1-n:0].

|#

(defthm ru-15
  (let ((e (expo r))
        (x (trunc r k)))
    (implies (and (rationalp r)
                  (> r 0)
                  (not (zp n))
                  (natp k)
                  (< n k)
                  (<= k (1+ e)))
             (equal (- r (trunc r n))
                    (+ (* (expt 2 (- e n)) (bitn x (- e n)))
                       (- r (trunc r (1+ n)))))))
  :rule-classes ()
  :hints  (("Goal" :use ((:instance trunc-split (x (trunc r k)) (n (1+ (expo r))) (m (1+ n)) (k n))))))

(defthm ru-16
  (implies (and (rationalp x)
                (rationalp y)
                (integerp n)
                (= x (* (expt 2 n) y)))
           (= y (* (expt 2 (- n)) x)))
  :rule-classes ())

(defthm ru-17
  (let ((e (expo r))
        (f (re (* (expt 2 (1- n)) (sig r)))))
    (implies (and (rationalp r)
                  (> r 0)
                  (not (zp n))
                  (natp k)
                  (< n k)
                  (<= k (1+ e)))
             (equal f (* (expt 2 (- n (1+ e))) (- r (trunc r n))))))
  :rule-classes ()
  :hints  (("Goal" :use (ru-10
                         (:instance ru-16 (x (- r (trunc r n)))
                                          (y (re (* (expt 2 (1- n)) (sig r))))
                                          (n (- (1+ (expo r)) n)))))))

(in-theory (disable re))

(defthm ru-18
  (let ((e (expo r))
        (x (trunc r k))
        (f (re (* (expt 2 (1- n)) (sig r)))))
    (implies (and (rationalp r)
                  (> r 0)
                  (not (zp n))
                  (natp k)
                  (< n k)
                  (<= k (1+ e)))
             (equal f
                    (+ (* 1/2 (bitn x (- e n)))
                       (* (expt 2 (- n (1+ (expo r))))
                          (- r (trunc r (1+ n))))))))
  :rule-classes ()
  :hints  (("Goal" :use (ru-17 ru-15))))

(defthm ru-19
  (let ((e (expo r)))
    (implies (and (rationalp r)
                  (> r 0)
                  (not (zp n))
                  (natp k)
                  (< n k)
                  (<= k (1+ e)))
             (< (- r (trunc r (1+ n)))
                (expt 2 (- e n)))))
  :rule-classes ()
  :hints  (("Goal" :use (:instance trunc-diff (x r) (n (1+ n))))))

(defthm ru-20
  (implies (and (rationalp x)
                (integerp m)
                (integerp n)
                (< x (expt 2 n)))
           (< (* x (expt 2 m)) (expt 2 (+ m n))))
  :rule-classes ())

(defthm ru-21
  (let ((e (expo r)))
    (implies (and (rationalp r)
                  (> r 0)
                  (not (zp n))
                  (natp k)
                  (< n k)
                  (<= k (1+ e)))
             (< (* (expt 2 (- n (1+ e)))
                   (- r (trunc r (1+ n))))
                1/2)))
  :rule-classes ()
  :hints  (("Goal" :use (ru-19
                         (:instance ru-20 (x (- r (trunc r (1+ n)))) (n (- (expo r) n)) (m (- n (1+ (expo r)))))))))

(defthm ru-23
  (let ((e (expo r))
        (x (trunc r k))
        (f (re (* (expt 2 (1- n)) (sig r)))))
    (implies (and (rationalp r)
                  (> r 0)
                  (not (zp n))
                  (natp k)
                  (< n k)
                  (<= k (1+ e))
                  (= (bitn x (- e n)) 0))
             (< f 1/2)))
  :rule-classes ()
  :hints  (("Goal" :use (ru-18 ru-21)
                   :in-theory
                   #!acl2(disable |(* x (+ y z))| |(* x (- y))|
                                  |(* x (expt x n))| |(* y x)|
                                  |(+ (+ x y) z)| |(+ 0 x)|
                                  NORMALIZE-FACTORS-GATHER-EXPONENTS
                                  SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))))

(defthm ru-24
  (let ((e (expo r)))
    (implies (and (rationalp r)
                  (> r 0)
                  (not (zp n))
                  (natp k)
                  (< n k)
                  (<= k (1+ e)))
             (>= (* (expt 2 (- n (1+ (expo r))))
                    (- r (trunc r (1+ n))))
                 0)))
  :rule-classes ()
  :hints  (("Goal" :use (:instance trunc-upper-pos (x r) (n (1+ n))))))


(defthm ru-25
  (let ((e (expo r))
        (x (trunc r k))
        (f (re (* (expt 2 (1- n)) (sig r)))))
    (implies (and (rationalp r)
                  (> r 0)
                  (not (zp n))
                  (natp k)
                  (< n k)
                  (<= k (1+ e))
                  (= (bitn x (- e n)) 1))
             (>= f 1/2)))
  :rule-classes ()
  :hints  (("Goal" :use (ru-18 ru-24)
                   :in-theory
                   #!acl2(disable |(* x (+ y z))| |(* x (- y))|
                                  |(* x (expt x n))| |(* y x)|
                                  |(+ (+ x y) z)| |(+ 0 x)|
                                  NORMALIZE-FACTORS-GATHER-EXPONENTS
                                  SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))))

(defthm ru-26
  (let ((e (expo r))
        (x (trunc r k))
        (f (re (* (expt 2 (1- n)) (sig r)))))
    (implies (and (rationalp r)
                  (> r 0)
                  (not (zp n))
                  (natp k)
                  (< n k)
                  (<= k (1+ e))
                  (= (bitn x (- e n)) 1))
             (iff (> f 1/2)
                  (> (* (expt 2 (- n (1+ (expo r))))
                        (- r (trunc r (1+ n))))
                     0))))
  :rule-classes ()
  :hints  (("Goal" :use (ru-18 ru-24)
                   :in-theory
                   #!acl2(disable |(* x (+ y z))| |(* x (- y))|
                                  |(* x (expt x n))| |(* y x)|
                                  |(+ (+ x y) z)| |(+ 0 x)|
                                  NORMALIZE-FACTORS-GATHER-EXPONENTS
                                  SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))))

(defthm ru-27
  (let ((e (expo r))
        (x (trunc r k))
        (f (re (* (expt 2 (1- n)) (sig r)))))
    (implies (and (rationalp r)
                  (> r 0)
                  (not (zp n))
                  (natp k)
                  (< n k)
                  (<= k (1+ e))
                  (= (bitn x (- e n)) 1))
             (iff (> f 1/2)
                  (> (- r (trunc r (1+ n)))
                     0))))
  :rule-classes ()
  :hints  (("Goal" :use (ru-26))))

(defthm ru-28
  (let ((e (expo r))
        (x (trunc r k))
        (f (re (* (expt 2 (1- n)) (sig r)))))
    (implies (and (rationalp r)
                  (> r 0)
                  (not (zp n))
                  (natp k)
                  (< n k)
                  (<= k (1+ e)))
             (and (iff (>= f 1/2)
                       (= (bitn x (- e n)) 1))
                  (iff (> f 1/2)
                       (and (= (bitn x (- e n)) 1)
                            (> (- r (trunc r (1+ n))) 0))))))
  :rule-classes ()
  :hints  (("Goal" :use (ru-23 ru-25 ru-27
                         (:instance bitn-0-1 (x (trunc r k)) (n (- (expo r) n)))))))

(defthm ru-29
  (let ((e (expo r))
        (x (trunc r k)))
    (implies (and (rationalp r)
                  (> r 0)
                  (not (zp n))
                  (natp k)
                  (< n k)
                  (<= k (1+ e)))
             (equal (- r (trunc r (1+ n)))
                    (+ (- r x) (bits x (- (1- e) n) 0)))))
  :rule-classes ()
  :hints  (("Goal" :use (ru-2
                         (:instance trunc-split (x (trunc r k)) (n (1+ (expo r))) (m (1+ (expo r))) (k (1+ n)))))))

(defthm ru-30
  (let* ((e (expo r))
         (x (trunc r k))
         (sticky (if (> r x) 1 0))
         (f (re (* (expt 2 (1- n)) (sig r)))))
    (implies (and (rationalp r)
                  (> r 0)
                  (not (zp n))
                  (natp k)
                  (< n k)
                  (<= k (1+ e)))
             (and (iff (>= f 1/2)
                       (= (bitn x (- e n)) 1))
                  (iff (> f 1/2)
                       (and (= (bitn x (- e n)) 1)
                            (or (= sticky 1) (not (= (bits x (- (1- e) n) 0) 0))))))))
  :rule-classes ()
  :hints  (("Goal" :use (ru-28 ru-29
                         (:instance trunc-upper-pos (x r) (n k))))))

(in-theory (disable evenp))

(defthm ru-31
  (implies (and (rationalp r)
                (> r 0)
                (not (zp n))
                (natp k)
                (< n k)
                (<= k (1+ (expo r))))
           (let* ((x (trunc r k))
                  (sticky (if (< x r) 1 0)))
	     (= (near r n)
                (if (round-up x sticky 'near n)
                    (fp+ (trunc r n) n)
                  (trunc r n)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable near)
                  :use (ru-14 ru-30 ru-8
                        (:instance bitn-bits (x (trunc r k)) (i (- (expo r) n)) (j 0) (k (- (expo r) n)))
                        (:instance bitn-0-1 (x (trunc r k)) (n (- (1+ (expo r)) n)))
                        (:instance bitn-0-1 (x (trunc r k)) (n (- (expo r) n)))))))

(defthm ru-32
  (implies (and (rationalp r)
                (> r 0)
                (not (zp n))
                (natp k)
                (< n k)
                (<= k (1+ (expo r))))
           (let* ((x (trunc r k))
                  (sticky (if (< x r) 1 0)))
	     (= (near+ r n)
                (if (round-up x sticky 'near+ n)
                    (fp+ (trunc r n) n)
                  (trunc r n)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable near+)
                  :use (ru-14 ru-30 ru-8
                        (:instance bitn-bits (x (trunc r k)) (i (- (expo r) n)) (j 0) (k (- (expo r) n)))
                        (:instance bitn-0-1 (x (trunc r k)) (n (- (1+ (expo r)) n)))
                        (:instance bitn-0-1 (x (trunc r k)) (n (- (expo r) n)))))))

(defthm ru-33
  (implies (and (rationalp r)
                (> r 0)
                (not (zp n))
                (natp k)
                (< n k)
                (<= k (1+ (expo r))))
           (let* ((x (trunc r k))
                  (sticky (if (< x r) 1 0)))
	     (= (inf r n)
                (if (round-up x sticky 'inf n)
                    (fp+ (trunc r n) n)
                  (trunc r n)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable inf)
                  :use (ru-8))))

(defthm ru-34
  (implies (and (rationalp r)
                (> r 0)
                (not (zp n))
                (natp k)
                (< n k)
                (<= k (1+ (expo r))))
           (let* ((x (trunc r k))
                  (sticky (if (< x r) 1 0)))
	     (= (minf r n)
                (if (round-up x sticky 'minf n)
                    (fp+ (trunc r n) n)
                  (trunc r n)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable minf)
                  :use (ru-0))))

(defthm round-up-thm
  (implies (and (common-rounding-mode-p mode)
                (rationalp r)
                (> r 0)
                (not (zp n))
                (natp k)
                (< n k)
                (<= k (1+ (expo r))))
           (let* ((x (trunc r k))
                  (sticky (if (< x r) 1 0)))
	     (= (rnd r mode n)
                (if (round-up x sticky mode n)
                    (fp+ (trunc r n) n)
                  (trunc r n)))))
  :rule-classes ()
  :hints (("Goal" :use (ru-0 ru-8 ru-31 ru-32 ru-33 ru-34)
                  :in-theory (e/d (rnd ieee-mode-p common-rounding-mode-p) (fp+ round-up)))))


