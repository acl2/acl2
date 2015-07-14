(in-package "RTL")

(local (include-book "../rel9-rtl-pkg/lib/top"))

(include-book "../rel9-rtl-pkg/lib/util")

(local (include-book "arithmetic-5/top" :dir :system))

;; The following lemmas from arithmetic-5 have given me trouble:

(local-in-theory #!acl2(disable |(mod (+ x y) z) where (<= 0 z)| |(mod (+ x (- (mod a b))) y)| |(mod (mod x y) z)| |(mod (+ x (mod a b)) y)|
                    simplify-products-gather-exponents-equal mod-cancel-*-const cancel-mod-+ reduce-additive-constant-< 
                    |(floor x 2)| |(equal x (if a b c))| |(equal (if a b c) x)|))

;; From basic.lisp:

(defund fl (x)
  (declare (xargs :guard (real/rationalp x)))
  (floor x 1))

;; From bits.lisp:

(defund bvecp (x k)
  (declare (xargs :guard (integerp k)))
  (and (integerp x)
       (<= 0 x)
       (< x (expt 2 k))))

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


;;---------------------------------------------------------------------------

#|
Lemma(exactp-factors): Assume that x and y are k-exact for some k.  If xy is non-zero and p-exact, then so are x and y.

Proof: Let m and n be the smallest integers such that x' = 2^n*x and y' = 2^m*y are integers.  Thus, x' and y' are odd.
Since x, y, or x*y, respectively, is p-exact iff x', y', or x'*y' is p-exact, we may replace x and y with
x' and y'.  That is, we may assume without loss of generality that x and y are odd integers.

An odd integer z is p-exact iff |z| < 2^p.  Thus, since xy is p-exact, xy < 2^p, which implies x < 2^p and
y < 2^p, and hence x and y are p-exact.
|#

(local-defun pow2 (n)
  (if (or (zp n) (oddp n))
      0
    (1+ (pow2 (/ n 2)))))

(local-defthmd pow2-oddp-1
  (implies (integerp n)
           (equal (expt 2 (1- n))
                  (* 1/2 (expt 2 n))))
  :hints (("Goal" :use ((:instance expt (r 2) (i n))
                        (:instance expt (r 2) (i (1- n)))))))

(local-defthm pow2-oddp
  (implies (not (zp n))
           (and (integerp (/ n (expt 2 (pow2 n))))
                (oddp (/ n (expt 2 (pow2 n))))))
  :rule-classes ()
  :hints (("Subgoal *1/3" :use ((:instance pow2-oddp-1 (n (- (pow2 (/ n 2)))))))
          ("Subgoal *1/2" :use ((:instance pow2-oddp-1 (n (- (pow2 (/ n 2)))))))))

(local-defthm exactp-factors-1
  (implies (and (integerp x) (integerp y))
           (integerp (* x y)))
  :rule-classes ())

(local-defthm exactp-factors-2
  (implies (and (integerp n) 
                (oddp n)
                (not (zp k)))
           (not (integerp (/ n (expt 2 k)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance pow2-oddp-1 (n k))
                        (:instance exactp-factors-1 (x (/ n (expt 2 k))) (y (expt 2 (1- k))))))))

(local-defthm exactp-factors-3
  (implies (and (integerp n)
                (integerp k) 
                (oddp n))
           (iff (integerp (* (expt 2 k) n))
                (>= k 0)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance exactp-factors-2 (k (- k)))))))

(local-defthm exactp-factors-4
  (implies (and (integerp n)
                (integerp k) 
                (oddp n))
           (iff (exactp n k)
                (> k (expo n))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance exactp-factors-3 (k (- (1- k) (expo n)))))
                  :in-theory (enable exactp2))))

(local-defthm exactp-factors-5
  (implies (and (integerp x)
                (integerp y) 
                (oddp x)
                (oddp y))
           (>= (expo (* x y)) (expo x)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance expo-monotone (y (* x y)))))))

(local-defthm exactp-factors-6
  (implies (integerp x)
           (iff (oddp x) (= (mod x 2) 1)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance fl-integerp (x (/ x 2)))
                        (:instance mod-def (y 2))
                        (:instance mod012 (m x)))
                  :in-theory (disable fl-integerp))))

(local-defthm exactp-factors-7
  (implies (and (integerp x)
                (integerp y) 
                (oddp x)
                (oddp y))
           (oddp (* x y)))
  :hints (("Goal" :use (exactp-factors-6
                        (:instance exactp-factors-6 (x y))
                        (:instance exactp-factors-6 (x (* x y)))
                        (:instance mod-mod-times (n 2) (a x) (b y))))))

(local-defthm exactp-factors-8
  (implies (and (integerp x)
                (integerp y) 
                (oddp x)
                (oddp y)
                (integerp k)
                (exactp (* x y) k))
           (exactp x k))
  :rule-classes ()
  :hints (("Goal" :use (exactp-factors-5
                        exactp-factors-7
                        (:instance exactp-factors-4 (n (* x y)))
                        (:instance exactp-factors-4 (n x))))))

(local-defthm exactp-factors-9
  (implies (and (rationalp x)
                (rationalp y)
                (integerp k)
                (integerp n)
                (not (zerop x))
                (not (zerop y))
                (exactp x k)
                (exactp y k))
           (let ((xp (/ (abs (* (expt 2 (- (1- k) (expo x))) x))
                        (expt 2 (pow2 (abs (* (expt 2 (- (1- k) (expo x))) x))))))
                 (yp (/ (abs (* (expt 2 (- (1- k) (expo y))) y))
                        (expt 2 (pow2 (abs (* (expt 2 (- (1- k) (expo y))) y)))))))
             (and (integerp xp)
                  (oddp xp)
                  (iff (exactp x n) (exactp xp n))
                  (integerp yp)
                  (oddp yp)
                  (iff (exactp x n) (exactp xp n))
                  (iff (exactp y n) (exactp yp n))
                  (iff (exactp (* x y) n) (exactp (* xp yp) n)))))                  
  :rule-classes ()
  :hints (("Goal" :in-theory (enable exactp2)
                  :use (exactp-minus
                        (:instance exactp-minus (x y))
                        (:instance exactp-minus (x (* x y)))
                        (:instance exactp-shift (x (abs x)) (k (- (1- k) (+ (expo x) (pow2 (abs (* (expt 2 (- (1- k) (expo x))) x)))))))
                        (:instance exactp-shift (x (abs y)) (k (- (1- k) (+ (expo y) (pow2 (abs (* (expt 2 (- (1- k) (expo y))) y)))))))
                        (:instance exactp-shift (x (abs (* x y)))
                                                (k (+ (- (1- k) (+ (expo x) (pow2 (abs (* (expt 2 (- (1- k) (expo x))) x)))))
                                                   (- (1- k) (+ (expo y) (pow2 (abs (* (expt 2 (- (1- k) (expo y))) y))))))))
                        (:instance pow2-oddp (n (abs (* (expt 2 (- (1- k) (expo x))) x))))
                        (:instance pow2-oddp (n (abs (* (expt 2 (- (1- k) (expo y))) y))))))))

(local-defthm exactp-factors
  (implies (and (rationalp x)
                (rationalp y)
                (integerp k)
                (integerp n)
                (not (zerop x))
                (not (zerop y))
                (exactp x k)
                (exactp y k)
                (exactp (* x y) n))
           (exactp x n))
  :rule-classes ()
  :hints (("Goal" :use (exactp-factors-9
                        (:instance exactp-factors-8 (k n)
                                                    (x (/ (abs (* (expt 2 (- (1- k) (expo x))) x))
                                                          (expt 2 (pow2 (abs (* (expt 2 (- (1- k) (expo x))) x))))))
                                                    (y (/ (abs (* (expt 2 (- (1- k) (expo y))) y))
                                                          (expt 2 (pow2 (abs (* (expt 2 (- (1- k) (expo y))) y)))))))))))

(local-defthmd expo-fp-
  (implies (and (rationalp x)
                (> x 0)
                (not (= x (expt 2 (expo x))))
                (integerp n)
                (> n 0)
                (exactp x n))
           (equal (expo (fp- x n)) (expo x)))
  :hints (("Goal" :use (expo-lower-bound expo-upper-bound
                        (:instance fp-2 (y (expt 2 (expo x))))
                        (:instance exactp-2**n (n (expo x)) (m n))
                        (:instance expo<= (x (fp- x n)) (n (expo x)))
                        (:instance expo>= (x (fp- x n)) (n (expo x)))))))


;;;**********************************************************************
;;;                 Sign, Significand, and Exponent
;;;**********************************************************************

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

(defthmd expo-lower-bound
    (implies (and (rationalp x)
		  (not (equal x 0)))
	     (<= (expt 2 (expo x)) (abs x)))
  :rule-classes :linear)

(defthmd expo-upper-bound
    (implies (and (rationalp x))
	     (< (abs x) (expt 2 (1+ (expo x)))))
  :rule-classes :linear)

(defthm expo-unique
  (implies (and (<= (expt 2 n) (abs x))
                (< (abs x) (expt 2 (1+ n)))
                (rationalp x)
                (integerp n))
           (equal n (expo x)))
  :rule-classes ())

(defthm fp-rep
    (implies (rationalp x)
	     (equal x (* (sgn x) (sig x) (expt 2 (expo x)))))
  :rule-classes ())

(defthm fp-abs
    (implies (rationalp x)
	     (equal (abs x) (* (sig x) (expt 2 (expo x)))))
  :rule-classes ())

(defthmd expo>=
    (implies (and (<= (expt 2 n) x)
                  (rationalp x)
		  (integerp n))
	     (<= n (expo x)))
  :rule-classes :linear)

(defthmd expo<=
    (implies (and (< x (* 2 (expt 2 n)))
                  (< 0 x)
                  (rationalp x)
		  (integerp n))
	     (<= (expo x) n))
  :rule-classes :linear)

(defthm expo-2**n
    (implies (integerp n)
	     (equal (expo (expt 2 n))
		    n)))

(defthmd expo-monotone
  (implies (and (<= (abs x) (abs y))
                (case-split (rationalp x))
                (case-split (not (equal x 0)))
                (case-split (rationalp y)))
           (<= (expo x) (expo y)))
  :rule-classes :linear)

(defthmd bvecp-expo
    (implies (case-split (natp x))
	     (bvecp x (1+ (expo x)))))

(defthmd mod-expo
  (implies (and (< 0 x)
                (rationalp x))
           (equal (mod x (expt 2 (expo x)))
                  (- x (expt 2 (expo x))))))

(defthmd sig-lower-bound
  (implies (and (rationalp x)
                (not (equal x 0)))
           (<= 1 (sig x)))
  :rule-classes (:rewrite :linear))

(defthmd sig-upper-bound
  (< (sig x) 2)
  :rule-classes (:rewrite :linear))

(defthmd sig-self
  (implies (and (rationalp x)
                (<= 1 x)
                (< x 2))
           (equal (sig x) x)))

(defthm sig-sig
    (equal (sig (sig x)) 
	   (sig x)))

(defthm expo-minus
  (implies (rationalp x)
           (equal (expo (- x)) (expo x)))
  :hints (("Goal" :in-theory (enable expo))))

(defthm sig-minus
  (implies (rationalp x)
           (equal (sig (- x)) (sig x)))
  :hints (("Goal" :in-theory (enable sig))))

(defthm expo-sig
  (implies (rationalp x)
           (equal (expo (sig x)) 0))
  :hints (("Goal" :in-theory (enable expo)
                  :use (sig-upper-bound sig-lower-bound))))

(defthm fp-rep-unique
    (implies (and (rationalp x)
		  (rationalp m)
		  (<= 1 m)
		  (< m 2)
		  (integerp e)
		  (= (abs x) (* m (expt 2 e))))
	     (and (= m (sig x))
		  (= e (expo x))))
  :rule-classes ())

(defthmd sgn-shift
  (equal (sgn (* x (expt 2 k)))
         (sgn x)))

(defthmd expo-shift
  (implies (and (rationalp x)
                (not (equal x 0))
                (integerp n))
           (equal (expo (* (expt 2 n) x)) 
                  (+ n (expo x)))))

(defthmd sig-shift
  (equal (sig (* (expt 2 n) x)) 
         (sig x)))

(defthmd sgn-prod
  (implies (and (case-split (rationalp x))
                (case-split (rationalp y)))
           (equal (sgn (* x y))
                  (* (sgn x) (sgn y)))))

(defthmd expo-prod
    (implies (and (rationalp x)
		  (not (= x 0))
		  (rationalp y)
		  (not (= y 0)))
	     (equal (expo (* x y))
		    (if (< (* (sig x) (sig y)) 2)
			(+ (expo x) (expo y))
		      (+ 1 (expo x) (expo y))))))

(defthmd expo-prod-lower
    (implies (and (rationalp x)
		  (not (= x 0))
		  (rationalp y)
		  (not (= y 0)))
	     (<= (+ (expo x) (expo y)) (expo (* x y))))
  :rule-classes :linear)

(defthmd expo-prod-upper
    (implies (and (rationalp x)
		  (not (= x 0))
		  (rationalp y)
		  (not (= y 0)))
	     (>= (+ (expo x) (expo y) 1) (expo (* x y))))
  :rule-classes :linear)

(defthmd sig-prod
    (implies (and (rationalp x)
		  (not (= x 0))
		  (rationalp y)
		  (not (= y 0)))
	     (equal (sig (* x y))
		    (if (< (* (sig x) (sig y)) 2)
			(* (sig x) (sig y))
		      (* 1/2 (sig x) (sig y))))))


;;;**********************************************************************
;;;                          Exactness
;;;**********************************************************************

(defund exactp (x n)
  (integerp (* (sig x) (expt 2 (1- n)))))

(defthmd exactp2
    (implies (and (rationalp x)
		  (integerp n))
	     (equal (exactp x n)
		    (integerp (* x (expt 2 (- (1- n) (expo x))))))))

(defthm exactp-sig
  (equal (exactp (sig x) n)
         (exactp x n)))

(defthm exactp-minus
  (equal (exactp (* -1 x) n)
         (exactp x n)))

(defthm minus-exactp
  (equal (exactp (- x) n)
         (exactp x n))
  :hints (("Goal" :use (exactp-minus))))

(defthm exactp-abs
  (equal (exactp (abs x) n)
         (exactp x n)))

(defthmd exactp-shift
  (implies (and (rationalp x)
                (integerp k)
                (integerp n))
           (equal (exactp (* (expt 2 k) x) n)
                  (exactp x n))))

(defthmd exactp-<=
    (implies (and (exactp x m)
                  (<= m n)
                  (rationalp x)
		  (integerp n)
		  (integerp m))
	     (exactp x n)))

(defthmd exactp-2**n
  (implies  (and (case-split (integerp m))
                 (case-split (> m 0)))
            (exactp (expt 2 n) m)))

(defthm bvecp-exactp
  (implies (bvecp x n)
           (exactp x n)))

(defthm exactp-prod
    (implies (and (rationalp x)
		  (rationalp y)
		  (integerp m)
		  (integerp n)
		  (exactp x m)
		  (exactp y n))
	     (exactp (* x y) (+ m n)))
  :rule-classes ())

(defthm exactp-x2
    (implies (and (rationalp x)
		  (integerp n)
		  (exactp (* x x) (* 2 n)))
	     (exactp x n))
  :rule-classes ())

(defthm exactp-factors
  (implies (and (rationalp x)
                (rationalp y)
                (integerp k)
                (integerp n)
                (not (zerop x))
                (not (zerop y))
                (exactp x k)
                (exactp y k)
                (exactp (* x y) n))
           (exactp x n))
  :rule-classes ())

(defthm exact-bits-1
  (implies (and (equal (expo x) (1- n))
                (rationalp x)
                (integerp k))
           (equal (integerp (/ x (expt 2 k)))
		  (exactp x (- n k))))
  :rule-classes ())

(defthm exact-bits-2
  (implies (and (equal (expo x) (1- n))
                (rationalp x)
                (<= 0 x)
                (integerp k)
                )
           (equal (integerp (/ x (expt 2 k)))
		  (equal (bits x (1- n) k)
                         (/ x (expt 2 k)))))
  :rule-classes ())

(defthm exact-bits-3
  (implies (integerp x)
           (equal (integerp (/ x (expt 2 k)))
		  (equal (bits x (1- k) 0)
                         0)))
  :rule-classes ())

(defthm exact-k+1
    (implies (and (natp n)
		  (natp x)
		  (= (expo x) (1- n))
		  (natp k)
		  (< k (1- n))
		  (exactp x (- n k)))
	     (iff (exactp x (1- (- n k)))
		  (= (bitn x k) 0)))
  :rule-classes ())

(defthm exactp-diff
    (implies (and (rationalp x)
		  (rationalp y)
		  (integerp k)
		  (integerp n)
		  (> n 0)
		  (> n k)
		  (exactp x n)
		  (exactp y n)
		  (<= (+ k (expo (- x y))) (expo x))
		  (<= (+ k (expo (- x y))) (expo y)))
	     (exactp (- x y) (- n k)))
  :rule-classes ())

(defthm exactp-diff-cor
    (implies (and (rationalp x)
		  (rationalp y)
		  (integerp n)
		  (> n 0)
		  (exactp x n)
		  (exactp y n)
		  (<= (abs (- x y)) (abs x))
		  (<= (abs (- x y)) (abs y)))
	     (exactp (- x y) n))
  :rule-classes ())

(defun fp+ (x n)
  (+ x (expt 2 (- (1+ (expo x)) n))))

(defthm fp+-positive
  (implies (<= 0 x)
           (< 0 (fp+ x n)))
  :rule-classes :type-prescription)

(defthm fp+1
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0)
		  (exactp x n))
	     (exactp (fp+ x n) n))
  :rule-classes ())

(defthm fp+2
    (implies (and (rationalp x)
		  (> x 0)
		  (rationalp y)
		  (> y x)
		  (integerp n)
		  (> n 0)
		  (exactp x n)
		  (exactp y n))
	     (>= y (fp+ x n)))
  :rule-classes ())

(defthm fp+expo
    (implies (and (rationalp x)
		  (> x 0)
		  (integerp n)
		  (> n 0)
		  (exactp x n)
  		  (not (= (expo (fp+ x n)) (expo x))))
	     (equal (fp+ x n) (expt 2 (1+ (expo x)))))
  :rule-classes ())

(defthm expo-diff-min
    (implies (and (rationalp x)
		  (rationalp y)
		  (integerp n)
		  (> n 0)
		  (exactp x n)
		  (exactp y n)
		  (not (= y x)))
	     (>= (expo (- y x)) (- (1+ (min (expo x) (expo y))) n)))
  :rule-classes ())

(defun fp- (x n)
  (if (= x (expt 2 (expo x)))
      (- x (expt 2 (- (expo x) n)))
    (- x (expt 2 (- (1+ (expo x)) n)))))

(defthm fp--non-negative
   (implies (and (rationalp x)
                 (integerp n)
                 (> n 0)
                 (> x 0))
            (and (rationalp (fp- x n))
                 (< 0 (fp- x n))))
   :rule-classes :type-prescription)

(defthm exactp-fp-
  (implies (and (rationalp x)
                (> x 0)
                (integerp n)
                (> n 0)
                (exactp x n))
           (exactp (fp- x n) n))
  :hints (("Goal" :use (fp-1))))

(defthm fp+-
  (implies (and (rationalp x)
                (> x 0)
                (integerp n)
                (> n 0)
                (exactp x n))
           (equal (fp+ (fp- x n) n)
                  x)))

(defthm fp-+
  (implies (and (rationalp x)
                (> x 0)
                (integerp n)
                (> n 0)
                (exactp x n))
           (equal (fp- (fp+ x n) n)
                  x)))

(defthm fp-2
  (implies (and (rationalp x)
                (rationalp y)
                (> y 0)
                (> x y)
                (integerp n)
                (> n 0)
                (exactp x n)
                (exactp y n))
           (<= y (fp- x n)))
  :rule-classes ())

 (defthmd expo-fp-
   (implies (and (rationalp x)
                 (> x 0)
                 (not (= x (expt 2 (expo x))))
                 (integerp n)
                 (> n 0)
                 (exactp x n))
            (equal (expo (fp- x n)) (expo x))))
