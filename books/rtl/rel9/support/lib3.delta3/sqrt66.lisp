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

(in-package "ACL2")
(local (include-book "../lib3/top"))


(defund fl (x)
  (declare (xargs :guard (real/rationalp x)))
  (floor x 1))

(defund cg (x)
  (declare (xargs :guard (real/rationalp x)))
  (- (fl (- x))))


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

(defund away (x n)
  (* (sgn x)
     (cg (* (expt 2 (1- n)) (sig x)))
     (expt 2 (- (1+ (expo x)) n))))

(defund trunc (x n)
  (declare (xargs :guard (integerp n)))
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

(defund exactp (x n)
  (integerp (* (sig x) (expt 2 (1- n)))))

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


(include-book "../lib3/util")

(local (include-book "arithmetic-5/top" :dir :system))



(defund trunc-sqrt (x n)
  (if (zp n)
      0
    (let* ((lower (trunc-sqrt x (1- n)))
           (upper (+ lower (expt 2 (- n)))))
      (if (<= (* upper upper) x)
          upper
        lower))))

(defund sticky-sqrt (x n)
  (let ((trunc (trunc-sqrt x (1- n))))
    (if (< (* trunc trunc) x)
        (+ trunc (expt 2 (- n)))
      trunc)))

(local-in-theory (enable trunc-sqrt sticky-sqrt))

(defund qsqrt (x n)
  (let ((e (1+ (fl (/ (expo x) 2)))))
    (* (expt 2 e)
       (sticky-sqrt (/ x (expt 2 (* 2 e))) n))))

(defthmd qsqrt-pos
  (implies (and (rationalp x)
                (> x 0))
           (> (qsqrt x n) 0))
  :hints (("Goal" :in-theory (enable qsqrt))))

(defthmd qsqrt-shift
  (implies (and (rationalp x)
                (> x 0)
                (integerp k)
                (integerp n)
                (> n 1))
           (equal (qsqrt (* (expt 2 (* 2 k)) x) n)
                  (* (expt 2 k) (qsqrt x n))))
  :hints (("Goal" :use ((:instance expo-shift (n (* 2 k)))
                        (:instance fl+int-rewrite (n k) (x (/ (expo x) 2))))
                  :in-theory (e/d (qsqrt) (fl+int-rewrite sticky-sqrt)))))

(local-defthm trunc-sqrt-bounds-1
  (implies (and (rationalp x)
                (<= 1/4 x))
           (= (trunc-sqrt x 1) 1/2))
  :rule-classes ()
  :hints (("Goal" :use (:instance trunc-sqrt (n 1)))))

(local-defthm trunc-sqrt-bounds-2
  (implies (and (rationalp x)
                (not (zp n)))
           (< (+ x (expt 2 (- n)))
              (+ x (expt 2 (- 1 n)))))
:rule-classes ())

(local-defthm trunc-sqrt-bounds-3
  (implies (and (rationalp x)
                (rationalp y)
                (< x y)
                (<= y 1))
           (<= x 1))
:rule-classes ())

(local-defthm trunc-sqrt-bounds-4
  (implies (and (rationalp x)
                (not (zp n))
                (<= (+ (expt 2 (+ 1 (- n))) x) 1))
           (<= (+ (expt 2 (- n)) x) 1))
  :rule-classes ()
  :hints (("Goal" :use (trunc-sqrt-bounds-2
                        (:instance trunc-sqrt-bounds-3 (x (+ x (expt 2 (- n))))
                                                       (y (+ x (expt 2 (- 1 n)))))))))

(defthm trunc-sqrt-bounds
  (implies (and (rationalp x)
                (<= 1/4 x)
                (not (zp n)))
           (and (<= 1/2 (trunc-sqrt x n))
                (<= (trunc-sqrt x n) (- 1 (expt 2 (- n))))))
  :rule-classes ()
  :hints (("Subgoal *1/2" :use (trunc-sqrt-bounds-1
                                (:instance trunc-sqrt-bounds-4 (x (trunc-sqrt x (1- n))))))))


(defthm expo-trunc-sqrt
  (implies (and (rationalp x)
                (<= 1/4 x)
                (not (zp n)))
           (equal (expo (trunc-sqrt x n))
                  -1))
  :hints (("Goal" :use (trunc-sqrt-bounds
                        (:instance expo-unique (x (trunc-sqrt x n)) (n -1))))))

(local-defthm exactp-trunc-sqrt-1
  (implies (integerp x)
           (integerp (* 2 x)))
  :rule-classes ())

(local-defthm exactp-trunc-sqrt-2
  (implies (and (rationalp x)
                (natp n)
                (integerp (* (expt 2 (+ -1 n)) x)))
           (integerp (* (expt 2 n) x)))
  :hints (("Goal" :use (:instance exactp-trunc-sqrt-1 (x (* (expt 2 (+ -1 n)) x))))))

(local-defthm exactp-trunc-sqrt-3
  (implies (and (rationalp x)
                (<= 1/4 x)
                (not (zp n)))
           (integerp (* (trunc-sqrt x n) (expt 2 n))))
  :rule-classes ())

(defthm exactp-trunc-sqrt
  (implies (and (rationalp x)
                (<= 1/4 x)
                (not (zp n)))
           (exactp (trunc-sqrt x n)
                   n))
  :rule-classes ()
  :hints (("Goal" :in-theory (e/d (exactp2) (trunc-sqrt))
                  :use exactp-trunc-sqrt-3)))

(local-defthmd trunc-trunc-sqrt-1
  (implies (and (rationalp x)
                (<= 1/4 x)
                (not (zp n))
                (> n 1))
           (and (<= (trunc-sqrt x (1- n))
                    (trunc-sqrt x n))
                (< (trunc-sqrt x n)
                   (+ (trunc-sqrt x (1- n))
                      (expt 2 (- 1 n))))))
  :hints (("Goal" :expand ((trunc-sqrt x n)))))


(local-defthmd trunc-trunc-sqrt-2
  (implies (and (rationalp x)
                (<= 1/4 x)
                (not (zp n))
                (> n 1))
           (equal (trunc (trunc-sqrt x n) (+ -1 n))
                  (trunc-sqrt x (1- n))))
  :hints (("Goal" :in-theory (disable trunc-sqrt)
                  :use (trunc-trunc-sqrt-1
                        trunc-sqrt-bounds
                        (:instance trunc-sqrt-bounds (n (1- n)))
                        (:instance exactp-trunc-sqrt (n (1- n)))
                        (:instance trunc-upper-pos (x (trunc-sqrt x n)) (n (1- n)))
                        (:instance trunc-exactp-a (x (trunc-sqrt x n)) (n (1- n)))
                        (:instance trunc-exactp-c (a (trunc-sqrt x (1- n))) (x (trunc-sqrt x n)) (n (1- n)))
                        (:instance fp+2 (n (1- n)) (x (trunc-sqrt x (1- n))) (y (trunc (trunc-sqrt x n) (1- n))))))))

(local-defun natp-induct (n)
  (if (zp n)
      ()
    (1+ (natp-induct (1- n)))))

(local-defthmd trunc-trunc-sqrt-3
  (implies (and (rationalp x)
                (<= 1/4 x)
                (not (zp m))
                (natp n)
                (> n m))
           (equal (trunc (trunc-sqrt x n) m)
                  (trunc-sqrt x m)))
  :hints (("Goal" :induct (natp-induct n))
          ("Subgoal *1/2" :in-theory (disable trunc-sqrt)
                         :use (trunc-trunc-sqrt-2
                               (:instance trunc-trunc (x (trunc-sqrt x n)) (n (1- n)))))))

(defthmd trunc-trunc-sqrt
  (implies (and (rationalp x)
                (<= 1/4 x)
                (not (zp m))
                (natp n)
                (>= n m))
           (equal (trunc (trunc-sqrt x n) m)
                  (trunc-sqrt x m)))
  :hints (("Goal" :in-theory (disable trunc-sqrt)
                         :use (trunc-trunc-sqrt-3
                               exactp-trunc-sqrt
                               (:instance trunc-exactp-b (x (trunc-sqrt x n)))
                               (:instance trunc-trunc (x (trunc-sqrt x n)) (n (1- n)))))))

(defthm trunc-sqrt-square-bounds
  (implies (and (not (zp n))
                (rationalp x)
                (<= 1/4 x)
                (< x 1))
           (and (<= (* (trunc-sqrt x n)
                       (trunc-sqrt x n))
                    x)
                (< x
                   (* (+ (trunc-sqrt x n) (expt 2 (- n)))
                      (+ (trunc-sqrt x n) (expt 2 (- n)))))))
  :rule-classes ())

(local-defthm square-leq-1
  (implies (and (rationalp x)
                (rationalp y)
                (> y 0))
           (iff (> x 0) (> (* x y) 0)))
  :rule-classes ())

(defthm square-leq
  (implies (and (rationalp x)
                (rationalp y)
                (>= x 0)
                (>= y 0))
           (iff (<= (* x x) (* y y))
                (<= x y)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance square-leq-1 (x (- x y)) (y (+ x y)))))))

(local-defthm trunc-sqrt-unique-1
  (implies (and (not (zp n))
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (rationalp a)
                (exactp a n)
                (>= a 1/2)
                (<= (* a a) x)
                (< x (* (+ a (expt 2 (- n))) (+ a (expt 2 (- n))))))
           (= (expo a) -1))
  :rule-classes ()
  :hints (("Goal" :use ((:instance expo-unique (x a) (n -1))
                        (:instance square-leq (y a) (x 2))))))

(defthm trunc-sqrt-unique
  (implies (and (not (zp n))
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (rationalp a)
                (exactp a n)
                (>= a 1/2)
                (<= (* a a) x)
                (< x (* (+ a (expt 2 (- n))) (+ a (expt 2 (- n))))))
           (= a (trunc-sqrt x n)))
  :rule-classes ()
  :hints (("Goal" :use (trunc-sqrt-unique-1
                        trunc-sqrt-square-bounds
                        exactp-trunc-sqrt
                        trunc-sqrt-bounds
                        (:instance square-leq (x (+ a (expt 2 (- n)))) (y (trunc-sqrt x n)))
                        (:instance square-leq (x (+ (trunc-sqrt x n) (expt 2 (- n)))) (y a))
                        (:instance fp+2 (x a) (y (trunc-sqrt x n)))
                        (:instance fp+2 (y a) (x (trunc-sqrt x n)))))))

(local-defthm sticky-sqrt-bounds-1
  (implies (and (rationalp x)
                (integerp a)
                (integerp b)
                (< b a)
                (<= (+ (expt 2 a) x) 1))
           (< (+ (expt 2 b) x) 1))
  :rule-classes ())

(defthm sticky-sqrt-bounds
  (implies (and (rationalp x)
                (<= 1/4 x)
                (natp n)
                (>= n 2))
           (and (<= 1/2 (sticky-sqrt x n))
                (< (sticky-sqrt x n) 1)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance trunc-sqrt-bounds (n (1- n)))
                        (:instance sticky-sqrt-bounds-1 (x (trunc-sqrt x (1- n)))
                                                   (a (- 1 n))
                                                   (b (- n)))))))

(defthm expo-sticky-sqrt
  (implies (and (rationalp x)
                (<= 1/4 x)
                (natp n)
                (>= n 2))
           (equal (expo (sticky-sqrt x n))
                  -1))
  :hints (("Goal" :use (sticky-sqrt-bounds
                        (:instance expo-unique (x (sticky-sqrt x n)) (n -1))))))

(local-defthm exactp-sticky-sqrt-1
  (implies (and (rationalp x)
                (<= 1/4 x)
                (natp n)
                (>= n 2)
                (integerp (* (sticky-sqrt x n) (expt 2 n))))
           (exactp (sticky-sqrt x n) n))
  :rule-classes ()
  :hints (("Goal" :in-theory (e/d (exactp2) (sticky-sqrt)))))

(local-defthm exactp-sticky-sqrt-2
  (implies (and (rationalp x)
                (<= 1/4 x)
                (natp n)
                (>= n 2))
           (integerp (* (sticky-sqrt x n) (expt 2 n))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable exactp2)
                  :use ((:instance exactp-trunc-sqrt (n (1- n)))))))

(defthmd exactp-sticky-sqrt
  (implies (and (rationalp x)
                (<= 1/4 x)
                (natp n)
                (>= n 2))
           (exactp (sticky-sqrt x n) n))
  :hints (("Goal" :use (exactp-sticky-sqrt-1 exactp-sticky-sqrt-2)
                  :in-theory (disable sticky-sqrt))))

(local-defthm sticky-sqrt-lower-1
  (implies (and (natp n)
                (>= n 2)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (rationalp l)
                (<= (* l l) x)
                (= (* (trunc-sqrt x (1- n)) (trunc-sqrt x (1- n ))) x))
           (<= (* l l) (* (sticky-sqrt x n) (sticky-sqrt x n))))
  :rule-classes ())

(local-defthm sticky-sqrt-lower-4
  (implies (and (natp n)
                (>= n 2)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (rationalp l)
                (<= (* l l) x)
                (= (* (trunc-sqrt x (1- n)) (trunc-sqrt x (1- n))) x))
           (<= (* l l) (* (sticky-sqrt x n) (sticky-sqrt x n))))
  :rule-classes ())

(local-defthm sticky-sqrt-lower-5
  (implies (and (natp n)
                (>= n 2)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (rationalp l)
                (<= (* l l) x)
                (= (* (trunc-sqrt x (1- n)) (trunc-sqrt x (1- n))) x))
           (<= l (sticky-sqrt x n)))
  :rule-classes ()
  :hints (("Goal" :use (sticky-sqrt-lower-4
                        (:instance square-leq  (x l) (y (sticky-sqrt x n)))))))

(local-defthm sticky-sqrt-lower-6
  (implies (and (natp n)
                (>= n 2)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (rationalp l)
                (<= (* l l) x)
                (= (* (trunc-sqrt x (1- n)) (trunc-sqrt x (1- n))) x))
           (<= (sticky l n)
               (sticky-sqrt x n)))
  :rule-classes ()
  :hints (("Goal" :use (sticky-sqrt-lower-5
                        (:instance exactp-trunc-sqrt (n (1- n)))
                        (:instance exactp-<= (x (trunc-sqrt x (1- n))) (m (1- n)))
                        (:instance sticky-monotone (x l) (y (sticky-sqrt x n)))
                        (:instance sticky-exactp-b (x (sticky-sqrt x n)))))))

(local-defthm sticky-sqrt-lower-7
  (implies (and (rationalp x)
                (rationalp y)
                (>= x 0)
                (>= y 0))
           (>= (* x y) 0))
  :rule-classes ())

(local-defthm sticky-sqrt-lower-8
  (implies (and (rationalp x)
                (rationalp y)
                (< (* x x) (* y y))
                (>= y 0))
           (< x y))
  :rule-classes ()
  :hints (("Goal" :use ((:instance sticky-sqrt-lower-7 (x (- x y)) (y (+ x y)))))))

(local-defthm sticky-sqrt-lower-9
  (implies (and (natp n)
                (>= n 2)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (rationalp l)
                (<= (* l l) x)
                (< (* (trunc-sqrt x (1- n)) (trunc-sqrt x (1- n))) x))
           (< l (fp+ (trunc-sqrt x (1- n)) (1- n))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance trunc-sqrt-square-bounds (n (1- n)))
                        (:instance sticky-sqrt-lower-8 (x l)
                                                   (y (+ (trunc-sqrt x (1- n)) (expt 2 (- 1 n)))))))))

(local-defthm sticky-sqrt-lower-10
  (implies (and (natp n)
                (>= n 2)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (rationalp l)
                (<= (* l l) x)
                (< (* (trunc-sqrt x (1- n)) (trunc-sqrt x (1- n))) x))
           (<= (trunc l (1- n))
               (trunc-sqrt x (1- n))))
  :rule-classes ()
  :hints (("Goal" :use (sticky-sqrt-lower-9
                        (:instance trunc-sqrt-bounds (n (1- n)))
                        (:instance exactp-trunc-sqrt (n (1- n)))
                        (:instance trunc-upper-pos (x l) (n (1- n)))
                        (:instance trunc-exactp-a (x l) (n (1- n)))
                        (:instance fp+2 (y (trunc l (1- n))) (x (trunc-sqrt x (1- n))) (n (1- n)))))))

(local-defthm sticky-sqrt-lower-11
  (implies (and (natp n)
                (>= n 2)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (rationalp l)
                (<= (* l l) x)
                (exactp l (1- n))
                (< (* (trunc-sqrt x (1- n)) (trunc-sqrt x (1- n))) x))
           (<= (sticky l n)
               (sticky-sqrt x n)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable sticky)
                  :use (sticky-sqrt-lower-10
                        (:instance trunc-exactp-b (x l) (n (1- n)))))))


(local-defthm sticky-sqrt-lower-12
  (implies (and (natp n)
                (>= n 2)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (rationalp l)
                (> l 0)
                (<= (* l l) x)
                (< (* (trunc-sqrt x (1- n)) (trunc-sqrt x (1- n))) x))
           (<= (expo l) -1))
  :rule-classes ()
  :hints (("Goal" :use (sticky-sqrt-lower-10
                        (:instance expo-monotone (x (trunc l (1- n))) (y (trunc-sqrt x (1- n))))))))

(local-defthm sticky-sqrt-lower-13
  (implies (and (integerp a)
                (integerp b)
                (<= a b))
           (<= (expt 2 a) (expt 2 b)))
  :rule-classes ())


(local-defthm sticky-sqrt-lower-14
  (implies (and (natp n)
                (>= n 2)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (rationalp l)
                (> l 0)
                (<= (* l l) x)
                (< (* (trunc-sqrt x (1- n)) (trunc-sqrt x (1- n))) x))
           (<= (EXPT 2 (+ 1 (- N) (EXPO L)))
               (EXPT 2 (- N))))
  :rule-classes ()
  :hints (("Goal" :use (sticky-sqrt-lower-12
                        (:instance sticky-sqrt-lower-13 (a (+ 1 (- N) (EXPO L))) (b (- N)))))))

(local-defthm sticky-sqrt-lower-15
  (implies (and (rationalp a)
                (rationalp b)
                (<= a b)
                (rationalp c)
                (rationalp d)
                (<= c d))
           (<= (+ a c) (+ b d)))
  :rule-classes ())

(local-defthm sticky-sqrt-lower-16
  (implies (and (natp n)
                (>= n 2)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (rationalp l)
                (> l 0)
                (<= (* l l) x)
                (< (* (trunc-sqrt x (1- n)) (trunc-sqrt x (1- n))) x))
           (<= (+ (TRUNC L (+ -1 N)) (EXPT 2 (+ 1 (- N) (EXPO L))))
               (+ (TRUNC-SQRT x (1- N)) (EXPT 2 (- N)))))
  :rule-classes ()
  :hints (("Goal" :use (sticky-sqrt-lower-10
                        sticky-sqrt-lower-14
                        (:instance sticky-sqrt-lower-15 (a (TRUNC L (+ -1 N)))
                                                    (b (TRUNC-SQRT x (1- N)))
                                                    (c (EXPT 2 (+ 1 (- N) (EXPO L))))
                                                    (d (EXPT 2 (- N))))))))

(local-defthm sticky-sqrt-lower-17
  (implies (and (natp n)
                (>= n 2)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (rationalp l)
                (<= (* l l) x)
                (not (exactp l (1- n)))
                (>= l 0)
                (< (* (trunc-sqrt x (1- n)) (trunc-sqrt x (1- n))) x))
           (<= (sticky l n)
               (sticky-sqrt x n)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable sgn sticky)
                  :use (sticky-sqrt-lower-16))))

(local-defthm sticky-sqrt-lower-18
  (implies (and (natp n)
                (>= n 2)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (rationalp l)
                (<= (* l l) x)
                (not (exactp l (1- n)))
                (< l 0)
                (< (* (trunc-sqrt x (1- n)) (trunc-sqrt x (1- n))) x))
           (<= (sticky l n)
               (sticky-sqrt x n)))
  :rule-classes ()
  :hints (("Goal" :use (sticky-sqrt-lower-1
                        (:instance sticky-negative (x l))))))

(defthm sticky-sqrt-lower
  (implies (and (natp n)
                (>= n 2)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (rationalp l)
                (<= (* l l) x))
           (<= (sticky l n)
               (sticky-sqrt x n)))
  :rule-classes ()
  :hints (("Goal" :use (sticky-sqrt-lower-6
                        sticky-sqrt-lower-11
                        sticky-sqrt-lower-17
                        sticky-sqrt-lower-18
                        (:instance trunc-sqrt-square-bounds (n (1- n)))))))

#|
Proof: Let a = trunc-sqrt(n-2, x) and r = sticky-sqrt(x, n).
Suppose a^2 = x.  Then r = a, l^2 <= x = a^2 = r^2, and l <= r.
By sticky-monotone, sticky-exactp-b, and exactp-trunc-sqrt,

  sticky(l, n) <= sticky(r, n) = r.

Thus, we may assume a^2 < x and r = a + 2^(1-n).  By trunc-sqrt-square-bounds,
l^2 <= x < (a + 2^(2-n))^2, and hence l < a + 2^(2-n) = fp+(a, n-1).
It follows from trunc-upper-pos, trunc-exactp-a, and fp+2 that
trunc(l, n-1) <= a.  Thus,

  sticky(l, n) <= trunc(l, n-1) + 2^(1+expo(l)-n)
               <= a + 2^(1-n)
                = r.
|#

(local-defthm sticky-sqrt-upper-1
  (implies (and (natp n)
                (>= n 2)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (rationalp h)
                (>= h 0)
                (>= (* h h) x)
                (= x (* (trunc-sqrt x (1- n)) (trunc-sqrt x (1- n)))))
           (>= h (sticky-sqrt x n)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance square-leq (x (sticky-sqrt x n)) (y h))))))

(local-defthm sticky-sqrt-upper-2
  (implies (and (natp n)
                (>= n 2)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (rationalp h)
                (>= h 0)
                (>= (* h h) x)
                (= x (* (trunc-sqrt x (1- n)) (trunc-sqrt x (1- n)))))
           (>= (sticky h n)
               (sticky-sqrt x n)))
  :rule-classes ()
  :hints (("Goal" :use (sticky-sqrt-upper-1
                        (:instance exactp-trunc-sqrt (n (1- n)))
                        (:instance exactp-<= (x (trunc-sqrt x (1- n))) (m (1- n)))
                        (:instance sticky-monotone (x (sticky-sqrt x n)) (y h))
                        (:instance sticky-exactp-b (x (sticky-sqrt x n)))))))

(local-defthm sticky-sqrt-upper-3
  (implies (and (natp n)
                (>= n 2)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (rationalp h)
                (>= h 0)
                (>= (* h h) x)
                (>= h (sticky-sqrt x n))
                (> x (* (trunc-sqrt x (1- n)) (trunc-sqrt x (1- n)))))
           (>= (sticky h n)
               (sticky-sqrt x n)))
  :rule-classes ()
  :hints (("Goal" :use (sticky-sqrt-lower-1
                        exactp-sticky-sqrt
                        (:instance sticky-monotone (x (sticky-sqrt x n)) (y h))
                        (:instance sticky-exactp-b (x (sticky-sqrt x n)))))))

(local-defthm sticky-sqrt-upper-4
  (implies (and (natp n)
                (>= n 2)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (rationalp h)
                (>= h 0)
                (>= (* h h) x)
                (< h (sticky-sqrt x n))
                (> x (* (trunc-sqrt x (1- n)) (trunc-sqrt x (1- n)))))
           (> h (trunc-sqrt x (1- n))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance trunc-sqrt-square-bounds (n (- n 2)))
                        (:instance square-leq (x (trunc-sqrt x (1- n))) (y h))))))

(local-defthm sticky-sqrt-upper-5
  (implies (and (natp n)
                (>= n 2)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (rationalp h)
                (>= h 0)
                (>= (* h h) x)
                (< h (sticky-sqrt x n))
                (> x (* (trunc-sqrt x (1- n)) (trunc-sqrt x (1- n)))))
           (>= (trunc h (1- n)) (trunc-sqrt x (1- n))))
  :rule-classes ()
  :hints (("Goal" :use (sticky-sqrt-upper-4
                        (:instance exactp-trunc-sqrt (n (1- n)))
                        (:instance trunc-exactp-c (a (trunc-sqrt x (1- n))) (x h) (n (1- n)))))))

(local-defthm sticky-sqrt-upper-6
  (implies (and (natp n)
                (>= n 2)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (rationalp h)
                (>= h 0)
                (>= (* h h) x)
                (< h (sticky-sqrt x n))
                (> x (* (trunc-sqrt x (1- n)) (trunc-sqrt x (1- n)))))
           (not (exactp h (1- n))))
  :rule-classes ()
  :hints (("Goal" :use (sticky-sqrt-upper-4
                        (:instance trunc-sqrt-bounds (n (1- n)))
                        (:instance exactp-trunc-sqrt (n (1- n)))
                        (:instance exactp-<= (x (trunc-sqrt x (1- n))) (m (1- n)))
                        (:instance exactp-<= (x h) (m (1- n)))
                        (:instance fp+2 (x (trunc-sqrt x (1- n))) (y h))))))

(local-defthm sticky-sqrt-upper-7
  (implies (and (natp n)
                (>= n 2)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (rationalp h)
                (>= h 0)
                (>= (* h h) x)
                (< h (sticky-sqrt x n))
                (> x (* (trunc-sqrt x (1- n)) (trunc-sqrt x (1- n)))))
           (equal (expo h) -1))
  :hints (("Goal" :use (sticky-sqrt-upper-4
                        sticky-sqrt-bounds
                        (:instance trunc-sqrt-bounds (n (1- n)))
                        (:instance expo-unique (x h) (n -1))))))

(local-defthm sticky-sqrt-upper-8
  (implies (and (natp n)
                (>= n 2)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (rationalp h)
                (>= h 0)
                (>= (* h h) x)
                (< h (sticky-sqrt x n))
                (> x (* (trunc-sqrt x (1- n)) (trunc-sqrt x (1- n)))))
           (>= (sticky h n)
               (sticky-sqrt x n)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable sgn sticky)
                  :use (sticky-sqrt-upper-6
                        sticky-sqrt-upper-5))))

(defthm sticky-sqrt-upper
  (implies (and (natp n)
                (>= n 2)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (rationalp h)
                (>= h 0)
                (>= (* h h) x))
           (>= (sticky h n)
               (sticky-sqrt x n)))
  :rule-classes ()
  :hints (("Goal" :use (sticky-sqrt-upper-2
                        sticky-sqrt-upper-3
                        sticky-sqrt-upper-8
                        (:instance trunc-sqrt-square-bounds (n (1- n)))))))

#|
Proof: Let a = trunc-sqrt(x, n-1) and r = sticky-sqrt(x, n).
We may assume that h < r; otherwise, by sticky-monotone,
sticky-exactp-b, and exactp-trunc-sqrt,

  sticky(h, n) >= sticky(r, n) = r.

If a^2 = x, then r = a, h^2 >= x = a^2 = r^2, and h >= r.
Thus, by trunc-sqrt-square-bounds, a^2 < x and r = a + 2^(1-n) = fp+(a, n).
Since h^2 >= x > a^2, h > a.  It follows from trunc-exactp-c that
trunc(h, n-1) >= a.  By fp+2, h is not n-exact, and hence

  sticky(h, n) = trunc(h, n-1) + 2^(1-n)
              >= a + 2^(1-n)
               = r.
|#

(in-theory (disable trunc-sqrt sticky-sqrt))

(local-defthm sticky-sticky-sqrt-1
  (implies (and (natp n)
                (>= n 3)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (= x (* (trunc-sqrt x (- n 2)) (trunc-sqrt x (- n 2)))))
           (and (= (sticky-sqrt x n)
                   (sticky-sqrt x (1- n)))
                (= (sticky-sqrt x (1- n))
                   (trunc-sqrt x (- n 2)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable trunc-sqrt sticky-sqrt))))

(local-defthm sticky-sticky-sqrt-2
  (implies (and (natp n)
                (>= n 3)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (= x (* (trunc-sqrt x (- n 2)) (trunc-sqrt x (- n 2)))))
           (= (sticky (sticky-sqrt x n) (1- n))
              (sticky-sqrt x (1- n))))
  :rule-classes ()
  :hints (("Goal" :use (sticky-sticky-sqrt-1
                        (:instance exactp-sticky-sqrt (n (1- n)))
                        (:instance sticky-exactp-b (x (sticky-sqrt x n)) (n (1- n)))))))

(local-defthm sticky-sticky-sqrt-3
  (implies (and (natp n)
                (>= n 3)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (not (= (trunc-sqrt x (- n 2)) (trunc-sqrt x (1- n)))))
           (and (= (sticky-sqrt x (1- n))
                   (+ (trunc-sqrt x (- n 2)) (expt 2 (- 1 n))))
                (= (trunc-sqrt x (1- n))
                   (+ (trunc-sqrt x (- n 2)) (expt 2 (- 1 n))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable trunc-sqrt sticky-sqrt)
                  :use ((:instance trunc-sqrt-square-bounds (n (- n 2)))
                        (:instance trunc-sqrt-square-bounds (n (1- n)))))))

(local-defthm sticky-sticky-sqrt-4
  (implies (and (natp n)
                (>= n 3)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (not (= (trunc-sqrt x (- n 2)) (trunc-sqrt x (1- n))))
                (= x (* (trunc-sqrt x (1- n)) (trunc-sqrt x (1- n)))))
           (= (sticky-sqrt x n)
              (+ (trunc-sqrt x (- n 2)) (expt 2 (- 1 n)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable sticky-sqrt)
                  :use (sticky-sticky-sqrt-3))))


(local-defthm sticky-sticky-sqrt-5
  (implies (and (natp n)
                (>= n 3)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (not (= (trunc-sqrt x (- n 2)) (trunc-sqrt x (1- n))))
                (= x (* (trunc-sqrt x (1- n)) (trunc-sqrt x (1- n)))))
           (= (sticky (sticky-sqrt x n) (1- n))
              (sticky-sqrt x (1- n))))
  :rule-classes ()
  :hints (("Goal" :use (sticky-sticky-sqrt-3
                        sticky-sticky-sqrt-4
                        (:instance exactp-sticky-sqrt (n (1- n)))
                        (:instance sticky-exactp-b (x (sticky-sqrt x n)) (n (1- n)))))))

(local-defthm sticky-sticky-sqrt-6
  (implies (and (natp n)
                (>= n 3)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (not (= (trunc-sqrt x (- n 2)) (trunc-sqrt x (1- n))))
                (not (= x (* (trunc-sqrt x (1- n)) (trunc-sqrt x (1- n))))))
           (= (sticky-sqrt x n)
              (+ (trunc-sqrt x (- n 2)) (expt 2 (- 1 n)) (expt 2 (- n)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable sticky-sqrt)
                  :use (sticky-sticky-sqrt-3
                        (:instance trunc-sqrt-square-bounds (n (1- n)))))))

(local-defthmd sticky-sticky-sqrt-7
  (implies (and (natp n)
                (>= n 3)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (not (= x (* (trunc-sqrt x (1- n)) (trunc-sqrt x (1- n))))))
           (equal (sticky-sqrt x n)
                  (+ (trunc-sqrt x (1- n)) (expt 2 (- n)))))
  :hints (("Goal" :in-theory (enable sticky-sqrt)
                  :use (sticky-sticky-sqrt-3
                        (:instance trunc-sqrt-square-bounds (n (1- n)))))))

(local-defthm sticky-sticky-sqrt-8
  (implies (and (rationalp x)
                (not (integerp x))
                (integerp y))
           (not (integerp (+ x y))))
  :rule-classes ())

(local-defthm sticky-sticky-sqrt-9
  (implies (and (natp n)
                (>= n 3)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (not (= x (* (trunc-sqrt x (1- n)) (trunc-sqrt x (1- n))))))
           (not (integerp (* (expt 2 (- n 1)) (sticky-sqrt x n)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable sticky-sticky-sqrt-7 exactp2)
                  :use ((:instance sticky-sticky-sqrt-8 (x (expt 2 (- 2 (* 2 n))))
                                                   (y (* (expt 2 (- n 1)) (sticky-sqrt x (1- n)))))
                        (:instance exactp-trunc-sqrt (n (1- n)))))))

(local-defthm sticky-sticky-sqrt-10
  (implies (and (natp n)
                (>= n 3)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (not (= x (* (trunc-sqrt x (1- n)) (trunc-sqrt x (1- n))))))
           (not (exactp (sticky-sqrt x n) (1- n))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable exactp2)
                  :use (sticky-sticky-sqrt-9))))

(local-defthm sticky-sticky-sqrt-11
  (implies (integerp n)
           (< (+ (expt 2 (- 1 n)) (expt 2 (- n)))
              (expt 2 (- 2 n))))
  :rule-classes ())

(local-defthm sticky-sticky-sqrt-12
  (implies (and (natp n)
                (>= n 3)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (not (= (trunc-sqrt x (- n 2)) (trunc-sqrt x (1- n))))
                (not (= x (* (trunc-sqrt x (1- n)) (trunc-sqrt x (1- n))))))
           (< (sticky-sqrt x n)
              (fp+ (trunc-sqrt x (- n 2)) (- n 2))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable sticky-sqrt)
                  :use (sticky-sticky-sqrt-6
                        sticky-sticky-sqrt-11
                        (:instance trunc-sqrt-square-bounds (n (- n 2)))))))

(local-defthm sticky-sticky-sqrt-13
  (implies (and (natp n)
                (>= n 3)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (not (= (trunc-sqrt x (- n 2)) (trunc-sqrt x (1- n))))
                (not (= x (* (trunc-sqrt x (1- n)) (trunc-sqrt x (1- n))))))
           (>= (sticky-sqrt x n)
               (trunc-sqrt x (- n 2))))
  :rule-classes ()
  :hints (("Goal" :use (sticky-sticky-sqrt-6))))

(local-defthm sticky-sticky-sqrt-14
  (implies (and (natp n)
                (>= n 3)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (not (= (trunc-sqrt x (- n 2)) (trunc-sqrt x (1- n))))
                (not (= x (* (trunc-sqrt x (1- n)) (trunc-sqrt x (1- n))))))
           (>= (trunc (sticky-sqrt x n) (- n 2))
               (trunc-sqrt x (- n 2))))
  :rule-classes ()
  :hints (("Goal" :use (sticky-sticky-sqrt-13
                        (:instance exactp-trunc-sqrt (n (- n 2)))
                        (:instance trunc-exactp-c (a (trunc-sqrt x (- n 2))) (x (sticky-sqrt x n)) (n (- n 2)))))))

(local-defthm sticky-sticky-sqrt-15
  (implies (and (natp n)
                (>= n 3)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (not (= (trunc-sqrt x (- n 2)) (trunc-sqrt x (1- n))))
                (not (= x (* (trunc-sqrt x (1- n)) (trunc-sqrt x (1- n))))))
           (<= (trunc (sticky-sqrt x n) (- n 2))
               (trunc-sqrt x (- n 2))))
  :rule-classes ()
  :hints (("Goal" :use (sticky-sticky-sqrt-12
                        sticky-sqrt-bounds
                        (:instance exactp-trunc-sqrt (n (- n 2)))
                        (:instance trunc-sqrt-bounds (n (- n 2)))
                        (:instance trunc-upper-pos (x (sticky-sqrt x n)) (n (- n 2)))
                        (:instance fp+2 (x (trunc-sqrt x (- n 2))) (y (trunc (sticky-sqrt x n) (- n 2))) (n (- n 2)))))))

(local-defthm sticky-sticky-sqrt-16
  (implies (and (natp n)
                (>= n 3)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (not (= (trunc-sqrt x (- n 2)) (trunc-sqrt x (1- n))))
                (not (= x (* (trunc-sqrt x (1- n)) (trunc-sqrt x (1- n))))))
           (= (trunc (sticky-sqrt x n) (- n 2))
              (trunc-sqrt x (- n 2))))
  :rule-classes ()
  :hints (("Goal" :use (sticky-sticky-sqrt-15
                        sticky-sticky-sqrt-14))))

(local-defthm sticky-sticky-sqrt-17
  (implies (and (natp n)
                (>= n 3)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (not (= (trunc-sqrt x (- n 2)) (trunc-sqrt x (1- n))))
                (not (= x (* (trunc-sqrt x (1- n)) (trunc-sqrt x (1- n))))))
           (= (sticky (sticky-sqrt x n) (1- n))
              (+ (trunc-sqrt x (- n 2)) (expt 2 (- 1 n)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable sgn sticky)
                  :use (sticky-sticky-sqrt-10
                        sticky-sticky-sqrt-16
                        sticky-sqrt-bounds
                        (:instance exactp-<= (x (sticky-sqrt x n)) (m (- n 2)) (n (1- n)))))))

(local-defthm sticky-sticky-sqrt-18
  (implies (and (natp n)
                (>= n 3)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (not (= x (* (trunc-sqrt x (1- n)) (trunc-sqrt x (1- n))))))
           (< (* (trunc-sqrt x (- n 2)) (trunc-sqrt x (- n 2))) x))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable trunc-sqrt)
                  :use ((:instance trunc-sqrt-square-bounds (n (1- n)))
                        (:instance square-leq (x (trunc-sqrt x (- n 2))) (y (trunc-sqrt x (1- n))))))))

(local-defthm sticky-sticky-sqrt-19
  (implies (and (natp n)
                (>= n 3)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (not (= x (* (trunc-sqrt x (1- n)) (trunc-sqrt x (1- n))))))
           (= (sticky-sqrt x (1- n))
              (+ (trunc-sqrt x (- n 2)) (expt 2 (- 1 n)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable sticky-sqrt)
                  :use (sticky-sticky-sqrt-18))))

(local-defthm sticky-sticky-sqrt-20
  (implies (and (natp n)
                (>= n 3)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (not (= (trunc-sqrt x (- n 2)) (trunc-sqrt x (1- n))))
                (not (= x (* (trunc-sqrt x (1- n)) (trunc-sqrt x (1- n))))))
           (= (sticky (sticky-sqrt x n) (1- n))
              (sticky-sqrt x (1- n))))
  :rule-classes ()
  :hints (("Goal" :use (sticky-sticky-sqrt-17
                        sticky-sticky-sqrt-19))))

(local-defthm sticky-sticky-sqrt-21
  (implies (and (natp n)
                (>= n 3)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (= (trunc-sqrt x (- n 2)) (trunc-sqrt x (1- n)))
                (not (= x (* (trunc-sqrt x (1- n)) (trunc-sqrt x (1- n))))))
           (= (sticky-sqrt x n)
              (+ (trunc-sqrt x (- n 2)) (expt 2 (- n)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable sticky-sqrt)
                  :use (sticky-sticky-sqrt-3
                        (:instance trunc-sqrt-square-bounds (n (1- n)))))))

(local-defthm sticky-sticky-sqrt-22
  (implies (and (natp n)
                (>= n 3)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (= (trunc-sqrt x (- n 2)) (trunc-sqrt x (1- n)))
                (not (= x (* (trunc-sqrt x (1- n)) (trunc-sqrt x (1- n))))))
           (< (sticky-sqrt x n)
              (fp+ (trunc-sqrt x (- n 2)) (- n 2))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable sticky-sqrt)
                  :use (sticky-sticky-sqrt-21
                        sticky-sticky-sqrt-11
                        (:instance trunc-sqrt-square-bounds (n (- n 2)))))))

(local-defthm sticky-sticky-sqrt-23
  (implies (and (natp n)
                (>= n 3)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (= (trunc-sqrt x (- n 2)) (trunc-sqrt x (1- n)))
                (not (= x (* (trunc-sqrt x (1- n)) (trunc-sqrt x (1- n))))))
           (>= (sticky-sqrt x n)
               (trunc-sqrt x (- n 2))))
  :rule-classes ()
  :hints (("Goal" :use (sticky-sticky-sqrt-21))))

(local-defthm sticky-sticky-sqrt-24
  (implies (and (natp n)
                (>= n 3)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (= (trunc-sqrt x (- n 2)) (trunc-sqrt x (1- n)))
                (not (= x (* (trunc-sqrt x (1- n)) (trunc-sqrt x (1- n))))))
           (>= (trunc (sticky-sqrt x n) (- n 2))
               (trunc-sqrt x (- n 2))))
  :rule-classes ()
  :hints (("Goal" :use (sticky-sticky-sqrt-23
                        (:instance exactp-trunc-sqrt (n (- n 2)))
                        (:instance trunc-exactp-c (a (trunc-sqrt x (- n 2))) (x (sticky-sqrt x n)) (n (- n 2)))))))

(local-defthm sticky-sticky-sqrt-25
  (implies (and (natp n)
                (>= n 3)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (= (trunc-sqrt x (- n 2)) (trunc-sqrt x (1- n)))
                (not (= x (* (trunc-sqrt x (1- n)) (trunc-sqrt x (1- n))))))
           (<= (trunc (sticky-sqrt x n) (- n 2))
               (trunc-sqrt x (- n 2))))
  :rule-classes ()
  :hints (("Goal" :use (sticky-sticky-sqrt-22
                        sticky-sqrt-bounds
                        (:instance exactp-trunc-sqrt (n (- n 2)))
                        (:instance trunc-sqrt-bounds (n (- n 2)))
                        (:instance trunc-upper-pos (x (sticky-sqrt x n)) (n (- n 2)))
                        (:instance fp+2 (x (trunc-sqrt x (- n 2))) (y (trunc (sticky-sqrt x n) (- n 2))) (n (- n 2)))))))

(local-defthm sticky-sticky-sqrt-26
  (implies (and (natp n)
                (>= n 3)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (= (trunc-sqrt x (- n 2)) (trunc-sqrt x (1- n)))
                (not (= x (* (trunc-sqrt x (1- n)) (trunc-sqrt x (1- n))))))
           (= (trunc (sticky-sqrt x n) (- n 2))
              (trunc-sqrt x (- n 2))))
  :rule-classes ()
  :hints (("Goal" :use (sticky-sticky-sqrt-25
                        sticky-sticky-sqrt-24))))

(local-defthm sticky-sticky-sqrt-27
  (implies (and (natp n)
                (>= n 3)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (= (trunc-sqrt x (- n 2)) (trunc-sqrt x (1- n)))
                (not (= x (* (trunc-sqrt x (1- n)) (trunc-sqrt x (1- n))))))
           (= (sticky (sticky-sqrt x n) (1- n))
              (+ (trunc-sqrt x (- n 2)) (expt 2 (- 1 n)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable sgn sticky)
                  :use (sticky-sticky-sqrt-10
                        sticky-sticky-sqrt-26
                        sticky-sqrt-bounds
                        (:instance exactp-<= (x (sticky-sqrt x n)) (m (- n 2)) (n (1- n)))))))

(local-defthm sticky-sticky-sqrt-28
  (implies (and (natp n)
                (>= n 3)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (not (= x (* (trunc-sqrt x (1- n)) (trunc-sqrt x (1- n))))))
           (= (sticky (sticky-sqrt x n) (1- n))
              (sticky-sqrt x (1- n))))
  :rule-classes ()
  :hints (("Goal" :use (sticky-sticky-sqrt-20
                        sticky-sticky-sqrt-27
                        sticky-sticky-sqrt-19))))

(local-defthm sticky-sticky-sqrt-29
  (implies (and (natp n)
                (>= n 3)
                (rationalp x)
                (<= 1/4 x)
                (< x 1))
           (= (sticky (sticky-sqrt x n) (1- n))
              (sticky-sqrt x (1- n))))
  :rule-classes ()
  :hints (("Goal" :use (sticky-sticky-sqrt-2
                        sticky-sticky-sqrt-5
                        sticky-sticky-sqrt-28))))

#|
Proof: Let a1 = trunc-sqrt(x, n-2), r1 = sticky-sqrt(x, n-1), a2 = trunc-sqrt(x, n-1), and r2 = sticky-sqrt(x, n).
expo(a1) = expo(r1) = expo(a2) = expo(r2) = 0.
Show sticky(r2, n-1) = r1.  Note that 1 <= a1^2 <= a^2 <= x.

Case 1: a1 = a2 and a2^2 = x.

a1 = r1 = a2 = r2.  Since r2 is (n-1)-exact, sticky(r2, n-1) = r2 = r1.

Case 2: a1 = a2 and a2^2 < x.

r1 = a1 + 2^(2-n) is not (n-2)-exact, r2 = a2 + 2^(1-n) is not (n-1)-exact.
sticky(r2, n-1) = trunc(r2, n-2) + 2^(2-n) = a1 + 2^(2-n) = r1.

Case 3: a1 < a2 and a2^2 = x.

r1 = a2 = r2 = a1 + 2^(2-n) is (n-1)-exact.
sticky(r2, n-1) = r2 = r1.

Case 4: a1 < a2 and a2^2 < x.

r1 = a2 = a1 + 2^(2-n) and r2 = a2 + 2^(1-n) = a1 + 2^(2-n) + 2^(1-n).
sticky(r2, n-1) = trunc(r2, n-2) + 2^(2-n) = a1 + 2^(2-n) = r1.
|#

(local-defthm sticky-sticky-sqrt-30
  (implies (and (natp n)
                (>= n 2)
                (natp m)
                (> m n)
                (rationalp x)
                (<= 1/4 x)
                (< x 1))
          (= (sticky (sticky-sqrt x (1- m)) n)
             (sticky (sticky-sqrt x m) n)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance sticky-sticky-sqrt-29 (n m))
                        (:instance sticky-sticky (x (sticky-sqrt x m)) (n (1- m)) (m n))))))

(local-defun natp-induct (n)
  (if (zp n)
      ()
    (1+ (natp-induct (1- n)))))

(defthmd sticky-sticky-sqrt
  (implies (and (natp n)
                (>= n 2)
                (natp m)
                (>= m n)
                (rationalp x)
                (<= 1/4 x)
                (< x 1))
           (equal (sticky (sticky-sqrt x m) n)
                  (sticky-sqrt x n)))
  :hints (("Goal" :induct (natp-induct m))
          ("Subgoal *1/2" :use (sticky-sticky-sqrt-30
                                exactp-sticky-sqrt
                                (:instance sticky-exactp-b (x (sticky-sqrt x n)))))))

(defthm rnd-sticky-sqrt
  (implies (and (not (zp k))
                (natp n)
                (>= n (+ k 2))
                (natp m)
                (>= m n)
                (common-rounding-mode-p mode)
                (rationalp x)
                (<= 1/4 x)
                (< x 1))
           (= (rnd (sticky-sqrt x m) mode k)
              (rnd (sticky-sqrt x n) mode k)))
  :rule-classes ()
  :hints (("Goal" :use (sticky-sticky-sqrt
                        (:instance rnd-sticky (x (sticky-sqrt x m)) (m k))))))

(local-defthm trunc-sticky-sqrt-1
  (implies (and (natp n)
                (>= n 2)
                (rationalp x)
                (<= 1/4 x)
                (< x 1))
           (and (<= (trunc-sqrt x n) (sticky-sqrt x (1+ n)))
                (< (sticky-sqrt x (1+ n)) (fp+ (trunc-sqrt x n) n))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable sticky-sqrt))))

(local-defthm trunc-sticky-sqrt-2
  (implies (and (natp n)
                (>= n 2)
                (rationalp x)
                (<= 1/4 x)
                (< x 1))
           (= (trunc (sticky-sqrt x (1+ n)) n)
              (trunc-sqrt x n)))
  :rule-classes ()
  :hints (("Goal" :use (trunc-sqrt-bounds
                        exactp-trunc-sqrt
                        trunc-sticky-sqrt-1
                        (:instance trunc-exactp-b (x (trunc-sqrt x n)))
                        (:instance trunc-monotone (x (trunc-sqrt x n)) (y (sticky-sqrt x (1+ n))))
                        (:instance sticky-sqrt-bounds (n (1+ n)))
                        (:instance fp+2 (x (trunc-sqrt x n)) (y (trunc (sticky-sqrt x (1+ n)) n)))
                        (:instance trunc-upper-pos (x (sticky-sqrt x (1+ n))))))))

(defthmd trunc-sticky-sqrt
  (implies (and (natp n)
                (>= n 2)
                (natp m)
                (> m n)
                (rationalp x)
                (<= 1/4 x)
                (< x 1))
           (equal (trunc (sticky-sqrt x m) n)
                  (trunc-sqrt x n)))
  :hints (("Goal" :use (trunc-sticky-sqrt-2
                        (:instance sticky-sticky-sqrt (n (1+ n)))
                        (:instance trunc-sticky (x (sticky-sqrt x m)) (n (1+ n)) (m n))))))

(local-defthmd trunc-trunc-sticky-1
   (implies (and (natp n)
                (>= n 2)
                (natp m)
                (>= m n)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (= (* (trunc-sqrt x n) (trunc-sqrt x n)) x))
            (equal (trunc-sqrt x m)
                   (trunc-sqrt x n)))
  :hints (("Goal" :induct (natp-induct m))
          ("Subgoal *1/2" :in-theory (enable trunc-sqrt))))

(local-defthmd trunc-trunc-sticky-2
   (implies (and (natp n)
                (>= n 2)
                (natp m)
                (> m n)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (= (* (trunc-sqrt x n) (trunc-sqrt x n)) x))
            (equal (sticky-sqrt x m)
                   (trunc-sqrt x n)))
  :hints (("Goal" :use ((:instance trunc-trunc-sticky-1 (m (1- m))))
                  :in-theory (enable sticky-sqrt))))

(local-defthmd trunc-trunc-sticky-3
   (implies (and (natp n)
                (>= n 2)
                (natp m)
                (>= m n)
                (rationalp x)
                (<= 1/4 x)
                (< x 1))
            (<= (trunc-sqrt x n)
                (trunc-sqrt x m)))
  :hints (("Goal" :induct (natp-induct m))
          ("Subgoal *1/2" :in-theory (enable trunc-sqrt))))

(local-defthmd trunc-trunc-sticky-4
   (implies (and (natp n)
                (>= n 2)
                (natp m)
                (> m n)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (< (* (trunc-sqrt x n) (trunc-sqrt x n)) x))
            (< (trunc-sqrt x n)
               (sticky-sqrt x m)))
  :hints (("Goal" :use (trunc-sqrt-bounds
                        (:instance trunc-sqrt-bounds (n (1- m)))
                        (:instance trunc-trunc-sticky-3 (m (1- m)))
                        (:instance square-leq (x (trunc-sqrt x m)) (y (trunc-sqrt x n)))
                        (:instance square-leq (x (trunc-sqrt x n)) (y (trunc-sqrt x m))))
                  :in-theory (enable sticky-sqrt))))

(defthm trunc-trunc-sticky
   (implies (and (natp n)
                (>= n 2)
                (natp m)
                (> m n)
                (rationalp x)
                (<= 1/4 x)
                (< x 1))
           (iff (= (* (trunc-sqrt x n) (trunc-sqrt x n)) x)
                (= (sticky-sqrt x m) (trunc-sqrt x n))))
  :rule-classes ()
  :hints (("Goal" :use (trunc-trunc-sticky-2
                        trunc-trunc-sticky-4
                        trunc-sqrt-square-bounds))))

(defthmd sqrt-sticky-sqrt
  (implies (and (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (integerp n)
                (> n 1))
           (equal (qsqrt x n)
                  (sticky-sqrt x n)))
  :hints (("Goal" :in-theory (enable qsqrt)
                  :use ((:instance expo-unique (n -1))
                        (:instance expo-unique (n -2))))))

(local-defthm sqrt66-lower-1
  (implies (rationalp x)
           (and (>= x (* 2 (fl (/ x 2))))
                (<  x (+ 2 (* 2 (fl (/ x 2)))))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance fl-def (x (/ x 2)))))))

(local-defthm sqrt66-lower-2
  (implies (integerp x)
           (or (= x (* 2 (fl (/ x 2))))
               (= x (1+ (* 2 (fl (/ x 2)))))))
  :rule-classes ()
  :hints (("Goal" :use (sqrt66-lower-1))))

(local-defthm sqrt66-lower-3
  (implies (and (rationalp x)
                (> x 0))
           (let* ((e (1+ (fl (/ (expo x) 2))))
                  (x0 (/ x (expt 2 (* 2 e)))))
             (or (= x0 (/ (sig x) 2))
                 (= x0 (/ (sig x) 4)))))
  :rule-classes ()
  :hints (("Goal" :use (fp-abs
                        (:instance sqrt66-lower-2 (x (expo x)))))))

(defthm x0-bounds-1
  (implies (and (rationalp x)
                (> x 0)
                (or (= x0 (/ (sig x) 2))
                    (= x0 (/ (sig x) 4))))
           (and (>= x0 1/4)
                (< x0 1)))
  :rule-classes ()
  :hints (("Goal" :use (sig-upper-bound
                        sig-lower-bound))))

(defthm x0-bounds
  (let* ((e (1+ (fl (/ (expo x) 2))))
         (x0 (/ x (expt 2 (* 2 e)))))
    (implies (and (rationalp x)
                  (> x 0))
             (and (>= x0 1/4)
                  (< x0 1))))
  :rule-classes ()
  :hints (("Goal" :use (sqrt66-lower-3
                        (:instance x0-bounds-1 (x0 (/ x (expt 2 (* 2 (1+ (fl (/ (expo x) 2))))))))))))

(local-defthm sqrt66-lower-4
  (implies (and (rationalp x)
                (> x 0))
           (and (< (/ (sig x) 4) 1)
                (<= 1/4 (/ (sig x) 4))
                (< (/ (sig x) 2) 1)
                (<= 1/4 (/ (sig x) 2))))
  :rule-classes ()
  :hints (("Goal" :use (sig-lower-bound
                        sig-upper-bound))))

(local-defthm sqrt66-lower-5
  (implies (and (rationalp x)
                (> x 0)
                (or (= x0 (/ (sig x) 2))
                    (= x0 (/ (sig x) 4))))
           (and (<= 1/4 x0)
                (< x0 1)))
  :rule-classes ()
  :hints (("Goal" :use (sqrt66-lower-4
                        sig-upper-bound
                        sig-lower-bound))))

(local-defthm sqrt66-lower-6
  (implies (and (rationalp x)
                (> x 0))
           (let* ((e (1+ (fl (/ (expo x) 2))))
                  (x0 (/ x (expt 2 (* 2 e)))))
             (and (<= 1/4 x0)
                  (< x0 1))))
  :rule-classes ()
  :hints (("Goal" :use (sqrt66-lower-3
                        (:instance sqrt66-lower-5 (x0 (/ x (expt 2 (* 2 (1+ (fl (/ (expo x) 2))))))))))))

(local-defthm sqrt66-lower-7
  (implies (and (rationalp x)
                (> x 0)
                (rationalp l)
                (<= (* l l) x))
           (let* ((e (1+ (fl (/ (expo x) 2))))
                  (x0 (/ x (expt 2 (* 2 e))))
                  (l0 (/ l (expt 2 e))))
             (<= (* l0 l0) x0)))
  :rule-classes ())

(local-defthm sqrt66-lower-8
  (implies (and (rationalp x)
                (> x 0)
                (integerp n)
                (> n 1)
                (rationalp l)
                (<= (* l l) x))
           (<= (sticky l n) (qsqrt x n)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable qsqrt)
                  :use (sqrt66-lower-6
                        sqrt66-lower-7
                        (:instance sticky-shift (x (/ l (expt 2 (1+ (fl (/ (expo x) 2))))))
                                                (k (1+ (fl (/ (expo x) 2)))))
                        (:instance sticky-sqrt-lower (l (/ l (expt 2 (1+ (fl (/ (expo x) 2))))))
                                                 (x (/ x (expt 2 (* 2 (1+ (fl (/ (expo x) 2))))))))))))

(defthm qsqrt-lower
  (implies (and (rationalp x)
                (> x 0)
                (rationalp l)
                (<= (* l l) x)
                (common-rounding-mode-p mode)
                (not (zp k))
                (integerp n)
                (>= n (+ k 2)))
           (<= (rnd l mode k)
               (rnd (qsqrt x n) mode k)))
  :rule-classes ()
  :hints (("Goal" :use (sqrt66-lower-8
                        (:instance rnd-sticky (x l) (m k))
                        (:instance rnd-monotone (x (sticky l n)) (y (qsqrt x n)) (n k))))))

#|
Proof: Let e = fl(expo(x)/2), x0 = x/2^(2*e), and l0 = l/2^e.
Then 1 <= x0 < 4 and l0^2 = l^2/2^(2*e) <= x/2^(2*e) = x0.
By sticky-shift and sticky-sqrt-lower,

  sticky(l, 66) = 2^e * sticky(l0, n)
               <= 2^e * sticky-sqrt(x0, n)
                = sqrt(x, n).

By rnd-sticky and rnd-monotone,

  rnd(l, mode, k) = rnd(sticky(l, n), mode, k)
                 <= rnd(sqrt(x, n), mode, k)
|#

(local-defthm sqrt66-upper-1
  (implies (and (rationalp x)
                (> x 0)
                (rationalp h)
                (>= h 0)
                (>= (* h h) x))
           (let* ((e (1+ (fl (/ (expo x) 2))))
                  (x0 (/ x (expt 2 (* 2 e))))
                  (h0 (/ h (expt 2 e))))
             (>= (* h0 h0) x0)))
  :rule-classes ())

(local-defthm sqrt66-upper-2
  (implies (and (rationalp x)
                (> x 0)
                (integerp n)
                (> n 2)
                (rationalp h)
                (>= h 0)
                (>= (* h h) x))
            (>= (sticky h n) (qsqrt x n)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable qsqrt)
                  :use (sqrt66-lower-6
                        sqrt66-upper-1
                        (:instance sticky-shift (x (/ h (expt 2 (1+ (fl (/ (expo x) 2))))))
                                                (k (1+ (fl (/ (expo x) 2)))))
                        (:instance sticky-sqrt-upper (h (/ h (expt 2 (1+ (fl (/ (expo x) 2))))))
                                                     (x (/ x (expt 2 (* 2 (1+ (fl (/ (expo x) 2))))))))))))

(defthm qsqrt-upper
  (implies (and (rationalp x)
                (> x 0)
                (rationalp h)
                (>= h 0)
                (>= (* h h) x)
                (common-rounding-mode-p mode)
                (not (zp k))
                (integerp n)
                (>= n (+ k 2)))
           (>= (rnd h mode k)
               (rnd (qsqrt x n) mode k)))
  :rule-classes ()
  :hints (("Goal" :use (sqrt66-upper-2
                        (:instance rnd-sticky (x h) (m k))
                        (:instance rnd-monotone (y (sticky h n)) (x (qsqrt x n)) (n k))))))

(local-defthm sq-leq-1
  (implies (and (rationalp x)
                (rationalp y)
                (> x 0)
                (> y 0))
           (iff (<= x y)
                (<= (* x x) (* x y))))
  :rule-classes ())

(local-defthm sq-leq-2
  (implies (and (rationalp x)
                (rationalp y)
                (> x 0)
                (> y 0))
           (iff (<= x y)
                (<= (* x y) (* y y))))
  :rule-classes ())

(local-defthm sq-leq
  (implies (and (rationalp x)
                (rationalp y)
                (> x 0)
                (> y 0))
           (iff (<= x y)
                (<= (* x x) (* y y))))
  :rule-classes ()
  :hints (("Goal" :use (sq-leq-1 sq-leq-2)
                  :in-theory
                  #!acl2(disable normalize-factors-gather-exponents
                                 simplify-products-gather-exponents-<))))

(local-defthm exactp-cmp-sticky-sqrt-1
  (implies (and (rationalp x) (>= x 1/4) (< x 1)
                (rationalp y) (> y 0)
                (integerp n) (> n 1)
                (exactp y (1- n))
                (< y (trunc-sqrt x (1- n))))
           (and (< (* y y) x) (< y (sticky-sqrt x n))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable sticky-sqrt)
                  :use ((:instance trunc-sqrt-square-bounds (n (1- n)))
                        (:instance sq-leq (x (trunc-sqrt x (1- n))))))))

(local-defthm exactp-cmp-sticky-sqrt-2
  (implies (integerp k)
           (> (expt 2 k) (expt 2 (1- k))))
  :rule-classes ())

(local-defthm exactp-cmp-sticky-sqrt-3
  (implies (and (rationalp x) (>= x 1/4) (< x 1)
                (rationalp y) (> y 0)
                (integerp n) (> n 1))
           (> (+ (trunc-sqrt x (1- n)) (expt 2 (- 1 n)))
              (sticky-sqrt x n)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable sticky-sqrt)
                  :use ((:instance exactp-cmp-sticky-sqrt-2 (k (- 1 n)))))))

(local-defthm exactp-cmp-sticky-sqrt-4
  (implies (and (rationalp x) (>= x 1/4) (< x 1)
                (rationalp y) (> y 0)
                (integerp n) (> n 1)
                (exactp y (1- n))
                (> y (trunc-sqrt x (1- n))))
           (and (> (* y y) x) (> y (sticky-sqrt x n))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable expo-trunc-sqrt)
                  :use (exactp-cmp-sticky-sqrt-3
                        (:instance exactp-trunc-sqrt (n (1- n)))
                        (:instance expo-trunc-sqrt (n (1- n)))
                        (:instance fp+2 (x (trunc-sqrt x (1- n))) (n (1- n)))
                        (:instance trunc-sqrt-square-bounds (n (1- n)))
                        (:instance sq-leq (x (+ (trunc-sqrt x (1- n)) (expt 2 (- 1 n)))))))))

(defthm exactp-cmp-sticky-sqrt
  (implies (and (rationalp x) (>= x 1/4) (< x 1)
                (rationalp y) (> y 0)
                (integerp n) (> n 1)
                (exactp y (1- n)))
           (and (iff (< (* y y) x) (< y (sticky-sqrt x n)))
                (iff (> (* y y) x) (> y (sticky-sqrt x n)))))
  :rule-classes ()
  :hints (("Goal" :cases ((< y (trunc-sqrt x (1- n))) (> y (trunc-sqrt x (1- n))))
                  :in-theory (enable sticky-sqrt)
                  :use (exactp-cmp-sticky-sqrt-1
                        exactp-cmp-sticky-sqrt-4
                        (:instance trunc-sqrt-square-bounds (n (1- n)))))))

(local-defthm exactp-cmp-qsqrt-1
  (implies (integerp n)
           (or (= (fl (/ n 2)) (/ n 2))
               (= (fl (/ n 2)) (/ (1- n) 2))))
  :rule-classes ())

(local-defthm exactp-cmp-qsqrt-2
  (implies (and (rationalp x) (> x 0)
                (rationalp y) (> y 0)
                (< x y))
           (< (/ x y) 1))
  :rule-classes ())

(local-defthm exactp-cmp-qsqrt-3
  (implies (and (rationalp x) (> x 0)
                (integerp k) (< x (expt 2 k)))
           (< (/ x (expt 2 k)) 1))
  :rule-classes ()
  :hints (("Goal" :use (:instance exactp-cmp-qsqrt-2 (y (expt 2 k))))))

(local-defthm exactp-cmp-qsqrt-4
  (implies (and (rationalp x) (> x 0))
           (< (/ x (expt 2 (* 2 (1+ (/ (1- (expo x)) 2))))) 1))
  :rule-classes ()
  :hints (("Goal" :use (expo-upper-bound
                        (:instance exactp-cmp-qsqrt-3 (k (* 2 (1+ (/ (1- (expo x)) 2)))))))))

(local-defthm exactp-cmp-qsqrt-5
  (implies (and (rationalp x) (> x 0))
           (< (expt 2 (1+ (expo x)))
              (expt 2 (+ 2 (expo x)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance exactp-cmp-sticky-sqrt-2 (k (+ 2 (expo x))))))))

(local-defthm exactp-cmp-qsqrt-6
  (implies (and (rationalp x) (> x 0))
           (< x (expt 2 (* 2 (1+ (/ (expo x) 2))))))
  :rule-classes ()
  :hints (("Goal"
           :in-theory
           #!acl2(disable |(* (expt c m) (expt d n))|
                          |(< (expt x n) (expt x m))|
                          EXPT-IS-INCREASING-FOR-BASE->-1
                          SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<
                          NORMALIZE-FACTORS-GATHER-EXPONENTS
                          |(* (expt x m) (expt x n))|)
           :use (exactp-cmp-qsqrt-5
                 expo-upper-bound))))

(local-defthm exactp-cmp-qsqrt-7
  (implies (and (rationalp x) (> x 0))
           (< (/ x (expt 2 (* 2 (1+ (/ (expo x) 2))))) 1))
  :rule-classes ()
  :hints (("Goal" :use (exactp-cmp-qsqrt-6
                        (:instance exactp-cmp-qsqrt-3 (k (* 2 (1+ (/ (expo x) 2)))))))))

(local-defthm exactp-cmp-qsqrt-8
  (implies (and (rationalp x) (> x 0))
                (< (/ x (expt 2 (* 2 (1+ (fl (/ (expo x) 2)))))) 1))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable fl-integerp)
                  :use (exactp-cmp-qsqrt-4 exactp-cmp-qsqrt-7
                        (:instance exactp-cmp-qsqrt-1 (n (expo x)))))))

(local-defthm exactp-cmp-qsqrt-9
  (implies (and (rationalp x) (> x 0)
                (rationalp y) (> y 0)
                (rationalp z) (> z 0)
                (>= x y))
           (>= (* x z) (* y z)))
  :rule-classes ())

(local-defthm exactp-cmp-qsqrt-10
  (implies (and (rationalp x) (> x 0)
                (rationalp y) (> y 0)
                (>= x (/ y 4)))
           (>= (/ x y) 1/4))
  :rule-classes ()
  :hints (("Goal" :use ((:instance exactp-cmp-qsqrt-9 (y (/ y 4)) (z (/ y)))))))

(local-defthm exactp-cmp-qsqrt-11
  (implies (and (rationalp x) (> x 0)
                (integerp k) (>= x (expt 2 (- k 2))))
           (>= (/ x (expt 2 k)) 1/4))
  :rule-classes ()
  :hints (("Goal" :use (:instance exactp-cmp-qsqrt-10 (y (expt 2 k))))))

(local-defthm exactp-cmp-qsqrt-12
  (implies (and (rationalp x) (> x 0))
           (>= (/ x (expt 2 (* 2 (1+ (/ (expo x) 2))))) 1/4))
  :rule-classes ()
  :hints (("Goal" :use (expo-lower-bound
                        (:instance exactp-cmp-qsqrt-11 (k (* 2 (1+ (/ (expo x) 2)))))))))

(local-defthm exactp-cmp-qsqrt-13
  (implies (and (rationalp x) (> x 0))
           (< (expt 2 (1- (expo x)))
              (expt 2 (expo x))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance exactp-cmp-sticky-sqrt-2 (k (expo x)))))))

(local-defthm exactp-cmp-qsqrt-14
  (implies (and (rationalp x) (> x 0))
           (>= x (expt 2 (1- (expo x)))))
  :rule-classes ()
  :hints (("Goal"
           :in-theory
           #!acl2(disable |(* (expt c m) (expt d n))|
                          |(< (expt x n) (expt x m))|
                          EXPT-IS-INCREASING-FOR-BASE->-1
                          SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<
                          NORMALIZE-FACTORS-GATHER-EXPONENTS
                          |(* (expt x m) (expt x n))|)
           :use (exactp-cmp-qsqrt-13
                 expo-lower-bound))))

(local-defthm exactp-cmp-qsqrt-15
  (implies (and (rationalp x) (> x 0))
           (>= (/ x (expt 2 (* 2 (1+ (/ (1- (expo x)) 2))))) 1/4))
  :rule-classes ()
  :hints (("Goal" :use (exactp-cmp-qsqrt-14
                        (:instance exactp-cmp-qsqrt-11 (k (* 2 (1+ (/ (1- (expo x)) 2)))))))))

(local-defthm exactp-cmp-qsqrt-16
  (implies (and (rationalp x) (> x 0))
                (>= (/ x (expt 2 (* 2 (1+ (fl (/ (expo x) 2)))))) 1/4))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable fl-integerp)
                  :use (exactp-cmp-qsqrt-12 exactp-cmp-qsqrt-15
                        (:instance exactp-cmp-qsqrt-1 (n (expo x)))))))

(local-defthm exactp-cmp-qsqrt-17
  (implies (and (rationalp x) (> x 0)
                (rationalp y) (> y 0)
                (integerp n) (> n 1)
                (exactp y (1- n)))
           (let ((e (1+ (fl (/ (expo x) 2)))))
             (and (iff (< (/ (* y y) (expt 2 (* 2 e)))
                          (/ x (expt 2 (* 2 e))))
                       (< (/ y (expt 2 e))
                          (/ (qsqrt x n) (expt 2 e))))
                  (iff (> (/ (* y y) (expt 2 (* 2 e)))
                          (/ x (expt 2 (* 2 e))))
                       (> (/ y (expt 2 e))
                          (/ (qsqrt x n) (expt 2 e)))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable qsqrt)
                  :use (exactp-cmp-qsqrt-8
                        exactp-cmp-qsqrt-16
                        (:instance exactp-shift (x y)
                                                (k (- (1+ (fl (/ (expo x) 2)))))
                                                (n (1- n)))
                        (:instance exactp-cmp-sticky-sqrt (x (/ x (expt 2 (* 2 (1+ (fl (/ (expo x) 2)))))))
                                                          (y (/ y (expt 2 (1+ (fl (/ (expo x) 2)))))))))))

(local-defthm exactp-cmp-qsqrt-18
  (implies (and (rationalp x)
                (rationalp y)
                (integerp k))
           (iff (< x y)
                (< (* x (expt 2 k)) (* y (expt 2 k)))))
  :rule-classes ())

(defthm exactp-cmp-qsqrt
  (implies (and (rationalp x) (> x 0)
                (rationalp y) (> y 0)
                (integerp n) (> n 1)
                (exactp y (1- n)))
           (and (iff (< (* y y) x) (< y (qsqrt x n)))
                (iff (> (* y y) x) (> y (qsqrt x n)))))
  :rule-classes ()
  :hints (("Goal" :use (exactp-cmp-qsqrt-17
                        (:instance exactp-cmp-qsqrt-18 (x (/ (* y y) (expt 2 (* 2 (1+ (fl (/ (expo x) 2)))))))
                                                       (y (/ x (expt 2 (* 2 (1+ (fl (/ (expo x) 2)))))))
                                                       (k (* 2 (1+ (fl (/ (expo x) 2))))))
                        (:instance exactp-cmp-qsqrt-18 (x (/ y (expt 2 (1+ (fl (/ (expo x) 2))))))
                                                       (y (/ (qsqrt x n) (expt 2 (1+ (fl (/ (expo x) 2))))))
                                                       (k (1+ (fl (/ (expo x) 2)))))
                        (:instance exactp-cmp-qsqrt-18 (y (/ (* y y) (expt 2 (* 2 (1+ (fl (/ (expo x) 2)))))))
                                                       (x (/ x (expt 2 (* 2 (1+ (fl (/ (expo x) 2)))))))
                                                       (k (* 2 (1+ (fl (/ (expo x) 2))))))
                        (:instance exactp-cmp-qsqrt-18 (y (/ y (expt 2 (1+ (fl (/ (expo x) 2))))))
                                                       (x (/ (qsqrt x n) (expt 2 (1+ (fl (/ (expo x) 2))))))
                                                       (k (1+ (fl (/ (expo x) 2)))))))))

