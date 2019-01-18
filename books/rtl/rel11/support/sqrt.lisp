; RTL - A Formal Theory of Register-Transfer Logic and Computer Arithmetic
; Copyright (C) 1995-2013 Advanced Mirco Devices, Inc.
;
; Contact:
;   David Russinoff
;   1106 W 9th St., Austin, TX 78703
;   http://www.russsinoff.com/
;
; See license file books/rtl/rel11/license.txt.
;
; Author: David M. Russinoff (david@russinoff.com)

(in-package "RTL")

(include-book "definitions")
(local (include-book "basic"))
(local (include-book "float"))
(local (include-book "round"))

(local (include-book "arithmetic-5/top" :dir :system))

(defund rtz-sqrt (x n)
  (declare (xargs :guard (and (real/rationalp x)
                              (natp n))
                  :verify-guards nil))
  (if (zp n)
      0
    (let* ((lower (rtz-sqrt x (1- n)))
           (upper (+ lower (expt 2 (- n)))))
      (if (<= (* upper upper) x)
          upper
        lower))))

(defund rto-sqrt (x n)
  (declare (xargs :guard (and (real/rationalp x)
                              (posp n))
                  :verify-guards nil))
  (let ((trunc (rtz-sqrt x (1- n))))
    (if (< (* trunc trunc) x)
        (+ trunc (expt 2 (- n)))
      trunc)))

(local-in-theory (enable rtz-sqrt rto-sqrt))

(defund qsqrt (x n)
  (declare (xargs :guard (and (real/rationalp x)
                              (posp n))
                  :verify-guards nil))
  (let ((e (1+ (fl (/ (expo x) 2)))))
    (* (expt 2 e)
       (rto-sqrt (/ x (expt 2 (* 2 e))) n))))

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
                  :in-theory (e/d (qsqrt) (fl+int-rewrite rto-sqrt)))))

(local-defthm rtz-sqrt-bounds-1
  (implies (and (rationalp x)
                (<= 1/4 x))
           (= (rtz-sqrt x 1) 1/2))
  :rule-classes ()
  :hints (("Goal" :use (:instance rtz-sqrt (n 1)))))

(local-defthm rtz-sqrt-bounds-2
  (implies (and (rationalp x)
                (not (zp n)))
           (< (+ x (expt 2 (- n)))
              (+ x (expt 2 (- 1 n)))))
:rule-classes ())

(local-defthm rtz-sqrt-bounds-3
  (implies (and (rationalp x)
                (rationalp y)
                (< x y)
                (<= y 1))
           (<= x 1))
:rule-classes ())

(local-defthm rtz-sqrt-bounds-4
  (implies (and (rationalp x)
                (not (zp n))
                (<= (+ (expt 2 (+ 1 (- n))) x) 1))
           (<= (+ (expt 2 (- n)) x) 1))
  :rule-classes ()
  :hints (("Goal" :use (rtz-sqrt-bounds-2
                        (:instance rtz-sqrt-bounds-3 (x (+ x (expt 2 (- n))))
                                                       (y (+ x (expt 2 (- 1 n)))))))))

(defthm rtz-sqrt-bounds
  (implies (and (rationalp x)
                (<= 1/4 x)
                (not (zp n)))
           (and (<= 1/2 (rtz-sqrt x n))
                (<= (rtz-sqrt x n) (- 1 (expt 2 (- n))))))
  :rule-classes ()
  :hints (("Subgoal *1/2" :use (rtz-sqrt-bounds-1
                                (:instance rtz-sqrt-bounds-4 (x (rtz-sqrt x (1- n))))))))


(defthm expo-rtz-sqrt
  (implies (and (rationalp x)
                (<= 1/4 x)
                (not (zp n)))
           (equal (expo (rtz-sqrt x n))
                  -1))
  :hints (("Goal" :use (rtz-sqrt-bounds
                        (:instance expo-unique (x (rtz-sqrt x n)) (n -1))))))

(local-defthm exactp-rtz-sqrt-1
  (implies (integerp x)
           (integerp (* 2 x)))
  :rule-classes ())

(local-defthm exactp-rtz-sqrt-2
  (implies (and (rationalp x)
                (natp n)
                (integerp (* (expt 2 (+ -1 n)) x)))
           (integerp (* (expt 2 n) x)))
  :hints (("Goal" :use (:instance exactp-rtz-sqrt-1 (x (* (expt 2 (+ -1 n)) x))))))

(local-defthm exactp-rtz-sqrt-3
  (implies (and (rationalp x)
                (<= 1/4 x)
                (not (zp n)))
           (integerp (* (rtz-sqrt x n) (expt 2 n))))
  :rule-classes ())

(defthm exactp-rtz-sqrt
  (implies (and (rationalp x)
                (<= 1/4 x)
                (not (zp n)))
           (exactp (rtz-sqrt x n)
                   n))
  :rule-classes ()
  :hints (("Goal" :in-theory (e/d (exactp2) (rtz-sqrt))
                  :use exactp-rtz-sqrt-3)))

(local-defthmd rtz-rtz-sqrt-1
  (implies (and (rationalp x)
                (<= 1/4 x)
                (not (zp n))
                (> n 1))
           (and (<= (rtz-sqrt x (1- n))
                    (rtz-sqrt x n))
                (< (rtz-sqrt x n)
                   (+ (rtz-sqrt x (1- n))
                      (expt 2 (- 1 n))))))
  :hints (("Goal" :expand ((rtz-sqrt x n)))))


(local-defthmd rtz-rtz-sqrt-2
  (implies (and (rationalp x)
                (<= 1/4 x)
                (not (zp n))
                (> n 1))
           (equal (rtz (rtz-sqrt x n) (+ -1 n))
                  (rtz-sqrt x (1- n))))
  :hints (("Goal" :in-theory (disable rtz-sqrt)
                  :use (rtz-rtz-sqrt-1
                        rtz-sqrt-bounds
                        (:instance rtz-sqrt-bounds (n (1- n)))
                        (:instance exactp-rtz-sqrt (n (1- n)))
                        (:instance rtz-upper-pos (x (rtz-sqrt x n)) (n (1- n)))
                        (:instance rtz-exactp-a (x (rtz-sqrt x n)) (n (1- n)))
                        (:instance rtz-exactp-c (a (rtz-sqrt x (1- n))) (x (rtz-sqrt x n)) (n (1- n)))
                        (:instance fp+2 (n (1- n)) (x (rtz-sqrt x (1- n))) (y (rtz (rtz-sqrt x n) (1- n))))))))

(local-defun natp-induct (n)
  (if (zp n)
      ()
    (1+ (natp-induct (1- n)))))

(local-defthmd rtz-rtz-sqrt-3
  (implies (and (rationalp x)
                (<= 1/4 x)
                (not (zp m))
                (natp n)
                (> n m))
           (equal (rtz (rtz-sqrt x n) m)
                  (rtz-sqrt x m)))
  :hints (("Goal" :induct (natp-induct n))
          ("Subgoal *1/2" :in-theory (disable rtz-sqrt)
                         :use (rtz-rtz-sqrt-2
                               (:instance rtz-rtz (x (rtz-sqrt x n)) (n (1- n)))))))

(defthmd rtz-rtz-sqrt
  (implies (and (rationalp x)
                (<= 1/4 x)
                (not (zp m))
                (natp n)
                (>= n m))
           (equal (rtz (rtz-sqrt x n) m)
                  (rtz-sqrt x m)))
  :hints (("Goal" :in-theory (disable rtz-sqrt)
                         :use (rtz-rtz-sqrt-3
                               exactp-rtz-sqrt
                               (:instance rtz-exactp-b (x (rtz-sqrt x n)))
                               (:instance rtz-rtz (x (rtz-sqrt x n)) (n (1- n)))))))

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

(local-defthm rtz-sqrt-unique-1
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
  :hints (("Goal" :use (rtz-sqrt-unique-1
                        rtz-sqrt-square-bounds
                        exactp-rtz-sqrt
                        rtz-sqrt-bounds
                        (:instance square-leq (x (+ a (expt 2 (- n)))) (y (rtz-sqrt x n)))
                        (:instance square-leq (x (+ (rtz-sqrt x n) (expt 2 (- n)))) (y a))
                        (:instance fp+2 (x a) (y (rtz-sqrt x n)))
                        (:instance fp+2 (y a) (x (rtz-sqrt x n)))))))

(local-defthm rto-sqrt-bounds-1
  (implies (and (rationalp x)
                (integerp a)
                (integerp b)
                (< b a)
                (<= (+ (expt 2 a) x) 1))
           (< (+ (expt 2 b) x) 1))
  :rule-classes ())

(defthm rto-sqrt-bounds
  (implies (and (rationalp x)
                (<= 1/4 x)
                (natp n)
                (>= n 2))
           (and (<= 1/2 (rto-sqrt x n))
                (< (rto-sqrt x n) 1)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rtz-sqrt-bounds (n (1- n)))
                        (:instance rto-sqrt-bounds-1 (x (rtz-sqrt x (1- n)))
                                                   (a (- 1 n))
                                                   (b (- n)))))))

(defthm expo-rto-sqrt
  (implies (and (rationalp x)
                (<= 1/4 x)
                (natp n)
                (>= n 2))
           (equal (expo (rto-sqrt x n))
                  -1))
  :hints (("Goal" :use (rto-sqrt-bounds
                        (:instance expo-unique (x (rto-sqrt x n)) (n -1))))))

(local-defthm exactp-rto-sqrt-1
  (implies (and (rationalp x)
                (<= 1/4 x)
                (natp n)
                (>= n 2)
                (integerp (* (rto-sqrt x n) (expt 2 n))))
           (exactp (rto-sqrt x n) n))
  :rule-classes ()
  :hints (("Goal" :in-theory (e/d (exactp2) (rto-sqrt)))))

(local-defthm exactp-rto-sqrt-2
  (implies (and (rationalp x)
                (<= 1/4 x)
                (natp n)
                (>= n 2))
           (integerp (* (rto-sqrt x n) (expt 2 n))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable exactp2)
                  :use ((:instance exactp-rtz-sqrt (n (1- n)))))))

(defthmd exactp-rto-sqrt
  (implies (and (rationalp x)
                (<= 1/4 x)
                (natp n)
                (>= n 2))
           (exactp (rto-sqrt x n) n))
  :hints (("Goal" :use (exactp-rto-sqrt-1 exactp-rto-sqrt-2)
                  :in-theory (disable rto-sqrt))))

(local-defthm rto-sqrt-lower-1
  (implies (and (natp n)
                (>= n 2)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (rationalp l)
                (<= (* l l) x)
                (= (* (rtz-sqrt x (1- n)) (rtz-sqrt x (1- n ))) x))
           (<= (* l l) (* (rto-sqrt x n) (rto-sqrt x n))))
  :rule-classes ())

(local-defthm rto-sqrt-lower-4
  (implies (and (natp n)
                (>= n 2)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (rationalp l)
                (<= (* l l) x)
                (= (* (rtz-sqrt x (1- n)) (rtz-sqrt x (1- n))) x))
           (<= (* l l) (* (rto-sqrt x n) (rto-sqrt x n))))
  :rule-classes ())

(local-defthm rto-sqrt-lower-5
  (implies (and (natp n)
                (>= n 2)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (rationalp l)
                (<= (* l l) x)
                (= (* (rtz-sqrt x (1- n)) (rtz-sqrt x (1- n))) x))
           (<= l (rto-sqrt x n)))
  :rule-classes ()
  :hints (("Goal" :use (rto-sqrt-lower-4
                        (:instance square-leq  (x l) (y (rto-sqrt x n)))))))

(local-defthm rto-sqrt-lower-6
  (implies (and (natp n)
                (>= n 2)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (rationalp l)
                (<= (* l l) x)
                (= (* (rtz-sqrt x (1- n)) (rtz-sqrt x (1- n))) x))
           (<= (rto l n)
               (rto-sqrt x n)))
  :rule-classes ()
  :hints (("Goal" :use (rto-sqrt-lower-5
                        (:instance exactp-rtz-sqrt (n (1- n)))
                        (:instance exactp-<= (x (rtz-sqrt x (1- n))) (m (1- n)))
                        (:instance rto-monotone (x l) (y (rto-sqrt x n)))
                        (:instance rto-exactp-b (x (rto-sqrt x n)))))))

(local-defthm rto-sqrt-lower-7
  (implies (and (rationalp x)
                (rationalp y)
                (>= x 0)
                (>= y 0))
           (>= (* x y) 0))
  :rule-classes ())

(local-defthm rto-sqrt-lower-8
  (implies (and (rationalp x)
                (rationalp y)
                (< (* x x) (* y y))
                (>= y 0))
           (< x y))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rto-sqrt-lower-7 (x (- x y)) (y (+ x y)))))))

(local-defthm rto-sqrt-lower-9
  (implies (and (natp n)
                (>= n 2)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (rationalp l)
                (<= (* l l) x)
                (< (* (rtz-sqrt x (1- n)) (rtz-sqrt x (1- n))) x))
           (< l (fp+ (rtz-sqrt x (1- n)) (1- n))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rtz-sqrt-square-bounds (n (1- n)))
                        (:instance rto-sqrt-lower-8 (x l)
                                                   (y (+ (rtz-sqrt x (1- n)) (expt 2 (- 1 n)))))))))

(local-defthm rto-sqrt-lower-10
  (implies (and (natp n)
                (>= n 2)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (rationalp l)
                (<= (* l l) x)
                (< (* (rtz-sqrt x (1- n)) (rtz-sqrt x (1- n))) x))
           (<= (rtz l (1- n))
               (rtz-sqrt x (1- n))))
  :rule-classes ()
  :hints (("Goal" :use (rto-sqrt-lower-9
                        (:instance rtz-sqrt-bounds (n (1- n)))
                        (:instance exactp-rtz-sqrt (n (1- n)))
                        (:instance rtz-upper-pos (x l) (n (1- n)))
                        (:instance rtz-exactp-a (x l) (n (1- n)))
                        (:instance fp+2 (y (rtz l (1- n))) (x (rtz-sqrt x (1- n))) (n (1- n)))))))

(local-defthm rto-sqrt-lower-11
  (implies (and (natp n)
                (>= n 2)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (rationalp l)
                (<= (* l l) x)
                (exactp l (1- n))
                (< (* (rtz-sqrt x (1- n)) (rtz-sqrt x (1- n))) x))
           (<= (rto l n)
               (rto-sqrt x n)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable rto)
                  :use (rto-sqrt-lower-10
                        (:instance rtz-exactp-b (x l) (n (1- n)))))))


(local-defthm rto-sqrt-lower-12
  (implies (and (natp n)
                (>= n 2)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (rationalp l)
                (> l 0)
                (<= (* l l) x)
                (< (* (rtz-sqrt x (1- n)) (rtz-sqrt x (1- n))) x))
           (<= (expo l) -1))
  :rule-classes ()
  :hints (("Goal" :use (rto-sqrt-lower-10
                        (:instance expo-monotone (x (rtz l (1- n))) (y (rtz-sqrt x (1- n))))))))

(local-defthm rto-sqrt-lower-13
  (implies (and (integerp a)
                (integerp b)
                (<= a b))
           (<= (expt 2 a) (expt 2 b)))
  :rule-classes ())


(local-defthm rto-sqrt-lower-14
  (implies (and (natp n)
                (>= n 2)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (rationalp l)
                (> l 0)
                (<= (* l l) x)
                (< (* (rtz-sqrt x (1- n)) (rtz-sqrt x (1- n))) x))
           (<= (EXPT 2 (+ 1 (- N) (EXPO L)))
               (EXPT 2 (- N))))
  :rule-classes ()
  :hints (("Goal" :use (rto-sqrt-lower-12
                        (:instance rto-sqrt-lower-13 (a (+ 1 (- N) (EXPO L))) (b (- N)))))))

(local-defthm rto-sqrt-lower-15
  (implies (and (rationalp a)
                (rationalp b)
                (<= a b)
                (rationalp c)
                (rationalp d)
                (<= c d))
           (<= (+ a c) (+ b d)))
  :rule-classes ())

(local-defthm rto-sqrt-lower-16
  (implies (and (natp n)
                (>= n 2)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (rationalp l)
                (> l 0)
                (<= (* l l) x)
                (< (* (rtz-sqrt x (1- n)) (rtz-sqrt x (1- n))) x))
           (<= (+ (RTZ L (+ -1 N)) (EXPT 2 (+ 1 (- N) (EXPO L))))
               (+ (RTZ-SQRT x (1- N)) (EXPT 2 (- N)))))
  :rule-classes ()
  :hints (("Goal" :use (rto-sqrt-lower-10
                        rto-sqrt-lower-14
                        (:instance rto-sqrt-lower-15 (a (RTZ L (+ -1 N)))
                                                    (b (RTZ-SQRT x (1- N)))
                                                    (c (EXPT 2 (+ 1 (- N) (EXPO L))))
                                                    (d (EXPT 2 (- N))))))))

(local-defthm rto-sqrt-lower-17
  (implies (and (natp n)
                (>= n 2)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (rationalp l)
                (<= (* l l) x)
                (not (exactp l (1- n)))
                (>= l 0)
                (< (* (rtz-sqrt x (1- n)) (rtz-sqrt x (1- n))) x))
           (<= (rto l n)
               (rto-sqrt x n)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable sgn rto)
                  :use (rto-sqrt-lower-16))))

(local-defthm rto-sqrt-lower-18
  (implies (and (natp n)
                (>= n 2)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (rationalp l)
                (<= (* l l) x)
                (not (exactp l (1- n)))
                (< l 0)
                (< (* (rtz-sqrt x (1- n)) (rtz-sqrt x (1- n))) x))
           (<= (rto l n)
               (rto-sqrt x n)))
  :rule-classes ()
  :hints (("Goal" :use (rto-sqrt-lower-1
                        (:instance rto-negative (x l))))))

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
  :hints (("Goal" :use (rto-sqrt-lower-6
                        rto-sqrt-lower-11
                        rto-sqrt-lower-17
                        rto-sqrt-lower-18
                        (:instance rtz-sqrt-square-bounds (n (1- n)))))))

#|
Proof: Let a = rtz-sqrt(n-2, x) and r = rto-sqrt(x, n).
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

(local-defthm rto-sqrt-upper-1
  (implies (and (natp n)
                (>= n 2)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (rationalp h)
                (>= h 0)
                (>= (* h h) x)
                (= x (* (rtz-sqrt x (1- n)) (rtz-sqrt x (1- n)))))
           (>= h (rto-sqrt x n)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance square-leq (x (rto-sqrt x n)) (y h))))))

(local-defthm rto-sqrt-upper-2
  (implies (and (natp n)
                (>= n 2)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (rationalp h)
                (>= h 0)
                (>= (* h h) x)
                (= x (* (rtz-sqrt x (1- n)) (rtz-sqrt x (1- n)))))
           (>= (rto h n)
               (rto-sqrt x n)))
  :rule-classes ()
  :hints (("Goal" :use (rto-sqrt-upper-1
                        (:instance exactp-rtz-sqrt (n (1- n)))
                        (:instance exactp-<= (x (rtz-sqrt x (1- n))) (m (1- n)))
                        (:instance rto-monotone (x (rto-sqrt x n)) (y h))
                        (:instance rto-exactp-b (x (rto-sqrt x n)))))))

(local-defthm rto-sqrt-upper-3
  (implies (and (natp n)
                (>= n 2)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (rationalp h)
                (>= h 0)
                (>= (* h h) x)
                (>= h (rto-sqrt x n))
                (> x (* (rtz-sqrt x (1- n)) (rtz-sqrt x (1- n)))))
           (>= (rto h n)
               (rto-sqrt x n)))
  :rule-classes ()
  :hints (("Goal" :use (rto-sqrt-lower-1
                        exactp-rto-sqrt
                        (:instance rto-monotone (x (rto-sqrt x n)) (y h))
                        (:instance rto-exactp-b (x (rto-sqrt x n)))))))

(local-defthm rto-sqrt-upper-4
  (implies (and (natp n)
                (>= n 2)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (rationalp h)
                (>= h 0)
                (>= (* h h) x)
                (< h (rto-sqrt x n))
                (> x (* (rtz-sqrt x (1- n)) (rtz-sqrt x (1- n)))))
           (> h (rtz-sqrt x (1- n))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rtz-sqrt-square-bounds (n (- n 2)))
                        (:instance square-leq (x (rtz-sqrt x (1- n))) (y h))))))

(local-defthm rto-sqrt-upper-5
  (implies (and (natp n)
                (>= n 2)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (rationalp h)
                (>= h 0)
                (>= (* h h) x)
                (< h (rto-sqrt x n))
                (> x (* (rtz-sqrt x (1- n)) (rtz-sqrt x (1- n)))))
           (>= (rtz h (1- n)) (rtz-sqrt x (1- n))))
  :rule-classes ()
  :hints (("Goal" :use (rto-sqrt-upper-4
                        (:instance exactp-rtz-sqrt (n (1- n)))
                        (:instance rtz-exactp-c (a (rtz-sqrt x (1- n))) (x h) (n (1- n)))))))

(local-defthm rto-sqrt-upper-6
  (implies (and (natp n)
                (>= n 2)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (rationalp h)
                (>= h 0)
                (>= (* h h) x)
                (< h (rto-sqrt x n))
                (> x (* (rtz-sqrt x (1- n)) (rtz-sqrt x (1- n)))))
           (not (exactp h (1- n))))
  :rule-classes ()
  :hints (("Goal" :use (rto-sqrt-upper-4
                        (:instance rtz-sqrt-bounds (n (1- n)))
                        (:instance exactp-rtz-sqrt (n (1- n)))
                        (:instance exactp-<= (x (rtz-sqrt x (1- n))) (m (1- n)))
                        (:instance exactp-<= (x h) (m (1- n)))
                        (:instance fp+2 (x (rtz-sqrt x (1- n))) (y h))))))

(local-defthm rto-sqrt-upper-7
  (implies (and (natp n)
                (>= n 2)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (rationalp h)
                (>= h 0)
                (>= (* h h) x)
                (< h (rto-sqrt x n))
                (> x (* (rtz-sqrt x (1- n)) (rtz-sqrt x (1- n)))))
           (equal (expo h) -1))
  :hints (("Goal" :use (rto-sqrt-upper-4
                        rto-sqrt-bounds
                        (:instance rtz-sqrt-bounds (n (1- n)))
                        (:instance expo-unique (x h) (n -1))))))

(local-defthm rto-sqrt-upper-8
  (implies (and (natp n)
                (>= n 2)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (rationalp h)
                (>= h 0)
                (>= (* h h) x)
                (< h (rto-sqrt x n))
                (> x (* (rtz-sqrt x (1- n)) (rtz-sqrt x (1- n)))))
           (>= (rto h n)
               (rto-sqrt x n)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable sgn rto)
                  :use (rto-sqrt-upper-6
                        rto-sqrt-upper-5))))

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
  :hints (("Goal" :use (rto-sqrt-upper-2
                        rto-sqrt-upper-3
                        rto-sqrt-upper-8
                        (:instance rtz-sqrt-square-bounds (n (1- n)))))))

#|
Proof: Let a = rtz-sqrt(x, n-1) and r = rto-sqrt(x, n).
We may assume that h < r; otherwise, by rto-monotone,
rto-exactp-b, and exactp-rtz-sqrt,

  rto(h, n) >= rto(r, n) = r.

If a^2 = x, then r = a, h^2 >= x = a^2 = r^2, and h >= r.
Thus, by rtz-sqrt-square-bounds, a^2 < x and r = a + 2^(1-n) = fp+(a, n).
Since h^2 >= x > a^2, h > a.  It follows from rtz-exactp-c that
rtz(h, n-1) >= a.  By fp+2, h is not n-exact, and hence

  rto(h, n) = rtz(h, n-1) + 2^(1-n)
              >= a + 2^(1-n)
               = r.
|#

(in-theory (disable rtz-sqrt rto-sqrt))

(local-defthm rto-rto-sqrt-1
  (implies (and (natp n)
                (>= n 3)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (= x (* (rtz-sqrt x (- n 2)) (rtz-sqrt x (- n 2)))))
           (and (= (rto-sqrt x n)
                   (rto-sqrt x (1- n)))
                (= (rto-sqrt x (1- n))
                   (rtz-sqrt x (- n 2)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable rtz-sqrt rto-sqrt))))

(local-defthm rto-rto-sqrt-2
  (implies (and (natp n)
                (>= n 3)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (= x (* (rtz-sqrt x (- n 2)) (rtz-sqrt x (- n 2)))))
           (= (rto (rto-sqrt x n) (1- n))
              (rto-sqrt x (1- n))))
  :rule-classes ()
  :hints (("Goal" :use (rto-rto-sqrt-1
                        (:instance exactp-rto-sqrt (n (1- n)))
                        (:instance rto-exactp-b (x (rto-sqrt x n)) (n (1- n)))))))

(local-defthm rto-rto-sqrt-3
  (implies (and (natp n)
                (>= n 3)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (not (= (rtz-sqrt x (- n 2)) (rtz-sqrt x (1- n)))))
           (and (= (rto-sqrt x (1- n))
                   (+ (rtz-sqrt x (- n 2)) (expt 2 (- 1 n))))
                (= (rtz-sqrt x (1- n))
                   (+ (rtz-sqrt x (- n 2)) (expt 2 (- 1 n))))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable rtz-sqrt rto-sqrt)
                  :use ((:instance rtz-sqrt-square-bounds (n (- n 2)))
                        (:instance rtz-sqrt-square-bounds (n (1- n)))))))

(local-defthm rto-rto-sqrt-4
  (implies (and (natp n)
                (>= n 3)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (not (= (rtz-sqrt x (- n 2)) (rtz-sqrt x (1- n))))
                (= x (* (rtz-sqrt x (1- n)) (rtz-sqrt x (1- n)))))
           (= (rto-sqrt x n)
              (+ (rtz-sqrt x (- n 2)) (expt 2 (- 1 n)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable rto-sqrt)
                  :use (rto-rto-sqrt-3))))


(local-defthm rto-rto-sqrt-5
  (implies (and (natp n)
                (>= n 3)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (not (= (rtz-sqrt x (- n 2)) (rtz-sqrt x (1- n))))
                (= x (* (rtz-sqrt x (1- n)) (rtz-sqrt x (1- n)))))
           (= (rto (rto-sqrt x n) (1- n))
              (rto-sqrt x (1- n))))
  :rule-classes ()
  :hints (("Goal" :use (rto-rto-sqrt-3
                        rto-rto-sqrt-4
                        (:instance exactp-rto-sqrt (n (1- n)))
                        (:instance rto-exactp-b (x (rto-sqrt x n)) (n (1- n)))))))

(local-defthm rto-rto-sqrt-6
  (implies (and (natp n)
                (>= n 3)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (not (= (rtz-sqrt x (- n 2)) (rtz-sqrt x (1- n))))
                (not (= x (* (rtz-sqrt x (1- n)) (rtz-sqrt x (1- n))))))
           (= (rto-sqrt x n)
              (+ (rtz-sqrt x (- n 2)) (expt 2 (- 1 n)) (expt 2 (- n)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable rto-sqrt)
                  :use (rto-rto-sqrt-3
                        (:instance rtz-sqrt-square-bounds (n (1- n)))))))

(local-defthmd rto-rto-sqrt-7
  (implies (and (natp n)
                (>= n 3)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (not (= x (* (rtz-sqrt x (1- n)) (rtz-sqrt x (1- n))))))
           (equal (rto-sqrt x n)
                  (+ (rtz-sqrt x (1- n)) (expt 2 (- n)))))
  :hints (("Goal" :in-theory (enable rto-sqrt)
                  :use (rto-rto-sqrt-3
                        (:instance rtz-sqrt-square-bounds (n (1- n)))))))

(local-defthm rto-rto-sqrt-8
  (implies (and (rationalp x)
                (not (integerp x))
                (integerp y))
           (not (integerp (+ x y))))
  :rule-classes ())

(local-defthm rto-rto-sqrt-9
  (implies (and (natp n)
                (>= n 3)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (not (= x (* (rtz-sqrt x (1- n)) (rtz-sqrt x (1- n))))))
           (not (integerp (* (expt 2 (- n 1)) (rto-sqrt x n)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable rto-rto-sqrt-7 exactp2)
                  :use ((:instance rto-rto-sqrt-8 (x (expt 2 (- 2 (* 2 n))))
                                                   (y (* (expt 2 (- n 1)) (rto-sqrt x (1- n)))))
                        (:instance exactp-rtz-sqrt (n (1- n)))))))

(local-defthm rto-rto-sqrt-10
  (implies (and (natp n)
                (>= n 3)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (not (= x (* (rtz-sqrt x (1- n)) (rtz-sqrt x (1- n))))))
           (not (exactp (rto-sqrt x n) (1- n))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable exactp2)
                  :use (rto-rto-sqrt-9))))

(local-defthm rto-rto-sqrt-11
  (implies (integerp n)
           (< (+ (expt 2 (- 1 n)) (expt 2 (- n)))
              (expt 2 (- 2 n))))
  :rule-classes ())

(local-defthm rto-rto-sqrt-12
  (implies (and (natp n)
                (>= n 3)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (not (= (rtz-sqrt x (- n 2)) (rtz-sqrt x (1- n))))
                (not (= x (* (rtz-sqrt x (1- n)) (rtz-sqrt x (1- n))))))
           (< (rto-sqrt x n)
              (fp+ (rtz-sqrt x (- n 2)) (- n 2))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable rto-sqrt)
                  :use (rto-rto-sqrt-6
                        rto-rto-sqrt-11
                        (:instance rtz-sqrt-square-bounds (n (- n 2)))))))

(local-defthm rto-rto-sqrt-13
  (implies (and (natp n)
                (>= n 3)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (not (= (rtz-sqrt x (- n 2)) (rtz-sqrt x (1- n))))
                (not (= x (* (rtz-sqrt x (1- n)) (rtz-sqrt x (1- n))))))
           (>= (rto-sqrt x n)
               (rtz-sqrt x (- n 2))))
  :rule-classes ()
  :hints (("Goal" :use (rto-rto-sqrt-6))))

(local-defthm rto-rto-sqrt-14
  (implies (and (natp n)
                (>= n 3)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (not (= (rtz-sqrt x (- n 2)) (rtz-sqrt x (1- n))))
                (not (= x (* (rtz-sqrt x (1- n)) (rtz-sqrt x (1- n))))))
           (>= (rtz (rto-sqrt x n) (- n 2))
               (rtz-sqrt x (- n 2))))
  :rule-classes ()
  :hints (("Goal" :use (rto-rto-sqrt-13
                        (:instance exactp-rtz-sqrt (n (- n 2)))
                        (:instance rtz-exactp-c (a (rtz-sqrt x (- n 2))) (x (rto-sqrt x n)) (n (- n 2)))))))

(local-defthm rto-rto-sqrt-15
  (implies (and (natp n)
                (>= n 3)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (not (= (rtz-sqrt x (- n 2)) (rtz-sqrt x (1- n))))
                (not (= x (* (rtz-sqrt x (1- n)) (rtz-sqrt x (1- n))))))
           (<= (rtz (rto-sqrt x n) (- n 2))
               (rtz-sqrt x (- n 2))))
  :rule-classes ()
  :hints (("Goal" :use (rto-rto-sqrt-12
                        rto-sqrt-bounds
                        (:instance exactp-rtz-sqrt (n (- n 2)))
                        (:instance rtz-sqrt-bounds (n (- n 2)))
                        (:instance rtz-upper-pos (x (rto-sqrt x n)) (n (- n 2)))
                        (:instance fp+2 (x (rtz-sqrt x (- n 2))) (y (rtz (rto-sqrt x n) (- n 2))) (n (- n 2)))))))

(local-defthm rto-rto-sqrt-16
  (implies (and (natp n)
                (>= n 3)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (not (= (rtz-sqrt x (- n 2)) (rtz-sqrt x (1- n))))
                (not (= x (* (rtz-sqrt x (1- n)) (rtz-sqrt x (1- n))))))
           (= (rtz (rto-sqrt x n) (- n 2))
              (rtz-sqrt x (- n 2))))
  :rule-classes ()
  :hints (("Goal" :use (rto-rto-sqrt-15
                        rto-rto-sqrt-14))))

(local-defthm rto-rto-sqrt-17
  (implies (and (natp n)
                (>= n 3)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (not (= (rtz-sqrt x (- n 2)) (rtz-sqrt x (1- n))))
                (not (= x (* (rtz-sqrt x (1- n)) (rtz-sqrt x (1- n))))))
           (= (rto (rto-sqrt x n) (1- n))
              (+ (rtz-sqrt x (- n 2)) (expt 2 (- 1 n)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable sgn rto)
                  :use (rto-rto-sqrt-10
                        rto-rto-sqrt-16
                        rto-sqrt-bounds
                        (:instance exactp-<= (x (rto-sqrt x n)) (m (- n 2)) (n (1- n)))))))

(local-defthm rto-rto-sqrt-18
  (implies (and (natp n)
                (>= n 3)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (not (= x (* (rtz-sqrt x (1- n)) (rtz-sqrt x (1- n))))))
           (< (* (rtz-sqrt x (- n 2)) (rtz-sqrt x (- n 2))) x))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable rtz-sqrt)
                  :use ((:instance rtz-sqrt-square-bounds (n (1- n)))
                        (:instance square-leq (x (rtz-sqrt x (- n 2))) (y (rtz-sqrt x (1- n))))))))

(local-defthm rto-rto-sqrt-19
  (implies (and (natp n)
                (>= n 3)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (not (= x (* (rtz-sqrt x (1- n)) (rtz-sqrt x (1- n))))))
           (= (rto-sqrt x (1- n))
              (+ (rtz-sqrt x (- n 2)) (expt 2 (- 1 n)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable rto-sqrt)
                  :use (rto-rto-sqrt-18))))

(local-defthm rto-rto-sqrt-20
  (implies (and (natp n)
                (>= n 3)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (not (= (rtz-sqrt x (- n 2)) (rtz-sqrt x (1- n))))
                (not (= x (* (rtz-sqrt x (1- n)) (rtz-sqrt x (1- n))))))
           (= (rto (rto-sqrt x n) (1- n))
              (rto-sqrt x (1- n))))
  :rule-classes ()
  :hints (("Goal" :use (rto-rto-sqrt-17
                        rto-rto-sqrt-19))))

(local-defthm rto-rto-sqrt-21
  (implies (and (natp n)
                (>= n 3)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (= (rtz-sqrt x (- n 2)) (rtz-sqrt x (1- n)))
                (not (= x (* (rtz-sqrt x (1- n)) (rtz-sqrt x (1- n))))))
           (= (rto-sqrt x n)
              (+ (rtz-sqrt x (- n 2)) (expt 2 (- n)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable rto-sqrt)
                  :use (rto-rto-sqrt-3
                        (:instance rtz-sqrt-square-bounds (n (1- n)))))))

(local-defthm rto-rto-sqrt-22
  (implies (and (natp n)
                (>= n 3)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (= (rtz-sqrt x (- n 2)) (rtz-sqrt x (1- n)))
                (not (= x (* (rtz-sqrt x (1- n)) (rtz-sqrt x (1- n))))))
           (< (rto-sqrt x n)
              (fp+ (rtz-sqrt x (- n 2)) (- n 2))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable rto-sqrt)
                  :use (rto-rto-sqrt-21
                        rto-rto-sqrt-11
                        (:instance rtz-sqrt-square-bounds (n (- n 2)))))))

(local-defthm rto-rto-sqrt-23
  (implies (and (natp n)
                (>= n 3)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (= (rtz-sqrt x (- n 2)) (rtz-sqrt x (1- n)))
                (not (= x (* (rtz-sqrt x (1- n)) (rtz-sqrt x (1- n))))))
           (>= (rto-sqrt x n)
               (rtz-sqrt x (- n 2))))
  :rule-classes ()
  :hints (("Goal" :use (rto-rto-sqrt-21))))

(local-defthm rto-rto-sqrt-24
  (implies (and (natp n)
                (>= n 3)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (= (rtz-sqrt x (- n 2)) (rtz-sqrt x (1- n)))
                (not (= x (* (rtz-sqrt x (1- n)) (rtz-sqrt x (1- n))))))
           (>= (rtz (rto-sqrt x n) (- n 2))
               (rtz-sqrt x (- n 2))))
  :rule-classes ()
  :hints (("Goal" :use (rto-rto-sqrt-23
                        (:instance exactp-rtz-sqrt (n (- n 2)))
                        (:instance rtz-exactp-c (a (rtz-sqrt x (- n 2))) (x (rto-sqrt x n)) (n (- n 2)))))))

(local-defthm rto-rto-sqrt-25
  (implies (and (natp n)
                (>= n 3)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (= (rtz-sqrt x (- n 2)) (rtz-sqrt x (1- n)))
                (not (= x (* (rtz-sqrt x (1- n)) (rtz-sqrt x (1- n))))))
           (<= (rtz (rto-sqrt x n) (- n 2))
               (rtz-sqrt x (- n 2))))
  :rule-classes ()
  :hints (("Goal" :use (rto-rto-sqrt-22
                        rto-sqrt-bounds
                        (:instance exactp-rtz-sqrt (n (- n 2)))
                        (:instance rtz-sqrt-bounds (n (- n 2)))
                        (:instance rtz-upper-pos (x (rto-sqrt x n)) (n (- n 2)))
                        (:instance fp+2 (x (rtz-sqrt x (- n 2))) (y (rtz (rto-sqrt x n) (- n 2))) (n (- n 2)))))))

(local-defthm rto-rto-sqrt-26
  (implies (and (natp n)
                (>= n 3)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (= (rtz-sqrt x (- n 2)) (rtz-sqrt x (1- n)))
                (not (= x (* (rtz-sqrt x (1- n)) (rtz-sqrt x (1- n))))))
           (= (rtz (rto-sqrt x n) (- n 2))
              (rtz-sqrt x (- n 2))))
  :rule-classes ()
  :hints (("Goal" :use (rto-rto-sqrt-25
                        rto-rto-sqrt-24))))

(local-defthm rto-rto-sqrt-27
  (implies (and (natp n)
                (>= n 3)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (= (rtz-sqrt x (- n 2)) (rtz-sqrt x (1- n)))
                (not (= x (* (rtz-sqrt x (1- n)) (rtz-sqrt x (1- n))))))
           (= (rto (rto-sqrt x n) (1- n))
              (+ (rtz-sqrt x (- n 2)) (expt 2 (- 1 n)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable sgn rto)
                  :use (rto-rto-sqrt-10
                        rto-rto-sqrt-26
                        rto-sqrt-bounds
                        (:instance exactp-<= (x (rto-sqrt x n)) (m (- n 2)) (n (1- n)))))))

(local-defthm rto-rto-sqrt-28
  (implies (and (natp n)
                (>= n 3)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (not (= x (* (rtz-sqrt x (1- n)) (rtz-sqrt x (1- n))))))
           (= (rto (rto-sqrt x n) (1- n))
              (rto-sqrt x (1- n))))
  :rule-classes ()
  :hints (("Goal" :use (rto-rto-sqrt-20
                        rto-rto-sqrt-27
                        rto-rto-sqrt-19))))

(local-defthm rto-rto-sqrt-29
  (implies (and (natp n)
                (>= n 3)
                (rationalp x)
                (<= 1/4 x)
                (< x 1))
           (= (rto (rto-sqrt x n) (1- n))
              (rto-sqrt x (1- n))))
  :rule-classes ()
  :hints (("Goal" :use (rto-rto-sqrt-2
                        rto-rto-sqrt-5
                        rto-rto-sqrt-28))))

#|
Proof: Let a1 = rtz-sqrt(x, n-2), r1 = rto-sqrt(x, n-1), a2 = rtz-sqrt(x, n-1), and r2 = rto-sqrt(x, n).
expo(a1) = expo(r1) = expo(a2) = expo(r2) = 0.
Show rto(r2, n-1) = r1.  Note that 1 <= a1^2 <= a^2 <= x.

Case 1: a1 = a2 and a2^2 = x.

a1 = r1 = a2 = r2.  Since r2 is (n-1)-exact, rto(r2, n-1) = r2 = r1.

Case 2: a1 = a2 and a2^2 < x.

r1 = a1 + 2^(2-n) is not (n-2)-exact, r2 = a2 + 2^(1-n) is not (n-1)-exact.
rto(r2, n-1) = rtz(r2, n-2) + 2^(2-n) = a1 + 2^(2-n) = r1.

Case 3: a1 < a2 and a2^2 = x.

r1 = a2 = r2 = a1 + 2^(2-n) is (n-1)-exact.
rto(r2, n-1) = r2 = r1.

Case 4: a1 < a2 and a2^2 < x.

r1 = a2 = a1 + 2^(2-n) and r2 = a2 + 2^(1-n) = a1 + 2^(2-n) + 2^(1-n).
rto(r2, n-1) = rtz(r2, n-2) + 2^(2-n) = a1 + 2^(2-n) = r1.
|#

(local-defthm rto-rto-sqrt-30
  (implies (and (natp n)
                (>= n 2)
                (natp m)
                (> m n)
                (rationalp x)
                (<= 1/4 x)
                (< x 1))
          (= (rto (rto-sqrt x (1- m)) n)
             (rto (rto-sqrt x m) n)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rto-rto-sqrt-29 (n m))
                        (:instance rto-rto (x (rto-sqrt x m)) (n (1- m)) (m n))))))

(local-defun natp-induct (n)
  (if (zp n)
      ()
    (1+ (natp-induct (1- n)))))

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
  :hints (("Goal" :induct (natp-induct m))
          ("Subgoal *1/2" :use (rto-rto-sqrt-30
                                exactp-rto-sqrt
                                (:instance rto-exactp-b (x (rto-sqrt x n)))))))

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
  :hints (("Goal" :use (rto-rto-sqrt
                        (:instance rnd-rto (x (rto-sqrt x m)) (m k))))))

(local-defthm rtz-rto-sqrt-1
  (implies (and (natp n)
                (>= n 2)
                (rationalp x)
                (<= 1/4 x)
                (< x 1))
           (and (<= (rtz-sqrt x n) (rto-sqrt x (1+ n)))
                (< (rto-sqrt x (1+ n)) (fp+ (rtz-sqrt x n) n))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable rto-sqrt))))

(local-defthm rtz-rto-sqrt-2
  (implies (and (natp n)
                (>= n 2)
                (rationalp x)
                (<= 1/4 x)
                (< x 1))
           (= (rtz (rto-sqrt x (1+ n)) n)
              (rtz-sqrt x n)))
  :rule-classes ()
  :hints (("Goal" :use (rtz-sqrt-bounds
                        exactp-rtz-sqrt
                        rtz-rto-sqrt-1
                        (:instance rtz-exactp-b (x (rtz-sqrt x n)))
                        (:instance rtz-monotone (x (rtz-sqrt x n)) (y (rto-sqrt x (1+ n))))
                        (:instance rto-sqrt-bounds (n (1+ n)))
                        (:instance fp+2 (x (rtz-sqrt x n)) (y (rtz (rto-sqrt x (1+ n)) n)))
                        (:instance rtz-upper-pos (x (rto-sqrt x (1+ n))))))))

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
  :hints (("Goal" :use (rtz-rto-sqrt-2
                        (:instance rto-rto-sqrt (n (1+ n)))
                        (:instance rtz-rto (x (rto-sqrt x m)) (n (1+ n)) (m n))))))

(local-defthmd rtz-rtz-rto-1
   (implies (and (natp n)
                (>= n 2)
                (natp m)
                (>= m n)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (= (* (rtz-sqrt x n) (rtz-sqrt x n)) x))
            (equal (rtz-sqrt x m)
                   (rtz-sqrt x n)))
  :hints (("Goal" :induct (natp-induct m))
          ("Subgoal *1/2" :in-theory (enable rtz-sqrt))))

(local-defthmd rtz-rtz-rto-2
   (implies (and (natp n)
                (>= n 2)
                (natp m)
                (> m n)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (= (* (rtz-sqrt x n) (rtz-sqrt x n)) x))
            (equal (rto-sqrt x m)
                   (rtz-sqrt x n)))
  :hints (("Goal" :use ((:instance rtz-rtz-rto-1 (m (1- m))))
                  :in-theory (enable rto-sqrt))))

(local-defthmd rtz-rtz-rto-3
   (implies (and (natp n)
                (>= n 2)
                (natp m)
                (>= m n)
                (rationalp x)
                (<= 1/4 x)
                (< x 1))
            (<= (rtz-sqrt x n)
                (rtz-sqrt x m)))
  :hints (("Goal" :induct (natp-induct m))
          ("Subgoal *1/2" :in-theory (enable rtz-sqrt))))

(local-defthmd rtz-rtz-rto-4
   (implies (and (natp n)
                (>= n 2)
                (natp m)
                (> m n)
                (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (< (* (rtz-sqrt x n) (rtz-sqrt x n)) x))
            (< (rtz-sqrt x n)
               (rto-sqrt x m)))
  :hints (("Goal" :use (rtz-sqrt-bounds
                        (:instance rtz-sqrt-bounds (n (1- m)))
                        (:instance rtz-rtz-rto-3 (m (1- m)))
                        (:instance square-leq (x (rtz-sqrt x m)) (y (rtz-sqrt x n)))
                        (:instance square-leq (x (rtz-sqrt x n)) (y (rtz-sqrt x m))))
                  :in-theory (enable rto-sqrt))))

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
  :hints (("Goal" :use (rtz-rtz-rto-2
                        rtz-rtz-rto-4
                        rtz-sqrt-square-bounds))))

(defthmd qsqrt-rto-sqrt
  (implies (and (rationalp x)
                (<= 1/4 x)
                (< x 1)
                (integerp n)
                (> n 1))
           (equal (qsqrt x n)
                  (rto-sqrt x n)))
  :hints (("Goal" :in-theory (enable qsqrt)
                  :use ((:instance expo-unique (n -1))
                        (:instance expo-unique (n -2))))))

(local-defthm qsqrt-lower-1
  (implies (rationalp x)
           (and (>= x (* 2 (fl (/ x 2))))
                (<  x (+ 2 (* 2 (fl (/ x 2)))))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance fl-def (x (/ x 2)))))))

(local-defthm qsqrt-lower-2
  (implies (integerp x)
           (or (= x (* 2 (fl (/ x 2))))
               (= x (1+ (* 2 (fl (/ x 2)))))))
  :rule-classes ()
  :hints (("Goal" :use (qsqrt-lower-1))))

(local-defthm qsqrt-lower-3
  (implies (and (rationalp x)
                (> x 0))
           (let* ((e (1+ (fl (/ (expo x) 2))))
                  (x0 (/ x (expt 2 (* 2 e)))))
             (or (= x0 (/ (sig x) 2))
                 (= x0 (/ (sig x) 4)))))
  :rule-classes ()
  :hints (("Goal" :use (fp-abs
                        (:instance qsqrt-lower-2 (x (expo x)))))))

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
  :hints (("Goal" :use (qsqrt-lower-3
                        (:instance x0-bounds-1 (x0 (/ x (expt 2 (* 2 (1+ (fl (/ (expo x) 2))))))))))))

(local-defthm qsqrt-lower-4
  (implies (and (rationalp x)
                (> x 0))
           (and (< (/ (sig x) 4) 1)
                (<= 1/4 (/ (sig x) 4))
                (< (/ (sig x) 2) 1)
                (<= 1/4 (/ (sig x) 2))))
  :rule-classes ()
  :hints (("Goal" :use (sig-lower-bound
                        sig-upper-bound))))

(local-defthm qsqrt-lower-5
  (implies (and (rationalp x)
                (> x 0)
                (or (= x0 (/ (sig x) 2))
                    (= x0 (/ (sig x) 4))))
           (and (<= 1/4 x0)
                (< x0 1)))
  :rule-classes ()
  :hints (("Goal" :use (qsqrt-lower-4
                        sig-upper-bound
                        sig-lower-bound))))

(defthm qsqrt-expo
  (implies (and (rationalp x)
                (> x 0))
           (let* ((e (1+ (fl (/ (expo x) 2))))
                  (xp (/ x (expt 2 (* 2 e)))))
             (and (<= 1/4 xp)
                  (< xp 1))))
  :rule-classes ()
  :hints (("Goal" :use (qsqrt-lower-3
                        (:instance qsqrt-lower-5 (x0 (/ x (expt 2 (* 2 (1+ (fl (/ (expo x) 2))))))))))))

(local-defthm qsqrt-lower-7
  (implies (and (rationalp x)
                (> x 0)
                (rationalp l)
                (<= (* l l) x))
           (let* ((e (1+ (fl (/ (expo x) 2))))
                  (x0 (/ x (expt 2 (* 2 e))))
                  (l0 (/ l (expt 2 e))))
             (<= (* l0 l0) x0)))
  :rule-classes ())

(local-defthm qsqrt-lower-8
  (implies (and (rationalp x)
                (> x 0)
                (integerp n)
                (> n 1)
                (rationalp l)
                (<= (* l l) x))
           (<= (rto l n) (qsqrt x n)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable qsqrt)
                  :use (qsqrt-expo
                        qsqrt-lower-7
                        (:instance rto-shift (x (/ l (expt 2 (1+ (fl (/ (expo x) 2))))))
                                                (k (1+ (fl (/ (expo x) 2)))))
                        (:instance rto-sqrt-lower (l (/ l (expt 2 (1+ (fl (/ (expo x) 2))))))
                                                 (x (/ x (expt 2 (* 2 (1+ (fl (/ (expo x) 2))))))))))))

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
  :hints (("Goal" :use (qsqrt-lower-8
                        (:instance rnd-rto (x l) (m k))
                        (:instance rnd-monotone (x (rto l n)) (y (qsqrt x n)) (n k))))))

#|
Proof: Let e = fl(expo(x)/2), x0 = x/2^(2*e), and l0 = l/2^e.
Then 1 <= x0 < 4 and l0^2 = l^2/2^(2*e) <= x/2^(2*e) = x0.
By rto-shift and rto-sqrt-lower,

  rto(l, 66) = 2^e * rto(l0, n)
               <= 2^e * rto-sqrt(x0, n)
                = sqrt(x, n).

By rnd-rto and rnd-monotone,

  rnd(l, mode, k) = rnd(rto(l, n), mode, k)
                 <= rnd(sqrt(x, n), mode, k)
|#

(local-defthm qsqrt-upper-1
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

(local-defthm qsqrt-upper-2
  (implies (and (rationalp x)
                (> x 0)
                (integerp n)
                (> n 2)
                (rationalp h)
                (>= h 0)
                (>= (* h h) x))
            (>= (rto h n) (qsqrt x n)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable qsqrt)
                  :use (qsqrt-expo
                        qsqrt-upper-1
                        (:instance rto-shift (x (/ h (expt 2 (1+ (fl (/ (expo x) 2))))))
                                                (k (1+ (fl (/ (expo x) 2)))))
                        (:instance rto-sqrt-upper (h (/ h (expt 2 (1+ (fl (/ (expo x) 2))))))
                                                     (x (/ x (expt 2 (* 2 (1+ (fl (/ (expo x) 2))))))))))))

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
  :hints (("Goal" :use (qsqrt-upper-2
                        (:instance rnd-rto (x h) (m k))
                        (:instance rnd-monotone (y (rto h n)) (x (qsqrt x n)) (n k))))))

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

(local-defthm exactp-cmp-rto-sqrt-1
  (implies (and (rationalp x) (>= x 1/4) (< x 1)
                (rationalp y) (> y 0)
                (integerp n) (> n 1)
                (exactp y (1- n))
                (< y (rtz-sqrt x (1- n))))
           (and (< (* y y) x) (< y (rto-sqrt x n))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable rto-sqrt)
                  :use ((:instance rtz-sqrt-square-bounds (n (1- n)))
                        (:instance sq-leq (x (rtz-sqrt x (1- n))))))))

(local-defthm exactp-cmp-rto-sqrt-2
  (implies (integerp k)
           (> (expt 2 k) (expt 2 (1- k))))
  :rule-classes ())

(local-defthm exactp-cmp-rto-sqrt-3
  (implies (and (rationalp x) (>= x 1/4) (< x 1)
                (rationalp y) (> y 0)
                (integerp n) (> n 1))
           (> (+ (rtz-sqrt x (1- n)) (expt 2 (- 1 n)))
              (rto-sqrt x n)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable rto-sqrt)
                  :use ((:instance exactp-cmp-rto-sqrt-2 (k (- 1 n)))))))

(local-defthm exactp-cmp-rto-sqrt-4
  (implies (and (rationalp x) (>= x 1/4) (< x 1)
                (rationalp y) (> q 0)
                (integerp n) (> n 1)
                (exactp y (1- n))
                (> y (rtz-sqrt x (1- n))))
           (and (> (* y y) x) (> y (rto-sqrt x n))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable expo-rtz-sqrt)
                  :use (exactp-cmp-rto-sqrt-3
                        (:instance exactp-rtz-sqrt (n (1- n)))
                        (:instance expo-rtz-sqrt (n (1- n)))
                        (:instance fp+2 (x (rtz-sqrt x (1- n))) (n (1- n)))
                        (:instance rtz-sqrt-square-bounds (n (1- n)))
                        (:instance sq-leq (x (+ (rtz-sqrt x (1- n)) (expt 2 (- 1 n)))))))))

(defthm exactp-cmp-rto-sqrt
  (implies (and (rationalp x) (>= x 1/4) (< x 1)
                (rationalp q) (> q 0)
                (integerp n) (> n 1)
                (exactp q (1- n)))
           (and (iff (< (* q q) x) (< q (rto-sqrt x n)))
                (iff (> (* q q) x) (> q (rto-sqrt x n)))))
  :rule-classes ()
  :hints (("Goal" :cases ((< q (rtz-sqrt x (1- n))) (> q (rtz-sqrt x (1- n))))
                  :in-theory (enable rto-sqrt)
                  :use ((:instance exactp-cmp-rto-sqrt-1 (y q))
                        (:instance exactp-cmp-rto-sqrt-4 (y q))
                        (:instance rtz-sqrt-square-bounds (n (1- n)))))))

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
  :hints (("Goal" :use ((:instance exactp-cmp-rto-sqrt-2 (k (+ 2 (expo x))))))))

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
  :hints (("Goal" :use ((:instance exactp-cmp-rto-sqrt-2 (k (expo x)))))))

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
                        (:instance exactp-cmp-rto-sqrt (x (/ x (expt 2 (* 2 (1+ (fl (/ (expo x) 2)))))))
                                                       (q (/ y (expt 2 (1+ (fl (/ (expo x) 2)))))))))))

(local-defthm exactp-cmp-qsqrt-18
  (implies (and (rationalp x)
                (rationalp y)
                (integerp k))
           (iff (< x y)
                (< (* x (expt 2 k)) (* y (expt 2 k)))))
  :rule-classes ())

(local-defthm exactp-cmp-qsqrt-19
  (implies (and (rationalp x) (> x 0)
                (rationalp q) (> q 0)
                (integerp n) (> n 1)
                (exactp q (1- n)))
           (and (iff (< (* q q) x) (< q (qsqrt x n)))
                (iff (> (* q q) x) (> q (qsqrt x n)))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance exactp-cmp-qsqrt-17 (y q))
                        (:instance exactp-cmp-qsqrt-18 (x (/ (* q q) (expt 2 (* 2 (1+ (fl (/ (expo x) 2)))))))
                                                       (y (/ x (expt 2 (* 2 (1+ (fl (/ (expo x) 2)))))))
                                                       (k (* 2 (1+ (fl (/ (expo x) 2))))))
                        (:instance exactp-cmp-qsqrt-18 (x (/ q (expt 2 (1+ (fl (/ (expo x) 2))))))
                                                       (y (/ (qsqrt x n) (expt 2 (1+ (fl (/ (expo x) 2))))))
                                                       (k (1+ (fl (/ (expo x) 2)))))
                        (:instance exactp-cmp-qsqrt-18 (y (/ (* q q) (expt 2 (* 2 (1+ (fl (/ (expo x) 2)))))))
                                                       (x (/ x (expt 2 (* 2 (1+ (fl (/ (expo x) 2)))))))
                                                       (k (* 2 (1+ (fl (/ (expo x) 2))))))
                        (:instance exactp-cmp-qsqrt-18 (y (/ q (expt 2 (1+ (fl (/ (expo x) 2))))))
                                                       (x (/ (qsqrt x n) (expt 2 (1+ (fl (/ (expo x) 2))))))
                                                       (k (1+ (fl (/ (expo x)
                                                                     2)))))))))

(defthm exactp-cmp-qsqrt
  (implies (and (rationalp x) (> x 0)
                (rationalp q) (> q 0)
                (integerp n) (> n 1)
                (exactp q (1- n)))
           (and (iff (< (* q q) x) (< q (qsqrt x n)))
                (iff (> (* q q) x) (> q (qsqrt x n)))
                (iff (= (* q q) x) (= q (qsqrt x n)))))
  :rule-classes ()
  :hints (("Goal" :use (exactp-cmp-qsqrt-19))))

(defthmd qsqrt-sqrt
  (implies (and (rationalp x) (> x 0)
                (integerp n) (> n 1)
		(exactp (qsqrt x n) (1- n)))
	   (equal (* (qsqrt x n) (qsqrt x n))
	          x))
  :hints (("Goal" :use (qsqrt-pos (:instance exactp-cmp-qsqrt (q (qsqrt x n)))))))

(defthm rnd-qsqrt-equal
  (implies (and (rationalp x)
                (> x 0)
                (not (zp k))
                (natp n)
                (>= n (+ k 2))
                (natp m)
                (>= m n)
		(common-mode-p mode))
           (equal (rnd (qsqrt x m) mode k)
	          (rnd (qsqrt x n) mode k)))
  :rule-classes ()
  :hints (("Goal" :use (qsqrt-expo
                        (:instance rnd-rto-sqrt (x (/ x (expt 2 (* 2 (1+ (fl (/ (expo x) 2))))))))
                        (:instance rnd-shift (n k) (k (1+ (fl (/ (expo x) 2))))
			                     (x (rto-sqrt (/ x (expt 2 (* 2 (1+ (fl (/ (expo x) 2)))))) n)))
                        (:instance rnd-shift (n k) (k (1+ (fl (/ (expo x) 2))))
			                     (x (rto-sqrt (/ x (expt 2 (* 2 (1+ (fl (/ (expo x) 2)))))) m))))
		  :in-theory (enable qsqrt))))

(defthm qsqrt-exact-equal
  (implies (and (rationalp x)
                (> x 0)
                (not (zp k))
                (natp n)
                (> n k)
                (natp m)
		(> m k)
		(exactp (qsqrt x n) k))
	   (equal (qsqrt x n) (qsqrt x m)))
  :rule-classes ()
  :hints (("Goal" :use (qsqrt-sqrt qsqrt-pos
                        (:instance exactp-<= (x (qsqrt x n)) (m k) (n (1- n)))
                        (:instance exactp-<= (x (qsqrt x n)) (m k) (n (1- m)))
                        (:instance exactp-cmp-qsqrt (q (qsqrt x n)) (n m))))))
