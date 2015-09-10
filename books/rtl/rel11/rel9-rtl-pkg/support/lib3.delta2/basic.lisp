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

(in-package "RTL")

(local (include-book "../lib3/top"))

;;;**********************************************************************
;;;                       FLOOR and CEILING
;;;**********************************************************************

(defund fl (x)
  (declare (xargs :guard (real/rationalp x)))
  (floor x 1))

(defthm fl-def
  (and (integerp (fl x))
       (implies (case-split (rationalp x))
	        (and (<= (fl x) x)
		     (< x (1+ (fl x))))))
  :rule-classes ((:linear :corollary
                          (implies (case-split (rationalp x))
                                   (and (<= (fl x) x)
                                        (< x (1+ (fl x))))))
                 (:type-prescription :corollary
                                     (integerp (fl x)))))

(defthm fl-unique
    (implies (and (rationalp x)
		  (integerp n)
		  (<= n x)
		  (< x (1+ n)))
	     (equal (fl x) n))
  :rule-classes ())

(defthm fl-integerp
  (equal (equal (fl x) x)
         (integerp x)))

(defthm quot-bnd
  (implies (and (<= 0 x)
                (<= 0 y)
                (rationalp x)
                (rationalp y))
           (<= (* y (fl (/ x y)))
               x))
  :rule-classes :linear)

(defthm fl-monotone-linear
    (implies (and (<= x y)
		  (rationalp x)
		  (rationalp y))
	     (<= (fl x) (fl y)))
  :rule-classes :linear)

(defthm n<=fl-linear
    (implies (and (<= n x)
		  (rationalp x)
		  (integerp n))
	     (<= n (fl x)))
  :rule-classes :linear)

(defthm fl+int-rewrite
    (implies (and (integerp n)
		  (rationalp x))
	     (equal (fl (+ x n)) (+ (fl x) n))))

(defthm fl/int-rewrite
  (implies (and (integerp n)
                (<= 0 n)
                (rationalp x))
           (equal (fl (* (fl x) (/ n)))
                  (fl (/ x n)))))

(defthm fl/int-rewrite-alt
  (implies (and (integerp n)
                (<= 0 n)
                (rationalp x))
           (equal (fl (* (/ n) (fl x)))
                  (fl (/ x n)))))

(defthmd fl-minus
  (implies (rationalp x)
           (equal (fl (* -1 x))
                  (if (integerp x)
                      (* -1 x)
                    (1- (* -1 (fl x)))))))

(defthm fl-m-n
  (implies (and (< 0 n)
                (integerp m)
                (integerp n))
           (= (fl (- (/ m n)))
              (1- (- (fl (/ (1- m) n))))))
  :rule-classes ())

(defund cg (x)
  (declare (xargs :guard (real/rationalp x)))
  (- (fl (- x))))

(defthm cg-def
  (and (integerp (cg x))
       (implies (case-split (rationalp x))
                (and (>= (cg x) x)
                     (> (1+ x) (cg x)))))
  :rule-classes ((:linear :corollary
                          (implies (case-split (rationalp x))
                                   (and (>= (cg x) x)
                                        (> (1+ x) (cg x)))))
                 (:type-prescription :corollary
                                     (integerp (cg x)))))

(defthm cg-unique
    (implies (and (rationalp x)
		  (integerp n)
		  (>= n x)
		  (> (1+ x) n))
	     (equal (cg x) n))
  :rule-classes ())

(defthm cg-integerp
    (implies (rationalp x)
	     (equal (equal (cg x) x)
                    (integerp x))))

(defthm cg-monotone-linear
    (implies (and (rationalp x)
		  (rationalp y)
		  (<= x y))
	     (<= (cg x) (cg y)))
  :rule-classes :linear)

(defthm n>=cg-linear
    (implies (and (>= n x)
		  (rationalp x)
		  (integerp n))
	     (>= n (cg x)))
  :rule-classes :linear)

(defthm cg+int-rewrite
    (implies (and (integerp n)
		  (rationalp x))
	     (equal (cg (+ x n)) (+ (cg x) n))))

(defthm cg/int-rewrite
  (implies (and (integerp n)
                (> n 0)
                (rationalp x))
           (equal (cg (* (cg x) (/ n)))
                  (cg (/ x n)))))

(defthm cg/int-rewrite-alt
  (implies (and (integerp n)
                (> n 0)
                (rationalp x))
           (equal (cg (* (/ n) (cg x)))
                  (cg (/ x n)))))

(defthm fl-cg
  (implies (rationalp x)
           (equal (cg x)
                  (if (integerp x)
                      (fl x)
                    (1+ (fl x)))))
  :rule-classes ())


;;;**********************************************************************
;;;                         MOD
;;;**********************************************************************
(in-theory (disable mod))

(defthm mod-def
  (implies (case-split (acl2-numberp x))
           (equal (mod x y)
                  (- x (* y (fl (/ x y))))))
  :rule-classes ())

(defthm mod-0
    (and (equal (mod 0 y)
                0)
         (equal (mod x 0)
                (fix x))))

(defthm rationalp-mod
  (implies (rationalp x)
           (rationalp (mod x y)))
  :rule-classes (:rewrite :type-prescription))

(defthm integerp-mod
  (implies (and (integerp m) (integerp n))
           (integerp (mod m n)))
  :rule-classes (:rewrite :type-prescription))


(defthm natp-mod
   (implies (and (natp m)
                 (natp n))
            (natp (mod m n)))
   :rule-classes ((:type-prescription :typed-term (mod m n))))


(defthm natp-mod-2
   (implies (and (integerp m)
                 (integerp n)
                 (> n 0))
            (natp (mod m n)))
   :rule-classes ((:type-prescription :typed-term (mod m n))))


(defthm mod-bnd-1
  (implies (and (case-split (< 0 n))
                (case-split (not (complex-rationalp m)))
                (case-split (not (complex-rationalp n))))
           (< (mod m n) n))
  :rule-classes :linear)

(defthm mod-by-1
  (implies (integerp m)
           (equal (mod m 1)
                  0)))

(defthm mod-bnd-2
  (implies (and (<= 0 m)
                (case-split (rationalp m)))
           (<= (mod m n) m))
  :rule-classes :linear)

(defthm mod-does-nothing
  (implies (and (< m n)
                (<= 0 m)
                (case-split (rationalp m)))
           (equal (mod m n)
                  m)))

(defthm mod-0-fl
  (implies (acl2-numberp m)
           (iff (= (mod m n) 0)
	        (= m (* (fl (/ m n)) n))))
  :rule-classes ())

(defthm mod-0-int
  (implies (and (integerp m)
                (integerp n)
                (not (= n 0)))
           (iff (= (mod m n) 0)
                (integerp (/ m n))))
  :rule-classes ())

(defthm mod-mult-n
  (equal (mod (* a n) n)
         (* n (mod a 1))))

(defthm mod-mult-n-alt
  (equal (mod (* n a) n)
         (* n (mod a 1))))

(defthm mod-squeeze
    (implies (and (= (mod m n) 0)
		  (< m (* (1+ a) n))
                  (< (* (1- a) n) m)
                  (integerp a)
		  (integerp m)
		  (integerp n))
	     (= m (* a n)))
  :rule-classes ())

(defthm mod-must-be-n
    (implies (and (= (mod m n) 0)
		  (< m (* 2 n))
                  (< 0 m)
		  (rationalp m)
		  (rationalp n))
	     (= m n))
  :rule-classes ())

(defthm mod-0-0
  (implies (and (integerp p)
                (rationalp m)
                (rationalp n))
           (iff (= (mod m (* n p)) 0)
                (and (= (mod m n) 0)
                     (= (mod (fl (/ m n)) p) 0))))
  :rule-classes ())

(defthm mod-equal-int
  (implies (and (= (mod a n) (mod b n))
                (rationalp a)
                (rationalp b))
           (integerp (/ (- a b) n)))
  :rule-classes ())

(defthm mod-equal-int-reverse
  (implies (and (integerp (/ (- a b) n))
                (rationalp a)
                (rationalp b)
                (rationalp n)
                (< 0 n))
           (= (mod a n) (mod b n)))
  :rule-classes ())

(defthm mod-force-equal
  (implies (and (< (abs (- a b)) n)
                (rationalp a)
                (rationalp b)
                (integerp n))
          (iff (= (mod a n) (mod b n))
               (= a b)))
  :rule-classes ())

(defthm mod-mult
    (implies (and (integerp a)
                  (rationalp m)
		  (rationalp n))
	     (equal (mod (+ m (* a n)) n)
		    (mod m n))))

(defthm mod-force
  (implies (and (<= (* a n) m)
                (< m (* (1+ a) n))
                (integerp a)
                (rationalp m)
                (rationalp n))
           (= (mod m n) (- m (* a n))))
  :rule-classes ())

(defthm mod-bnd-3
  (implies (and (< m (+ (* a n) r))
                (<= (* a n) m)
                (integerp a)
                (case-split (rationalp m))
                (case-split (rationalp n)))
           (< (mod m n) r))
  :rule-classes :linear)

(defthmd mod-sum
    (implies (and (rationalp a)
		  (rationalp b))
	     (equal (mod (+ a (mod b n)) n)
		    (mod (+ a b) n))))

(defthmd mod-mod-sum
    (implies (and (rationalp a)
		  (rationalp b))
	     (equal (mod (+ (mod a n) (mod b n)) n)
		    (mod (+ a b) n))))

(defthmd mod-diff
  (implies (and (case-split (rationalp a))
                (case-split (rationalp b)))
           (equal (mod (- a (mod b n)) n)
                  (mod (- a b) n))))

(defthmd mod-of-mod
  (implies (and (case-split (natp k))
                (case-split (natp n)))
           (equal (mod (mod x (* k n)) n)
                  (mod x n))))

(defthmd mod-of-mod-cor
  (implies (and (<= b a)
                (case-split (integerp b))
                (case-split (integerp a)))
           (equal (mod (mod x (expt 2 a)) (expt 2 b))
                  (mod x (expt 2 b)))))

(defthmd mod-prod
  (implies (and (rationalp m)
                (rationalp n)
                (rationalp k))
           (equal (mod (* k m) (* k n))
                  (* k (mod m n)))))

(defthm mod012
  (implies (integerp m)
           (or (equal (mod m 2) 0)
               (equal (mod m 2) 1)))
  :rule-classes ())

(defthm mod-plus-mod-2
  (implies (and (integerp a)
                (integerp b))
           (iff (= (mod (+ a b) 2) (mod a 2))
                (= (mod b 2) 0)))
  :rule-classes ())

(defthm mod-mod-2-not-equal
  (implies (acl2-numberp m)
           (not (= (mod m 2) (mod (1+ m) 2))))
  :rule-classes ())

(defthm mod-2*m+1-rewrite
  (implies (integerp m)
           (equal (mod (1+ (* 2 m)) 2) 1)))

(defthm mod-mod-times
    (implies (and (integerp a)
		  (integerp b)
		  (integerp n)
		  (> n 0))
	     (= (mod (* (mod a n) b) n)
		(mod (* a b) n)))
  :rule-classes ())


(defthm mod-times-mod
    (implies (and (integerp a)
		  (integerp b)
		  (integerp c)
		  (not (zp n))
		  (= (mod a n) (mod b n)))
	     (= (mod (* a c) n) (mod (* b c) n)))
  :rule-classes ())


(defthm mod-plus-mod
    (implies (and (integerp a)
		  (integerp b)
		  (integerp c)
		  (not (zp n))
		  (= (mod a n) (mod b n)))
	     (= (mod (+ a c) n) (mod (+ b c) n)))
  :rule-classes ())



