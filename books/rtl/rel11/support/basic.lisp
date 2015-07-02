(in-package "RTL")

(include-book "std/util/defrule" :dir :system)

(local (include-book "arithmetic-5/top" :dir :system))

;; The following lemmas from arithmetic-5 have given me trouble:
#|
(local (in-theory #!acl2(disable |(mod (+ x y) z) where (<= 0 z)| |(mod (+ x (- (mod a b))) y)| |(mod (mod x y) z)| |(mod (+ x (mod a b)) y)|
                    simplify-products-gather-exponents-equal mod-cancel-*-const cancel-mod-+ reduce-additive-constant-< 
                    |(floor x 2)| |(equal x (if a b c))| |(equal (if a b c) x)|)))
|#

;;;**********************************************************************
;;;                       FLOOR and CEILING
;;;**********************************************************************

(defund fl (x)
  (declare (xargs :guard (real/rationalp x)))
  (floor x 1))

(defruled fl-default
  (implies (not (real/rationalp x))
           (equal (fl x) 0))
  :enable (fl))

(defrule fl-def
  (and (integerp (fl x))    
       (implies (case-split (real/rationalp x))
	        (and (<= (fl x) x)
		     (< x (1+ (fl x))))))
  :enable (fl)
  :rule-classes ((:linear :corollary
                          (implies (case-split (real/rationalp x))
                                   (and (<= (fl x) x)
                                        (< x (1+ (fl x))))))
                 (:type-prescription :corollary
                                     (integerp (fl x)))))

(defthm fl-unique
    (implies (and (real/rationalp x)
		  (integerp n)
		  (<= n x)
		  (< x (1+ n)))
	     (equal (fl x) n))
  :rule-classes ())

(defthm fl-integerp
  (equal (equal (fl x) x)
         (integerp x)))

(defthm integerp-fl
  (implies (integerp x)
           (equal (fl x) x)))

(defrule quot-bnd
  (implies (and (<= 0 x)
                (<= 0 y)
                (real/rationalp x)
                (real/rationalp y))
           (<= (* y (fl (/ x y)))
               x))
  :enable (fl)
  :rule-classes :linear)

(defthm fl-monotone-linear
    (implies (and (<= x y)
		  (real/rationalp x)
		  (real/rationalp y))
	     (<= (fl x) (fl y)))
  :rule-classes :linear)

(defthm n<=fl-linear
    (implies (and (<= n x)
		  (real/rationalp x)
		  (integerp n))
	     (<= n (fl x)))
  :rule-classes :linear)

(defthm fl+int-rewrite
    (implies (and (integerp n)
		  (real/rationalp x))
	     (equal (fl (+ x n)) (+ (fl x) n))))

(defrule fl/int-rewrite
  (implies (and (integerp n)
                (<= 0 n)
                (real/rationalp x))
           (equal (fl (* (fl x) (/ n)))
                  (fl (/ x n))))
  :enable (fl))

(defrule fl/int-rewrite-alt
  (implies (and (integerp n)
                (<= 0 n)
                (real/rationalp x))
           (equal (fl (* (/ n) (fl x)))
                  (fl (/ x n))))
  :enable (fl))

(defthm fl-half-int
  (implies (and (integerp n)
                (not (= n 0))
                (not (= n -1)))
           (< (abs (fl (/ n 2))) (abs n)))
  :rule-classes ())

(defthmd fl-minus
  (implies (real/rationalp x)
           (equal (fl (* -1 x))
                  (if (integerp x)
                      (* -1 x)
                    (1- (* -1 (fl x)))))))

(defrule fl-m-n
  (implies (and (< 0 n)
                (integerp m)
                (integerp n))
           (= (fl (- (/ m n)))
              (1- (- (fl (/ (1- m) n))))))
  :prep-books (
    (set-default-hints '((ACL2::nonlinearp-default-hint
                          ACL2::stable-under-simplificationp ACL2::hist
                          ACL2::pspv))))
  :enable (fl)
  :rule-classes ())

(defund cg (x)
  (declare (xargs :guard (real/rationalp x)))
  (- (fl (- x))))

(defruled cg-default
  (implies (not (real/rationalp x))
           (equal (cg x) 0))
  :enable (cg fl-default))

(defrule cg-def
  (and (integerp (cg x))
       (implies (case-split (real/rationalp x))
                (and (>= (cg x) x)
                     (> (1+ x) (cg x)))))
  :enable (cg)
  :rule-classes ((:linear :corollary
                          (implies (case-split (real/rationalp x))
                                   (and (>= (cg x) x)
                                        (> (1+ x) (cg x)))))
                 (:type-prescription :corollary
                                     (integerp (cg x)))))

(defthm cg-unique
    (implies (and (real/rationalp x)
		  (integerp n)
		  (>= n x)
		  (> (1+ x) n))
	     (equal (cg x) n))
  :rule-classes ())

(defthm cg-integerp
    (implies (real/rationalp x)
	     (equal (equal (cg x) x)
                    (integerp x))))

(defthm cg-monotone-linear
    (implies (and (real/rationalp x)
		  (real/rationalp y)
		  (<= x y))
	     (<= (cg x) (cg y)))
  :rule-classes :linear)

(defthm n>=cg-linear
    (implies (and (>= n x)
		  (real/rationalp x)
		  (integerp n))
	     (>= n (cg x)))
  :rule-classes :linear)

(defthm cg+int-rewrite
    (implies (and (integerp n)
		  (real/rationalp x))
	     (equal (cg (+ x n)) (+ (cg x) n))))

(defrule cg/int-rewrite
  (implies (and (integerp n)
                (> n 0)
                (real/rationalp x))
           (equal (cg (* (cg x) (/ n)))
                  (cg (/ x n))))
  :enable (cg))

(defrule cg/int-rewrite-alt
  (implies (and (integerp n)
                (> n 0)
                (real/rationalp x))
           (equal (cg (* (/ n) (cg x)))
                  (cg (/ x n))))
  :enable (cg))

(defthm fl-cg
  (implies (real/rationalp x)
           (equal (cg x)
                  (if (integerp x)
                      (fl x)
                    (1+ (fl x)))))
  :rule-classes ())


;;;**********************************************************************
;;;                         MOD
;;;**********************************************************************

(defrule mod-def
  (implies (case-split (acl2-numberp x))
           (equal (mod x y)
                  (- x (* y (fl (/ x y))))))
  :enable (fl)
  :rule-classes ())

(defthm mod-0
    (and (equal (mod 0 y)
                0)
         (equal (mod x 0)
                (fix x))))

#-non-standard-analysis
(defthm rationalp-mod
  (implies (rationalp x)
           (rationalp (mod x y)))
  :rule-classes (:rewrite :type-prescription))

#+non-standard-analysis
(defthm rationalp-mod
  (implies (and (rationalp x)
                (rationalp y))
           (rationalp (mod x y)))
  :rule-classes (:rewrite :type-prescription))

#+non-standard-analysis
(defthm realp-mod
  (implies (real/rationalp x)
           (real/rationalp (mod x y)))
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
                (case-split (not (complex/complex-rationalp m)))
                (case-split (not (complex/complex-rationalp n))))
           (< (mod m n) n))
  :rule-classes :linear)

(defthm mod-by-1
  (implies (integerp m)
           (equal (mod m 1)
                  0)))

(defrule mod-bnd-2
  (implies (and (<= 0 m)
                (case-split (real/rationalp m)))
           (<= (mod m n) m))
  :enable (mod)
  :rule-classes :linear)

(defthm mod-does-nothing
  (implies (and (< m n)
                (<= 0 m)
                (case-split (real/rationalp m)))
           (equal (mod m n)
                  m)))

(defrule mod-0-fl
  (implies (acl2-numberp m)
           (iff (= (mod m n) 0)
	        (= m (* (fl (/ m n)) n))))
  :enable (fl)
  :rule-classes ())

(defthm mod-0-int
  (implies (and (integerp m)
                (integerp n)
                (not (= n 0)))
           (iff (= (mod m n) 0)
                (integerp (/ m n))))
  :rule-classes ())

(defrule mod-mult-n
  (equal (mod (* a n) n)
         (* n (mod a 1)))
  :enable (mod))

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
		  (real/rationalp m)
		  (real/rationalp n))
	     (= m n))
  :rule-classes ())

(defrule mod-0-0
  (implies (and (integerp p)
                (real/rationalp m)
                (real/rationalp n))
           (iff (= (mod m (* n p)) 0)
                (and (= (mod m n) 0)
                     (= (mod (fl (/ m n)) p) 0))))
  :enable (mod)
  :rule-classes ())

(defthm mod-equal-int
  (implies (and (= (mod a n) (mod b n))
                (real/rationalp a)
                (real/rationalp b))
           (integerp (/ (- a b) n)))
  :rule-classes ())

(defthm mod-equal-int-reverse
  (implies (and (integerp (/ (- a b) n))
                (real/rationalp a)
                (real/rationalp b)
                (real/rationalp n)
                (< 0 n))
           (= (mod a n) (mod b n)))
  :rule-classes ())

(defthm mod-force-equal
  (implies (and (< (abs (- a b)) n)
                (real/rationalp a)
                (real/rationalp b)
                (integerp n))
          (iff (= (mod a n) (mod b n))
               (= a b)))
  :rule-classes ())

(defthmd mod-mult
    (implies (and (integerp a)
                  (real/rationalp m)
		  (real/rationalp n))
	     (equal (mod (+ m (* a n)) n)
		    (mod m n))))

(defrule mod-force
  (implies (and (<= (* a n) m)
                (< m (* (1+ a) n))
                (integerp a)
                (real/rationalp m)
                (real/rationalp n))
           (= (mod m n) (- m (* a n))))
  :prep-books (
    (set-default-hints '((ACL2::nonlinearp-default-hint++
                          ACL2::id ACL2::stable-under-simplificationp ACL2::hist nil))))
  :rule-classes ())

(defrule mod-bnd-3
  (implies (and (< m (+ (* a n) r))
                (<= (* a n) m)
                (integerp a)
                (case-split (real/rationalp m))
                (case-split (real/rationalp n)))
           (< (mod m n) r))
  :prep-books (
    (set-default-hints '((ACL2::nonlinearp-default-hint++
                          ACL2::id ACL2::stable-under-simplificationp ACL2::hist nil))))
  :use (mod-force)
  :rule-classes :linear)

(defthmd mod-sum
    (implies (and (real/rationalp a)
		  (real/rationalp b))
	     (equal (mod (+ a (mod b n)) n)
		    (mod (+ a b) n))))

(defthmd mod-diff
  (implies (and (case-split (real/rationalp a))
                (case-split (real/rationalp b)))
           (equal (mod (- a (mod b n)) n)
                  (mod (- a b) n))))

(defruled mod-of-mod
  (implies (and (case-split (natp k))
                (case-split (natp n)))
           (equal (mod (mod x (* k n)) n)
                  (mod x n)))
  :prep-books (
    (set-default-hints '((ACL2::nonlinearp-default-hint
                          ACL2::stable-under-simplificationp ACL2::hist
                          ACL2::pspv)))))

(defthmd mod-of-mod-cor
  (implies (and (<= b a)
                (case-split (integerp b))
                (case-split (integerp a)))
           (equal (mod (mod x (expt 2 a)) (expt 2 b))
                  (mod x (expt 2 b)))))

(defthmd mod-prod
  (implies (and (real/rationalp m)
                (real/rationalp n)
                (real/rationalp k))
           (equal (mod (* k m) (* k n))
                  (* k (mod m n)))))

(defthm mod-mod-times
    (implies (and (integerp a)
		  (integerp b)
		  (integerp n)
		  (> n 0))
	     (= (mod (* (mod a n) b) n)
		(mod (* a b) n)))
  :rule-classes ())

(defthm mod-plus-mod
    (implies (and (integerp a)
		  (integerp b)
		  (integerp c)
		  (not (zp n))
		  (= (mod a n) (mod b n)))
	     (= (mod (+ a c) n) (mod (+ b c) n)))
  :rule-classes ())

(defthm mod-times-mod
    (implies (and (integerp a)
		  (integerp b)
		  (integerp c)
		  (not (zp n))
		  (= (mod a n) (mod b n)))
	     (= (mod (* a c) n) (mod (* b c) n)))
  :rule-classes ())

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

(in-theory (disable mod))

;;;**********************************************************************
;;;                         CHOP
;;;**********************************************************************

(defund chop (x k)
  (/ (fl (* (expt 2 k) x)) (expt 2 k)))

(defthmd chop-mod
  (implies (and (real/rationalp x)
                (integerp k))
           (equal (chop x k)
                  (-  x (mod x (expt 2 (- k))))))
  :hints (("Goal" :in-theory (enable chop)
                  :use ((:instance mod-def (y (expt 2 (- k))))))))

(defthmd chop-chop
  (implies (and (real/rationalp x)
                (integerp k)
                (integerp m)
                (<= k m))
           (and (equal (chop (chop x m) k)
                       (chop x k))
                (equal (chop (chop x k) m)
                       (chop x k))))
  :hints (("Goal" :in-theory (enable chop)
                  :use ((:instance fl/int-rewrite (x (* (expt 2 m) x)) (n (expt 2 (- m k))))))))

(defthmd chop-shift
  (implies (and (real/rationalp x)
                (integerp k)
                (integerp m))
           (equal (chop (* (expt 2 k) x) m)
                  (* (expt 2 k) (chop x (+ k m)))))
  :hints (("Goal" :in-theory (enable chop))))

(local (defthm chop-bound-1
  (implies (and (real/rationalp x)
                (integerp n)
                (rationalp h)
                (natp m))
           (iff (and (<= n x) (<= x h))
                (and (<= (* (expt 2 m) n) (* (expt 2 m) x))
                     (<= (* (expt 2 m) x) (* (expt 2 m) h)))))
  :rule-classes ()))

(local (defthm chop-bound-2
  (implies (and (real/rationalp x)
                (integerp n)
                (natp m))
           (iff (<= n x) (<= (* (expt 2 m) n) (* (expt 2 m) x))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance chop-bound-1 (h x)))))))

(local (defthm chop-bound-3
  (implies (and (real/rationalp x)
                (integerp n)
                (natp m))
           (iff (<= (* (expt 2 m) n) (* (expt 2 m) x))
                (<= (* (expt 2 m) n) (fl (* (expt 2 m) x)))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable acl2::simplify-products-gather-exponents-<)))))

(local (defthm chop-bound-4
  (implies (and (real/rationalp x)
                (integerp n)
                (natp m))
           (iff (<= n x)
                (<= (* (expt 2 m) n) (fl (* (expt 2 m) x)))))
  :hints (("Goal" :in-theory (enable chop)
                  :use (chop-bound-2 chop-bound-3)))
  :rule-classes ()))

(local (defthm chop-bound-5
  (implies (and (real/rationalp x)
                (integerp n)
                (natp m))
           (iff (<= n (* (expt 2 (- m)) (fl (* (expt 2 m) x))))
                (<= (* (expt 2 m) n) (fl (* (expt 2 m) x)))))
  :hints (("Goal" :in-theory (enable chop)
                  :use ((:instance chop-bound-2 (x (* (expt 2 (- m)) (fl (* (expt 2 m) x))))))))
  :rule-classes ()))

(defthm chop-bound
  (implies (and (real/rationalp x)
                (integerp n)
                (natp m))
           (iff (<= n x) (<= n (chop x m))))
  :hints (("Goal" :in-theory (enable chop)
                  :use (chop-bound-4 chop-bound-5)))
  :rule-classes ())

(local (defthm chop-small-1
  (implies (and (real/rationalp x)
                (real/rationalp y)
                (real/rationalp z)
                (> z 0)
                (> y 0)
                (< x y)
                (<= (- y) x))
           (and (< (* x z) (* y z))
                (<= (* (- y) z) (* x z))))
  :rule-classes ()))

(local (defthm chop-small-2
  (implies (and (real/rationalp x)
                (integerp m)
                (< x (expt 2 (- m)))
                (<= (- (expt 2 (- m))) x))
           (and (< (* (expt 2 m) x) 1)
                (<= -1 (* (expt 2 m) x))))
  :rule-classes ()
 :hints (("Goal" :use ((:instance chop-small-1 (y (expt 2 (- m))) (z (expt 2 m))))))))

(local (defthm chop-small-3
  (implies (and (real/rationalp x)
                (integerp m)
                (< x (expt 2 (- m)))
                (<= (- (expt 2 (- m))) x))
           (and (< (fl (* (expt 2 m) x)) 1)
                (<= -1 (fl (* (expt 2 m) x)))))
  :rule-classes ()
 :hints (("Goal" :use (chop-small-2)))))

(local (defthm chop-small-4
  (implies (and (real/rationalp x)
                (integerp m)
                (< x (expt 2 (- m)))
                (<= (- (expt 2 (- m))) x))
           (equal (fl (* (expt 2 m) x))
                  (if (>= x 0) 0 -1)))
  :rule-classes ()
 :hints (("Goal" :use (chop-small-3)))))

(defthmd chop-small
  (implies (and (real/rationalp x)
                (integerp m)
                (< x (expt 2 (- m)))
                (<= (- (expt 2 (- m))) x))
           (equal (chop x m)
                  (if (>= x 0)
                      0
                    (- (expt 2 (- m))))))
 :hints (("Goal" :use (chop-small-4)
                 :in-theory (enable chop))))

(local (defthm chop-0-1
  (implies (and (real/rationalp x)
                (integerp m)
                (< (abs (chop x m)) (expt 2 (- m))))
           (< (abs (fl (* (expt 2 m) x))) 1))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable chop)))))

(local (defthm chop-0-2
  (implies (and (real/rationalp x)
                (integerp m)
                (< (abs (chop x m)) (expt 2 (- m))))
           (equal (fl (* (expt 2 m) x)) 0))
  :rule-classes ()
  :hints (("Goal" :use (chop-0-1)))))

(defthm chop-0
  (implies (and (real/rationalp x)
                (integerp m)
                (< (abs (chop x m)) (expt 2 (- m))))
           (equal (chop x m) 0))
  :hints (("Goal" :in-theory (enable chop)
                  :use (chop-0-2))))
