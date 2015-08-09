(in-package "ACL2")

(set-enforce-redundancy t)

(local (include-book "../arithmetic/fl"))
(local (include-book "../support/merge"))
(local (include-book "../support/guards"))
(local (include-book "../arithmetic/hacks"))
(local (include-book "../arithmetic/cg"))
(local (include-book "../support/ash"))
(local (include-book "../arithmetic/fl-hacks"))
(local (include-book "../arithmetic/mod"))
(local (include-book "../arithmetic/even-odd"))
(local (include-book "../arithmetic/extra-rules"))
(local (include-book "../arithmetic/top"))

(include-book "rtl")
(include-book "rtlarr")

(set-inhibit-warnings "theory") ; avoid warning in the next event
(local (in-theory nil))

;;;**********************************************************************
;;;                       FLOOR and CEILING
;;;**********************************************************************

(defthm fl-unique
    (implies (and (rationalp x)
		  (integerp n)
		  (<= n x)
		  (< x (1+ n)))
	     (equal (fl x) n))
  :rule-classes ())

(defund cg (x)
  (declare (xargs :guard (real/rationalp x)))
  (- (fl (- x))))

(defthm cg-unique
    (implies (and (rationalp x)
		  (integerp n)
		  (>= n x)
		  (> (1+ x) n))
	     (equal (cg x) n))
  :rule-classes ())

(defthm fl-cg
    (implies (and (rationalp x)
		  (not (integerp x)))
	     (equal (cg x) (1+ (fl x))))
  :rule-classes ())

(defthmd floor-fl ; perhaps this could be harmlessly enabled
  (equal (floor m n) (fl (/ m n))))

(defthm fl-integer-type
  (integerp (fl x))
  :rule-classes :type-prescription)

(defthm cg-integer-type
  (integerp (cg x))
  :rule-classes :type-prescription)

(defthm fl-integerp
  (equal (equal (fl x) x)
         (integerp x)))

(defthm cg-integerp
    (implies (rationalp x)
	     (equal (equal (cg x) x)
                    (integerp x))))

(defthm fl-def-linear
    (implies (case-split (rationalp x))
	     (and (<= (fl x) x)
		  (< x (1+ (fl x)))))
  :rule-classes :linear)

(defthm cg-def-linear
    (implies (case-split (rationalp x))
	     (and (>= (cg x) x)
		  (> (1+ x) (cg x))))
  :rule-classes :linear)

(defthm fl-monotone-linear
    (implies (and (<= x y)
		  (rationalp x)
		  (rationalp y))
	     (<= (fl x) (fl y)))
  :rule-classes :linear)

(defthm cg-monotone-linear
    (implies (and (rationalp x)
		  (rationalp y)
		  (<= x y))
	     (<= (cg x) (cg y)))
  :rule-classes :linear)

(defthm n<=fl-linear
    (implies (and (<= n x)
		  (rationalp x)
		  (integerp n))
	     (<= n (fl x)))
  :rule-classes :linear)

(defthm n>=cg-linear
    (implies (and (>= n x)
		  (rationalp x)
		  (integerp n))
	     (>= n (cg x)))
  :rule-classes :linear)

(defthm fl+int-rewrite
    (implies (and (integerp n)
		  (rationalp x))
	     (equal (fl (+ x n)) (+ (fl x) n))))

(defthm cg+int-rewrite
    (implies (and (integerp n)
		  (rationalp x))
	     (equal (cg (+ x n)) (+ (cg x) n))))

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

(defthm fl-m-1
    (implies (and (< 0 n)
                  (integerp m)
		  (integerp n)
		  )
	     (= (fl (- (/ (1+ m) n)))
		(1- (- (fl (/ m n))))))
  :rule-classes ())


;;;**********************************************************************
;;;                       EXPONENTIATION
;;;**********************************************************************

(defthm expt-2-positive-rational-type
  (and (rationalp (expt 2 i))
       (< 0 (expt 2 i)))
  :rule-classes (:rewrite (:type-prescription :typed-term (expt 2 i))))

(defthm expt-2-positive-integer-type
  (implies (<= 0 i)
           (and (integerp (expt 2 i))
                (< 0 (expt 2 i))))
  :rule-classes (:type-prescription))

(defthm expt-2-type-linear
  (implies (<= 0 i)
           (<= 1 (expt 2 i)))
  :rule-classes ((:linear :trigger-terms ((expt 2 i)))))

(defthmd expt-weak-monotone
  (implies (and (integerp n)
                (integerp m))
           (equal (<= (expt 2 n) (expt 2 m))
		  (<= n m))))

(defthmd expt-strong-monotone
  (implies (and (integerp n)
                (integerp m))
           (equal (< (expt 2 n) (expt 2 m))
		  (< n m))))

(defthmd expt-inverse
  (equal (/ (expt 2 i))
         (expt 2 (* -1 i))))

(defthm ash-rewrite
    (implies (integerp n)
	     (equal (ash n i)
		    (fl (* n (expt 2 i))))))

(defthm exp+1
    (implies (and (integerp m)
		  (integerp n)
		  (<= n m))
	     (> (* (- 1 (expt 2 m)) (- 1 (expt 2 n)))
		(- 1 (expt 2 (1+ m)))))
  :rule-classes ())

(defthm exp+2
    (implies (and (integerp n)
		  (integerp m)
		  (<= n m)
		  (<= m 0))
	     (< (* (1+ (expt 2 m)) (1+ (expt 2 n)))
		(1+ (expt 2 (+ m 2)))))
  :rule-classes ())

(defthm exp-invert
    (implies (and (integerp n)
		  (<= n -1))
	     (<= (/ (- 1 (expt 2 n)))
		 (1+ (expt 2 (1+ n)))))
  :rule-classes ())


;;;**********************************************************************
;;;                         MOD
;;;**********************************************************************

(in-theory (disable mod))

(defthm mod-0
  (implies (acl2-numberp m)
           (equal (mod m 0) m)))

(defthm rationalp-mod
  (implies (case-split (rationalp m))
           (rationalp (mod m n)))
  :rule-classes (:rewrite :type-prescription))

(defthm integerp-mod
  (implies (and (integerp m) (integerp n))
           (integerp (mod m n)))
  :rule-classes
  (:rewrite :type-prescription))

(defthm natp-mod
  (implies (and (natp m)
                (natp n))
           (natp (mod m n)))
  :rule-classes ((:type-prescription :typed-term (mod m n))))

(defthm mod-bnd-1
  (implies (and (case-split (< 0 n))
                (case-split (not (complex-rationalp m)))
                (case-split (not (complex-rationalp n)))
                )
           (< (mod m n) n))
  :rule-classes :linear)

(defthm mod-bnd-2
  (implies (and (<= 0 m)
                (case-split (rationalp m)))
           (<= (mod m n) m))
  :rule-classes :linear)

(defthm quot-mod
    (implies (case-split (acl2-numberp m))
	     (equal (+ (* n (fl (/ m n))) (mod m n))
		    m))
  :rule-classes ())

(defthm mod-mult
    (implies (and (integerp a)
                  (rationalp m)
		  (rationalp n))
	     (equal (mod (+ m (* a n)) n)
		    (mod m n))))

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

(defthm mod-diff
  (implies (and (case-split (rationalp a))
                (case-split (rationalp b)))
           (equal (mod (- a (mod b n)) n)
                  (mod (- a b) n))))

(defthm mod-does-nothing
  (implies (and (< x y)
                (<= 0 x)
                (case-split (rationalp x)))
           (equal (mod x y)
                  x)))

(defthm mod-by-1
  (implies (integerp x)
           (equal (mod x 1)
                  0)))

(defthm mod-of-mod
  (implies (and (<= b a)
                (case-split (integerp b))
                (case-split (integerp a)))
           (equal (mod (mod x (expt 2 a)) (expt 2 b))
                  (mod x (expt 2 b)))))

(defthm mod-must-be-n
    (implies (and (= (mod m n) 0)
		  (< m (* 2 n))
                  (< 0 m)
		  (rationalp m)
		  (rationalp n)
		  )
	     (= m n))
  :rule-classes ())

(defthm mod-prod
  (implies (and (rationalp m)
                (rationalp n)
                (rationalp k))
           (equal (mod (* k m) (* k n))
                  (* k (mod m n)))))

(defthm mod-bnd-3
  (implies (and (< m (+ (* a n) r))
                (<= (* a n) m)
                (integerp a)
                (case-split (rationalp m))
                (case-split (rationalp n)))
           (< (mod m n) r))
  :rule-classes :linear)

(defthm mod-force
  (implies (and (<= (* a n) m)
                (< m (* (1+ a) n))
                (integerp a)
                (rationalp m)
                (rationalp n))
           (= (mod m n) (- m (* a n))))
  :rule-classes ())

(defthm mod-equal-int
  (implies(and (= (mod a n) (mod b n))
               (rationalp a)
               (rationalp b))
          (integerp (/ (- a b) n)))
  :rule-classes ())

(defthm mod-0-fl
    (implies (acl2-numberp m)
	     (iff (= (mod m n) 0)
		  (= m (* (fl (/ m n)) n))))
  :rule-classes ())

(defthm quot-bnd
  (implies (and (<= 0 n)
                (<= 0 m)
                (rationalp m)
                (rationalp n)
                )
           (<= (* n (fl (/ m n)))
               m))
  :rule-classes :linear)

(defthm mod-0-0
  (implies (and (integerp p)
                (rationalp m)
                (rationalp n)
                )
           (iff (= (mod m (* n p)) 0)
                (and (= (mod m n) 0)
                     (= (mod (fl (/ m n)) p) 0))))
  :rule-classes ())


(defthm mod-mult-2
    (implies (integerp a)
	     (equal (mod (* a n) n)
		    0)))

(defthm mod-force-equal
  (implies (and (= (mod a n) (mod b n))
                (< (abs (- a b)) n)
                (rationalp a)
                (rationalp b)
                (integerp n))
           (= a b))
  :rule-classes ())

(defthm nk>=k-linear
    (implies (and (integerp n)
		  (integerp k)
		  (not (= n 0)))
	     (>= (abs (* n k)) k))
  :rule-classes :linear)

(defthm mod012
  (implies (integerp x)
           (or (equal (mod x 2) 0)
               (equal (mod x 2) 1)))
  :rule-classes ())

(defthm mod-plus-mod-2
    (implies (and (integerp x)
		  (integerp y))
	     (iff (= (mod (+ x y) 2) (mod x 2))
		  (= (mod y 2) 0)))
  :rule-classes ())

(defthm mod-mod-2-not-equal
    (implies (acl2-numberp x)
	     (not (= (mod x 2) (mod (1+ x) 2))))
  :rule-classes ())

(defthm x-or-x/2
    (implies (integerp x)
	     (or (integerp (/ x 2)) (integerp (/ (1+ x) 2))))
  :rule-classes ())

(defthm mod-mult-2-gen
  (equal (mod (* a n) n)
         (* n (mod a 1))))

(defthm mod-mult-2-alt-gen
  (equal (mod (* n a) n)
         (* n (mod a 1))))

(defthm mod-2*i+1-rewrite
    (implies (integerp i)
	     (equal (mod (1+ (* 2 i)) 2) 1)))

(defund fl-half (x)
  (1- (fl (/ (1+ x) 2))))

(defthm fl-half-lemma
    (implies (and (integerp x)
		  (not (integerp (/ x 2))))
	     (= x (1+ (* 2 (fl-half x)))))
  :rule-classes ())
