;;;***************************************************************
;;;An ACL2 Library of Floating Point Arithmetic

;;;David M. Russinoff
;;;Advanced Micro Devices, Inc.
;;;August, 1999
;;; modified by Matt Kaufmann, AMD, September, 1999
;;;***************************************************************

(in-package "ACL2")

(local (include-book "../support/merge"))

(deflabel rtl-lib3-basic-start)

(defun fl (x) (floor x 1))

(defun cg (x) (- (fl (- x))))

; Change for v2-8:  Daron and Pete have deleted some stuff that is no longer
; necessary given their ordinals-related changes, in particular introduction of
; natp.  Such changes are made throughout this file.

(in-theory (disable fl cg))

;;;**********************************************************************
;;;                       FLOOR and CEILING
;;;**********************************************************************

(defun fl (x) (floor x 1))

(defun cg (x) (- (fl (- x))))

(in-theory (disable fl cg))

(defthm int-fl-rules
    (implies (rationalp x)
	     (integerp (fl x)))
    :rule-classes (:rewrite :type-prescription)
    ;; The following hint is not necessary, but is in keeping with our
    ;; desire to keep proof hacking out of the present file.
    :hints (("Goal" :by int-fl)))

(defthm int-cg-rules
    (implies (rationalp x)
	     (integerp (cg x)))
    :rule-classes (:rewrite :type-prescription)
    ;; The following hint is not necessary, but is in keeping with our
    ;; desire to keep proof hacking out of the present file.
    :hints (("Goal" :by int-cg)))

(defthm fl-int-2
    (implies (rationalp x)
	     (iff (equal (fl x) x)
		  (integerp x))))

(defthm cg-int-2
    (implies (rationalp x)
	     (iff (equal (cg x) x)
		  (integerp x))))

(defthm fl-def-linear
    (implies (rationalp x)
	     (and (<= (fl x) x)
		  (< x (1+ (fl x)))))
  :rule-classes :linear
  ;; The following hint is not necessary, but is in keeping with our
  ;; desire to keep proof hacking out of the present file.
  :hints (("Goal" :by fl-def)))

(defthm cg-monotone-linear
    (implies (and (rationalp x)
		  (rationalp y)
		  (<= x y))
	     (<= (cg x) (cg y)))
  :rule-classes :linear
  ;; The following hint is not necessary, but is in keeping with our
  ;; desire to keep proof hacking out of the present file.
  :hints (("Goal" :by cg-monotone)))

(defthm fl-unique
    (implies (and (rationalp x)
		  (integerp n)
		  (<= n x)
		  (< x (1+ n)))
	     (equal (fl x) n))
  :rule-classes ())

(defthm cg-unique
    (implies (and (rationalp x)
		  (integerp n)
		  (>= n x)
		  (> (1+ x) n))
	     (equal (cg x) n))
  :rule-classes ())

(defthm cg-def-linear
    (implies (rationalp x)
	     (and (>= (cg x) x)
		  (> (1+ x) (cg x))))
  :rule-classes :linear
  ;; The following hint is not necessary, but is in keeping with our
  ;; desire to keep proof hacking out of the present file.
  :hints (("Goal" :by cg-def)))

(defthm fl-monotone-linear
    (implies (and (<= x y)
		  (rationalp x)
		  (rationalp y))
	     (<= (fl x) (fl y)))
  :rule-classes :linear
  ;; The following hint is not necessary, but is in keeping with our
  ;; desire to keep proof hacking out of the present file.
  :hints (("Goal" :by fl-monotone)))

(defthm n<=fl-linear
    (implies (and (<= n x)
		  (rationalp x)
		  (integerp n))
	     (<= n (fl x)))
  :rule-classes :linear
  ;; The following hint is not necessary, but is in keeping with our
  ;; desire to keep proof hacking out of the present file.
  :hints (("Goal" :by n<=fl)))

(defthm n>=cg-linear
    (implies (and (>= n x)
		  (rationalp x)
		  (integerp n))
	     (>= n (cg x)))
  :rule-classes :linear
  ;; The following hint is not necessary, but is in keeping with our
  ;; desire to keep proof hacking out of the present file.
  :hints (("Goal" :by n>=cg)))

(defthm fl+int-rewrite
    (implies (and (integerp n)
		  (rationalp x))
	     (equal (fl (+ x n)) (+ (fl x) n)))
  ;; The following hint is not necessary, but is in keeping with our
  ;; desire to keep proof hacking out of the present file.
  :hints (("Goal" :by fl+int)))

(defthm cg+int-rewrite
    (implies (and (integerp n)
		  (rationalp x))
	     (equal (cg (+ x n)) (+ (cg x) n)))
  ;; The following hint is not necessary, but is in keeping with our
  ;; desire to keep proof hacking out of the present file.
  :hints (("Goal" :by cg+int)))

(defthm fl/int-rewrite
    (implies (and (integerp n)
		  (> n 0)
		  (rationalp x))
	     (equal (fl (/ (fl x) n))
		    (fl (/ x n))))
  ;; The following hint is not necessary, but is in keeping with our
  ;; desire to keep proof hacking out of the present file.
  :hints (("Goal" :by fl/int)))

(defthm fl-cg
    (implies (and (rationalp x)
		  (not (integerp x)))
	     (equal (cg x) (1+ (fl x))))
  :rule-classes ())

(defthm cg/int-rewrite
    (implies (and (integerp n)
		  (> n 0)
		  (rationalp x))
	     (equal (cg (/ (cg x) n))
		    (cg (/ x n))))
  ;; The following hint is not necessary, but is in keeping with our
  ;; desire to keep proof hacking out of the present file.
  :hints (("Goal" :by cg/int)))

(defthm floor-m+1
    (implies (and (integerp m)
		  (integerp n)
		  (>= m 0)
		  (> n 0))
	     (= (fl (- (/ (1+ m) n)))
		(1- (- (fl (/ m n))))))
  :rule-classes ())

(defthm floor-2
    (implies (integerp m)
	     (= (fl (- (/ (1+ m) 2)))
		(1- (- (fl (/ m 2))))))
  :rule-classes ())

(defthm floor-fl
    (implies (and (integerp m)
		  (integerp n)
		  (> n 0)
		  (>= m 0))
	     (= (floor m n) (fl (/ m n))))
  :rule-classes ())


;;;**********************************************************************
;;;                       EXPONENTIATION
;;;**********************************************************************

(defthm expt-positive
  (implies (and (rationalp x)
                (posp base))
           (and (rationalp (expt base x))
                (< 0 (expt base x))))
  :rule-classes (:type-prescription :rewrite))

(defthm natp-posp-expt
  (implies (natp n)
           (posp (expt 2 n)))
  :rule-classes (:type-prescription :rewrite))

(defthm expt>=1
    (implies (and (integerp n)
		  (>= n 0))
	     (and (integerp (expt 2 n))
		  (>= (expt 2 n) 1)))
  :rule-classes ())

(defthm expt-monotone
    (implies (and (integerp n)
		  (integerp m)
		  (<= n m))
	     (<= (expt 2 n) (expt 2 m)))
  :rule-classes ())

(defthm expt-strong-monotone
    (implies (and (integerp n)
		  (integerp m))
	     (iff (< n m) (< (expt 2 n) (expt 2 m))))
  :rule-classes ())

;!! It might be nice to decide to orient the following two equations
;as shown and make them into rewrite rules.

(defthm expt-
    (implies (and (integerp a)
		  (integerp b))
	     (= (/ (expt 2 a) (expt 2 b)) (expt 2 (- a b))))
  :rule-classes ())

(defthm expo+
    (implies (and (integerp n)
		  (integerp m))
	     (= (expt 2 (+ m n))
		(* (expt 2 m) (expt 2 n))))
  :rule-classes ())


;;;**********************************************************************
;;;                         REMAINDERS
;;;**********************************************************************

(in-theory (disable rem))

(defthm integerp-rationalp
    (implies (integerp x)
	     (rationalp x)))

(defthm rem-0
  (implies (natp m)
           (equal (rem m 0) m)))

(defthm rationalp-rem
    (implies (and (rationalp m)
		  (rationalp n))
	     (rationalp (rem m n)))
  :rule-classes :type-prescription)

(defthm rationalp-rem-rewrite
    (implies (and (rationalp m)
		  (rationalp n))
	     (rationalp (rem m n))))

(defthm integerp-rem
    (implies (and (integerp m)
		  (integerp n))
	     (integerp (rem m n)))
  :rule-classes :type-prescription)

(defthm integerp-rem-rewrite
    (implies (and (integerp m)
		  (integerp n))
	     (integerp (rem m n))))

(defthm natp-rem
  (implies (and (natp m)
                (natp n))
           (natp (rem m n)))
  :rule-classes :type-prescription
  :hints (("Goal" :use rem>=0)))

(defthm natp-rem-rewrite
  (implies (and (natp m)
                (natp n))
           (natp (rem m n))))

(defthm rem-bnd-1
    (implies (and (natp m)
		  (natp n)
		  (not (= n 0)))
	     (< (rem m n) n))
  :rule-classes :linear)

(defthm rem-bnd-2
    (implies (and (natp m)
		  (natp n))
	     (<= (rem m n) m))
  :rule-classes :linear)

(defthm quot-rem
    (implies (and (natp m)
		  (natp n))
	     (equal (+ (* n (fl (/ m n))) (rem m n))
		    m))
  :rule-classes ())

(defthm rem-mult
    (implies (and (natp m)
		  (natp a)
		  (natp n))
	     (equal (rem (+ m (* a n)) n)
		    (rem m n))))

(defthm rem-sum
    (implies (and (natp a)
		  (natp b)
		  (natp n))
	     (equal (rem (+ a (rem b n)) n)
		    (rem (+ a b) n))))

(defthm rem-diff
    (implies (and (natp a)
		  (natp b)
		  (natp n)
		  (>= a b))
	     (equal (rem (- a (rem b n)) n)
		    (rem (- a b) n))))

(defthm rem-equal
    (implies (and (natp m)
		  (natp n)
		  (< m n))
	     (equal (rem m n) m)))

(defthm rem-1
  (implies (natp x)
           (equal (rem x 1) 0)))

(defthm rem-of-rem
    (implies (and (natp x)
		  (natp a)
		  (natp b)
		  (>= a b))
	     (equal (rem (rem x (expt 2 a)) (expt 2 b))
		    (rem x (expt 2 b)))))

(defthm rem-must-be-n
    (implies (and (natp m)
		  (natp n)
		  (not (= m 0))
		  (< m (* 2 n))
		  (= (rem m n) 0))
	     (= m n))
  :rule-classes ())

(defthm rem-prod
    (implies (and (natp m)
		  (natp n)
		  (natp k)
		  (not (= n 0)))
	     (equal (rem (* k m) (* k n))
		    (* k (rem m n)))))

(defthm rem-bnd-3
    (implies (and (natp m)
		  (natp n)
		  (natp a)
		  (natp r)
		  (<= (* a n) m)
		  (< m (+ (* a n) r)))
	     (< (rem m n) r))
  ;; Free variables make this rule very weak, but it seems harmless
  ;; enough to make it a :linear rule.
  :rule-classes :linear)

(defthm rem-force
    (implies (and (natp m)
		  (natp n)
		  (natp a)
		  (> (* (1+ a) n) m)
		  (>= m (* a n)))
	     (= (rem m n) (- m (* a n))))
  :rule-classes ())

(defthm rem-equal-int
    (implies (and (natp a)
		  (natp b)
		  (natp n)
		  (= (rem a n) (rem b n)))
	     (integerp (/ (- a b) n)))
  :rule-classes ())

(defthm rem-0-fl
    (implies (and (natp m)
		  (natp n))
	     (iff (= (rem m n) 0)
		  (= m (* (fl (/ m n)) n))))
  :rule-classes ())

(defthm quot-bnd
    (implies (and (natp m)
		  (natp n))
	     (>= m (* (fl (/ m n)) n)))
  :rule-classes :linear)

(defthm rem-0-0
    (implies (and (natp m)
		  (natp n)
		  (natp p)
                  (not (= p 0)))
	     (iff (= (rem m (* n p)) 0)
		  (and (= (rem m n) 0)
		       (= (rem (fl (/ m n)) p) 0))))
  :rule-classes ())

(defthm rem-mult-2
    (implies (and (natp n)
		  (natp a))
	     (equal (rem (* a n) n)
		    0)))

(defthm rem-force-equal
    (implies (and (natp a)
		  (natp b)
		  (natp n)
		  (< (abs (- a b)) n)
		  (= (rem a n) (rem b n)))
	     (= a b))
  :rule-classes ())

(defthm nk>=k-linear
    (implies (and (integerp n)
		  (integerp k)
		  (not (= n 0)))
	     (>= (abs (* n k)) k))
  :rule-classes :linear)

(defthm rem-mod-2
    (implies (natp x)
	     (or (= (rem x 2) 0)
		 (= (rem x 2) 1)))
  :rule-classes ())

(defthm rem-plus-mod-2
    (implies (and (natp x)
		  (natp y))
	     (iff (= (rem (+ x y) 2) (rem x 2))
		  (= (rem y 2) 0)))
  :rule-classes ())

(defthm rem-mod-2-not-equal
    (implies (natp x)
	     (not (= (rem x 2) (rem (1+ x) 2))))
  :rule-classes ())

(defthm x-or-x/2
    (implies (integerp x)
	     (or (integerp (/ x 2)) (integerp (/ (1+ x) 2))))
  :rule-classes ())

(defthm rem-2*i-rewrite
    (implies (integerp i)
             ;; Rule A3 in fp.lisp suggests using (* 2 i) instead of
             ;; (+ i i).
             (equal (rem (* 2 i) 2) 0)))

(defthm rem-2*i+1
    (implies (integerp i)
	     (not (equal (rem (1+ (* 2 i)) 2) 0)))
  :rule-classes ())

(defthm rem-2*i+1-rewrite
    (implies (natp i)
	     (equal (rem (1+ (* 2 i)) 2) 1)))

(defun fl-half (x)
  (1- (fl (/ (1+ x) 2))))

(in-theory (disable fl-half))

(defthm fl-half-lemma
    (implies (and (integerp x)
		  (not (integerp (/ x 2))))
	     (= x (1+ (* 2 (fl-half x)))))
  :rule-classes ())

(include-book "../support/rewrite-theory")

(deftheory rtl-lib3-basic-theory
  (rewrite-theory 'rtl-lib3-basic-start))
