(in-package "RTL")

(include-book "std/util/defrule" :dir :system)

(include-book "tools/with-arith5-help" :dir :system)
(local (acl2::allow-arith5-help))
(local (in-theory (acl2::enable-arith5)))

;;;**********************************************************************
;;;                       FLOOR and CEILING
;;;**********************************************************************

(defund fl (x)
  (declare (xargs :guard (real/rationalp x)))
  (floor x 1))

(defruled fl-default
  (implies (not (real/rationalp x))
           (equal (fl x) 0))
  :enable fl)

(defrule fl-def
  (and (integerp (fl x))
       (implies (case-split (real/rationalp x))
	        (and (<= (fl x) x)
		     (< x (1+ (fl x))))))
  :enable fl
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
  :enable fl
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
  :enable fl)

(defrule fl/int-rewrite-alt
  (implies (and (integerp n)
                (<= 0 n)
                (real/rationalp x))
           (equal (fl (* (/ n) (fl x)))
                  (fl (/ x n))))
  :enable fl)

(defrule fl-int-div-radix
  (implies (and (integerp n)
                (not (= n 0))
                (not (= n -1))
                (integerp radix)
                (>= radix 2))
           (< (abs (fl (/ n radix))) (abs n)))
  :enable fl
  :rule-classes ())

(defrule fl-half-int
  (implies (and (integerp n)
                (not (= n 0))
                (not (= n -1)))
           (< (abs (fl (/ n 2))) (abs n)))
  :use (:instance fl-int-div-radix (radix 2))
  :rule-classes ())

(defthmd fl-minus
  (implies (real/rationalp x)
           (equal (fl (* -1 x))
                  (if (integerp x)
                      (* -1 x)
                    (1- (* -1 (fl x)))))))

(defthmd minus-fl
  (implies (real/rationalp x)
           (equal (fl (- x))
                  (if (integerp x)
                      (- x)
                    (1- (- (fl x))))))
  :hints (("Goal" :use (fl-minus))))

(defrule fl-m-n
  (implies (and (< 0 n)
                (integerp m)
                (integerp n))
           (= (fl (- (/ m n)))
              (1- (- (fl (/ (1- m) n))))))
  :enable fl
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
  :enable cg
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
  :enable cg)

(defrule cg/int-rewrite-alt
  (implies (and (integerp n)
                (> n 0)
                (real/rationalp x))
           (equal (cg (* (/ n) (cg x)))
                  (cg (/ x n))))
  :enable cg)

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
  :enable fl
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
  :enable mod
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
  :enable fl
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
  :enable mod)

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
  :enable mod
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

(defund congruent (a b n)
  (declare (xargs :guard (and (real/rationalp a)
                              (real/rationalp b)
                              (real/rationalp n)
                              (not (= n 0)))))
  (equal (mod a n) (mod b n)))

(defthmd mod-mult
    (implies (and (integerp a)
                  (real/rationalp m)
		  (real/rationalp n))
	     (equal (mod (+ m (* a n)) n)
		    (mod m n))))

(acl2::with-arith5-nonlinear-help (defrule mod-force
  (implies (and (<= (* a n) m)
                (< m (* (1+ a) n))
                (integerp a)
                (real/rationalp m)
                (real/rationalp n))
           (= (mod m n) (- m (* a n))))
  :rule-classes ()))

(defrule mod-bnd-3
  (implies (and (< m (+ (* a n) r))
                (<= (* a n) m)
                (integerp a)
                (case-split (real/rationalp m))
                (case-split (real/rationalp n)))
           (< (mod m n) r))
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
                  (mod x n))))

(defthmd mod-of-mod-cor-r
  (implies (and (<= b a)
                (case-split (integerp b))
                (case-split (integerp a))
                (integerp radix)
                (> radix 0))
           (equal (mod (mod x (expt radix a)) (expt radix b))
                  (mod x (expt radix b)))))

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

(defrule mod-plus-mod-radix
  (implies (and (real/rationalp a)
                (real/rationalp b)
                (real/rationalp radix))
           (iff (= (mod (+ a b) radix) (mod a radix))
                (= (mod b radix) 0)))
  :rule-classes ())

(defrule mod-plus-mod-2
  (implies (and (integerp a)
                (integerp b))
           (iff (= (mod (+ a b) 2) (mod a 2))
                (= (mod b 2) 0)))
  :use (:instance mod-plus-mod-radix (radix 2))
  :rule-classes ())

(defthm mod-mod-2-not-equal
  (implies (acl2-numberp m)
           (not (= (mod m 2) (mod (1+ m) 2))))
  :rule-classes ())

(defthm mod-2*m+1-rewrite
  (implies (integerp m)
           (equal (mod (1+ (* 2 m)) 2) 1)))

(defrule fl-mod
  (implies (not (zp m))
	   (equal (fl (/ (mod a (* m n)) n))
	          (mod (fl (/ a n)) m)))
  :prep-lemmas
   ((acl2::with-arith5-nonlinear-help
     (defrule lemma
      (implies (posp m)
               (equal (mod (fl x) m)
                      (fl (mod x m))))
      :enable fl))))

(in-theory (disable mod))


;;;**********************************************************************
;;;                         CHOP-R
;;;**********************************************************************

(defnd radixp (b)
  (and (integerp b) (>= b 2)))

(defrule radixp-forward
  (implies (radixp b)
           (and (integerp b) (>= b 2)))
  :rule-classes :forward-chaining)

(defund chop-r (x k r)
  (declare (xargs :guard (and (real/rationalp x)
                              (integerp k)
                              (radixp r))))
  (/ (fl (* (expt r k) x)) (expt r k)))

(defruled chop-r-mod
  (implies (and (real/rationalp x)
                (integerp k))
           (equal (chop-r x k r)
                  (-  x (mod x (expt r (- k))))))
  :enable chop-r
  :use (:instance mod-def
         (y (expt r (- k)))))

(acl2::with-arith5-nonlinear-help (defrule chop-r-down
  (implies (and (real/rationalp x)
                (integerp n)
                (radixp r))
           (<= (chop-r x n r) x))
  :enable chop-r
  :rule-classes ()))

(defrule chop-r-monotone
  (implies (and (real/rationalp x)
                (real/rationalp y)
                (integerp n)
                (<= x y)
                (radixp r))
           (<= (chop-r x n r) (chop-r y n r)))
  :enable chop-r
  :use (:instance fl-monotone-linear
         (x (* x (expt r n)))
         (y (* y (expt r n))))
  :rule-classes ())

(defruled chop-r-chop-r
  (implies (and (real/rationalp x)
                (integerp k)
                (integerp m)
                (<= k m)
                (radixp r))
           (and (equal (chop-r (chop-r x m r) k r)
                       (chop-r x k r))
                (equal (chop-r (chop-r x k r) m r)
                       (chop-r x k r))))
  :enable chop-r
  :use (:instance fl/int-rewrite
         (x (* (expt r m) x))
         (n (expt r (- m k)))))

(defruled chop-r-shift
  (implies (and (real/rationalp x)
                (integerp k)
                (integerp m))
           (equal (chop-r (* (expt r k) x) m r)
                  (* (expt r k) (chop-r x (+ k m) r))))
  :enable chop-r)

(acl2::with-arith5-nonlinear-help (defrule chop-r-bound
  (implies (and (real/rationalp x)
                (integerp n)
                (natp m)
                (radixp r))
           (iff (<= n x) (<= n (chop-r x m r))))
  :enable chop-r
  :use (:instance fl-monotone-linear
         (x (* n (expt r m)))
         (y (* x (expt r m))))
  :rule-classes ()))

(acl2::with-arith5-nonlinear-help (defruled chop-r-small
  (implies (and (real/rationalp x)
                (integerp m)
                (< x (expt r (- m)))
                (<= (- (expt r (- m))) x)
                (radixp r))
           (equal (chop-r x m r)
                  (if (>= x 0)
                      0
                    (- (expt r (- m))))))
  :enable chop-r
  :use (:instance fl-unique
         (x (* x (expt r m)))
         (n (if (>= x 0) 0 -1)))))

(defrule chop-r-0
  (implies (and (real/rationalp x)
                (integerp m)
                (< (abs (chop-r x m r)) (expt r (- m)))
                (radixp r))
           (equal (chop-r x m r) 0))
  :enable chop-r)

(acl2::with-arith5-nonlinear-help
 (defrule chop-r-int-bounds
   (implies (and (natp k)
                 (natp n)
                 (real/rationalp x)
                 (radixp r))
            (and (<= (chop-r (fl (/ x (expt r n))) (- k) r)
                     (/ (chop-r x (- k) r) (expt r n)))
                 (<= (/ (+ (chop-r x (- k) r) (expt r k))
                        (expt r n))
                     (+ (chop-r (fl (/ x (expt r n))) (- k) r)
                        (expt r k)))))
   :enable chop-r
   :use
   ((:instance fl/int-rewrite (x (/ x (expt r n))) (n (expt r k)))
    (:instance fl/int-rewrite (x (/ x (expt r k))) (n (expt r n)))
    (:instance mod-def (x (fl (/ x (expt r k)))) (y (expt r n))))))

(defruled chop-r-int-neg
   (implies (and (natp k)
                 (natp n)
                 (real/rationalp x)
                 (real/rationalp y)
                 (radixp r)
                 (= (fl (/ x (expt r k)))
                    (fl (/ y (expt r k))))
                 (not (integerp (/ x (expt r k)))))
            (equal (chop-r (1- (- (fl (/ y (expt r n))))) (- k) r)
                   (chop-r (- (/ x (expt r n))) (- k) r)))
  :use (lemma1 lemma2)
  :prep-lemmas
  ((acl2::with-arith5-help
    (defruled lemma1
      (implies (and (natp k)
                    (natp n)
                    (real/rationalp x)
                    (real/rationalp y)
                    (radixp r)
                    (= (fl (/ x (expt r k)))
                       (fl (/ y (expt r k)))))
               (equal (chop-r (1- (- (fl (/ y (expt r n))))) (- k) r)
                      (- (* (expt r k)
                            (1+ (fl (/ x (expt r (+ k n)))))))))
      :enable chop-r
      :use ((:instance fl/int-rewrite (x (/ y (expt r n))) (n (expt r k)))
            (:instance fl/int-rewrite (x (/ y (expt r k))) (n (expt r n)))
            (:instance fl/int-rewrite (x (/ x (expt r k))) (n (expt r n)))
            (:instance fl-m-n (m (1+ (fl (/ y (expt r n))))) (n (expt r k))))))
   (acl2::with-arith5-nonlinear-help
    (defruled lemma2
      (implies (and (natp k)
                    (natp n)
                    (real/rationalp x)
                    (radixp r)
                    (not (integerp (/ x (expt r k)))))
               (equal (chop-r (- (/ x (expt r n))) (- k) r)
                      (- (* (expt r k)
                            (1+ (fl (/ x (expt r (+ k n)))))))))
      :enable chop-r
      :use ((:instance fl/int-rewrite (x (- (/ x (expt r n)))) (n (expt r k)))
            (:instance minus-fl (x (/ x (expt r n))))
            (:instance fl-m-n (m (1+ (fl (/ x (expt r k))))) (n (expt r n)))
            (:instance fl/int-rewrite (x (/ x (expt r k))) (n (expt r n))))))))


;;;**********************************************************************
;;;                         CHOP
;;;**********************************************************************

(defund chop (x k)
  (declare (xargs :guard (and (real/rationalp x)
                              (integerp k))))
  (/ (fl (* (expt 2 k) x)) (expt 2 k)))

(local (defrule |chop as chop-r|
  (equal (chop x k)
         (chop-r x k 2))
  :enable (chop chop-r)))

(defruled chop-mod
  (implies (and (real/rationalp x)
                (integerp k))
           (equal (chop x k)
                  (-  x (mod x (expt 2 (- k))))))
  :enable chop-r-mod)

(defrule chop-down
  (implies (and (rationalp x)
                (integerp n))
           (<= (chop x n) x))
  :use (:instance chop-r-down (r 2))
  :rule-classes ())

(defrule chop-monotone
  (implies (and (rationalp x)
                (rationalp y)
                (integerp n)
                (<= x y))
           (<= (chop x n) (chop y n)))
  :use (:instance chop-r-monotone (r 2))
  :rule-classes ())

(defruled chop-chop
  (implies (and (real/rationalp x)
                (integerp k)
                (integerp m)
                (<= k m))
           (and (equal (chop (chop x m) k)
                       (chop x k))
                (equal (chop (chop x k) m)
                       (chop x k))))
  :enable chop-r-chop-r)

(defruled chop-shift
  (implies (and (real/rationalp x)
                (integerp k)
                (integerp m))
           (equal (chop (* (expt 2 k) x) m)
                  (* (expt 2 k) (chop x (+ k m)))))
  :use (:instance chop-r-shift (r 2)))

(defrule chop-bound
  (implies (and (real/rationalp x)
                (integerp n)
                (natp m))
           (iff (<= n x) (<= n (chop x m))))
  :use (:instance chop-r-bound (r 2))
  :rule-classes ())

(defruled chop-small
  (implies (and (real/rationalp x)
                (integerp m)
                (< x (expt 2 (- m)))
                (<= (- (expt 2 (- m))) x))
           (equal (chop x m)
                  (if (>= x 0)
                      0
                    (- (expt 2 (- m))))))
  :enable chop-r-small)

(defrule chop-0
  (implies (and (real/rationalp x)
                (integerp m)
                (< (abs (chop x m)) (expt 2 (- m))))
           (equal (chop x m) 0))
  :enable (chop-r-0))


(defrule chop-int-bounds
  (implies (and (natp k)
                (natp n)
                (real/rationalp x))
           (and (<= (chop (fl (/ x (expt 2 n))) (- k))
                    (/ (chop x (- k)) (expt 2 n)))
                (<= (/ (+ (chop x (- k)) (expt 2 k))
                       (expt 2 n))
                    (+ (chop (fl (/ x (expt 2 n))) (- k))
                       (expt 2 k)))))
  :use (:instance chop-r-int-bounds (r 2))
  :rule-classes ())

(defruled chop-int-neg
  (implies (and (natp k)
                (natp n)
                (real/rationalp x)
                (real/rationalp y)
                (= (fl (/ x (expt 2 k)))
                   (fl (/ y (expt 2 k))))
                (not (integerp (/ x (expt 2 k)))))
           (equal (chop (1- (- (fl (/ y (expt 2 n))))) (- k))
                  (chop (- (/ x (expt 2 n))) (- k))))
  :use (:instance chop-r-int-neg (r 2)))
