(in-package "ACL2")

(include-book "rtl")
(include-book "bvecp-lemmas") ;bvecp and type lemmas for the RTL primitives
(local (include-book "../arithmetic/top"))
(local (include-book "bits"))

;would like to remove some of this stuff

;;;;;;;;;;;;;;;;;;; other helpful lemmas

(defthm nonneg-+
  (implies (and (<= 0 x)
                (<= 0 y))
           (<= 0 (+ x y))))

(defthm integerp-+
  (implies (and (integerp x)
                (integerp y))
           (integerp (+ x y))))

#|
;should be a forward-chaining rule?
(defthm bvecp-implies-natp
  (implies (bvecp x k)
           (and (integerp x)
                (>= x 0)))
  :hints (("Goal" :in-theory (enable bvecp))))

;free var
;should be a forward-chaining rule?
(defthm bvecp-implies-rationalp
  (implies (bvecp x k)
           (rationalp x))
  :hints (("Goal" :in-theory (enable bvecp))))
|#

;why do we have this?
(defthm unknown-upper-bound
  (< (unknown key size n) (expt 2 size))
  :hints
  (("goal" :use bvecp-unknown
    :in-theory (set-difference-theories
                (enable bvecp)
                '(bvecp-unknown))))
  :rule-classes
  (:rewrite (:linear :trigger-terms ((unknown key size n)))))

(defthm bv-arrp-implies-nonnegative-integerp
  (implies (bv-arrp obj size)
           (and (INTEGERP (ag index obj))
                (<= 0 (ag index obj))))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :use (:instance
                        ag-maps-bv-arr-to-bvecp (a index) (r obj) (k size))
           :in-theory (set-difference-theories
                       (enable bvecp)
                       '(ag-maps-bv-arr-to-bvecp)))))

;(local (in-theory (enable floor-fl)))

;These next two are for the bus unit bvecp lemmas:

;could use (local (in-theory (enable expt-compare-with-double)))
;remove?
(defthm bits-does-nothing-hack
  (implies (and (< x (expt 2 i))
                (integerp x)
                (<= 0 x)
                (integerp i)
                (<= 0 i))
           (equal (BITS (* 2 x) i 0)
                  (* 2 x)))
  :hints (("Goal" :use (:instance bits-tail (x (* 2 x)) (i i))
           :in-theory (set-difference-theories
                       (enable bvecp)
                       '(bits-tail)))))

;remove?
(defthm bits-does-nothing-hack-2
  (implies (and (< x (expt 2 i))
                (integerp x)
                (<= 0 x)
                (integerp i)
                (<= 0 i))
           (equal (bits (+ 1 (* 2 x)) i 0)
                  (+ 1 (* 2 x))))
  :hints (("goal" :in-theory (set-difference-theories
                              (enable expt-split)
                              '(bits-tail
                                ))
           :use (:instance bits-tail (x (+ 1 (* 2 x))) (i i)))))


;is this one too expensive?
(defthm bvecp-def
  (implies (and (< x (expt 2 k))
                (integerp x)
                (<= 0 x)
                )
           (bvecp x k))
  :hints (("Goal" :in-theory (enable bvecp)))
  :rule-classes ((:rewrite :backchain-limit-lst (1 nil nil))))

(defthm if1-0
  (equal (if1 0 y z)
         z))

(defthm if1-non-0
  (implies (not (equal x 0))
           (equal (if1 x y z)
                  y)))

(defthm if1-x-x
  (equal (if1 tst x x)
         x))

(defthm bvecp-if1
  (equal (bvecp (if1 x y z) n)
         (if1 x (bvecp y n) (bvecp z n))))

(defthm bv-arrp-if1
  (equal (bv-arrp (if1 x y z) n)
         (if1 x (bv-arrp y n) (bv-arrp z n))))

;remove these?


#|
(defthm bvecp-1-values
  (implies (and (bvecp x 1)
                (not (equal x 0)))
           (equal (equal x 1) t))
  :hints (("Goal" :in-theory (enable bvecp))))

(defthm bvecp-2-values
  (implies (and (bvecp x 2)
                (not (equal x 2))
                (not (equal x 1))
                (not (equal x 0)))
           (equal (equal x 3) t))
  :hints (("Goal" :in-theory (enable bvecp))))

(defthm bvecp-3-values
  (implies (and (bvecp x 3)
                (not (equal x 6))
                (not (equal x 5))
                (not (equal x 4))
                (not (equal x 3))
                (not (equal x 2))
                (not (equal x 1))
                (not (equal x 0)))
           (equal (equal x 7) t))
  :hints (("Goal" :in-theory (enable bvecp))))

(defthm bvecp-4-values
  (implies (and (bvecp x 4)
                (not (equal x 14))
                (not (equal x 13))
                (not (equal x 12))
                (not (equal x 11))
                (not (equal x 10))
                (not (equal x 9))
                (not (equal x 8))
                (not (equal x 7))
                (not (equal x 6))
                (not (equal x 5))
                (not (equal x 4))
                (not (equal x 3))
                (not (equal x 2))
                (not (equal x 1))
                (not (equal x 0)))
           (equal (equal x 15) t))
  :hints (("Goal" :in-theory (enable bvecp))))

(defthm bvecp-5-values
  (implies (and (bvecp x 5)
                (not (equal x 30))
                (not (equal x 29))
                (not (equal x 28))
                (not (equal x 27))
                (not (equal x 26))
                (not (equal x 25))
                (not (equal x 24))
                (not (equal x 23))
                (not (equal x 22))
                (not (equal x 21))
                (not (equal x 20))
                (not (equal x 19))
                (not (equal x 18))
                (not (equal x 17))
                (not (equal x 16))
                (not (equal x 15))
                (not (equal x 14))
                (not (equal x 13))
                (not (equal x 12))
                (not (equal x 11))
                (not (equal x 14))
                (not (equal x 13))
                (not (equal x 12))
                (not (equal x 11))
                (not (equal x 10))
                (not (equal x 9))
                (not (equal x 8))
                (not (equal x 7))
                (not (equal x 6))
                (not (equal x 5))
                (not (equal x 4))
                (not (equal x 3))
                (not (equal x 2))
                (not (equal x 1))
                (not (equal x 0)))
           (equal (equal x 31) t))
  :hints (("Goal" :in-theory (enable bvecp))))


;can remove these two?
(defthm natp-*
  (implies (and (integerp x)
                (>= x 0)
                (integerp y)
                (>= y 0))
           (and (integerp (* x y))
                (>= (* x y) 0))))

(defthm natp-+
  (implies (and (integerp x)
                (>= x 0)
                (integerp y)
                (>= y 0))
           (and (integerp (+ x y))
                (>= (+ x y) 0))))


;drop?
(DEFTHM BITS-bvecp-FW
  (IMPLIES (EQUAL N (- (1+ I) J))
           (BVECP (BITS X I J) N))
  :RULE-CLASSES
  ((:FORWARD-CHAINING :TRIGGER-TERMS ((BITS X I J)))))
|#


;BOZO where all should this go?  make an if1 book!
(defthmd if1-lnot
  (implies (bvecp tst 1)
	   (equal (if1 (lnot tst 1) x y)
		  (if1 tst y x)))
  :hints (("Goal" :in-theory (enable if1 bvecp))))
