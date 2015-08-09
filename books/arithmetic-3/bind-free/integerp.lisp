; See the top-level arithmetic-3 LICENSE file for authorship,
; copyright, and license information.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; integerp.lisp
;;;
;;;
;;; This book contains several lemmatta about when a sum or
;;; product is or is not an integer.
;;;
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")


(local
 (include-book "../pass1/top"))

(include-book "building-blocks")

(include-book "default-hint")

(set-default-hints '((nonlinearp-default-hint stable-under-simplificationp
                                              hist pspv)))

(table acl2-defaults-table :state-ok t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; 1. A whole slew of type-prescription rules about ratios.

;;; NOTE: It might be a good idea to add a bind-free/meta rule
;;; generalizing the following.

;;; We used to limit the coverage of these rules to the case
;;; where there were only two factors.  It would be nice to be
;;; able to write a bind-free or meta type rule to handle the
;;; general situation, rather than proliferating rules as below.
;;; This would also ensure complete coverage for even larger
;;; terms.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(encapsulate
 ()

 (set-non-linearp t)

 (local
  (defthm not-integerp-helper
    (implies (and (rationalp a)
                  (rationalp x)
                  (< 0 a)
                  (< a x))
             (and (< 0 (* (/ x) a))
                  (< (* (/ x) a) 1)))
    :rule-classes nil))

 (defthm not-integerp-1a
   (implies (and (rationalp a)
                 (rationalp x)
                 (< 0 a)
                 (< a x))
            (not (integerp (* (/ x) a))))
   :hints (("Goal" :use not-integerp-helper))
   :rule-classes :type-prescription)

 )

(defthm not-integerp-1b
  (implies (and (rationalp a)
		(rationalp x)
		(< 0 a)
		(< a x))
	   (not (integerp (* a (/ x)))))
  :hints (("Goal" :use not-integerp-1a))
  :rule-classes :type-prescription)

(defthm not-integerp-1c
  (implies (and (rationalp a)
                (rationalp b)
		(rationalp x)
		(< 0 (* a b))
		(< (* a b) x))
	   (not (integerp (* (/ x) a b))))
  :rule-classes :type-prescription)

(defthm not-integerp-1d
  (implies (and (rationalp a)
                (rationalp b)
		(rationalp x)
		(< 0 (* a b))
		(< (* a b) x))
	   (not (integerp (* a (/ x) b))))
  :hints (("Goal" :use not-integerp-1c))
  :rule-classes :type-prescription)

(defthm not-integerp-1e
  (implies (and (rationalp a)
                (rationalp b)
		(rationalp x)
		(< 0 (* a b))
		(< (* a b) x))
	   (not (integerp (* a b (/ x)))))
  :hints (("Goal" :use not-integerp-1c))
  :rule-classes :type-prescription)

(defthm not-integerp-1f
  (implies (and (rationalp a)
                (rationalp x)
		(rationalp y)
		(< 0 a)
		(< a (* x y)))
	   (not (integerp (* (/ x) (/ y) a))))
  :hints (("Goal" :use (:instance not-integerp-1a
                                  (a a)
                                  (x (* x y)))))
  :rule-classes :type-prescription)

(defthm not-integerp-1g
  (implies (and (rationalp a)
                (rationalp x)
		(rationalp y)
		(< 0 a)
		(< a (* x y)))
	   (not (integerp (* (/ x) a (/ y)))))
  :hints (("Goal" :use not-integerp-1f))
  :rule-classes :type-prescription)

(defthm not-integerp-1h
  (implies (and (rationalp a)
                (rationalp x)
		(rationalp y)
		(< 0 a)
		(< a (* x y)))
	   (not (integerp (* a (/ x) (/ y)))))
  :hints (("Goal" :use not-integerp-1f))
  :rule-classes :type-prescription)

(defthm not-integerp-1i
  (implies (and (rationalp a)
                (rationalp b)
                (rationalp c)
		(rationalp x)
		(< 0 (* a b c))
		(< (* a b c) x))
	   (not (integerp (* (/ x) a b c))))
  :rule-classes :type-prescription)

(defthm not-integerp-1j
  (implies (and (rationalp a)
                (rationalp b)
                (rationalp c)
		(rationalp x)
		(< 0 (* a b c))
		(< (* a b c) x))
	   (not (integerp (* a (/ x) b c))))
  :rule-classes :type-prescription)

(defthm not-integerp-1k
  (implies (and (rationalp a)
                (rationalp b)
                (rationalp c)
                (rationalp x)
		(< 0 (* a b c))
		(< (* a b c) x))
	   (not (integerp (* a b (/ x) c))))
  :hints (("Goal" :use not-integerp-1i))
  :rule-classes :type-prescription)

(defthm not-integerp-1l
  (implies (and (rationalp a)
                (rationalp b)
                (rationalp c)
		(rationalp x)
		(< 0 (* a b c))
		(< (* a b c) x))
	   (not (integerp (* a b c (/ x)))))
  :hints (("Goal" :use not-integerp-1i))
  :rule-classes :type-prescription)

(defthm not-integerp-1m
  (implies (and (rationalp a)
                (rationalp b)
                (rationalp x)
		(rationalp y)
		(< 0 (* a b))
		(< (* a b) (* x y)))
	   (not (integerp (* (/ x) (/ y) a b))))
  :rule-classes :type-prescription)

(defthm not-integerp-1n
  (implies (and (rationalp a)
                (rationalp b)
                (rationalp x)
		(rationalp y)
		(< 0 (* a b))
		(< (* a b) (* x y)))
	   (not (integerp (* (/ x) a (/ y) b))))
  :hints (("Goal" :use not-integerp-1m))
  :rule-classes :type-prescription)

(defthm not-integerp-1o
  (implies (and (rationalp a)
                (rationalp b)
                (rationalp x)
		(rationalp y)
		(< 0 (* a b))
		(< (* a b) (* x y)))
	   (not (integerp (* (/ x) a b (/ y)))))
  :hints (("Goal" :use not-integerp-1m))
  :rule-classes :type-prescription)

(defthm not-integerp-1p
  (implies (and (rationalp a)
                (rationalp b)
                (rationalp x)
		(rationalp y)
		(< 0 (* a b))
		(< (* a b) (* x y)))
	   (not (integerp (* a (/ x) (/ y) b))))
  :hints (("Goal" :use not-integerp-1m))
  :rule-classes :type-prescription)

(defthm not-integerp-1q
  (implies (and (rationalp a)
                (rationalp b)
                (rationalp x)
		(rationalp y)
		(< 0 (* a b))
		(< (* a b) (* x y)))
	   (not (integerp (* a (/ x) b (/ y)))))
  :hints (("Goal" :use not-integerp-1m))
  :rule-classes :type-prescription)

(defthm not-integerp-1r
  (implies (and (rationalp a)
                (rationalp b)
                (rationalp x)
		(rationalp y)
		(< 0 (* a b))
		(< (* a b) (* x y)))
	   (not (integerp (* a b (/ x) (/ y)))))
  :hints (("Goal" :use not-integerp-1m))
  :rule-classes :type-prescription)

(defthm not-integerp-1s
  (implies (and (rationalp a)
                (rationalp x)
                (rationalp y)
		(rationalp z)
		(< 0 a)
		(< a (* x y z)))
	   (not (integerp (* (/ x) (/ y) (/ z) a))))
  :hints (("Goal" :use (:instance not-integerp-1a
                                  (a a)
                                  (x (* x y z)))))
  :rule-classes :type-prescription)

(defthm not-integerp-1t
  (implies (and (rationalp a)
                (rationalp x)
                (rationalp y)
		(rationalp z)
		(< 0 a)
		(< a (* x y z)))
	   (not (integerp (* (/ x) (/ y) a (/ z)))))
  :hints (("Goal" :use not-integerp-1s))
  :rule-classes :type-prescription)

(defthm not-integerp-1u
  (implies (and (rationalp a)
                (rationalp x)
                (rationalp y)
		(rationalp z)
		(< 0 a)
		(< a (* x y z)))
	   (not (integerp (* (/ x) a (/ y) (/ z)))))
  :hints (("Goal" :use not-integerp-1s))
  :rule-classes :type-prescription)

(defthm not-integerp-1v
  (implies (and (rationalp a)
                (rationalp x)
                (rationalp y)
		(rationalp z)
		(< 0 a)
		(< a (* x y z)))
	   (not (integerp (* a (/ x) (/ y) (/ z)))))
  :hints (("Goal" :use not-integerp-1s))
  :rule-classes :type-prescription)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm not-integerp-2a
  (implies (and (rationalp a)
		(rationalp x)
		(< a 0)
		(< x a))
	   (not (integerp (* (/ x) a))))
  :hints (("Goal" :use (:instance not-integerp-1a
				  (a (- a))
				  (x (- x)))))
  :rule-classes :type-prescription)

(defthm not-integerp-2b
  (implies (and (rationalp a)
		(rationalp x)
		(< a 0)
		(< x a))
	   (not (integerp (* a (/ x)))))
  :hints (("Goal" :use not-integerp-2a))
  :rule-classes :type-prescription)

(defthm not-integerp-2c
  (implies (and (rationalp a)
                (rationalp b)
		(rationalp x)
		(< (* a b) 0)
		(< x (* a b)))
	   (not (integerp (* (/ x) a b))))
  :rule-classes :type-prescription)

(defthm not-integerp-2d
  (implies (and (rationalp a)
                (rationalp b)
		(rationalp x)
		(< (* a b) 0)
		(< x (* a b)))
	   (not (integerp (* a (/ x) b))))
  :hints (("Goal" :use not-integerp-2c))
  :rule-classes :type-prescription)

(defthm not-integerp-2e
  (implies (and (rationalp a)
                (rationalp b)
		(rationalp x)
		(< (* a b) 0)
		(< x (* a b)))
	   (not (integerp (* a b (/ x)))))
  :hints (("Goal" :use not-integerp-2c))
  :rule-classes :type-prescription)

(defthm not-integerp-2f
  (implies (and (rationalp a)
                (rationalp x)
		(rationalp y)
		(< a 0)
		(< (* x y) a))
	   (not (integerp (* (/ x) (/ y) a))))
  :hints (("Goal" :use (:instance not-integerp-2a
				  (a a)
				  (x (* x y)))))
  :rule-classes :type-prescription)

(defthm not-integerp-2g
  (implies (and (rationalp a)
                (rationalp x)
		(rationalp y)
		(< a 0)
		(< (* x y) a))
	   (not (integerp (* (/ x) a (/ y)))))
  :hints (("Goal" :use not-integerp-2f))
  :rule-classes :type-prescription)

(defthm not-integerp-2h
  (implies (and (rationalp a)
                (rationalp x)
		(rationalp y)
		(< a 0)
		(< (* x y) a))
	   (not (integerp (* a (/ x) (/ y)))))
  :hints (("Goal" :use not-integerp-2f))
  :rule-classes :type-prescription)

(defthm not-integerp-2i
  (implies (and (rationalp a)
                (rationalp b)
                (rationalp c)
		(rationalp x)
		(< (* a b c) 0)
		(< x (* a b c)))
	   (not (integerp (* (/ x) a b c))))
  :rule-classes :type-prescription)

(defthm not-integerp-2j
  (implies (and (rationalp a)
                (rationalp b)
                (rationalp c)
		(rationalp x)
		(< (* a b c) 0)
		(< x (* a b c)))
	   (not (integerp (* a (/ x) b c))))
  :rule-classes :type-prescription)

(defthm not-integerp-2k
  (implies (and (rationalp a)
                (rationalp b)
                (rationalp c)
		(rationalp x)
		(< (* a b c) 0)
		(< x (* a b c)))
	   (not (integerp (* a b (/ x) c))))
  :hints (("Goal" :use (:instance not-integerp-2a
				  (a (* a b c))
				  (x x))))
  :rule-classes :type-prescription)

(defthm not-integerp-2l
  (implies (and (rationalp a)
                (rationalp b)
                (rationalp c)
		(rationalp x)
		(< (* a b c) 0)
		(< x (* a b c)))
	   (not (integerp (* a b c (/ x)))))
  :hints (("Goal" :use not-integerp-2k))
  :rule-classes :type-prescription)

(defthm not-integerp-2m
  (implies (and (rationalp a)
                (rationalp b)
                (rationalp x)
		(rationalp y)
		(< (* a b) 0)
		(< (* x y) (* a b)))
	   (not (integerp (* (/ x) (/ y) a b))))
  :rule-classes :type-prescription)

(defthm not-integerp-2n
  (implies (and (rationalp a)
                (rationalp b)
                (rationalp x)
		(rationalp y)
		(< (* a b) 0)
		(< (* x y) (* a b)))
	   (not (integerp (* (/ x) a (/ y) b))))
  :hints (("Goal" :use (:instance not-integerp-2a
				  (a (* a b))
				  (x (* x y)))))
  :rule-classes :type-prescription)

(defthm not-integerp-2o
  (implies (and (rationalp a)
                (rationalp b)
                (rationalp x)
		(rationalp y)
		(< (* a b) 0)
		(< (* x y) (* a b)))
	   (not (integerp (* (/ x) a b (/ y)))))
  :hints (("Goal" :use not-integerp-2n))
  :rule-classes :type-prescription)

(defthm not-integerp-2p
  (implies (and (rationalp a)
                (rationalp b)
                (rationalp x)
		(rationalp y)
		(< (* a b) 0)
		(< (* x y) (* a b)))
	   (not (integerp (* a (/ x) (/ y) b))))
  :hints (("Goal" :use not-integerp-2n))
  :rule-classes :type-prescription)

(defthm not-integerp-2q
  (implies (and (rationalp a)
                (rationalp b)
                (rationalp x)
		(rationalp y)
		(< (* a b) 0)
		(< (* x y) (* a b)))
	   (not (integerp (* a (/ x) b (/ y)))))
  :hints (("Goal" :use not-integerp-2n))
  :rule-classes :type-prescription)

(defthm not-integerp-2r
  (implies (and (rationalp a)
                (rationalp b)
                (rationalp x)
		(rationalp y)
		(< (* a b) 0)
		(< (* x y) (* a b)))
	   (not (integerp (* a b (/ x) (/ y)))))
  :hints (("Goal" :use not-integerp-2n))
  :rule-classes :type-prescription)

(defthm not-integerp-2s
  (implies (and (rationalp a)
                (rationalp x)
                (rationalp y)
		(rationalp z)
		(< a 0)
		(< (* x y z) a))
	   (not (integerp (* (/ x) (/ y) (/ z) a))))
  :hints (("Goal" :use (:instance not-integerp-2a
				  (a a)
				  (x (* x y z)))))
  :rule-classes :type-prescription)

(defthm not-integerp-2t
  (implies (and (rationalp a)
                (rationalp x)
                (rationalp y)
		(rationalp z)
		(< a 0)
		(< (* x y z) a))
	   (not (integerp (* (/ x) (/ y) a (/ z)))))
  :hints (("Goal" :use not-integerp-2s))
  :rule-classes :type-prescription)

(defthm not-integerp-2u
  (implies (and (rationalp a)
                (rationalp x)
                (rationalp y)
		(rationalp z)
		(< a 0)
		(< (* x y z) a))
	   (not (integerp (* (/ x) a (/ y) (/ z)))))
  :hints (("Goal" :use not-integerp-2s))
  :rule-classes :type-prescription)

(defthm not-integerp-2v
  (implies (and (rationalp a)
                (rationalp x)
                (rationalp y)
		(rationalp z)
		(< a 0)
		(< (* x y z) a))
	   (not (integerp (* a (/ x) (/ y) (/ z)))))
  :hints (("Goal" :use not-integerp-2s))
  :rule-classes :type-prescription)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm not-integerp-3a
  (implies (and (rationalp a)
		(rationalp x)
		(< 0 a)
		(< x (- a)))
	   (not (integerp (* (/ x) a))))
  :hints (("Goal" :use (:instance not-integerp-1a
				  (a a)
				  (x (- x)))))
  :rule-classes :type-prescription)

(defthm not-integerp-3b
  (implies (and (rationalp a)
		(rationalp x)
		(< 0 a)
		(< x (- a)))
	   (not (integerp (* a (/ x)))))
  :hints (("Goal" :use not-integerp-3a))
  :rule-classes :type-prescription)

(defthm not-integerp-3c
  (implies (and (rationalp a)
                (rationalp b)
		(rationalp x)
		(< 0 (* a b))
		(< x (- (* a b))))
	   (not (integerp (* (/ x) a b))))
  :rule-classes :type-prescription)

(defthm not-integerp-3d
  (implies (and (rationalp a)
                (rationalp b)
		(rationalp x)
		(< 0 (* a b))
		(< x (- (* a b))))
	   (not (integerp (* a (/ x) b))))
  :hints (("Goal" :use not-integerp-3c))
  :rule-classes :type-prescription)

(defthm not-integerp-3e
  (implies (and (rationalp a)
                (rationalp b)
		(rationalp x)
		(< 0 (* a b))
		(< x (- (* a b))))
	   (not (integerp (* a b (/ x)))))
  :hints (("Goal" :use not-integerp-3d))
  :rule-classes :type-prescription)

(defthm not-integerp-3f
  (implies (and (rationalp a)
                (rationalp x)
		(rationalp y)
		(< 0 a)
		(< (* x y) (- a)))
	   (not (integerp (* (/ x) (/ y) a))))
  :hints (("Goal" :use (:instance not-integerp-3a
				  (a a)
				  (x (* x y)))))
  :rule-classes :type-prescription)

(defthm not-integerp-3g
  (implies (and (rationalp a)
                (rationalp x)
		(rationalp y)
		(< 0 a)
		(< (* x y) (- a)))
	   (not (integerp (* (/ x) a (/ y)))))
  :hints (("Goal" :use not-integerp-3f))
  :rule-classes :type-prescription)

(defthm not-integerp-3h
  (implies (and (rationalp a)
                (rationalp x)
		(rationalp y)
		(< 0 a)
		(< (* x y) (- a)))
	   (not (integerp (* a (/ x) (/ y)))))
  :hints (("Goal" :use not-integerp-3f))
  :rule-classes :type-prescription)

(defthm not-integerp-3i
  (implies (and (rationalp a)
                (rationalp b)
                (rationalp c)
		(rationalp x)
		(< 0 (* a b c))
		(< x (- (* a b c))))
	   (not (integerp (* (/ x) a b c))))
  :rule-classes :type-prescription)

(defthm not-integerp-3j
  (implies (and (rationalp a)
                (rationalp b)
                (rationalp c)
		(rationalp x)
		(< 0 (* a b c))
		(< x (- (* a b c))))
	   (not (integerp (* a (/ x) b c))))
  :rule-classes :type-prescription)

(defthm not-integerp-3k
  (implies (and (rationalp a)
                (rationalp b)
                (rationalp c)
		(rationalp x)
		(< 0 (* a b c))
		(< x (- (* a b c))))
	   (not (integerp (* a b (/ x) c))))
  :hints (("Goal" :use (:instance not-integerp-3a
				  (a (* a b c))
				  (x x))))
  :rule-classes :type-prescription)

(defthm not-integerp-3l
  (implies (and (rationalp a)
                (rationalp b)
                (rationalp c)
		(rationalp x)
		(< 0 (* a b c))
		(< x (- (* a b c))))
	   (not (integerp (* a b c (/ x)))))
  :hints (("Goal" :use not-integerp-3k))
  :rule-classes :type-prescription)

(defthm not-integerp-3m
  (implies (and (rationalp a)
                (rationalp b)
                (rationalp x)
		(rationalp y)
		(< 0 (* a b))
		(< (* x y) (- (* a b))))
	   (not (integerp (* (/ x) (/ y) a b))))
  :rule-classes :type-prescription)

(defthm not-integerp-3n
  (implies (and (rationalp a)
                (rationalp b)
                (rationalp x)
		(rationalp y)
		(< 0 (* a b))
		(< (* x y) (- (* a b))))
	   (not (integerp (* (/ x) a (/ y) b))))
  :hints (("Goal" :use (:instance not-integerp-3a
				  (a (* a b))
				  (x (* x y)))))
  :rule-classes :type-prescription)

(defthm not-integerp-3o
  (implies (and (rationalp a)
                (rationalp b)
                (rationalp x)
		(rationalp y)
		(< 0 (* a b))
		(< (* x y) (- (* a b))))
	   (not (integerp (* (/ x) a b (/ y)))))
  :hints (("Goal" :use not-integerp-3n))
  :rule-classes :type-prescription)

(defthm not-integerp-3p
  (implies (and (rationalp a)
                (rationalp b)
                (rationalp x)
		(rationalp y)
		(< 0 (* a b))
		(< (* x y) (- (* a b))))
	   (not (integerp (* a (/ x) (/ y) b))))
  :hints (("Goal" :use not-integerp-3n))
  :rule-classes :type-prescription)

(defthm not-integerp-3q
  (implies (and (rationalp a)
                (rationalp b)
                (rationalp x)
		(rationalp y)
		(< 0 (* a b))
		(< (* x y) (- (* a b))))
	   (not (integerp (* a (/ x) b (/ y)))))
  :hints (("Goal" :use not-integerp-3n))
  :rule-classes :type-prescription)

(defthm not-integerp-3r
  (implies (and (rationalp a)
                (rationalp b)
                (rationalp x)
		(rationalp y)
		(< 0 (* a b))
		(< (* x y) (- (* a b))))
	   (not (integerp (* a b (/ x) (/ y)))))
  :hints (("Goal" :use not-integerp-3n))
  :rule-classes :type-prescription)

(defthm not-integerp-3s
  (implies (and (rationalp a)
                (rationalp x)
                (rationalp y)
		(rationalp z)
		(< 0 a)
		(< (* x y z) (- a)))
	   (not (integerp (* (/ x) (/ y) (/ z) a))))
  :hints (("Goal" :use (:instance not-integerp-3a
				  (a a)
				  (x (* x y z)))))
  :rule-classes :type-prescription)

(defthm not-integerp-3t
  (implies (and (rationalp a)
                (rationalp x)
                (rationalp y)
		(rationalp z)
		(< 0 a)
		(< (* x y z) (- a)))
	   (not (integerp (* (/ x) (/ y) a (/ z)))))
  :hints (("Goal" :use not-integerp-3s))
  :rule-classes :type-prescription)

(defthm not-integerp-3u
  (implies (and (rationalp a)
                (rationalp x)
                (rationalp y)
		(rationalp z)
		(< 0 a)
		(< (* x y z) (- a)))
	   (not (integerp (* (/ x) a (/ y) (/ z)))))
  :hints (("Goal" :use not-integerp-3s))
  :rule-classes :type-prescription)

(defthm not-integerp-3v
  (implies (and (rationalp a)
                (rationalp x)
                (rationalp y)
		(rationalp z)
		(< 0 a)
		(< (* x y z) (- a)))
	   (not (integerp (* a (/ x) (/ y) (/ z)))))
  :hints (("Goal" :use not-integerp-3s))
  :rule-classes :type-prescription)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm not-integerp-4a
  (implies (and (rationalp a)
		(rationalp x)
		(< a 0)
		(< (- a) x))
	   (not (integerp (* (/ x) a))))
  :hints (("Goal" :use (:instance not-integerp-1a
				  (a (- a))
				  (x x))))
  :rule-classes :type-prescription)

(defthm not-integerp-4b
  (implies (and (rationalp a)
		(rationalp x)
		(< a 0)
		(< (- a) x))
	   (not (integerp (* a (/ x)))))
  :hints (("Goal" :use not-integerp-4a))
  :rule-classes :type-prescription)

(defthm not-integerp-4c
  (implies (and (rationalp a)
                (rationalp b)
		(rationalp x)
		(< (* a b) 0)
		(< (- (* a b)) x))
	   (not (integerp (* (/ x) a b))))
  :rule-classes :type-prescription)

(defthm not-integerp-4d
  (implies (and (rationalp a)
                (rationalp b)
		(rationalp x)
		(< (* a b) 0)
		(< (- (* a b)) x))
	   (not (integerp (* a (/ x) b))))
  :hints (("Goal" :use not-integerp-4c))
  :rule-classes :type-prescription)

(defthm not-integerp-4e
  (implies (and (rationalp a)
                (rationalp b)
		(rationalp x)
		(< (* a b) 0)
		(< (- (* a b)) x))
	   (not (integerp (* a b (/ x)))))
  :hints (("Goal" :use not-integerp-4c))
  :rule-classes :type-prescription)

(defthm not-integerp-4f
  (implies (and (rationalp a)
                (rationalp x)
		(rationalp y)
		(< a 0)
		(< (- a) (* x y)))
	   (not (integerp (* (/ x) (/ y) a))))
  :hints (("Goal" :use (:instance not-integerp-4a
				  (a a)
				  (x (* x y)))))
  :rule-classes :type-prescription)

(defthm not-integerp-4g
  (implies (and (rationalp a)
                (rationalp x)
		(rationalp y)
		(< a 0)
		(< (- a) (* x y)))
	   (not (integerp (* (/ x) a (/ y)))))
  :hints (("Goal" :use not-integerp-4f))
  :rule-classes :type-prescription)

(defthm not-integerp-4h
  (implies (and (rationalp a)
                (rationalp x)
		(rationalp y)
		(< a 0)
		(< (- a) (* x y)))
	   (not (integerp (* a (/ x) (/ y)))))
  :hints (("Goal" :use not-integerp-4f))
  :rule-classes :type-prescription)

(defthm not-integerp-4i
  (implies (and (rationalp a)
                (rationalp b)
                (rationalp c)
		(rationalp x)
		(< (* a b c) 0)
		(< (- (* a b c)) x))
	   (not (integerp (* (/ x) a b c))))
  :rule-classes :type-prescription)

(defthm not-integerp-4j
  (implies (and (rationalp a)
                (rationalp b)
                (rationalp c)
		(rationalp x)
		(< (* a b c) 0)
		(< (- (* a b c)) x))
	   (not (integerp (* a (/ x) b c))))
  :rule-classes :type-prescription)

(defthm not-integerp-4k
  (implies (and (rationalp a)
                (rationalp b)
                (rationalp c)
		(rationalp x)
		(< (* a b c) 0)
		(< (- (* a b c)) x))
	   (not (integerp (* a b (/ x) c))))
  :hints (("Goal" :use not-integerp-4i))
  :rule-classes :type-prescription)

(defthm not-integerp-4l
  (implies (and (rationalp a)
                (rationalp b)
                (rationalp c)
		(rationalp x)
		(< (* a b c) 0)
		(< (- (* a b c)) x))
	   (not (integerp (* a b c (/ x)))))
  :hints (("Goal" :use not-integerp-4i))
  :rule-classes :type-prescription)

(defthm not-integerp-4m
  (implies (and (rationalp a)
                (rationalp b)
                (rationalp x)
		(rationalp y)
		(< (* a b) 0)
		(< (- (* a b)) (* x y)))
	   (not (integerp (* (/ x) (/ y) a b))))
  :rule-classes :type-prescription)

(defthm not-integerp-4n
  (implies (and (rationalp a)
                (rationalp b)
                (rationalp x)
		(rationalp y)
		(< (* a b) 0)
		(< (- (* a b)) (* x y)))
	   (not (integerp (* (/ x) a (/ y) b))))
  :hints (("Goal" :use not-integerp-4m))
  :rule-classes :type-prescription)

(defthm not-integerp-4o
  (implies (and (rationalp a)
                (rationalp b)
                (rationalp x)
		(rationalp y)
		(< (* a b) 0)
		(< (- (* a b)) (* x y)))
	   (not (integerp (* (/ x) a b (/ y)))))
  :hints (("Goal" :use not-integerp-4m))
  :rule-classes :type-prescription)

(defthm not-integerp-4p
  (implies (and (rationalp a)
                (rationalp b)
                (rationalp x)
		(rationalp y)
		(< (* a b) 0)
		(< (- (* a b)) (* x y)))
	   (not (integerp (* a (/ x) (/ y) b))))
  :hints (("Goal" :use not-integerp-4m))
  :rule-classes :type-prescription)

(defthm not-integerp-4q
  (implies (and (rationalp a)
                (rationalp b)
                (rationalp x)
		(rationalp y)
		(< (* a b) 0)
		(< (- (* a b)) (* x y)))
	   (not (integerp (* a (/ x) b (/ y)))))
  :hints (("Goal" :use (:instance not-integerp-4a
				  (a (* a b))
				  (x (* x y)))))
  :rule-classes :type-prescription)

(defthm not-integerp-4r
  (implies (and (rationalp a)
                (rationalp b)
                (rationalp x)
		(rationalp y)
		(< (* a b) 0)
		(< (- (* a b)) (* x y)))
	   (not (integerp (* a b (/ x) (/ y)))))
  :hints (("Goal" :use not-integerp-4q))
  :rule-classes :type-prescription)

(defthm not-integerp-4s
  (implies (and (rationalp a)
                (rationalp x)
                (rationalp y)
		(rationalp z)
		(< a 0)
		(< (- a) (* x y z)))
	   (not (integerp (* (/ x) (/ y) (/ z) a))))
  :hints (("Goal" :use (:instance not-integerp-4a
				  (a a)
				  (x (* x y z)))))
  :rule-classes :type-prescription)

(defthm not-integerp-4t
  (implies (and (rationalp a)
                (rationalp x)
                (rationalp y)
		(rationalp z)
		(< a 0)
		(< (- a) (* x y z)))
	   (not (integerp (* (/ x) (/ y) a (/ z)))))
  :hints (("Goal" :use not-integerp-4s))
  :rule-classes :type-prescription)

(defthm not-integerp-4u
  (implies (and (rationalp a)
                (rationalp x)
                (rationalp y)
		(rationalp z)
		(< a 0)
		(< (- a) (* x y z)))
	   (not (integerp (* (/ x) a (/ y) (/ z)))))
  :hints (("Goal" :use not-integerp-4s))
  :rule-classes :type-prescription)

(defthm not-integerp-4v
  (implies (and (rationalp a)
                (rationalp x)
                (rationalp y)
		(rationalp z)
		(< a 0)
		(< (- a) (* x y z)))
	   (not (integerp (* a (/ x) (/ y) (/ z)))))
  :hints (("Goal" :use not-integerp-4s))
  :rule-classes :type-prescription)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; 2. Simplifying terms such as (integerp (+ a b c)).

;;; (implies (integerp b)
;;;          (equal (integerp (+ a b c))
;;;                 (integerp (+ a c))))

#|
This seems like a good place to record some of my thinking about how
to design a good arithmetic library.  The following is part of an
email exchange between me and Matt Kaufmann:

>
>Hi, Robert --
>
>I'm curious: Why did you choose the order of cases that you did in
>reduce-integerp-+-fn-1?  I can imagine instead swapping the second and third as
>shown below, so that if x is (+ a (+ b c)) and (+ b c) is known to be an
>integer, then we wind up subtracting all of (+ b c) from (+ a (+ b c)).
>
>(defun reduce-integerp-+-fn-1 (x mfc state)
>  (cond ((proveably-integer (fargn x 1) mfc state)
>         (list (cons 'z (fargn x 1))))
>        ((proveably-integer (fargn x 2) mfc state)
>         (list (cons 'z (fargn x 2))))
>        ((eq (fn-symb (fargn x 2)) 'BINARY-+)
>         (reduce-integerp-+-fn-1 (fargn x 2) mfc state))
>        (t
>         nil)))
Hi Matt,

I chose the order I did just so that I would not subtract the (+ b c).
I wanted to have a theorem which would behave in a consistent and
predictable manner, and still catch as much as it could.  The fact
that the (+ b c) appears as an addend of (+ a b c), as the user sees
it, seems rather accidental to me.  What if the sum was (+ a b c d)
and we knew (+ b c) was an integer?  The presence of the extra addend,
d, would prevent the rule from behaving as it did before.  Or what if
I knew that (+ a c) was an integer?

In the situation where I can find some partition of all the addends
such that I can rewrite an (integerp ...) to t or nil seems like a
situation where the extra work involved of checking various
combinations is worth while, and I do have a rule for that ---
meta-integerp which fires before this rule.  But if I can't reduce the
hypothesis to t or nil, I did not see that there was an obvious answer
to the question of how much to remove.  Thus I stayed with the easy
and predictable.  It really gets my goat when ACL2 will get one
theorem easily, but fails on another theorem "which is the same".  I
feel that, in particular, variable names should not affect whether
ACL2 wins or loses.

Robert
|#

(defun reduce-integerp-+-fn-1 (x mfc state)
  (declare (xargs :guard (and (pseudo-termp x)
                              (eq (fn-symb x) 'BINARY-+))))
  (cond ((and (not (equal (fargn x 1) ''0))
              (proveably-integer (fargn x 1) mfc state))
         (list (cons 'z (fargn x 1))))
        ((eq (fn-symb (fargn x 2)) 'BINARY-+)
         (reduce-integerp-+-fn-1 (fargn x 2) mfc state))
        ((and (not (equal (fargn x 2) ''0))
              (proveably-integer (fargn x 2) mfc state))
         (list (cons 'z (fargn x 2))))
        (t
         nil)))

(defun reduce-integerp-+-fn (x mfc state)
  (declare (xargs :guard (pseudo-termp x)))

  (if (eq (fn-symb x) 'BINARY-+)
      (reduce-integerp-+-fn-1 x mfc state)
    nil))

(local
 (defthm iff-integerp
     (equal (equal (integerp x)
                   (integerp y))
            (iff (integerp x)
                 (integerp y)))))

;;; Note: The use of rewriting-goal-literal ensures that we
;;; do not use this while backchaining --- it does not seem
;;; worthwhile to go through all this work unless we can
;;; decide the qustion one way or another, and meta-integerp
;;; would have done that if it could.

(defthm reduce-integerp-+
    (implies (and (syntaxp (rewriting-goal-literal x mfc state))
                  (bind-free (reduce-integerp-+-fn x mfc state)
                             (z))
                  (equal y (- x z))
                  (integerp z)
                  (acl2-numberp x))
             (equal (integerp x)
                    (integerp y))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Note that we put rules such as |(integerp (- x))| after
;;; rules such as not-integerp-1a.  ACL2 uses rules ``most
;;; recently seen first.''  Thus we place rules that simplify
;;; or normalize terms before those that decide their validity.
;;; This will allow the latter rules to make certain simple
;;; assumptions about the forms of the terms they see.

;;; (integerp (- x)) ===> (integerp x)

;;; We use negative-addends-p to handle the more general
;;; situation, e.g., (integerp (+ 3 (- x) (* -7 y))).

(defthm integerp-minus-x
    (implies (and (syntaxp (weak-negative-addends-p x))
                  (acl2-numberp x))
             (equal (integerp x)
                    (integerp (- x)))))

;;; (implies (and (integerp (* d x))
;;;               (integerp (/ c d)))
;;;          (integerp (* c x)))

;;; e.gg.,
;;; (implies (integerp (* 1/4 x))
;;;          (integerp (* 3/4 x)))

;;; (implies (integerp (* 1/4 x))
;;;          (integerp (* 1/2 x)))

(defun find-integerp-hyp-1 (type-alist c x)
  (cond ((endp type-alist)
         nil)
        ((let ((typed-term (caar type-alist))
               (type (cadar type-alist)))
           (and (eq (fn-symb typed-term) 'BINARY-*)
                (quotep (fargn typed-term 1))
                (equal (fargn typed-term 2) x)
                ;; We have a term of the form (* d x) where
                ;; d is a constant and x is as supplied.
                (ts-subsetp type *ts-integer*)
                ;; The term is known to be an integer.
                (integerp (/ (unquote c)
                             (unquote (fargn typed-term 1))))
                ;; And so is (/ c d).
                ))
         (list (cons 'd (fargn (caar type-alist) 1))
               (cons 'a (kwote (/ (unquote c)
                                  (unquote (fargn (caar type-alist) 1)))))))
        (t
         (find-integerp-hyp-1 (cdr type-alist) c x))))

(defun find-integerp-hyp (c x mfc state)
  (declare (ignore state))
  ;; We look in the type-alist for a term of the form
  ;; (integerp (* d x)) which is assumed true, where
  ;; c divided by d is an integer.  We return both d
  ;; and (/ c d) in a manner sutiable for bind-free.
  (find-integerp-hyp-1 c x (mfc-type-alist mfc)))

(defthm |(integerp (* c x))|
    (implies (and (bind-free (find-integerp-hyp c x mfc state)
                             (d a))
                  (equal (* d a) c)
                  (integerp (* d x))
                  (integerp a))
             (integerp (* c x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; The neccesity of this rule points out a problem with my
;;; current treatment of expt.  I should probably treat expt
;;; as ``above'' the other ``fundamental'' arithmetic
;;; operations --- +, -, *, /.  I have, up till now, been
;;; thinking of expt as a fancy or paramterized multiplication
;;; insead of treating it in its own right.

;;; The form of this rule also points out a flaw in my
;;; normalization procedures with respect to division and
;;; expt.  Better would probably be something like
;;; (* x (/ (expt x n))), and then the above rules would
;;; cover this case also.

(defthm nintergerp-extra
    (implies (and (rationalp x)
                  (< 0 x)
                  (rationalp y)
                  (< 0 y)
                  (integerp i)
                  (< 0 i)
                  (< x (expt y i)))
             (not (integerp (* x (expt (/ y) i))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; A couple of neat rules taken from the RTL books.  These are
;;; due to Eric Smith.

;renamed to avoid conflict with rtl/rel5
(defthm integerp-+-reduce-leading-rational-constant
  (implies (and (syntaxp (rational-constant-p c))
                (syntaxp (or (<= 1 (unquote c))
                             (< (unquote c) 0))))
           (equal (integerp (+ c x))
                  (integerp (+ (+ c (- (floor c 1))) x))))
  :hints (("Goal" :in-theory (disable floor))))

(encapsulate
 ()

 (local
  (defun INDUCT-NAT (x)
    (if (and (integerp x)
             (> x 0))
        (induct-nat (1- x))
      ())))

 (local
  (defthm x-or-x/2-4
    (implies (and (integerp x) (>= x 0))
	     (or (integerp (/ x 2)) (integerp (/ (1+ x) 2))))
    :rule-classes ()
    :hints (("Goal" :induct (induct-nat x)))))

 (local
  (defthm x-or-x/2-5
    (IMPLIES (integerp x)
	     (integerp (- x)))
    :rule-classes ()))

 (local
  (defthm x-or-x/2-11
    (implies (and (integerp x) (<= x 0))
	     (or (integerp (/ x 2)) (integerp (/ (1+ x) 2))))
    :rule-classes ()
    :hints (("Goal" :in-theory (disable FUNCTIONAL-SELF-INVERSION-OF-MINUS)
             :use ((:instance x-or-x/2-4 (x (- x)))
                   (:instance x-or-x/2-5 (x (* -1/2 x)))))
            ("Subgoal 1" :in-theory (enable FUNCTIONAL-SELF-INVERSION-OF-MINUS)))))

 (local
  (defthm X-OR-X/2
    (implies (integerp x)
	     (or (integerp (/ x 2)) (integerp (/ (1+ x) 2))))
    :rule-classes ()
    :hints (("Goal" :in-theory (disable FUNCTIONAL-SELF-INVERSION-OF-MINUS)
             :use ((:instance x-or-x/2-4)
                   (:instance x-or-x/2-11))))))


 (defthm even-and-odd-alternate
   (implies (rationalp x)
            (equal (integerp (+ 1/2 x))
                   (and (integerp (* 2 x))
                        (not (integerp x)))))
   :hints (("Subgoal 3'"
            :use ((:instance
                   (:theorem (implies (and (integerp x)
                                           (integerp y))
                                      (integerp (* x y))))
                   (x (+ 1/2 x))
                   (y 2))))
           ("Subgoal 2'"
            :use ((:instance X-OR-X/2
                             (x (* 2 x)))))))

 )