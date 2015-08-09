; Arithmetic-5 Library
; Written by Robert Krug
; Copyright/License:
; See the LICENSE file at the top level of the arithmetic-5 library.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; integerp.lisp
;;;
;;;
;;; This book contains several lemmatta about when a sum or
;;; product is or is not an integer.
;;;
;;; Now that I am preferring (expt x (- n)) to (/ (expt x n))
;;; I need even more rules here.  Will it never end?
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(include-book "building-blocks")

(local
 (include-book "default-hint"))

(local
 (include-book "../../support/top"))

(local
 (include-book "integerp-helper"))

;; (local
;;  (set-default-hints '((nonlinearp-default-hint stable-under-simplificationp
;; 					       hist pspv))))

(table acl2-defaults-table :state-ok t)


(local (in-theory (disable default-*-1
                           default-*-2
                           default-+-1
                           default-+-2
                           default-<-1
                           default-<-2
                           default-unary-/
                           default-unary-minus
                           default-realpart
                           default-numerator
                           default-imagpart
                           default-denominator
                           default-coerce-1
                           default-coerce-2
                           default-car
                           default-cdr)))

(local (in-theory (disable expt-type-prescription-rationalp
                           expt-type-prescription-nonzero
                           expt-type-prescription-positive-1
                           expt-type-prescription-positive-2
                           expt-type-prescription-integerp
                           expt-type-prescription-non-zero-base)))


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

;;; I have commented out some of the below rules which should
;;; be redundant.  I should make sure that this is really the
;;; case.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defthm expt-crock
   (implies (and (real/rationalp x)
		 (integerp n))
	    (equal (expt x (- n))
		   (/ (expt x n))))))

(encapsulate
 ()

;;; I surely don't need all this to prove not-integerp-helper!
;;; Clean this up.

 (local
  (include-book "common"))

 (local
  (include-book "normalize"))

 (local
  (include-book "simplify"))

 (local
  (include-book "collect"))

 (local
  (in-theory (disable NORMALIZE-FACTORS-SCATTER-EXPONENTS)))

 (local
  (defthm not-integerp-helper
    (implies (and ;(real/rationalp a)
              (real/rationalp x)
              (< 0 a)
              (< a x))
             (and (< 0 (* (/ x) a))
                  (< (* (/ x) a) 1)))
    :rule-classes nil))

 (defthm not-integerp-1a
   (implies (and ;(real/rationalp a)
             (real/rationalp x)
             (< 0 a)
             (< a x))
            (not (integerp (* (/ x) a))))
   :hints (("Goal" :use not-integerp-helper))
   :rule-classes :type-prescription)

 (defthm not-integerp-1a-expt
   (implies (and ;(real/rationalp a)
             (real/rationalp x)
             (integerp n)
             (< 0 a)
             (< a (expt x n)))
            (not (integerp (* (expt x (- n)) a))))
   :hints (("Goal" :use (:instance not-integerp-helper
				   (x (expt x n)))))
   :rule-classes :type-prescription)

 )

(local (in-theory (disable not-integerp-1a not-integerp-1a-expt)))


(defthm not-integerp-1b
  (implies (and ;(real/rationalp a)
		(real/rationalp x)
		(< 0 a)
		(< a x))
	   (not (integerp (* a (/ x)))))
  :hints (("Goal" :use not-integerp-1a))
  :rule-classes :type-prescription)

(defthm not-integerp-1b-expt
  (implies (and ;(real/rationalp a)
		(real/rationalp x)
		(integerp n)
		(< 0 a)
		(< a (expt x n)))
	   (not (integerp (* a (expt x (- n))))))
  :hints (("Goal" :use (:instance not-integerp-1a
				  (x (expt x n)))))
  :rule-classes :type-prescription)

(local (in-theory (disable not-integerp-1b not-integerp-1b-expt)))

;; (defthm not-integerp-1c
;;   (implies (and (rationalp a)
;;                 (rationalp b)
;; 		(rationalp x)
;; 		(< 0 (* a b))
;; 		(< (* a b) x))
;; 	   (not (integerp (* (/ x) a b))))
;;   :rule-classes :type-prescription)

(defthm not-integerp-1d
  (implies (and ;(real/rationalp a)
                (real/rationalp b)
		(real/rationalp x)
		(< 0 (* a b))
		(< (* a b) x))
	   (not (integerp (* a (/ x) b))))
  :hints (("Goal" :use (:instance not-integerp-1a
				  (a (* a b))
				  (x x))))
  :rule-classes :type-prescription)

(defthm not-integerp-1d-expt
  (implies (and ;(real/rationalp a)
                (real/rationalp b)
		(real/rationalp x)
		(integerp n)
		(< 0 (* a b))
		(< (* a b) (expt x n)))
	   (not (integerp (* a (expt x (- n)) b))))
  :hints (("Goal" :use (:instance not-integerp-1a
				  (a (* a b))
				  (x (expt x n)))))
  :rule-classes :type-prescription)

(local (in-theory (disable not-integerp-1d not-integerp-1d-expt)))

(defthm not-integerp-1e
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
		(real/rationalp x)
		(< 0 (* a b))
		(< (* a b) x))
	   (not (integerp (* a b (/ x)))))
  :hints (("Goal" :use (:instance not-integerp-1a
				  (a (* a b))
				  (x x))))
  :rule-classes :type-prescription)

(defthm not-integerp-1e-expt
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
		(real/rationalp x)
		(integerp n)
		(< 0 (* a b))
		(< (* a b) (expt x n)))
	   (not (integerp (* a b (expt x (- n))))))
  :hints (("Goal" :use (:instance not-integerp-1a
				  (a (* a b))
				  (x (expt x n)))))
  :rule-classes :type-prescription)

(local (in-theory (disable not-integerp-1e not-integerp-1e-expt)))


(defthm not-integerp-1f
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(real/rationalp y)
		(< 0 a)
		(< a (* x y)))
	   (not (integerp (* (/ x) (/ y) a))))
  :hints (("Goal" :use (:instance not-integerp-1a
                                  (a a)
                                  (x (* x y)))))
  :rule-classes :type-prescription)

(defthm not-integerp-1f-expt-a
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(integerp n)
		(real/rationalp y)
		(< 0 a)
		(< a (* (expt x n) y)))
	   (not (integerp (* (expt x (- n)) (/ y) a))))
  :hints (("Goal" :use (:instance not-integerp-1a
                                  (a a)
                                  (x (* (expt x n) y)))))
  :rule-classes :type-prescription)

(defthm not-integerp-1f-expt-b
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(real/rationalp y)
		(integerp n)
		(< 0 a)
		(< a (* x (expt y n))))
	   (not (integerp (* (/ x) (expt y (- n)) a))))
  :hints (("Goal" :use (:instance not-integerp-1a
                                  (a a)
                                  (x (* (expt y n) x)))))
  :rule-classes :type-prescription)

(defthm not-integerp-1f-expt-c
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(integerp n1)
		(real/rationalp y)
		(integerp n2)
		(< 0 a)
		(< a (* (expt x n1) (expt y n2))))
	   (not (integerp (* (expt x (- n1)) (expt y (- n2)) a))))
  :hints (("Goal" :use (:instance not-integerp-1a
                                  (a a)
                                  (x (* (expt x n1) (expt y n2))))))
  :rule-classes :type-prescription)

(local (in-theory (disable not-integerp-1f
                           not-integerp-1f-expt-a
                           not-integerp-1f-expt-b
                           not-integerp-1f-expt-c)))

(defthm not-integerp-1g
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(real/rationalp y)
		(< 0 a)
		(< a (* x y)))
	   (not (integerp (* (/ x) a (/ y)))))
  :hints (("Goal" :use not-integerp-1f))
  :rule-classes :type-prescription)

(defthm not-integerp-1g-expt-a
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(integerp n)
		(real/rationalp y)
		(< 0 a)
		(< a (* (expt x n) y)))
	   (not (integerp (* (expt x (- n)) a (/ y)))))
  :hints (("Goal" :use (:instance not-integerp-1f
				  (x (expt x n)))))
  :rule-classes :type-prescription)

(defthm not-integerp-1g-expt-b
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(real/rationalp y)
		(integerp n)
		(< 0 a)
		(< a (* x (expt y n))))
	   (not (integerp (* (/ x) a (expt y (- n))))))
  :hints (("Goal" :use (:instance not-integerp-1f
				  (y (expt y n)))))
  :rule-classes :type-prescription)

(defthm not-integerp-1g-expt-c
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(integerp n1)
		(real/rationalp y)
		(integerp n2)
		(< 0 a)
		(< a (* (expt x n1) (expt y n2))))
	   (not (integerp (* (expt x (- n1)) a (expt y (- n2))))))
  :hints (("Goal" :use (:instance not-integerp-1f
				  (x (expt x n1))
				  (y (expt y n2)))))
  :rule-classes :type-prescription)

(local (in-theory (disable not-integerp-1g
                           not-integerp-1g-expt-a
                           not-integerp-1g-expt-b
                           not-integerp-1g-expt-c)))


(defthm not-integerp-1h
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(real/rationalp y)
		(< 0 a)
		(< a (* x y)))
	   (not (integerp (* a (/ x) (/ y)))))
  :hints (("Goal" :use not-integerp-1f))
  :rule-classes :type-prescription)

(defthm not-integerp-1h-expt-a
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(integerp n)
		(real/rationalp y)
		(< 0 a)
		(< a (* (expt x n) y)))
	   (not (integerp (* a (expt x (- n)) (/ y)))))
  :hints (("Goal" :use (:instance not-integerp-1f
				  (x (expt x n)))))
  :rule-classes :type-prescription)

(defthm not-integerp-1h-expt-b
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(real/rationalp y)
		(integerp n)
		(< 0 a)
		(< a (* x (expt y n))))
	   (not (integerp (* a (/ x) (expt y (- n))))))
  :hints (("Goal" :use (:instance not-integerp-1f
				  (y (expt y n)))))
  :rule-classes :type-prescription)

(defthm not-integerp-1h-expt-c
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(integerp n1)
		(real/rationalp y)
		(integerp n2)
		(< 0 a)
		(< a (* (expt x n1) (expt y n2))))
	   (not (integerp (* a (expt x (- n1)) (expt y (- n2))))))
  :hints (("Goal" :use (:instance not-integerp-1f
				  (x (expt x n1))
				  (y (expt y n2)))))
  :rule-classes :type-prescription)

(local (in-theory (disable not-integerp-1h
                           not-integerp-1h-expt-a
                           not-integerp-1h-expt-b
                           not-integerp-1h-expt-c)))

;; (defthm not-integerp-1i
;;   (implies (and (real/rationalp a)
;;                 (real/rationalp b)
;;                 (real/rationalp c)
;; 		(real/rationalp x)
;; 		(< 0 (* a b c))
;; 		(< (* a b c) x))
;; 	   (not (integerp (* (/ x) a b c))))
;;   :rule-classes :type-prescription)

;; (defthm not-integerp-1j
;;   (implies (and (real/rationalp a)
;;                 (real/rationalp b)
;;                 (real/rationalp c)
;; 		(real/rationalp x)
;; 		(< 0 (* a b c))
;; 		(< (* a b c) x))
;; 	   (not (integerp (* a (/ x) b c))))
;;   :rule-classes :type-prescription)

(defthm not-integerp-1k
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
                (real/rationalp c)
                (real/rationalp x)
		(< 0 (* a b c))
		(< (* a b c) x))
	   (not (integerp (* a b (/ x) c))))
  :hints (("Goal" :use (:instance not-integerp-1a
				  (a (* a b c))
				  (x x))))
  :rule-classes :type-prescription)

(defthm not-integerp-1k-expt
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
                (real/rationalp c)
                (real/rationalp x)
		(integerp n)
		(< 0 (* a b c))
		(< (* a b c) (expt x n)))
	   (not (integerp (* a b (expt x (- n)) c))))
  :hints (("Goal" :use (:instance not-integerp-1a
				  (a (* a b c))
				  (x (expt x n)))))
  :rule-classes :type-prescription)

(local (in-theory (disable not-integerp-1k
                           not-integerp-1k-expt)))



(defthm not-integerp-1l
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
                ;(real/rationalp c)
		(real/rationalp x)
		(< 0 (* a b c))
		(< (* a b c) x))
	   (not (integerp (* a b c (/ x)))))
  :hints (("Goal" :use (:instance not-integerp-1a
				  (a (* a b c))
				  (x x))))
  :rule-classes :type-prescription)

(defthm not-integerp-1l-expt
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
                ;(real/rationalp c)
		(real/rationalp x)
		(integerp n)
		(< 0 (* a b c))
		(< (* a b c) (expt x n)))
	   (not (integerp (* a b c (expt x (- n))))))
  :hints (("Goal" :use (:instance not-integerp-1a
				  (a (* a b c))
				  (x (expt x n)))))
  :rule-classes :type-prescription)

(local (in-theory (disable not-integerp-1l
                           not-integerp-1l-expt)))

;; (defthm not-integerp-1m
;;   (implies (and (real/rationalp a)
;;                 (real/rationalp b)
;;                 (real/rationalp x)
;; 		(real/rationalp y)
;; 		(< 0 (* a b))
;; 		(< (* a b) (* x y)))
;; 	   (not (integerp (* (/ x) (/ y) a b))))
;;   :rule-classes :type-prescription)

(defthm not-integerp-1n
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
                (real/rationalp x)
		(real/rationalp y)
		(< 0 (* a b))
		(< (* a b) (* x y)))
	   (not (integerp (* (/ x) a (/ y) b))))
  :hints (("Goal" :use (:instance not-integerp-1a
				  (a (* a b))
				  (x (* x y)))))
  :rule-classes :type-prescription)

(defthm not-integerp-1n-expt-a
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
                (real/rationalp x)
		(integerp n)
		(real/rationalp y)
		(< 0 (* a b))
		(< (* a b) (* (expt x n) y)))
	   (not (integerp (* (expt x (- n)) a (/ y) b))))
  :hints (("Goal" :use (:instance not-integerp-1a
				  (a (* a b))
				  (x (* (expt x n) y)))))
  :rule-classes :type-prescription)

(defthm not-integerp-1n-expt-b
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
                (real/rationalp x)
		(real/rationalp y)
		(integerp n)
		(< 0 (* a b))
		(< (* a b) (* x (expt y n))))
	   (not (integerp (* (/ x) a (expt y (- n)) b))))
  :hints (("Goal" :use (:instance not-integerp-1a
				  (a (* a b))
				  (x (* x (expt y n))))))
  :rule-classes :type-prescription)

(defthm not-integerp-1n-expt-c
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
                (real/rationalp x)
		(integerp n1)
		(real/rationalp y)
		(integerp n2)
		(< 0 (* a b))
		(< (* a b) (* (expt x n1) (expt y n2))))
	   (not (integerp (* (expt x (- n1)) a (expt y (- n2)) b))))
  :hints (("Goal" :use (:instance not-integerp-1a
				  (a (* a b))
				  (x (* (expt x n1) (expt y n2))))))
  :rule-classes :type-prescription)


(local (in-theory (disable not-integerp-1n
                           not-integerp-1n-expt-a
                           not-integerp-1n-expt-b
                           not-integerp-1n-expt-c)))


(defthm not-integerp-1o
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
                (real/rationalp x)
		(real/rationalp y)
		(< 0 (* a b))
		(< (* a b) (* x y)))
	   (not (integerp (* (/ x) a b (/ y)))))
  :hints (("Goal" :use (:instance not-integerp-1a
				  (a (* a b))
				  (x (* x y)))))
  :rule-classes :type-prescription)

(defthm not-integerp-1o-expt-a
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
                (real/rationalp x)
		(integerp n)
		(real/rationalp y)
		(< 0 (* a b))
		(< (* a b) (* (expt x n) y)))
	   (not (integerp (* (expt x (- n)) a b (/ y)))))
  :hints (("Goal" :use (:instance not-integerp-1a
				  (a (* a b))
				  (x (* (expt x n) y)))))
  :rule-classes :type-prescription)

(defthm not-integerp-1o-expt-b
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
                (real/rationalp x)
		(real/rationalp y)
		(integerp n)
		(< 0 (* a b))
		(< (* a b) (* x (expt y n))))
	   (not (integerp (* (/ x) a b (expt y (- n))))))
  :hints (("Goal" :use (:instance not-integerp-1a
				  (a (* a b))
				  (x (* x (expt y n))))))
  :rule-classes :type-prescription)

(defthm not-integerp-1o-expt-c
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
                (real/rationalp x)
		(integerp n1)
		(real/rationalp y)
		(integerp n2)
		(< 0 (* a b))
		(< (* a b) (* (expt x n1) (expt y n2))))
	   (not (integerp (* (expt x (- n1)) a b (expt y (- n2))))))
  :hints (("Goal" :use (:instance not-integerp-1a
				  (a (* a b))
				  (x (* (expt x n1) (expt y n2))))))
  :rule-classes :type-prescription)

(local (in-theory (disable not-integerp-1o
                           not-integerp-1o-expt-a
                           not-integerp-1o-expt-b
                           not-integerp-1o-expt-c)))


(defthm not-integerp-1p
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
                (real/rationalp x)
		(real/rationalp y)
		(< 0 (* a b))
		(< (* a b) (* x y)))
	   (not (integerp (* a (/ x) (/ y) b))))
  :hints (("Goal" :use (:instance not-integerp-1a
				  (a (* a b))
				  (x (* x y)))))
  :rule-classes :type-prescription)

(defthm not-integerp-1p-expt-a
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
                (real/rationalp x)
		(integerp n)
		(real/rationalp y)
		(< 0 (* a b))
		(< (* a b) (* (expt x n) y)))
	   (not (integerp (* a (expt x (- n)) (/ y) b))))
  :hints (("Goal" :use (:instance not-integerp-1a
				  (a (* a b))
				  (x (* (expt x n) y)))))
  :rule-classes :type-prescription)

(defthm not-integerp-1p-expt-b
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
                (real/rationalp x)
		(real/rationalp y)
		(integerp n)
		(< 0 (* a b))
		(< (* a b) (* x (expt y n))))
	   (not (integerp (* a (/ x) (expt y (- n)) b))))
  :hints (("Goal" :use (:instance not-integerp-1a
				  (a (* a b))
				  (x (* x (expt y n))))))
  :rule-classes :type-prescription)

(defthm not-integerp-1p-expt-c
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
                (real/rationalp x)
		(integerp n1)
		(real/rationalp y)
		(integerp n2)
		(< 0 (* a b))
		(< (* a b) (* (expt x n1) (expt y n2))))
	   (not (integerp (* a (expt x (- n1)) (expt y (- n2)) b))))
  :hints (("Goal" :use (:instance not-integerp-1a
				  (a (* a b))
				  (x (* (expt x n1) (expt y n2))))))
  :rule-classes :type-prescription)

(local (in-theory (disable not-integerp-1p
                           not-integerp-1p-expt-a
                           not-integerp-1p-expt-b
                           not-integerp-1p-expt-c)))


(defthm not-integerp-1q
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
                (real/rationalp x)
		(real/rationalp y)
		(< 0 (* a b))
		(< (* a b) (* x y)))
	   (not (integerp (* a (/ x) b (/ y)))))
  :hints (("Goal" :use (:instance not-integerp-1a
				  (a (* a b))
				  (x (* x y)))))
  :rule-classes :type-prescription)

(defthm not-integerp-1q-expt-a
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
                (real/rationalp x)
		(integerp n)
		(real/rationalp y)
		(< 0 (* a b))
		(< (* a b) (* (expt x n) y)))
	   (not (integerp (* a (expt x (- n)) b (/ y)))))
  :hints (("Goal" :use (:instance not-integerp-1a
				  (a (* a b))
				  (x (* (expt x n) y)))))
  :rule-classes :type-prescription)

(defthm not-integerp-1q-expt-b
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
                (real/rationalp x)
		(real/rationalp y)
		(integerp n)
		(< 0 (* a b))
		(< (* a b) (* x (expt y n))))
	   (not (integerp (* a (/ x) b (expt y (- n))))))
  :hints (("Goal" :use (:instance not-integerp-1a
				  (a (* a b))
				  (x (* x (expt y n))))))
  :rule-classes :type-prescription)

(defthm not-integerp-1q-expt-c
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
                (real/rationalp x)
		(integerp n1)
		(real/rationalp y)
		(integerp n2)
		(< 0 (* a b))
		(< (* a b) (* (expt x n1) (expt y n2))))
	   (not (integerp (* a (expt x (- n1)) b (expt y (- n2))))))
  :hints (("Goal" :use (:instance not-integerp-1a
				  (a (* a b))
				  (x (* (expt x n1) (expt y n2))))))
  :rule-classes :type-prescription)

(local (in-theory (disable not-integerp-1q
                           not-integerp-1q-expt-a
                           not-integerp-1q-expt-b
                           not-integerp-1q-expt-c)))


(defthm not-integerp-1r
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
                (real/rationalp x)
		(real/rationalp y)
		(< 0 (* a b))
		(< (* a b) (* x y)))
	   (not (integerp (* a b (/ x) (/ y)))))
  :hints (("Goal" :use (:instance not-integerp-1a
				  (a (* a b))
				  (x (* x y)))))
  :rule-classes :type-prescription)

(defthm not-integerp-1r-expt-a
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
                (real/rationalp x)
		(integerp n)
		(real/rationalp y)
		(< 0 (* a b))
		(< (* a b) (* (expt x n) y)))
	   (not (integerp (* a b (expt x (- n)) (/ y)))))
  :hints (("Goal" :use (:instance not-integerp-1a
				  (a (* a b))
				  (x (* (expt x n) y)))))
  :rule-classes :type-prescription)

(defthm not-integerp-1r-expt-b
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
                (real/rationalp x)
		(real/rationalp y)
		(integerp n)
		(< 0 (* a b))
		(< (* a b) (* x (expt y n))))
	   (not (integerp (* a b (/ x) (expt y (- n))))))
  :hints (("Goal" :use (:instance not-integerp-1a
				  (a (* a b))
				  (x (* x (expt y n))))))
  :rule-classes :type-prescription)

(defthm not-integerp-1r-expt-c
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
                (real/rationalp x)
		(integerp n1)
		(real/rationalp y)
		(integerp n2)
		(< 0 (* a b))
		(< (* a b) (* (expt x n1) (expt y n2))))
	   (not (integerp (* a b (expt x (- n1)) (expt y (- n2))))))
  :hints (("Goal" :use (:instance not-integerp-1a
				  (a (* a b))
				  (x (* (expt x n1) (expt y n2))))))
  :rule-classes :type-prescription)

(local (in-theory (disable not-integerp-1r
                           not-integerp-1r-expt-a
                           not-integerp-1r-expt-b
                           not-integerp-1r-expt-c)))


(defthm not-integerp-1s
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
                (real/rationalp y)
		(real/rationalp z)
		(< 0 a)
		(< a (* x y z)))
	   (not (integerp (* (/ x) (/ y) (/ z) a))))
  :hints (("Goal" :use (:instance not-integerp-1a
                                  (a a)
                                  (x (* x y z)))))
  :rule-classes :type-prescription)

(defthm not-integerp-1s-expt-a
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(integerp n)
                (real/rationalp y)
		(real/rationalp z)
		(< 0 a)
		(< a (* (expt x n) y z)))
	   (not (integerp (* (expt x (- n)) (/ y) (/ z) a))))
  :hints (("Goal" :use (:instance not-integerp-1a
                                  (a a)
                                  (x (* (expt x n) y z)))))
  :rule-classes :type-prescription)

(defthm not-integerp-1s-expt-b
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
                (real/rationalp y)
		(integerp n)
		(real/rationalp z)
		(< 0 a)
		(< a (* x (expt y n) z)))
	   (not (integerp (* (/ x) (expt y (- n)) (/ z) a))))
  :hints (("Goal" :use (:instance not-integerp-1a
                                  (a a)
                                  (x (* x (expt y n) z)))))
  :rule-classes :type-prescription)

(defthm not-integerp-1s-expt-c
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
                (real/rationalp y)
		(real/rationalp z)
		(integerp n)
		(< 0 a)
		(< a (* x y (expt z n))))
	   (not (integerp (* (/ x) (/ y) (expt z (- n)) a))))
  :hints (("Goal" :use (:instance not-integerp-1a
                                  (a a)
                                  (x (* x y (expt z n))))))
  :rule-classes :type-prescription)

(defthm not-integerp-1s-expt-d
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(integerp n1)
                (real/rationalp y)
		(integerp n2)
		(real/rationalp z)
		(< 0 a)
		(< a (* (expt x n1) (expt y n2) z)))
	   (not (integerp (* (expt x (- n1)) (expt y (- n2)) (/ z) a))))
  :hints (("Goal" :use (:instance not-integerp-1a
                                  (a a)
                                  (x (* (expt x n1) (expt y n2) z)))))
  :rule-classes :type-prescription)

(defthm not-integerp-1s-expt-e
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(integerp n1)
                (real/rationalp y)
		(real/rationalp z)
		(integerp n2)
		(< 0 a)
		(< a (* (expt x n1) y (expt z n2))))
	   (not (integerp (* (expt x (- n1)) (/ y) (expt z (- n2)) a))))
  :hints (("Goal" :use (:instance not-integerp-1a
                                  (a a)
                                  (x (* (expt x n1) y (expt z n2))))))
  :rule-classes :type-prescription)

(defthm not-integerp-1s-expt-f
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
                (real/rationalp y)
		(integerp n1)
		(real/rationalp z)
		(integerp n2)
		(< 0 a)
		(< a (* x (expt y n1) (expt z n2))))
	   (not (integerp (* (/ x) (expt y (- n1)) (expt z (- n2)) a))))
  :hints (("Goal" :use (:instance not-integerp-1a
                                  (a a)
                                  (x (* x (expt y n1) (expt z n2))))))
  :rule-classes :type-prescription)

(defthm not-integerp-1s-expt-g
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(integerp n1)
                (real/rationalp y)
		(integerp n2)
		(real/rationalp z)
		(integerp n3)
		(< 0 a)
		(< a (* (expt x n1) (expt y n2) (expt z n3))))
	   (not (integerp (* (expt x (- n1)) (expt y (- n2)) (expt z (- n3)) a))))
  :hints (("Goal" :use (:instance not-integerp-1a
                                  (a a)
                                  (x (* (expt x n1) (expt y n2) (expt z n3))))))
  :rule-classes :type-prescription)


(local (in-theory (disable not-integerp-1s
                           not-integerp-1s-expt-a
                           not-integerp-1s-expt-b
                           not-integerp-1s-expt-c
                           not-integerp-1s-expt-d
                           not-integerp-1s-expt-e
                           not-integerp-1s-expt-f
                           not-integerp-1s-expt-g)))


(defthm not-integerp-1t
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
                (real/rationalp y)
		(real/rationalp z)
		(< 0 a)
		(< a (* x y z)))
	   (not (integerp (* (/ x) (/ y) a (/ z)))))
  :hints (("Goal" :use not-integerp-1s))
  :rule-classes :type-prescription)

(defthm not-integerp-1t-expt-a
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(integerp n)
                (real/rationalp y)
		(real/rationalp z)
		(< 0 a)
		(< a (* (expt x n) y z)))
	   (not (integerp (* (expt x (- n)) (/ y) a (/ z)))))
  :hints (("Goal" :use (:instance not-integerp-1s
				  (x (expt x n)))))
  :rule-classes :type-prescription)

(defthm not-integerp-1t-expt-b
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
                (real/rationalp y)
		(integerp n)
		(real/rationalp z)
		(< 0 a)
		(< a (* x (expt y n) z)))
	   (not (integerp (* (/ x) (expt y (- n)) a (/ z)))))
  :hints (("Goal" :use (:instance not-integerp-1s
				  (y (expt y n)))))
  :rule-classes :type-prescription)

(defthm not-integerp-1t-expt-c
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
                (real/rationalp y)
		(real/rationalp z)
		(integerp n)
		(< 0 a)
		(< a (* x y (expt z n))))
	   (not (integerp (* (/ x) (/ y) a (expt z (- n))))))
  :hints (("Goal" :use (:instance not-integerp-1s
				  (z (expt z n)))))
  :rule-classes :type-prescription)

(defthm not-integerp-1t-expt-d
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(integerp n1)
                (real/rationalp y)
		(integerp n2)
		(real/rationalp z)
		(< 0 a)
		(< a (* (expt x n1) (expt y n2) z)))
	   (not (integerp (* (expt x (- n1)) (expt y (- n2)) a (/ z)))))
  :hints (("Goal" :use (:instance not-integerp-1s
				  (x (expt x n1))
				  (y (expt y n2)))))
  :rule-classes :type-prescription)

(defthm not-integerp-1t-expt-e
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(integerp n1)
                (real/rationalp y)
		(real/rationalp z)
		(integerp n2)
		(< 0 a)
		(< a (* (expt x n1) y (expt z n2))))
	   (not (integerp (* (expt x (- n1)) (/ y) a (expt z (- n2))))))
  :hints (("Goal" :use (:instance not-integerp-1s
				  (x (expt x n1))
				  (z (expt z n2)))))
  :rule-classes :type-prescription)

(defthm not-integerp-1t-expt-f
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
                (real/rationalp y)
		(integerp n1)
		(real/rationalp z)
		(integerp n2)
		(< 0 a)
		(< a (* x (expt y n1) (expt z n2))))
	   (not (integerp (* (/ x) (expt y (- n1)) a (expt z (- n2))))))
  :hints (("Goal" :use (:instance not-integerp-1s
				  (y (expt y n1))
				  (z (expt z n2)))))
  :rule-classes :type-prescription)

(defthm not-integerp-1t-expt-g
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(integerp n1)
                (real/rationalp y)
		(integerp n2)
		(real/rationalp z)
		(integerp n3)
		(< 0 a)
		(< a (* (expt x n1) (expt y n2) (expt z n3))))
	   (not (integerp (* (expt x (- n1)) (expt y (- n2)) a (expt z (- n3))))))
  :hints (("Goal" :use (:instance not-integerp-1s
				  (x (expt x n1))
				  (y (expt y n2))
				  (z (expt z n3)))))
  :rule-classes :type-prescription)

(local (in-theory (disable not-integerp-1s
                           not-integerp-1s-expt-a
                           not-integerp-1s-expt-b
                           not-integerp-1s-expt-c
                           not-integerp-1s-expt-d
                           not-integerp-1s-expt-e
                           not-integerp-1s-expt-f
                           not-integerp-1s-expt-g)))

(defthm not-integerp-1u
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
                (real/rationalp y)
		(real/rationalp z)
		(< 0 a)
		(< a (* x y z)))
	   (not (integerp (* (/ x) a (/ y) (/ z)))))
  :hints (("Goal" :use (:instance not-integerp-1s
				  )))
  :rule-classes :type-prescription)

(defthm not-integerp-1u-expt-a
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(integerp n)
                (real/rationalp y)
		(real/rationalp z)
		(< 0 a)
		(< a (* (expt x n) y z)))
	   (not (integerp (* (expt x (- n)) a (/ y) (/ z)))))
  :hints (("Goal" :use (:instance not-integerp-1s
				  (x (expt x n)))))
  :rule-classes :type-prescription)

(defthm not-integerp-1u-expt-b
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
                (real/rationalp y)
		(integerp n)
		(real/rationalp z)
		(< 0 a)
		(< a (* x (expt y n) z)))
	   (not (integerp (* (/ x) a (expt y (- n)) (/ z)))))
  :hints (("Goal" :use (:instance not-integerp-1s
				  (y (expt y n)))))
  :rule-classes :type-prescription)

(defthm not-integerp-1u-expt-c
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
                (real/rationalp y)
		(real/rationalp z)
		(integerp n)
		(< 0 a)
		(< a (* x y (expt z n))))
	   (not (integerp (* (/ x) a (/ y) (expt z (- n))))))
  :hints (("Goal" :use (:instance not-integerp-1s
				  (z (expt z n)))))
  :rule-classes :type-prescription)

(defthm not-integerp-1u-expt-d
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(integerp n1)
                (real/rationalp y)
		(integerp n2)
		(real/rationalp z)
		(< 0 a)
		(< a (* (expt x n1) (expt y n2) z)))
	   (not (integerp (* (expt x (- n1)) a (expt y (- n2)) (/ z)))))
  :hints (("Goal" :use (:instance not-integerp-1s
				  (x (expt x n1))
				  (y (expt y n2)))))
  :rule-classes :type-prescription)

(defthm not-integerp-1u-expt-e
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(integerp n1)
                (real/rationalp y)
		(real/rationalp z)
		(integerp n2)
		(< 0 a)
		(< a (* (expt x n1) y (expt z n2))))
	   (not (integerp (* (expt x (- n1)) a (/ y) (expt z (- n2))))))
  :hints (("Goal" :use (:instance not-integerp-1s
				  (x (expt x n1))
				  (z (expt z n2)))))
  :rule-classes :type-prescription)

(defthm not-integerp-1u-expt-f
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
                (real/rationalp y)
		(integerp n1)
		(real/rationalp z)
		(integerp n2)
		(< 0 a)
		(< a (* x (expt y n1) (expt z n2))))
	   (not (integerp (* (/ x) a (expt y (- n1)) (expt z (- n2))))))
  :hints (("Goal" :use (:instance not-integerp-1s
				  (y (expt y n1))
				  (z (expt z n2)))))
  :rule-classes :type-prescription)

(defthm not-integerp-1u-expt-g
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(integerp n1)
                (real/rationalp y)
		(integerp n2)
		(real/rationalp z)
		(integerp n3)
		(< 0 a)
		(< a (* (expt x n1) (expt y n2) (expt z n3))))
	   (not (integerp (* (expt x (- n1)) a (expt y (- n2)) (expt z (- n3))))))
  :hints (("Goal" :use (:instance not-integerp-1s
				  (x (expt x n1))
				  (y (expt y n2))
				  (z (expt z n3)))))
  :rule-classes :type-prescription)

(local (in-theory (disable not-integerp-1u
                           not-integerp-1u-expt-a
                           not-integerp-1u-expt-b
                           not-integerp-1u-expt-c
                           not-integerp-1u-expt-d
                           not-integerp-1u-expt-e
                           not-integerp-1u-expt-f
                           not-integerp-1u-expt-g)))



(defthm not-integerp-1v
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
                (real/rationalp y)
		(real/rationalp z)
		(< 0 a)
		(< a (* x y z)))
	   (not (integerp (* a (/ x) (/ y) (/ z)))))
  :hints (("Goal" :use (:instance not-integerp-1s
				  )))
  :rule-classes :type-prescription)

(defthm not-integerp-1v-expt-a
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(integerp n)
                (real/rationalp y)
		(real/rationalp z)
		(< 0 a)
		(< a (* (expt x n) y z)))
	   (not (integerp (* a (expt x (- n)) (/ y) (/ z)))))
  :hints (("Goal" :use (:instance not-integerp-1s
				  (x (expt x n)))))
  :rule-classes :type-prescription)

(defthm not-integerp-1v-expt-b
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
                (real/rationalp y)
		(integerp n)
		(real/rationalp z)
		(< 0 a)
		(< a (* x (expt y n) z)))
	   (not (integerp (* a (/ x) (expt y (- n)) (/ z)))))
  :hints (("Goal" :use (:instance not-integerp-1s
				  (y (expt y n)))))
  :rule-classes :type-prescription)

(defthm not-integerp-1v-expt-c
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
                (real/rationalp y)
		(real/rationalp z)
		(integerp n)
		(< 0 a)
		(< a (* x y (expt z n))))
	   (not (integerp (* a (/ x) (/ y) (expt z (- n))))))
  :hints (("Goal" :use (:instance not-integerp-1s
				  (z (expt z n)))))
  :rule-classes :type-prescription)

(defthm not-integerp-1v-expt-d
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(integerp n1)
                (real/rationalp y)
		(integerp n2)
		(real/rationalp z)
		(< 0 a)
		(< a (* (expt x n1) (expt y n2) z)))
	   (not (integerp (* a (expt x (- n1)) (expt y (- n2)) (/ z)))))
  :hints (("Goal" :use (:instance not-integerp-1s
				  (x (expt x n1))
				  (y (expt y n2)))))
  :rule-classes :type-prescription)

(defthm not-integerp-1v-expt-e
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(integerp n1)
                (real/rationalp y)
		(real/rationalp z)
		(integerp n2)
		(< 0 a)
		(< a (* (expt x n1) y (expt z n2))))
	   (not (integerp (* a (expt x (- n1)) (/ y) (expt z (- n2))))))
  :hints (("Goal" :use (:instance not-integerp-1s
				  (x (expt x n1))
				  (z (expt z n2)))))
  :rule-classes :type-prescription)

(defthm not-integerp-1v-expt-f
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
                (real/rationalp y)
		(integerp n1)
		(real/rationalp z)
		(integerp n2)
		(< 0 a)
		(< a (* x (expt y n1) (expt z n2))))
	   (not (integerp (* a (/ x) (expt y (- n1)) (expt z (- n2))))))
  :hints (("Goal" :use (:instance not-integerp-1s
				  (y (expt y n1))
				  (z (expt z n2)))))
  :rule-classes :type-prescription)

(defthm not-integerp-1v-expt-g
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(integerp n1)
                (real/rationalp y)
		(integerp n2)
		(real/rationalp z)
		(integerp n3)
		(< 0 a)
		(< a (* (expt x n1) (expt y n2) (expt z n3))))
	   (not (integerp (* a (expt x (- n1)) (expt y (- n2)) (expt z (- n3))))))
  :hints (("Goal" :use (:instance not-integerp-1s
				  (x (expt x n1))
				  (y (expt y n2))
				  (z (expt z n3)))))
  :rule-classes :type-prescription)

(local (in-theory (disable not-integerp-1v
                           not-integerp-1v-expt-a
                           not-integerp-1v-expt-b
                           not-integerp-1v-expt-c
                           not-integerp-1v-expt-d
                           not-integerp-1v-expt-e
                           not-integerp-1v-expt-f
                           not-integerp-1v-expt-g)))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm not-integerp-2a
  (implies (and ;(real/rationalp a)
	        (real/rationalp x)
		(< a 0)
		(< x a))
	   (not (integerp (* (/ x) a))))
  :hints (("Goal" :use (:instance not-integerp-1a
				  (a (- a))
				  (x (- x)))))
  :rule-classes :type-prescription)

(defthm not-integerp-2a-expt
  (implies (and	;(real/rationalp a)
	        (real/rationalp x)
		(integerp n)
		(< a 0)
		(< (expt x n) a))
	   (not (integerp (* (expt x (- n)) a))))
  :hints (("Goal" :use (:instance not-integerp-2a
				  (x (expt x n)))))
  :rule-classes :type-prescription)

(local (in-theory (disable not-integerp-2a
                           not-integerp-2a-expt)))

(defthm not-integerp-2b
  (implies (and ;(real/rationalp a)
		(real/rationalp x)
		(< a 0)
		(< x a))
	   (not (integerp (* a (/ x)))))
  :hints (("Goal" :use not-integerp-2a))
  :rule-classes :type-prescription)

(defthm not-integerp-2b-expt
  (implies (and ;(real/rationalp a)
		(real/rationalp x)
		(integerp n)
		(< a 0)
		(< (expt x n) a))
	   (not (integerp (* a (expt x (- n))))))
  :hints (("Goal" :use (:instance not-integerp-2a
				  (x (expt x n)))))
  :rule-classes :type-prescription)

(local (in-theory (disable not-integerp-2b
                           not-integerp-2b-expt)))


;; (defthm not-integerp-2c
;;   (implies (and (real/rationalp a)
;;                 (real/rationalp b)
;; 		(real/rationalp x)
;; 		(< (* a b) 0)
;; 		(< x (* a b)))
;; 	   (not (integerp (* (/ x) a b))))
;;   :rule-classes :type-prescription)

(defthm not-integerp-2d
  (implies (and ;(real/rationalp a)
                (real/rationalp b)
		(real/rationalp x)
		(< (* a b) 0)
		(< x (* a b)))
	   (not (integerp (* a (/ x) b))))
  :hints (("Goal" :use (:instance not-integerp-2a
				  (a (* a b))
				  (x x))))
  :rule-classes :type-prescription)

(defthm not-integerp-2d-expt
  (implies (and ;(real/rationalp a)
                (real/rationalp b)
		(real/rationalp x)
		(integerp n)
		(< (* a b) 0)
		(< (expt x n) (* a b)))
	   (not (integerp (* a (expt x (- n)) b))))
  :hints (("Goal" :use (:instance not-integerp-2a
				  (a (* a b))
				  (x (expt x n)))))
  :rule-classes :type-prescription)

(local (in-theory (disable not-integerp-2d
                           not-integerp-2d-expt)))


(defthm not-integerp-2e
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
		(real/rationalp x)
		(< (* a b) 0)
		(< x (* a b)))
	   (not (integerp (* a b (/ x)))))
  :hints (("Goal" :use (:instance not-integerp-2a
				  (a (* a b))
				  (x x))))
  :rule-classes :type-prescription)

(defthm not-integerp-2e-expt
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
		(real/rationalp x)
		(integerp n)
		(< (* a b) 0)
		(< (expt x n) (* a b)))
	   (not (integerp (* a b (expt x (- n))))))
  :hints (("Goal" :use (:instance not-integerp-2a
				  (a (* a b))
				  (x (expt x n)))))
  :rule-classes :type-prescription)

(local (in-theory (disable not-integerp-2e
                           not-integerp-2e-expt)))


(defthm not-integerp-2f
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(real/rationalp y)
		(< a 0)
		(< (* x y) a))
	   (not (integerp (* (/ x) (/ y) a))))
  :hints (("Goal" :use (:instance not-integerp-2a
                                  (a a)
                                  (x (* x y)))))
  :rule-classes :type-prescription)

(defthm not-integerp-2f-expt-a
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(integerp n)
		(real/rationalp y)
		(< a 0)
		(< (* (expt x n) y) a))
	   (not (integerp (* (expt x (- n)) (/ y) a))))
  :hints (("Goal" :use (:instance not-integerp-2a
                                  (a a)
                                  (x (* (expt x n) y)))))
  :rule-classes :type-prescription)

(defthm not-integerp-2f-expt-b
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(real/rationalp y)
		(integerp n)
		(< a 0)
		(< (* x (expt y n)) a))
	   (not (integerp (* (/ x) (expt y (- n)) a))))
  :hints (("Goal" :use (:instance not-integerp-2a
                                  (a a)
                                  (x (* (expt y n) x)))))
  :rule-classes :type-prescription)

(defthm not-integerp-2f-expt-c
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(integerp n1)
		(real/rationalp y)
		(integerp n2)
		(< a 0)
		(< (* (expt x n1) (expt y n2)) a))
	   (not (integerp (* (expt x (- n1)) (expt y (- n2)) a))))
  :hints (("Goal" :use (:instance not-integerp-2a
                                  (a a)
                                  (x (* (expt x n1) (expt y n2))))))
  :rule-classes :type-prescription)

(local (in-theory (disable not-integerp-2f
                           not-integerp-2f-expt-a
                           not-integerp-2f-expt-b
                           not-integerp-2f-expt-c)))


(defthm not-integerp-2g
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(real/rationalp y)
		(< a 0)
		(< (* x y) a))
	   (not (integerp (* (/ x) a (/ y)))))
  :hints (("Goal" :use not-integerp-2f))
  :rule-classes :type-prescription)

(defthm not-integerp-2g-expt-a
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(integerp n)
		(real/rationalp y)
		(< a 0)
		(< (* (expt x n) y) a))
	   (not (integerp (* (expt x (- n)) a (/ y)))))
  :hints (("Goal" :use (:instance not-integerp-2f
				  (x (expt x n)))))
  :rule-classes :type-prescription)

(defthm not-integerp-2g-expt-b
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(real/rationalp y)
		(integerp n)
		(< a 0)
		(< (* x (expt y n)) a))
	   (not (integerp (* (/ x) a (expt y (- n))))))
  :hints (("Goal" :use (:instance not-integerp-2f
				  (y (expt y n)))))
  :rule-classes :type-prescription)

(defthm not-integerp-2g-expt-c
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(integerp n1)
		(real/rationalp y)
		(integerp n2)
		(< a 0)
		(< (* (expt x n1) (expt y n2)) a))
	   (not (integerp (* (expt x (- n1)) a (expt y (- n2))))))
  :hints (("Goal" :use (:instance not-integerp-2f
				  (x (expt x n1))
				  (y (expt y n2)))))
  :rule-classes :type-prescription)

(local (in-theory (disable not-integerp-2g
                           not-integerp-2g-expt-a
                           not-integerp-2g-expt-b
                           not-integerp-2g-expt-c)))


(defthm not-integerp-2h
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(real/rationalp y)
		(< a 0)
		(< (* x y) a))
	   (not (integerp (* a (/ x) (/ y)))))
  :hints (("Goal" :use not-integerp-2f))
  :rule-classes :type-prescription)

(defthm not-integerp-2h-expt-a
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(integerp n)
		(real/rationalp y)
		(< a 0)
		(< (* (expt x n) y) a))
	   (not (integerp (* a (expt x (- n)) (/ y)))))
  :hints (("Goal" :use (:instance not-integerp-2f
				  (x (expt x n)))))
  :rule-classes :type-prescription)

(defthm not-integerp-2h-expt-b
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(real/rationalp y)
		(integerp n)
		(< a 0)
		(< (* x (expt y n)) a))
	   (not (integerp (* a (/ x) (expt y (- n))))))
  :hints (("Goal" :use (:instance not-integerp-2f
				  (y (expt y n)))))
  :rule-classes :type-prescription)

(defthm not-integerp-2h-expt-c
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(integerp n1)
		(real/rationalp y)
		(integerp n2)
		(< a 0)
		(< (* (expt x n1) (expt y n2)) a))
	   (not (integerp (* a (expt x (- n1)) (expt y (- n2))))))
  :hints (("Goal" :use (:instance not-integerp-2f
				  (x (expt x n1))
				  (y (expt y n2)))))
  :rule-classes :type-prescription)

(local (in-theory (disable not-integerp-2h
                           not-integerp-2h-expt-a
                           not-integerp-2h-expt-b
                           not-integerp-2h-expt-c)))


;; (defthm not-integerp-2i
;;   (implies (and (real/rationalp a)
;;                 (real/rationalp b)
;;                 (real/rationalp c)
;; 		(real/rationalp x)
;; 		(< (* a b c) 0)
;; 		(< x (* a b c)))
;; 	   (not (integerp (* (/ x) a b c))))
;;   :rule-classes :type-prescription)

;; (defthm not-integerp-2j
;;   (implies (and (real/rationalp a)
;;                 (real/rationalp b)
;;                 (real/rationalp c)
;; 		(real/rationalp x)
;; 		(< (* a b c) 0)
;; 		(< x (* a b c)))
;; 	   (not (integerp (* a (/ x) b c))))
;;   :rule-classes :type-prescription)

(defthm not-integerp-2k
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
                (real/rationalp c)
                (real/rationalp x)
		(< (* a b c) 0)
		(< x (* a b c)))
	   (not (integerp (* a b (/ x) c))))
  :hints (("Goal" :use (:instance not-integerp-2a
				  (a (* a b c))
				  (x x))))
  :rule-classes :type-prescription)

(defthm not-integerp-2k-expt
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
                (real/rationalp c)
                (real/rationalp x)
		(integerp n)
		(< (* a b c) 0)
		(< (expt x n) (* a b c)))
	   (not (integerp (* a b (expt x (- n)) c))))
  :hints (("Goal" :use (:instance not-integerp-2a
				  (a (* a b c))
				  (x (expt x n)))))
  :rule-classes :type-prescription)

(local (in-theory (disable not-integerp-2k
                           not-integerp-2k-expt)))


(defthm not-integerp-2l
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
                ;(real/rationalp c)
		(real/rationalp x)
		(< (* a b c) 0)
		(< x (* a b c)))
	   (not (integerp (* a b c (/ x)))))
  :hints (("Goal" :use (:instance not-integerp-2a
				  (a (* a b c))
				  (x x))))
  :rule-classes :type-prescription)

(defthm not-integerp-2l-expt
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
                ;(real/rationalp c)
		(real/rationalp x)
		(integerp n)
		(< (* a b c) 0)
		(< (expt x n) (* a b c)))
	   (not (integerp (* a b c (expt x (- n))))))
  :hints (("Goal" :use (:instance not-integerp-2a
				  (a (* a b c))
				  (x (expt x n)))))
  :rule-classes :type-prescription)

(local (in-theory (disable not-integerp-2l
                           not-integerp-2l-expt)))

;; (defthm not-integerp-2m
;;   (implies (and (real/rationalp a)
;;                 (real/rationalp b)
;;                 (real/rationalp x)
;; 		(real/rationalp y)
;; 		(< (* a b) 0)
;; 		(< (* x y) (* a b)))
;; 	   (not (integerp (* (/ x) (/ y) a b))))
;;   :rule-classes :type-prescription)

(defthm not-integerp-2n
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
                (real/rationalp x)
		(real/rationalp y)
		(< (* a b) 0)
		(< (* x y) (* a b)))
	   (not (integerp (* (/ x) a (/ y) b))))
  :hints (("Goal" :use (:instance not-integerp-2a
				  (a (* a b))
				  (x (* x y)))))
  :rule-classes :type-prescription)

(defthm not-integerp-2n-expt-a
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
                (real/rationalp x)
		(integerp n)
		(real/rationalp y)
		(< (* a b) 0)
		(< (* (expt x n) y) (* a b)))
	   (not (integerp (* (expt x (- n)) a (/ y) b))))
  :hints (("Goal" :use (:instance not-integerp-2a
				  (a (* a b))
				  (x (* (expt x n) y)))))
  :rule-classes :type-prescription)

(defthm not-integerp-2n-expt-b
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
                (real/rationalp x)
		(real/rationalp y)
		(integerp n)
		(< (* a b) 0)
		(< (* x (expt y n)) (* a b)))
	   (not (integerp (* (/ x) a (expt y (- n)) b))))
  :hints (("Goal" :use (:instance not-integerp-2a
				  (a (* a b))
				  (x (* x (expt y n))))))
  :rule-classes :type-prescription)

(defthm not-integerp-2n-expt-c
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
                (real/rationalp x)
		(integerp n1)
		(real/rationalp y)
		(integerp n2)
		(< (* a b) 0)
		(< (* (expt x n1) (expt y n2)) (* a b)))
	   (not (integerp (* (expt x (- n1)) a (expt y (- n2)) b))))
  :hints (("Goal" :use (:instance not-integerp-2a
				  (a (* a b))
				  (x (* (expt x n1) (expt y n2))))))
  :rule-classes :type-prescription)

(local (in-theory (disable not-integerp-2n
                           not-integerp-2n-expt-a
                           not-integerp-2n-expt-b
                           not-integerp-2n-expt-c)))


(defthm not-integerp-2o
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
                (real/rationalp x)
		(real/rationalp y)
		(< (* a b) 0)
		(< (* x y) (* a b)))
	   (not (integerp (* (/ x) a b (/ y)))))
  :hints (("Goal" :use (:instance not-integerp-2a
				  (a (* a b))
				  (x (* x y)))))
  :rule-classes :type-prescription)

(defthm not-integerp-2o-expt-a
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
                (real/rationalp x)
		(integerp n)
		(real/rationalp y)
		(< (* a b) 0)
		(< (* (expt x n) y) (* a b)))
	   (not (integerp (* (expt x (- n)) a b (/ y)))))
  :hints (("Goal" :use (:instance not-integerp-2a
				  (a (* a b))
				  (x (* (expt x n) y)))))
  :rule-classes :type-prescription)

(defthm not-integerp-2o-expt-b
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
                (real/rationalp x)
		(real/rationalp y)
		(integerp n)
		(< (* a b) 0)
		(< (* x (expt y n)) (* a b)))
	   (not (integerp (* (/ x) a b (expt y (- n))))))
  :hints (("Goal" :use (:instance not-integerp-2a
				  (a (* a b))
				  (x (* x (expt y n))))))
  :rule-classes :type-prescription)

(defthm not-integerp-2o-expt-c
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
                (real/rationalp x)
		(integerp n1)
		(real/rationalp y)
		(integerp n2)
		(< (* a b) 0)
		(< (* (expt x n1) (expt y n2)) (* a b)))
	   (not (integerp (* (expt x (- n1)) a b (expt y (- n2))))))
  :hints (("Goal" :use (:instance not-integerp-2a
				  (a (* a b))
				  (x (* (expt x n1) (expt y n2))))))
  :rule-classes :type-prescription)

(local (in-theory (disable not-integerp-2o
                           not-integerp-2o-expt-a
                           not-integerp-2o-expt-b
                           not-integerp-2o-expt-c)))


(defthm not-integerp-2p
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
                (real/rationalp x)
		(real/rationalp y)
		(< (* a b) 0)
		(< (* x y) (* a b)))
	   (not (integerp (* a (/ x) (/ y) b))))
  :hints (("Goal" :use (:instance not-integerp-2a
				  (a (* a b))
				  (x (* x y)))))
  :rule-classes :type-prescription)

(defthm not-integerp-2p-expt-a
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
                (real/rationalp x)
		(integerp n)
		(real/rationalp y)
		(< (* a b) 0)
		(< (* (expt x n) y) (* a b)))
	   (not (integerp (* a (expt x (- n)) (/ y) b))))
  :hints (("Goal" :use (:instance not-integerp-2a
				  (a (* a b))
				  (x (* (expt x n) y)))))
  :rule-classes :type-prescription)

(defthm not-integerp-2p-expt-b
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
                (real/rationalp x)
		(real/rationalp y)
		(integerp n)
		(< (* a b) 0)
		(< (* x (expt y n)) (* a b)))
	   (not (integerp (* a (/ x) (expt y (- n)) b))))
  :hints (("Goal" :use (:instance not-integerp-2a
				  (a (* a b))
				  (x (* x (expt y n))))))
  :rule-classes :type-prescription)

(defthm not-integerp-2p-expt-c
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
                (real/rationalp x)
		(integerp n1)
		(real/rationalp y)
		(integerp n2)
		(< (* a b) 0)
		(< (* (expt x n1) (expt y n2)) (* a b)))
	   (not (integerp (* a (expt x (- n1)) (expt y (- n2)) b))))
  :hints (("Goal" :use (:instance not-integerp-2a
				  (a (* a b))
				  (x (* (expt x n1) (expt y n2))))))
  :rule-classes :type-prescription)

(local (in-theory (disable not-integerp-2p
                           not-integerp-2p-expt-a
                           not-integerp-2p-expt-b
                           not-integerp-2p-expt-c)))



(defthm not-integerp-2q
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
                (real/rationalp x)
		(real/rationalp y)
		(< (* a b) 0)
		(< (* x y) (* a b)))
	   (not (integerp (* a (/ x) b (/ y)))))
  :hints (("Goal" :use (:instance not-integerp-2a
				  (a (* a b))
				  (x (* x y)))))
  :rule-classes :type-prescription)

(defthm not-integerp-2q-expt-a
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
                (real/rationalp x)
		(integerp n)
		(real/rationalp y)
		(< (* a b) 0)
		(< (* (expt x n) y) (* a b)))
	   (not (integerp (* a (expt x (- n)) b (/ y)))))
  :hints (("Goal" :use (:instance not-integerp-2a
				  (a (* a b))
				  (x (* (expt x n) y)))))
  :rule-classes :type-prescription)

(defthm not-integerp-2q-expt-b
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
                (real/rationalp x)
		(real/rationalp y)
		(integerp n)
		(< (* a b) 0)
		(< (* x (expt y n)) (* a b)))
	   (not (integerp (* a (/ x) b (expt y (- n))))))
  :hints (("Goal" :use (:instance not-integerp-2a
				  (a (* a b))
				  (x (* x (expt y n))))))
  :rule-classes :type-prescription)

(defthm not-integerp-2q-expt-c
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
                (real/rationalp x)
		(integerp n1)
		(real/rationalp y)
		(integerp n2)
		(< (* a b) 0)
		(< (* (expt x n1) (expt y n2)) (* a b)))
	   (not (integerp (* a (expt x (- n1)) b (expt y (- n2))))))
  :hints (("Goal" :use (:instance not-integerp-2a
				  (a (* a b))
				  (x (* (expt x n1) (expt y n2))))))
  :rule-classes :type-prescription)

(local (in-theory (disable not-integerp-2q
                           not-integerp-2q-expt-a
                           not-integerp-2q-expt-b
                           not-integerp-2q-expt-c)))


(defthm not-integerp-2r
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
                (real/rationalp x)
		(real/rationalp y)
		(< (* a b) 0)
		(< (* x y) (* a b)))
	   (not (integerp (* a b (/ x) (/ y)))))
  :hints (("Goal" :use (:instance not-integerp-2a
				  (a (* a b))
				  (x (* x y)))))
  :rule-classes :type-prescription)

(defthm not-integerp-2r-expt-a
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
                (real/rationalp x)
		(integerp n)
		(real/rationalp y)
		(< (* a b) 0)
		(< (* (expt x n) y) (* a b)))
	   (not (integerp (* a b (expt x (- n)) (/ y)))))
  :hints (("Goal" :use (:instance not-integerp-2a
				  (a (* a b))
				  (x (* (expt x n) y)))))
  :rule-classes :type-prescription)

(defthm not-integerp-2r-expt-b
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
                (real/rationalp x)
		(real/rationalp y)
		(integerp n)
		(< (* a b) 0)
		(< (* x (expt y n)) (* a b)))
	   (not (integerp (* a b (/ x) (expt y (- n))))))
  :hints (("Goal" :use (:instance not-integerp-2a
				  (a (* a b))
				  (x (* x (expt y n))))))
  :rule-classes :type-prescription)

(defthm not-integerp-2r-expt-c
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
                (real/rationalp x)
		(integerp n1)
		(real/rationalp y)
		(integerp n2)
		(< (* a b) 0)
		(< (* (expt x n1) (expt y n2)) (* a b)))
	   (not (integerp (* a b (expt x (- n1)) (expt y (- n2))))))
  :hints (("Goal" :use (:instance not-integerp-2a
				  (a (* a b))
				  (x (* (expt x n1) (expt y n2))))))
  :rule-classes :type-prescription)

(local (in-theory (disable not-integerp-2r
                           not-integerp-2r-expt-a
                           not-integerp-2r-expt-b
                           not-integerp-2r-expt-c)))


(defthm not-integerp-2s
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
                (real/rationalp y)
		(real/rationalp z)
		(< a 0)
		(< (* x y z) a))
	   (not (integerp (* (/ x) (/ y) (/ z) a))))
  :hints (("Goal" :use (:instance not-integerp-2a
                                  (a a)
                                  (x (* x y z)))))
  :rule-classes :type-prescription)

(defthm not-integerp-2s-expt-a
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(integerp n)
                (real/rationalp y)
		(real/rationalp z)
		(< a 0)
		(< (* (expt x n) y z) a))
	   (not (integerp (* (expt x (- n)) (/ y) (/ z) a))))
  :hints (("Goal" :use (:instance not-integerp-2a
                                  (a a)
                                  (x (* (expt x n) y z)))))
  :rule-classes :type-prescription)

(defthm not-integerp-2s-expt-b
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
                (real/rationalp y)
		(integerp n)
		(real/rationalp z)
		(< a 0)
		(< (* x (expt y n) z) a))
	   (not (integerp (* (/ x) (expt y (- n)) (/ z) a))))
  :hints (("Goal" :use (:instance not-integerp-2a
                                  (a a)
                                  (x (* x (expt y n) z)))))
  :rule-classes :type-prescription)

(defthm not-integerp-2s-expt-c
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
                (real/rationalp y)
		(real/rationalp z)
		(integerp n)
		(< a 0)
		(< (* x y (expt z n)) a))
	   (not (integerp (* (/ x) (/ y) (expt z (- n)) a))))
  :hints (("Goal" :use (:instance not-integerp-2a
                                  (a a)
                                  (x (* x y (expt z n))))))
  :rule-classes :type-prescription)

(defthm not-integerp-2s-expt-d
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(integerp n1)
                (real/rationalp y)
		(integerp n2)
		(real/rationalp z)
		(< a 0)
		(< (* (expt x n1) (expt y n2) z) a))
	   (not (integerp (* (expt x (- n1)) (expt y (- n2)) (/ z) a))))
  :hints (("Goal" :use (:instance not-integerp-2a
                                  (a a)
                                  (x (* (expt x n1) (expt y n2) z)))))
  :rule-classes :type-prescription)

(defthm not-integerp-2s-expt-e
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(integerp n1)
                (real/rationalp y)
		(real/rationalp z)
		(integerp n2)
		(< a 0)
		(< (* (expt x n1) y (expt z n2)) a))
	   (not (integerp (* (expt x (- n1)) (/ y) (expt z (- n2)) a))))
  :hints (("Goal" :use (:instance not-integerp-2a
                                  (a a)
                                  (x (* (expt x n1) y (expt z n2))))))
  :rule-classes :type-prescription)

(defthm not-integerp-2s-expt-f
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
                (real/rationalp y)
		(integerp n1)
		(real/rationalp z)
		(integerp n2)
		(< a 0)
		(< (* x (expt y n1) (expt z n2)) a))
	   (not (integerp (* (/ x) (expt y (- n1)) (expt z (- n2)) a))))
  :hints (("Goal" :use (:instance not-integerp-2a
                                  (a a)
                                  (x (* x (expt y n1) (expt z n2))))))
  :rule-classes :type-prescription)

(defthm not-integerp-2s-expt-g
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(integerp n1)
                (real/rationalp y)
		(integerp n2)
		(real/rationalp z)
		(integerp n3)
		(< a 0)
		(< (* (expt x n1) (expt y n2) (expt z n3)) a))
	   (not (integerp (* (expt x (- n1)) (expt y (- n2)) (expt z (- n3)) a))))
  :hints (("Goal" :use (:instance not-integerp-2a
                                  (a a)
                                  (x (* (expt x n1) (expt y n2) (expt z n3))))))
  :rule-classes :type-prescription)

(local (in-theory (disable not-integerp-2s
                           not-integerp-2s-expt-a
                           not-integerp-2s-expt-b
                           not-integerp-2s-expt-c
                           not-integerp-2s-expt-d
                           not-integerp-2s-expt-e
                           not-integerp-2s-expt-f
                           not-integerp-2s-expt-g)))


(defthm not-integerp-2t
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
                (real/rationalp y)
		(real/rationalp z)
		(< a 0)
		(< (* x y z) a))
	   (not (integerp (* (/ x) (/ y) a (/ z)))))
  :hints (("Goal" :use not-integerp-2s))
  :rule-classes :type-prescription)

(defthm not-integerp-2t-expt-a
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(integerp n)
                (real/rationalp y)
		(real/rationalp z)
		(< a 0)
		(< (* (expt x n) y z) a))
	   (not (integerp (* (expt x (- n)) (/ y) a (/ z)))))
  :hints (("Goal" :use (:instance not-integerp-2s
				  (x (expt x n)))))
  :rule-classes :type-prescription)

(defthm not-integerp-2t-expt-b
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
                (real/rationalp y)
		(integerp n)
		(real/rationalp z)
		(< a 0)
		(< (* x (expt y n) z) a))
	   (not (integerp (* (/ x) (expt y (- n)) a (/ z)))))
  :hints (("Goal" :use (:instance not-integerp-2s
				  (y (expt y n)))))
  :rule-classes :type-prescription)

(defthm not-integerp-2t-expt-c
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
                (real/rationalp y)
		(real/rationalp z)
		(integerp n)
		(< a 0)
		(< (* x y (expt z n)) a))
	   (not (integerp (* (/ x) (/ y) a (expt z (- n))))))
  :hints (("Goal" :use (:instance not-integerp-2s
				  (z (expt z n)))))
  :rule-classes :type-prescription)

(defthm not-integerp-2t-expt-d
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(integerp n1)
                (real/rationalp y)
		(integerp n2)
		(real/rationalp z)
		(< a 0)
		(< (* (expt x n1) (expt y n2) z) a))
	   (not (integerp (* (expt x (- n1)) (expt y (- n2)) a (/ z)))))
  :hints (("Goal" :use (:instance not-integerp-2s
				  (x (expt x n1))
				  (y (expt y n2)))))
  :rule-classes :type-prescription)

(defthm not-integerp-2t-expt-e
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(integerp n1)
                (real/rationalp y)
		(real/rationalp z)
		(integerp n2)
		(< a 0)
		(< (* (expt x n1) y (expt z n2)) a))
	   (not (integerp (* (expt x (- n1)) (/ y) a (expt z (- n2))))))
  :hints (("Goal" :use (:instance not-integerp-2s
				  (x (expt x n1))
				  (z (expt z n2)))))
  :rule-classes :type-prescription)

(defthm not-integerp-2t-expt-f
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
                (real/rationalp y)
		(integerp n1)
		(real/rationalp z)
		(integerp n2)
		(< a 0)
		(< (* x (expt y n1) (expt z n2)) a))
	   (not (integerp (* (/ x) (expt y (- n1)) a (expt z (- n2))))))
  :hints (("Goal" :use (:instance not-integerp-2s
				  (y (expt y n1))
				  (z (expt z n2)))))
  :rule-classes :type-prescription)

(defthm not-integerp-2t-expt-g
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(integerp n1)
                (real/rationalp y)
		(integerp n2)
		(real/rationalp z)
		(integerp n3)
		(< a 0)
		(< (* (expt x n1) (expt y n2) (expt z n3)) a))
	   (not (integerp (* (expt x (- n1)) (expt y (- n2)) a (expt z (- n3))))))
  :hints (("Goal" :use (:instance not-integerp-2s
				  (x (expt x n1))
				  (y (expt y n2))
				  (z (expt z n3)))))
  :rule-classes :type-prescription)

(local (in-theory (disable not-integerp-2t
                           not-integerp-2t-expt-a
                           not-integerp-2t-expt-b
                           not-integerp-2t-expt-c
                           not-integerp-2t-expt-d
                           not-integerp-2t-expt-e
                           not-integerp-2t-expt-f
                           not-integerp-2t-expt-g)))


(defthm not-integerp-2u
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
                (real/rationalp y)
		(real/rationalp z)
		(< a 0)
		(< (* x y z) a))
	   (not (integerp (* (/ x) a (/ y) (/ z)))))
  :hints (("Goal" :use (:instance not-integerp-2s
				  )))
  :rule-classes :type-prescription)

(defthm not-integerp-2u-expt-a
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(integerp n)
                (real/rationalp y)
		(real/rationalp z)
		(< a 0)
		(< (* (expt x n) y z) a))
	   (not (integerp (* (expt x (- n)) a (/ y) (/ z)))))
  :hints (("Goal" :use (:instance not-integerp-2s
				  (x (expt x n)))))
  :rule-classes :type-prescription)

(defthm not-integerp-2u-expt-b
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
                (real/rationalp y)
		(integerp n)
		(real/rationalp z)
		(< a 0)
		(< (* x (expt y n) z) a))
	   (not (integerp (* (/ x) a (expt y (- n)) (/ z)))))
  :hints (("Goal" :use (:instance not-integerp-2s
				  (y (expt y n)))))
  :rule-classes :type-prescription)

(defthm not-integerp-2u-expt-c
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
                (real/rationalp y)
		(real/rationalp z)
		(integerp n)
		(< a 0)
		(< (* x y (expt z n)) a))
	   (not (integerp (* (/ x) a (/ y) (expt z (- n))))))
  :hints (("Goal" :use (:instance not-integerp-2s
				  (z (expt z n)))))
  :rule-classes :type-prescription)

(defthm not-integerp-2u-expt-d
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(integerp n1)
                (real/rationalp y)
		(integerp n2)
		(real/rationalp z)
		(< a 0)
		(< (* (expt x n1) (expt y n2) z) a))
	   (not (integerp (* (expt x (- n1)) a (expt y (- n2)) (/ z)))))
  :hints (("Goal" :use (:instance not-integerp-2s
				  (x (expt x n1))
				  (y (expt y n2)))))
  :rule-classes :type-prescription)

(defthm not-integerp-2u-expt-e
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(integerp n1)
                (real/rationalp y)
		(real/rationalp z)
		(integerp n2)
		(< a 0)
		(< (* (expt x n1) y (expt z n2)) a))
	   (not (integerp (* (expt x (- n1)) a (/ y) (expt z (- n2))))))
  :hints (("Goal" :use (:instance not-integerp-2s
				  (x (expt x n1))
				  (z (expt z n2)))))
  :rule-classes :type-prescription)

(defthm not-integerp-2u-expt-f
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
                (real/rationalp y)
		(integerp n1)
		(real/rationalp z)
		(integerp n2)
		(< a 0)
		(< (* x (expt y n1) (expt z n2)) a))
	   (not (integerp (* (/ x) a (expt y (- n1)) (expt z (- n2))))))
  :hints (("Goal" :use (:instance not-integerp-2s
				  (y (expt y n1))
				  (z (expt z n2)))))
  :rule-classes :type-prescription)

(defthm not-integerp-2u-expt-g
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(integerp n1)
                (real/rationalp y)
		(integerp n2)
		(real/rationalp z)
		(integerp n3)
		(< a 0)
		(< (* (expt x n1) (expt y n2) (expt z n3)) a))
	   (not (integerp (* (expt x (- n1)) a (expt y (- n2)) (expt z (- n3))))))
  :hints (("Goal" :use (:instance not-integerp-2s
				  (x (expt x n1))
				  (y (expt y n2))
				  (z (expt z n3)))))
  :rule-classes :type-prescription)

(local (in-theory (disable not-integerp-2u
                           not-integerp-2u-expt-a
                           not-integerp-2u-expt-b
                           not-integerp-2u-expt-c
                           not-integerp-2u-expt-d
                           not-integerp-2u-expt-e
                           not-integerp-2u-expt-f
                           not-integerp-2u-expt-g)))


(defthm not-integerp-2v
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
                (real/rationalp y)
		(real/rationalp z)
		(< a 0)
		(< (* x y z) a))
	   (not (integerp (* a (/ x) (/ y) (/ z)))))
  :hints (("Goal" :use (:instance not-integerp-2s
				  )))
  :rule-classes :type-prescription)

(defthm not-integerp-2v-expt-a
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(integerp n)
                (real/rationalp y)
		(real/rationalp z)
		(< a 0)
		(< (* (expt x n) y z) a))
	   (not (integerp (* a (expt x (- n)) (/ y) (/ z)))))
  :hints (("Goal" :use (:instance not-integerp-2s
				  (x (expt x n)))))
  :rule-classes :type-prescription)

(defthm not-integerp-2v-expt-b
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
                (real/rationalp y)
		(integerp n)
		(real/rationalp z)
		(< a 0)
		(< (* x (expt y n) z) a))
	   (not (integerp (* a (/ x) (expt y (- n)) (/ z)))))
  :hints (("Goal" :use (:instance not-integerp-2s
				  (y (expt y n)))))
  :rule-classes :type-prescription)

(defthm not-integerp-2v-expt-c
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
                (real/rationalp y)
		(real/rationalp z)
		(integerp n)
		(< a 0)
		(< (* x y (expt z n)) a))
	   (not (integerp (* a (/ x) (/ y) (expt z (- n))))))
  :hints (("Goal" :use (:instance not-integerp-2s
				  (z (expt z n)))))
  :rule-classes :type-prescription)

(defthm not-integerp-2v-expt-d
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(integerp n1)
                (real/rationalp y)
		(integerp n2)
		(real/rationalp z)
		(< a 0)
		(< (* (expt x n1) (expt y n2) z) a))
	   (not (integerp (* a (expt x (- n1)) (expt y (- n2)) (/ z)))))
  :hints (("Goal" :use (:instance not-integerp-2s
				  (x (expt x n1))
				  (y (expt y n2)))))
  :rule-classes :type-prescription)

(defthm not-integerp-2v-expt-e
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(integerp n1)
                (real/rationalp y)
		(real/rationalp z)
		(integerp n2)
		(< a 0)
		(< (* (expt x n1) y (expt z n2)) a))
	   (not (integerp (* a (expt x (- n1)) (/ y) (expt z (- n2))))))
  :hints (("Goal" :use (:instance not-integerp-2s
				  (x (expt x n1))
				  (z (expt z n2)))))
  :rule-classes :type-prescription)

(defthm not-integerp-2v-expt-f
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
                (real/rationalp y)
		(integerp n1)
		(real/rationalp z)
		(integerp n2)
		(< a 0)
		(< (* x (expt y n1) (expt z n2)) a))
	   (not (integerp (* a (/ x) (expt y (- n1)) (expt z (- n2))))))
  :hints (("Goal" :use (:instance not-integerp-2s
				  (y (expt y n1))
				  (z (expt z n2)))))
  :rule-classes :type-prescription)

(defthm not-integerp-2v-expt-g
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(integerp n1)
                (real/rationalp y)
		(integerp n2)
		(real/rationalp z)
		(integerp n3)
		(< a 0)
		(< (* (expt x n1) (expt y n2) (expt z n3)) a))
	   (not (integerp (* a (expt x (- n1)) (expt y (- n2)) (expt z (- n3))))))
  :hints (("Goal" :use (:instance not-integerp-2s
				  (x (expt x n1))
				  (y (expt y n2))
				  (z (expt z n3)))))
  :rule-classes :type-prescription)

(local (in-theory (disable not-integerp-2v
                           not-integerp-2v-expt-a
                           not-integerp-2v-expt-b
                           not-integerp-2v-expt-c
                           not-integerp-2v-expt-d
                           not-integerp-2v-expt-e
                           not-integerp-2v-expt-f
                           not-integerp-2v-expt-g)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm not-integerp-3a
  (implies (and ;(real/rationalp a)
	        (real/rationalp x)
		(< 0 a)
		(< x (- a)))
	   (not (integerp (* (/ x) a))))
  :hints (("Goal" :use (:instance not-integerp-1a
				  (a a)
				  (x (- x)))))
  :rule-classes :type-prescription)

(defthm not-integerp-3a-expt
  (implies (and	;(real/rationalp a)
	        (real/rationalp x)
		(integerp n)
		(< 0 a)
		(< (expt x n) (- a)))
	   (not (integerp (* (expt x (- n)) a))))
  :hints (("Goal" :use (:instance not-integerp-3a
				  (x (expt x n)))))
  :rule-classes :type-prescription)

(local (in-theory (disable not-integerp-3a
                           not-integerp-3a-expt)))


(defthm not-integerp-3b
  (implies (and ;(real/rationalp a)
		(real/rationalp x)
		(< 0 a)
		(< x (- a)))
	   (not (integerp (* a (/ x)))))
  :hints (("Goal" :use not-integerp-3a))
  :rule-classes :type-prescription)

(defthm not-integerp-3b-expt
  (implies (and ;(real/rationalp a)
		(real/rationalp x)
		(integerp n)
		(< 0 a)
		(< (expt x n) (- a)))
	   (not (integerp (* a (expt x (- n))))))
  :hints (("Goal" :use (:instance not-integerp-3a
				  (x (expt x n)))))
  :rule-classes :type-prescription)

(local (in-theory (disable not-integerp-3b
                           not-integerp-3b-expt)))


;; (defthm not-integerp-3c
;;   (implies (and (real/rationalp a)
;;                 (real/rationalp b)
;; 		(real/rationalp x)
;; 		(< 0 (* a b))
;; 		(< x (- (* a b))))
;; 	   (not (integerp (* (/ x) a b))))
;;   :rule-classes :type-prescription)

(defthm not-integerp-3d
  (implies (and ;(real/rationalp a)
                (real/rationalp b)
		(real/rationalp x)
		(< 0 (* a b))
		(< x (- (* a b))))
	   (not (integerp (* a (/ x) b))))
  :hints (("Goal" :use (:instance not-integerp-3a
				  (a (* a b))
				  (x x))))
  :rule-classes :type-prescription)

(defthm not-integerp-3d-expt
  (implies (and ;(real/rationalp a)
                (real/rationalp b)
		(real/rationalp x)
		(integerp n)
		(< 0 (* a b))
		(< (expt x n) (- (* a b))))
	   (not (integerp (* a (expt x (- n)) b))))
  :hints (("Goal" :use (:instance not-integerp-3a
				  (a (* a b))
				  (x (expt x n)))))
  :rule-classes :type-prescription)

(local (in-theory (disable not-integerp-3d
                           not-integerp-3d-expt)))


(defthm not-integerp-3e
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
		(real/rationalp x)
		(< 0 (* a b))
		(< x (- (* a b))))
	   (not (integerp (* a b (/ x)))))
  :hints (("Goal" :use (:instance not-integerp-3a
				  (a (* a b))
				  (x x))))
  :rule-classes :type-prescription)

(defthm not-integerp-3e-expt
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
		(real/rationalp x)
		(integerp n)
		(< 0 (* a b))
		(< (expt x n) (- (* a b))))
	   (not (integerp (* a b (expt x (- n))))))
  :hints (("Goal" :use (:instance not-integerp-3a
				  (a (* a b))
				  (x (expt x n)))))
  :rule-classes :type-prescription)

(local (in-theory (disable not-integerp-3e
                           not-integerp-3e-expt)))


(defthm not-integerp-3f
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(real/rationalp y)
		(< 0 a)
		(< (* x y) (- a)))
	   (not (integerp (* (/ x) (/ y) a))))
  :hints (("Goal" :use (:instance not-integerp-3a
                                  (a a)
                                  (x (* x y)))))
  :rule-classes :type-prescription)

(defthm not-integerp-3f-expt-a
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(integerp n)
		(real/rationalp y)
		(< 0 a)
		(< (* (expt x n) y) (- a)))
	   (not (integerp (* (expt x (- n)) (/ y) a))))
  :hints (("Goal" :use (:instance not-integerp-3a
                                  (a a)
                                  (x (* (expt x n) y)))))
  :rule-classes :type-prescription)

(defthm not-integerp-3f-expt-b
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(real/rationalp y)
		(integerp n)
		(< 0 a)
		(< (* x (expt y n)) (- a)))
	   (not (integerp (* (/ x) (expt y (- n)) a))))
  :hints (("Goal" :use (:instance not-integerp-3a
                                  (a a)
                                  (x (* (expt y n) x)))))
  :rule-classes :type-prescription)

(defthm not-integerp-3f-expt-c
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(integerp n1)
		(real/rationalp y)
		(integerp n2)
		(< 0 a)
		(< (* (expt x n1) (expt y n2)) (- a)))
	   (not (integerp (* (expt x (- n1)) (expt y (- n2)) a))))
  :hints (("Goal" :use (:instance not-integerp-3a
                                  (a a)
                                  (x (* (expt x n1) (expt y n2))))))
  :rule-classes :type-prescription)

(local (in-theory (disable not-integerp-3f
                           not-integerp-3f-expt-a
                           not-integerp-3f-expt-b
                           not-integerp-3f-expt-c)))


(defthm not-integerp-3g
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(real/rationalp y)
		(< 0 a)
		(< (* x y) (- a)))
	   (not (integerp (* (/ x) a (/ y)))))
  :hints (("Goal" :use not-integerp-3f))
  :rule-classes :type-prescription)

(defthm not-integerp-3g-expt-a
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(integerp n)
		(real/rationalp y)
		(< 0 a)
		(< (* (expt x n) y) (- a)))
	   (not (integerp (* (expt x (- n)) a (/ y)))))
  :hints (("Goal" :use (:instance not-integerp-3f
				  (x (expt x n)))))
  :rule-classes :type-prescription)

(defthm not-integerp-3g-expt-b
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(real/rationalp y)
		(integerp n)
		(< 0 a)
		(< (* x (expt y n)) (- a)))
	   (not (integerp (* (/ x) a (expt y (- n))))))
  :hints (("Goal" :use (:instance not-integerp-3f
				  (y (expt y n)))))
  :rule-classes :type-prescription)

(defthm not-integerp-3g-expt-c
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(integerp n1)
		(real/rationalp y)
		(integerp n2)
		(< 0 a)
		(< (* (expt x n1) (expt y n2)) (- a)))
	   (not (integerp (* (expt x (- n1)) a (expt y (- n2))))))
  :hints (("Goal" :use (:instance not-integerp-3f
				  (x (expt x n1))
				  (y (expt y n2)))))
  :rule-classes :type-prescription)

(local (in-theory (disable not-integerp-3g
                           not-integerp-3g-expt-a
                           not-integerp-3g-expt-b
                           not-integerp-3g-expt-c)))


(defthm not-integerp-3h
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(real/rationalp y)
		(< 0 a)
		(< (* x y) (- a)))
	   (not (integerp (* a (/ x) (/ y)))))
  :hints (("Goal" :use not-integerp-3f))
  :rule-classes :type-prescription)

(defthm not-integerp-3h-expt-a
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(integerp n)
		(real/rationalp y)
		(< 0 a)
		(< (* (expt x n) y) (- a)))
	   (not (integerp (* a (expt x (- n)) (/ y)))))
  :hints (("Goal" :use (:instance not-integerp-3f
				  (x (expt x n)))))
  :rule-classes :type-prescription)

(defthm not-integerp-3h-expt-b
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(real/rationalp y)
		(integerp n)
		(< 0 a)
		(< (* x (expt y n)) (- a)))
	   (not (integerp (* a (/ x) (expt y (- n))))))
  :hints (("Goal" :use (:instance not-integerp-3f
				  (y (expt y n)))))
  :rule-classes :type-prescription)

(defthm not-integerp-3h-expt-c
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(integerp n1)
		(real/rationalp y)
		(integerp n2)
		(< 0 a)
		(< (* (expt x n1) (expt y n2)) (- a)))
	   (not (integerp (* a (expt x (- n1)) (expt y (- n2))))))
  :hints (("Goal" :use (:instance not-integerp-3f
				  (x (expt x n1))
				  (y (expt y n2)))))
  :rule-classes :type-prescription)

(local (in-theory (disable not-integerp-3h
                           not-integerp-3h-expt-a
                           not-integerp-3h-expt-b
                           not-integerp-3h-expt-c)))


;; (defthm not-integerp-3i
;;   (implies (and (real/rationalp a)
;;                 (real/rationalp b)
;;                 (real/rationalp c)
;; 		(real/rationalp x)
;; 		(< 0 (* a b c))
;; 		(< x (- (* a b c))))
;; 	   (not (integerp (* (/ x) a b c))))
;;   :rule-classes :type-prescription)

;; (defthm not-integerp-3j
;;   (implies (and (real/rationalp a)
;;                 (real/rationalp b)
;;                 (real/rationalp c)
;; 		(real/rationalp x)
;; 		(< 0 (* a b c))
;; 		(< x (- (* a b c))))
;; 	   (not (integerp (* a (/ x) b c))))
;;   :rule-classes :type-prescription)

(defthm not-integerp-3k
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
                (real/rationalp c)
                (real/rationalp x)
		(< 0 (* a b c))
		(< x (- (* a b c))))
	   (not (integerp (* a b (/ x) c))))
  :hints (("Goal" :use (:instance not-integerp-3a
				  (a (* a b c))
				  (x x))))
  :rule-classes :type-prescription)

(defthm not-integerp-3k-expt
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
                (real/rationalp c)
                (real/rationalp x)
		(integerp n)
		(< 0 (* a b c))
		(< (expt x n) (- (* a b c))))
	   (not (integerp (* a b (expt x (- n)) c))))
  :hints (("Goal" :use (:instance not-integerp-3a
				  (a (* a b c))
				  (x (expt x n)))))
  :rule-classes :type-prescription)

(local (in-theory (disable not-integerp-3k
                           not-integerp-3k-expt)))


(defthm not-integerp-3l
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
                ;(real/rationalp c)
		(real/rationalp x)
		(< 0 (* a b c))
		(< x (- (* a b c))))
	   (not (integerp (* a b c (/ x)))))
  :hints (("Goal" :use (:instance not-integerp-3a
				  (a (* a b c))
				  (x x))))
  :rule-classes :type-prescription)

(defthm not-integerp-3l-expt
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
                ;(real/rationalp c)
		(real/rationalp x)
		(integerp n)
		(< 0 (* a b c))
		(< (expt x n) (- (* a b c))))
	   (not (integerp (* a b c (expt x (- n))))))
  :hints (("Goal" :use (:instance not-integerp-3a
				  (a (* a b c))
				  (x (expt x n)))))
  :rule-classes :type-prescription)

(local (in-theory (disable not-integerp-3l
                           not-integerp-3l-expt)))


;; (defthm not-integerp-3m
;;   (implies (and (real/rationalp a)
;;                 (real/rationalp b)
;;                 (real/rationalp x)
;; 		(real/rationalp y)
;; 		(< 0 (* a b))
;; 		(< (* x y) (- (* a b))))
;; 	   (not (integerp (* (/ x) (/ y) a b))))
;;   :rule-classes :type-prescription)

(defthm not-integerp-3n
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
                (real/rationalp x)
		(real/rationalp y)
		(< 0 (* a b))
		(< (* x y) (- (* a b))))
	   (not (integerp (* (/ x) a (/ y) b))))
  :hints (("Goal" :use (:instance not-integerp-3a
				  (a (* a b))
				  (x (* x y)))))
  :rule-classes :type-prescription)

(defthm not-integerp-3n-expt-a
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
                (real/rationalp x)
		(integerp n)
		(real/rationalp y)
		(< 0 (* a b))
		(< (* (expt x n) y) (- (* a b))))
	   (not (integerp (* (expt x (- n)) a (/ y) b))))
  :hints (("Goal" :use (:instance not-integerp-3a
				  (a (* a b))
				  (x (* (expt x n) y)))))
  :rule-classes :type-prescription)

(defthm not-integerp-3n-expt-b
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
                (real/rationalp x)
		(real/rationalp y)
		(integerp n)
		(< 0 (* a b))
		(< (* x (expt y n)) (- (* a b))))
	   (not (integerp (* (/ x) a (expt y (- n)) b))))
  :hints (("Goal" :use (:instance not-integerp-3a
				  (a (* a b))
				  (x (* x (expt y n))))))
  :rule-classes :type-prescription)

(defthm not-integerp-3n-expt-c
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
                (real/rationalp x)
		(integerp n1)
		(real/rationalp y)
		(integerp n2)
		(< 0 (* a b))
		(< (* (expt x n1) (expt y n2)) (- (* a b))))
	   (not (integerp (* (expt x (- n1)) a (expt y (- n2)) b))))
  :hints (("Goal" :use (:instance not-integerp-3a
				  (a (* a b))
				  (x (* (expt x n1) (expt y n2))))))
  :rule-classes :type-prescription)

(local (in-theory (disable not-integerp-3n
                           not-integerp-3n-expt-a
                           not-integerp-3n-expt-b
                           not-integerp-3n-expt-c)))


(defthm not-integerp-3o
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
                (real/rationalp x)
		(real/rationalp y)
		(< 0 (* a b))
		(< (* x y) (- (* a b))))
	   (not (integerp (* (/ x) a b (/ y)))))
  :hints (("Goal" :use (:instance not-integerp-3a
				  (a (* a b))
				  (x (* x y)))))
  :rule-classes :type-prescription)

(defthm not-integerp-3o-expt-a
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
                (real/rationalp x)
		(integerp n)
		(real/rationalp y)
		(< 0 (* a b))
		(< (* (expt x n) y) (- (* a b))))
	   (not (integerp (* (expt x (- n)) a b (/ y)))))
  :hints (("Goal" :use (:instance not-integerp-3a
				  (a (* a b))
				  (x (* (expt x n) y)))))
  :rule-classes :type-prescription)

(defthm not-integerp-3o-expt-b
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
                (real/rationalp x)
		(real/rationalp y)
		(integerp n)
		(< 0 (* a b))
		(< (* x (expt y n)) (- (* a b))))
	   (not (integerp (* (/ x) a b (expt y (- n))))))
  :hints (("Goal" :use (:instance not-integerp-3a
				  (a (* a b))
				  (x (* x (expt y n))))))
  :rule-classes :type-prescription)

(defthm not-integerp-3o-expt-c
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
                (real/rationalp x)
		(integerp n1)
		(real/rationalp y)
		(integerp n2)
		(< 0 (* a b))
		(< (* (expt x n1) (expt y n2)) (- (* a b))))
	   (not (integerp (* (expt x (- n1)) a b (expt y (- n2))))))
  :hints (("Goal" :use (:instance not-integerp-3a
				  (a (* a b))
				  (x (* (expt x n1) (expt y n2))))))
  :rule-classes :type-prescription)

(local (in-theory (disable not-integerp-3o
                           not-integerp-3o-expt-a
                           not-integerp-3o-expt-b
                           not-integerp-3o-expt-c)))


(defthm not-integerp-3p
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
                (real/rationalp x)
		(real/rationalp y)
		(< 0 (* a b))
		(< (* x y) (- (* a b))))
	   (not (integerp (* a (/ x) (/ y) b))))
  :hints (("Goal" :use (:instance not-integerp-3a
				  (a (* a b))
				  (x (* x y)))))
  :rule-classes :type-prescription)

(defthm not-integerp-3p-expt-a
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
                (real/rationalp x)
		(integerp n)
		(real/rationalp y)
		(< 0 (* a b))
		(< (* (expt x n) y) (- (* a b))))
	   (not (integerp (* a (expt x (- n)) (/ y) b))))
  :hints (("Goal" :use (:instance not-integerp-3a
				  (a (* a b))
				  (x (* (expt x n) y)))))
  :rule-classes :type-prescription)

(defthm not-integerp-3p-expt-b
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
                (real/rationalp x)
		(real/rationalp y)
		(integerp n)
		(< 0 (* a b))
		(< (* x (expt y n)) (- (* a b))))
	   (not (integerp (* a (/ x) (expt y (- n)) b))))
  :hints (("Goal" :use (:instance not-integerp-3a
				  (a (* a b))
				  (x (* x (expt y n))))))
  :rule-classes :type-prescription)

(defthm not-integerp-3p-expt-c
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
                (real/rationalp x)
		(integerp n1)
		(real/rationalp y)
		(integerp n2)
		(< 0 (* a b))
		(< (* (expt x n1) (expt y n2)) (- (* a b))))
	   (not (integerp (* a (expt x (- n1)) (expt y (- n2)) b))))
  :hints (("Goal" :use (:instance not-integerp-3a
				  (a (* a b))
				  (x (* (expt x n1) (expt y n2))))))
  :rule-classes :type-prescription)

(local (in-theory (disable not-integerp-3p
                           not-integerp-3p-expt-a
                           not-integerp-3p-expt-b
                           not-integerp-3p-expt-c)))


(defthm not-integerp-3q
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
                (real/rationalp x)
		(real/rationalp y)
		(< 0 (* a b))
		(< (* x y) (- (* a b))))
	   (not (integerp (* a (/ x) b (/ y)))))
  :hints (("Goal" :use (:instance not-integerp-3a
				  (a (* a b))
				  (x (* x y)))))
  :rule-classes :type-prescription)

(defthm not-integerp-3q-expt-a
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
                (real/rationalp x)
		(integerp n)
		(real/rationalp y)
		(< 0 (* a b))
		(< (* (expt x n) y) (- (* a b))))
	   (not (integerp (* a (expt x (- n)) b (/ y)))))
  :hints (("Goal" :use (:instance not-integerp-3a
				  (a (* a b))
				  (x (* (expt x n) y)))))
  :rule-classes :type-prescription)

(defthm not-integerp-3q-expt-b
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
                (real/rationalp x)
		(real/rationalp y)
		(integerp n)
		(< 0 (* a b))
		(< (* x (expt y n)) (- (* a b))))
	   (not (integerp (* a (/ x) b (expt y (- n))))))
  :hints (("Goal" :use (:instance not-integerp-3a
				  (a (* a b))
				  (x (* x (expt y n))))))
  :rule-classes :type-prescription)

(defthm not-integerp-3q-expt-c
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
                (real/rationalp x)
		(integerp n1)
		(real/rationalp y)
		(integerp n2)
		(< 0 (* a b))
		(< (* (expt x n1) (expt y n2)) (- (* a b))))
	   (not (integerp (* a (expt x (- n1)) b (expt y (- n2))))))
  :hints (("Goal" :use (:instance not-integerp-3a
				  (a (* a b))
				  (x (* (expt x n1) (expt y n2))))))
  :rule-classes :type-prescription)

(local (in-theory (disable not-integerp-3n
                           not-integerp-3n-expt-a
                           not-integerp-3n-expt-b
                           not-integerp-3n-expt-c)))


(defthm not-integerp-3r
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
                (real/rationalp x)
		(real/rationalp y)
		(< 0 (* a b))
		(< (* x y) (- (* a b))))
	   (not (integerp (* a b (/ x) (/ y)))))
  :hints (("Goal" :use (:instance not-integerp-3a
				  (a (* a b))
				  (x (* x y)))))
  :rule-classes :type-prescription)

(defthm not-integerp-3r-expt-a
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
                (real/rationalp x)
		(integerp n)
		(real/rationalp y)
		(< 0 (* a b))
		(< (* (expt x n) y) (- (* a b))))
	   (not (integerp (* a b (expt x (- n)) (/ y)))))
  :hints (("Goal" :use (:instance not-integerp-3a
				  (a (* a b))
				  (x (* (expt x n) y)))))
  :rule-classes :type-prescription)

(defthm not-integerp-3r-expt-b
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
                (real/rationalp x)
		(real/rationalp y)
		(integerp n)
		(< 0 (* a b))
		(< (* x (expt y n)) (- (* a b))))
	   (not (integerp (* a b (/ x) (expt y (- n))))))
  :hints (("Goal" :use (:instance not-integerp-3a
				  (a (* a b))
				  (x (* x (expt y n))))))
  :rule-classes :type-prescription)

(defthm not-integerp-3r-expt-c
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
                (real/rationalp x)
		(integerp n1)
		(real/rationalp y)
		(integerp n2)
		(< 0 (* a b))
		(< (* (expt x n1) (expt y n2)) (- (* a b))))
	   (not (integerp (* a b (expt x (- n1)) (expt y (- n2))))))
  :hints (("Goal" :use (:instance not-integerp-3a
				  (a (* a b))
				  (x (* (expt x n1) (expt y n2))))))
  :rule-classes :type-prescription)

(local (in-theory (disable not-integerp-3r
                           not-integerp-3r-expt-a
                           not-integerp-3r-expt-b
                           not-integerp-3r-expt-c)))


(defthm not-integerp-3s
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
                (real/rationalp y)
		(real/rationalp z)
		(< 0 a)
		(< (* x y z) (- a)))
	   (not (integerp (* (/ x) (/ y) (/ z) a))))
  :hints (("Goal" :use (:instance not-integerp-3a
                                  (a a)
                                  (x (* x y z)))))
  :rule-classes :type-prescription)

(defthm not-integerp-3s-expt-a
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(integerp n)
                (real/rationalp y)
		(real/rationalp z)
		(< 0 a)
		(< (* (expt x n) y z) (- a)))
	   (not (integerp (* (expt x (- n)) (/ y) (/ z) a))))
  :hints (("Goal" :use (:instance not-integerp-3a
                                  (a a)
                                  (x (* (expt x n) y z)))))
  :rule-classes :type-prescription)

(defthm not-integerp-3s-expt-b
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
                (real/rationalp y)
		(integerp n)
		(real/rationalp z)
		(< 0 a)
		(< (* x (expt y n) z) (- a)))
	   (not (integerp (* (/ x) (expt y (- n)) (/ z) a))))
  :hints (("Goal" :use (:instance not-integerp-3a
                                  (a a)
                                  (x (* x (expt y n) z)))))
  :rule-classes :type-prescription)

(defthm not-integerp-3s-expt-c
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
                (real/rationalp y)
		(real/rationalp z)
		(integerp n)
		(< 0 a)
		(< (* x y (expt z n)) (- a)))
	   (not (integerp (* (/ x) (/ y) (expt z (- n)) a))))
  :hints (("Goal" :use (:instance not-integerp-3a
                                  (a a)
                                  (x (* x y (expt z n))))))
  :rule-classes :type-prescription)

(defthm not-integerp-3s-expt-d
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(integerp n1)
                (real/rationalp y)
		(integerp n2)
		(real/rationalp z)
		(< 0 a)
		(< (* (expt x n1) (expt y n2) z) (- a)))
	   (not (integerp (* (expt x (- n1)) (expt y (- n2)) (/ z) a))))
  :hints (("Goal" :use (:instance not-integerp-3a
                                  (a a)
                                  (x (* (expt x n1) (expt y n2) z)))))
  :rule-classes :type-prescription)

(defthm not-integerp-3s-expt-e
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(integerp n1)
                (real/rationalp y)
		(real/rationalp z)
		(integerp n2)
		(< 0 a)
		(< (* (expt x n1) y (expt z n2)) (- a)))
	   (not (integerp (* (expt x (- n1)) (/ y) (expt z (- n2)) a))))
  :hints (("Goal" :use (:instance not-integerp-3a
                                  (a a)
                                  (x (* (expt x n1) y (expt z n2))))))
  :rule-classes :type-prescription)

(defthm not-integerp-3s-expt-f
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
                (real/rationalp y)
		(integerp n1)
		(real/rationalp z)
		(integerp n2)
		(< 0 a)
		(< (* x (expt y n1) (expt z n2)) (- a)))
	   (not (integerp (* (/ x) (expt y (- n1)) (expt z (- n2)) a))))
  :hints (("Goal" :use (:instance not-integerp-3a
                                  (a a)
                                  (x (* x (expt y n1) (expt z n2))))))
  :rule-classes :type-prescription)

(defthm not-integerp-3s-expt-g
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(integerp n1)
                (real/rationalp y)
		(integerp n2)
		(real/rationalp z)
		(integerp n3)
		(< 0 a)
		(< (* (expt x n1) (expt y n2) (expt z n3)) (- a)))
	   (not (integerp (* (expt x (- n1)) (expt y (- n2)) (expt z (- n3)) a))))
  :hints (("Goal" :use (:instance not-integerp-3a
                                  (a a)
                                  (x (* (expt x n1) (expt y n2) (expt z n3))))))
  :rule-classes :type-prescription)

(local (in-theory (disable not-integerp-3s
                           not-integerp-3s-expt-a
                           not-integerp-3s-expt-b
                           not-integerp-3s-expt-c
                           not-integerp-3s-expt-d
                           not-integerp-3s-expt-e
                           not-integerp-3s-expt-f
                           not-integerp-3s-expt-g
                           )))


(defthm not-integerp-3t
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
                (real/rationalp y)
		(real/rationalp z)
		(< 0 a)
		(< (* x y z) (- a)))
	   (not (integerp (* (/ x) (/ y) a (/ z)))))
  :hints (("Goal" :use not-integerp-3s))
  :rule-classes :type-prescription)

(defthm not-integerp-3t-expt-a
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(integerp n)
                (real/rationalp y)
		(real/rationalp z)
		(< 0 a)
		(< (* (expt x n) y z) (- a)))
	   (not (integerp (* (expt x (- n)) (/ y) a (/ z)))))
  :hints (("Goal" :use (:instance not-integerp-3s
				  (x (expt x n)))))
  :rule-classes :type-prescription)

(defthm not-integerp-3t-expt-b
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
                (real/rationalp y)
		(integerp n)
		(real/rationalp z)
		(< 0 a)
		(< (* x (expt y n) z) (- a)))
	   (not (integerp (* (/ x) (expt y (- n)) a (/ z)))))
  :hints (("Goal" :use (:instance not-integerp-3s
				  (y (expt y n)))))
  :rule-classes :type-prescription)

(defthm not-integerp-3t-expt-c
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
                (real/rationalp y)
		(real/rationalp z)
		(integerp n)
		(< 0 a)
		(< (* x y (expt z n)) (- a)))
	   (not (integerp (* (/ x) (/ y) a (expt z (- n))))))
  :hints (("Goal" :use (:instance not-integerp-3s
				  (z (expt z n)))))
  :rule-classes :type-prescription)

(defthm not-integerp-3t-expt-d
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(integerp n1)
                (real/rationalp y)
		(integerp n2)
		(real/rationalp z)
		(< 0 a)
		(< (* (expt x n1) (expt y n2) z) (- a)))
	   (not (integerp (* (expt x (- n1)) (expt y (- n2)) a (/ z)))))
  :hints (("Goal" :use (:instance not-integerp-3s
				  (x (expt x n1))
				  (y (expt y n2)))))
  :rule-classes :type-prescription)

(defthm not-integerp-3t-expt-e
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(integerp n1)
                (real/rationalp y)
		(real/rationalp z)
		(integerp n2)
		(< 0 a)
		(< (* (expt x n1) y (expt z n2)) (- a)))
	   (not (integerp (* (expt x (- n1)) (/ y) a (expt z (- n2))))))
  :hints (("Goal" :use (:instance not-integerp-3s
				  (x (expt x n1))
				  (z (expt z n2)))))
  :rule-classes :type-prescription)

(defthm not-integerp-3t-expt-f
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
                (real/rationalp y)
		(integerp n1)
		(real/rationalp z)
		(integerp n2)
		(< 0 a)
		(< (* x (expt y n1) (expt z n2)) (- a)))
	   (not (integerp (* (/ x) (expt y (- n1)) a (expt z (- n2))))))
  :hints (("Goal" :use (:instance not-integerp-3s
				  (y (expt y n1))
				  (z (expt z n2)))))
  :rule-classes :type-prescription)

(defthm not-integerp-3t-expt-g
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(integerp n1)
                (real/rationalp y)
		(integerp n2)
		(real/rationalp z)
		(integerp n3)
		(< 0 a)
		(< (* (expt x n1) (expt y n2) (expt z n3)) (- a)))
	   (not (integerp (* (expt x (- n1)) (expt y (- n2)) a (expt z (- n3))))))
  :hints (("Goal" :use (:instance not-integerp-3s
				  (x (expt x n1))
				  (y (expt y n2))
				  (z (expt z n3)))))
  :rule-classes :type-prescription)

(local (in-theory (disable not-integerp-3t
                           not-integerp-3t-expt-a
                           not-integerp-3t-expt-b
                           not-integerp-3t-expt-c
                           not-integerp-3t-expt-d
                           not-integerp-3t-expt-e
                           not-integerp-3t-expt-f
                           not-integerp-3t-expt-g
                           )))


(defthm not-integerp-3u
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
                (real/rationalp y)
		(real/rationalp z)
		(< 0 a)
		(< (* x y z) (- a)))
	   (not (integerp (* (/ x) a (/ y) (/ z)))))
  :hints (("Goal" :use (:instance not-integerp-3s
				  )))
  :rule-classes :type-prescription)

(defthm not-integerp-3u-expt-a
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(integerp n)
                (real/rationalp y)
		(real/rationalp z)
		(< 0 a)
		(< (* (expt x n) y z) (- a)))
	   (not (integerp (* (expt x (- n)) a (/ y) (/ z)))))
  :hints (("Goal" :use (:instance not-integerp-3s
				  (x (expt x n)))))
  :rule-classes :type-prescription)

(defthm not-integerp-3u-expt-b
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
                (real/rationalp y)
		(integerp n)
		(real/rationalp z)
		(< 0 a)
		(< (* x (expt y n) z) (- a)))
	   (not (integerp (* (/ x) a (expt y (- n)) (/ z)))))
  :hints (("Goal" :use (:instance not-integerp-3s
				  (y (expt y n)))))
  :rule-classes :type-prescription)

(defthm not-integerp-3u-expt-c
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
                (real/rationalp y)
		(real/rationalp z)
		(integerp n)
		(< 0 a)
		(< (* x y (expt z n)) (- a)))
	   (not (integerp (* (/ x) a (/ y) (expt z (- n))))))
  :hints (("Goal" :use (:instance not-integerp-3s
				  (z (expt z n)))))
  :rule-classes :type-prescription)

(defthm not-integerp-3u-expt-d
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(integerp n1)
                (real/rationalp y)
		(integerp n2)
		(real/rationalp z)
		(< 0 a)
		(< (* (expt x n1) (expt y n2) z) (- a)))
	   (not (integerp (* (expt x (- n1)) a (expt y (- n2)) (/ z)))))
  :hints (("Goal" :use (:instance not-integerp-3s
				  (x (expt x n1))
				  (y (expt y n2)))))
  :rule-classes :type-prescription)

(defthm not-integerp-3u-expt-e
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(integerp n1)
                (real/rationalp y)
		(real/rationalp z)
		(integerp n2)
		(< 0 a)
		(< (* (expt x n1) y (expt z n2)) (- a)))
	   (not (integerp (* (expt x (- n1)) a (/ y) (expt z (- n2))))))
  :hints (("Goal" :use (:instance not-integerp-3s
				  (x (expt x n1))
				  (z (expt z n2)))))
  :rule-classes :type-prescription)

(defthm not-integerp-3u-expt-f
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
                (real/rationalp y)
		(integerp n1)
		(real/rationalp z)
		(integerp n2)
		(< 0 a)
		(< (* x (expt y n1) (expt z n2)) (- a)))
	   (not (integerp (* (/ x) a (expt y (- n1)) (expt z (- n2))))))
  :hints (("Goal" :use (:instance not-integerp-3s
				  (y (expt y n1))
				  (z (expt z n2)))))
  :rule-classes :type-prescription)

(defthm not-integerp-3u-expt-g
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(integerp n1)
                (real/rationalp y)
		(integerp n2)
		(real/rationalp z)
		(integerp n3)
		(< 0 a)
		(< (* (expt x n1) (expt y n2) (expt z n3)) (- a)))
	   (not (integerp (* (expt x (- n1)) a (expt y (- n2)) (expt z (- n3))))))
  :hints (("Goal" :use (:instance not-integerp-3s
				  (x (expt x n1))
				  (y (expt y n2))
				  (z (expt z n3)))))
  :rule-classes :type-prescription)

(local (in-theory (disable not-integerp-3u
                           not-integerp-3u-expt-a
                           not-integerp-3u-expt-b
                           not-integerp-3u-expt-c
                           not-integerp-3u-expt-d
                           not-integerp-3u-expt-e
                           not-integerp-3u-expt-f
                           not-integerp-3u-expt-g
                           )))


(defthm not-integerp-3v
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
                (real/rationalp y)
		(real/rationalp z)
		(< 0 a)
		(< (* x y z) (- a)))
	   (not (integerp (* a (/ x) (/ y) (/ z)))))
  :hints (("Goal" :use (:instance not-integerp-3s
				  )))
  :rule-classes :type-prescription)

(defthm not-integerp-3v-expt-a
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(integerp n)
                (real/rationalp y)
		(real/rationalp z)
		(< 0 a)
		(< (* (expt x n) y z) (- a)))
	   (not (integerp (* a (expt x (- n)) (/ y) (/ z)))))
  :hints (("Goal" :use (:instance not-integerp-3s
				  (x (expt x n)))))
  :rule-classes :type-prescription)

(defthm not-integerp-3v-expt-b
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
                (real/rationalp y)
		(integerp n)
		(real/rationalp z)
		(< 0 a)
		(< (* x (expt y n) z) (- a)))
	   (not (integerp (* a (/ x) (expt y (- n)) (/ z)))))
  :hints (("Goal" :use (:instance not-integerp-3s
				  (y (expt y n)))))
  :rule-classes :type-prescription)

(defthm not-integerp-3v-expt-c
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
                (real/rationalp y)
		(real/rationalp z)
		(integerp n)
		(< 0 a)
		(< (* x y (expt z n)) (- a)))
	   (not (integerp (* a (/ x) (/ y) (expt z (- n))))))
  :hints (("Goal" :use (:instance not-integerp-3s
				  (z (expt z n)))))
  :rule-classes :type-prescription)

(defthm not-integerp-3v-expt-d
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(integerp n1)
                (real/rationalp y)
		(integerp n2)
		(real/rationalp z)
		(< 0 a)
		(< (* (expt x n1) (expt y n2) z) (- a)))
	   (not (integerp (* a (expt x (- n1)) (expt y (- n2)) (/ z)))))
  :hints (("Goal" :use (:instance not-integerp-3s
				  (x (expt x n1))
				  (y (expt y n2)))))
  :rule-classes :type-prescription)

(defthm not-integerp-3v-expt-e
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(integerp n1)
                (real/rationalp y)
		(real/rationalp z)
		(integerp n2)
		(< 0 a)
		(< (* (expt x n1) y (expt z n2)) (- a)))
	   (not (integerp (* a (expt x (- n1)) (/ y) (expt z (- n2))))))
  :hints (("Goal" :use (:instance not-integerp-3s
				  (x (expt x n1))
				  (z (expt z n2)))))
  :rule-classes :type-prescription)

(defthm not-integerp-3v-expt-f
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
                (real/rationalp y)
		(integerp n1)
		(real/rationalp z)
		(integerp n2)
		(< 0 a)
		(< (* x (expt y n1) (expt z n2)) (- a)))
	   (not (integerp (* a (/ x) (expt y (- n1)) (expt z (- n2))))))
  :hints (("Goal" :use (:instance not-integerp-3s
				  (y (expt y n1))
				  (z (expt z n2)))))
  :rule-classes :type-prescription)

(defthm not-integerp-3v-expt-g
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(integerp n1)
                (real/rationalp y)
		(integerp n2)
		(real/rationalp z)
		(integerp n3)
		(< 0 a)
		(< (* (expt x n1) (expt y n2) (expt z n3)) (- a)))
	   (not (integerp (* a (expt x (- n1)) (expt y (- n2)) (expt z (- n3))))))
  :hints (("Goal" :use (:instance not-integerp-3s
				  (x (expt x n1))
				  (y (expt y n2))
				  (z (expt z n3)))))
  :rule-classes :type-prescription)

(local (in-theory (disable not-integerp-3v
                           not-integerp-3v-expt-a
                           not-integerp-3v-expt-b
                           not-integerp-3v-expt-c
                           not-integerp-3v-expt-d
                           not-integerp-3v-expt-e
                           not-integerp-3v-expt-f
                           not-integerp-3v-expt-g
                           )))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm not-integerp-4a
  (implies (and ;(real/rationalp a)
	        (real/rationalp x)
		(< a 0)
		(< (- a) x))
	   (not (integerp (* (/ x) a))))
  :hints (("Goal" :use (:instance not-integerp-1a
				  (a (- a))
				  (x x))))
  :rule-classes :type-prescription)

(defthm not-integerp-4a-expt
  (implies (and	;(real/rationalp a)
	        (real/rationalp x)
		(integerp n)
		(< a 0)
		(< (- a) (expt x n)))
	   (not (integerp (* (expt x (- n)) a))))
  :hints (("Goal" :use (:instance not-integerp-4a
				  (x (expt x n)))))
  :rule-classes :type-prescription)

(local (in-theory (disable not-integerp-4a
                           not-integerp-4a-expt)))


(defthm not-integerp-4b
  (implies (and ;(real/rationalp a)
		(real/rationalp x)
		(< a 0)
		(< (- a) x))
	   (not (integerp (* a (/ x)))))
  :hints (("Goal" :use not-integerp-4a))
  :rule-classes :type-prescription)

(defthm not-integerp-4b-expt
  (implies (and ;(real/rationalp a)
		(real/rationalp x)
		(integerp n)
		(< a 0)
		(< (- a) (expt x n)))
	   (not (integerp (* a (expt x (- n))))))
  :hints (("Goal" :use (:instance not-integerp-4a
				  (x (expt x n)))))
  :rule-classes :type-prescription)

(local (in-theory (disable not-integerp-4b
                           not-integerp-4b-expt)))


;; (defthm not-integerp-4c
;;   (implies (and (real/rationalp a)
;;                 (real/rationalp b)
;; 		(real/rationalp x)
;; 		(< (* a b) 0)
;; 		(< (- (* a b)) x))
;; 	   (not (integerp (* (/ x) a b))))
;;   :rule-classes :type-prescription)

(defthm not-integerp-4d
  (implies (and ;(real/rationalp a)
                (real/rationalp b)
		(real/rationalp x)
		(< (* a b) 0)
		(< (- (* a b)) x))
	   (not (integerp (* a (/ x) b))))
  :hints (("Goal" :use (:instance not-integerp-4a
				  (a (* a b))
				  (x x))))
  :rule-classes :type-prescription)

(defthm not-integerp-4d-expt
  (implies (and ;(real/rationalp a)
                (real/rationalp b)
		(real/rationalp x)
		(integerp n)
		(< (* a b) 0)
		(< (- (* a b)) (expt x n)))
	   (not (integerp (* a (expt x (- n)) b))))
  :hints (("Goal" :use (:instance not-integerp-4a
				  (a (* a b))
				  (x (expt x n)))))
  :rule-classes :type-prescription)

(local (in-theory (disable not-integerp-4d
                           not-integerp-4d-expt)))


(defthm not-integerp-4e
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
		(real/rationalp x)
		(< (* a b) 0)
		(< (- (* a b)) x))
	   (not (integerp (* a b (/ x)))))
  :hints (("Goal" :use (:instance not-integerp-4a
				  (a (* a b))
				  (x x))))
  :rule-classes :type-prescription)

(defthm not-integerp-4e-expt
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
		(real/rationalp x)
		(integerp n)
		(< (* a b) 0)
		(< (- (* a b)) (expt x n)))
	   (not (integerp (* a b (expt x (- n))))))
  :hints (("Goal" :use (:instance not-integerp-4a
				  (a (* a b))
				  (x (expt x n)))))
  :rule-classes :type-prescription)

(local (in-theory (disable not-integerp-4e
                           not-integerp-4e-expt)))


(defthm not-integerp-4f
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(real/rationalp y)
		(< a 0)
		(< (- a) (* x y)))
	   (not (integerp (* (/ x) (/ y) a))))
  :hints (("Goal" :use (:instance not-integerp-4a
                                  (a a)
                                  (x (* x y)))))
  :rule-classes :type-prescription)

(defthm not-integerp-4f-expt-a
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(integerp n)
		(real/rationalp y)
		(< a 0)
		(< (- a) (* (expt x n) y)))
	   (not (integerp (* (expt x (- n)) (/ y) a))))
  :hints (("Goal" :use (:instance not-integerp-4a
                                  (a a)
                                  (x (* (expt x n) y)))))
  :rule-classes :type-prescription)

(defthm not-integerp-4f-expt-b
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(real/rationalp y)
		(integerp n)
		(< a 0)
		(< (- a) (* x (expt y n))))
	   (not (integerp (* (/ x) (expt y (- n)) a))))
  :hints (("Goal" :use (:instance not-integerp-4a
                                  (a a)
                                  (x (* (expt y n) x)))))
  :rule-classes :type-prescription)

(defthm not-integerp-4f-expt-c
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(integerp n1)
		(real/rationalp y)
		(integerp n2)
		(< a 0)
		(< (- a) (* (expt x n1) (expt y n2))))
	   (not (integerp (* (expt x (- n1)) (expt y (- n2)) a))))
  :hints (("Goal" :use (:instance not-integerp-4a
                                  (a a)
                                  (x (* (expt x n1) (expt y n2))))))
  :rule-classes :type-prescription)

(local (in-theory (disable not-integerp-4f
                           not-integerp-4f-expt-a
                           not-integerp-4f-expt-b
                           not-integerp-4f-expt-c)))


(defthm not-integerp-4g
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(real/rationalp y)
		(< a 0)
		(< (- a) (* x y)))
	   (not (integerp (* (/ x) a (/ y)))))
  :hints (("Goal" :use not-integerp-4f))
  :rule-classes :type-prescription)

(defthm not-integerp-4g-expt-a
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(integerp n)
		(real/rationalp y)
		(< a 0)
		(< (- a) (* (expt x n) y)))
	   (not (integerp (* (expt x (- n)) a (/ y)))))
  :hints (("Goal" :use (:instance not-integerp-4f
				  (x (expt x n)))))
  :rule-classes :type-prescription)

(defthm not-integerp-4g-expt-b
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(real/rationalp y)
		(integerp n)
		(< a 0)
		(< (- a) (* x (expt y n))))
	   (not (integerp (* (/ x) a (expt y (- n))))))
  :hints (("Goal" :use (:instance not-integerp-4f
				  (y (expt y n)))))
  :rule-classes :type-prescription)

(defthm not-integerp-4g-expt-c
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(integerp n1)
		(real/rationalp y)
		(integerp n2)
		(< a 0)
		(< (- a) (* (expt x n1) (expt y n2))))
	   (not (integerp (* (expt x (- n1)) a (expt y (- n2))))))
  :hints (("Goal" :use (:instance not-integerp-4f
				  (x (expt x n1))
				  (y (expt y n2)))))
  :rule-classes :type-prescription)

(local (in-theory (disable not-integerp-4g
                           not-integerp-4g-expt-a
                           not-integerp-4g-expt-b
                           not-integerp-4g-expt-c)))


(defthm not-integerp-4h
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(real/rationalp y)
		(< a 0)
		(< (- a) (* x y)))
	   (not (integerp (* a (/ x) (/ y)))))
  :hints (("Goal" :use not-integerp-4f))
  :rule-classes :type-prescription)

(defthm not-integerp-4h-expt-a
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(integerp n)
		(real/rationalp y)
		(< a 0)
		(< (- a) (* (expt x n) y)))
	   (not (integerp (* a (expt x (- n)) (/ y)))))
  :hints (("Goal" :use (:instance not-integerp-4f
				  (x (expt x n)))))
  :rule-classes :type-prescription)

(defthm not-integerp-4h-expt-b
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(real/rationalp y)
		(integerp n)
		(< a 0)
		(< (- a) (* x (expt y n))))
	   (not (integerp (* a (/ x) (expt y (- n))))))
  :hints (("Goal" :use (:instance not-integerp-4f
				  (y (expt y n)))))
  :rule-classes :type-prescription)

(defthm not-integerp-4h-expt-c
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(integerp n1)
		(real/rationalp y)
		(integerp n2)
		(< a 0)
		(< (- a) (* (expt x n1) (expt y n2))))
	   (not (integerp (* a (expt x (- n1)) (expt y (- n2))))))
  :hints (("Goal" :use (:instance not-integerp-4f
				  (x (expt x n1))
				  (y (expt y n2)))))
  :rule-classes :type-prescription)

(local (in-theory (disable not-integerp-4h
                           not-integerp-4h-expt-a
                           not-integerp-4h-expt-b
                           not-integerp-4h-expt-c)))


;; (defthm not-integerp-4i
;;   (implies (and (real/rationalp a)
;;                 (real/rationalp b)
;;                 (real/rationalp c)
;; 		(real/rationalp x)
;; 		(< (* a b c) 0)
;; 		(< (- (* a b c)) x))
;; 	   (not (integerp (* (/ x) a b c))))
;;   :rule-classes :type-prescription)

;; (defthm not-integerp-4j
;;   (implies (and (real/rationalp a)
;;                 (real/rationalp b)
;;                 (real/rationalp c)
;; 		(real/rationalp x)
;; 		(< (* a b c) 0)
;; 		(< (- (* a b c)) x))
;; 	   (not (integerp (* a (/ x) b c))))
;;   :rule-classes :type-prescription)

(defthm not-integerp-4k
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
                (real/rationalp c)
                (real/rationalp x)
		(< (* a b c) 0)
		(< (- (* a b c)) x))
	   (not (integerp (* a b (/ x) c))))
  :hints (("Goal" :use (:instance not-integerp-4a
				  (a (* a b c))
				  (x x))))
  :rule-classes :type-prescription)

(defthm not-integerp-4k-expt
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
                (real/rationalp c)
                (real/rationalp x)
		(integerp n)
		(< (* a b c) 0)
		(< (- (* a b c)) (expt x n)))
	   (not (integerp (* a b (expt x (- n)) c))))
  :hints (("Goal" :use (:instance not-integerp-4a
				  (a (* a b c))
				  (x (expt x n)))))
  :rule-classes :type-prescription)

(local (in-theory (disable not-integerp-4k
                           not-integerp-4k-expt)))


(defthm not-integerp-4l
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
                ;(real/rationalp c)
		(real/rationalp x)
		(< (* a b c) 0)
		(< (- (* a b c)) x))
	   (not (integerp (* a b c (/ x)))))
  :hints (("Goal" :use (:instance not-integerp-4a
				  (a (* a b c))
				  (x x))))
  :rule-classes :type-prescription)

(defthm not-integerp-4l-expt
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
                ;(real/rationalp c)
		(real/rationalp x)
		(integerp n)
		(< (* a b c) 0)
		(< (- (* a b c)) (expt x n)))
	   (not (integerp (* a b c (expt x (- n))))))
  :hints (("Goal" :use (:instance not-integerp-4a
				  (a (* a b c))
				  (x (expt x n)))))
  :rule-classes :type-prescription)

(local (in-theory (disable not-integerp-4l
                           not-integerp-4l-expt)))

;; (defthm not-integerp-4m
;;   (implies (and (real/rationalp a)
;;                 (real/rationalp b)
;;                 (real/rationalp x)
;; 		(real/rationalp y)
;; 		(< (* a b) 0)
;; 		(< (- (* a b)) (* x y)))
;; 	   (not (integerp (* (/ x) (/ y) a b))))
;;   :rule-classes :type-prescription)

(defthm not-integerp-4n
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
                (real/rationalp x)
		(real/rationalp y)
		(< (* a b) 0)
		(< (- (* a b)) (* x y)))
	   (not (integerp (* (/ x) a (/ y) b))))
  :hints (("Goal" :use (:instance not-integerp-4a
				  (a (* a b))
				  (x (* x y)))))
  :rule-classes :type-prescription)

(defthm not-integerp-4n-expt-a
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
                (real/rationalp x)
		(integerp n)
		(real/rationalp y)
		(< (* a b) 0)
		(< (- (* a b)) (* (expt x n) y)))
	   (not (integerp (* (expt x (- n)) a (/ y) b))))
  :hints (("Goal" :use (:instance not-integerp-4a
				  (a (* a b))
				  (x (* (expt x n) y)))))
  :rule-classes :type-prescription)

(defthm not-integerp-4n-expt-b
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
                (real/rationalp x)
		(real/rationalp y)
		(integerp n)
		(< (* a b) 0)
		(< (- (* a b)) (* x (expt y n))))
	   (not (integerp (* (/ x) a (expt y (- n)) b))))
  :hints (("Goal" :use (:instance not-integerp-4a
				  (a (* a b))
				  (x (* x (expt y n))))))
  :rule-classes :type-prescription)

(defthm not-integerp-4n-expt-c
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
                (real/rationalp x)
		(integerp n1)
		(real/rationalp y)
		(integerp n2)
		(< (* a b) 0)
		(< (- (* a b)) (* (expt x n1) (expt y n2))))
	   (not (integerp (* (expt x (- n1)) a (expt y (- n2)) b))))
  :hints (("Goal" :use (:instance not-integerp-4a
				  (a (* a b))
				  (x (* (expt x n1) (expt y n2))))))
  :rule-classes :type-prescription)

(local (in-theory (disable not-integerp-4n
                           not-integerp-4n-expt-a
                           not-integerp-4n-expt-b
                           not-integerp-4n-expt-c)))

(defthm not-integerp-4o
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
                (real/rationalp x)
		(real/rationalp y)
		(< (* a b) 0)
		(< (- (* a b)) (* x y)))
	   (not (integerp (* (/ x) a b (/ y)))))
  :hints (("Goal" :use (:instance not-integerp-4a
				  (a (* a b))
				  (x (* x y)))))
  :rule-classes :type-prescription)

(defthm not-integerp-4o-expt-a
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
                (real/rationalp x)
		(integerp n)
		(real/rationalp y)
		(< (* a b) 0)
		(< (- (* a b)) (* (expt x n) y)))
	   (not (integerp (* (expt x (- n)) a b (/ y)))))
  :hints (("Goal" :use (:instance not-integerp-4a
				  (a (* a b))
				  (x (* (expt x n) y)))))
  :rule-classes :type-prescription)

(defthm not-integerp-4o-expt-b
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
                (real/rationalp x)
		(real/rationalp y)
		(integerp n)
		(< (* a b) 0)
		(< (- (* a b)) (* x (expt y n))))
	   (not (integerp (* (/ x) a b (expt y (- n))))))
  :hints (("Goal" :use (:instance not-integerp-4a
				  (a (* a b))
				  (x (* x (expt y n))))))
  :rule-classes :type-prescription)

(defthm not-integerp-4o-expt-c
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
                (real/rationalp x)
		(integerp n1)
		(real/rationalp y)
		(integerp n2)
		(< (* a b) 0)
		(< (- (* a b)) (* (expt x n1) (expt y n2))))
	   (not (integerp (* (expt x (- n1)) a b (expt y (- n2))))))
  :hints (("Goal" :use (:instance not-integerp-4a
				  (a (* a b))
				  (x (* (expt x n1) (expt y n2))))))
  :rule-classes :type-prescription)

(local (in-theory (disable not-integerp-4o
                           not-integerp-4o-expt-a
                           not-integerp-4o-expt-b
                           not-integerp-4o-expt-c
                           )))


(defthm not-integerp-4p
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
                (real/rationalp x)
		(real/rationalp y)
		(< (* a b) 0)
		(< (- (* a b)) (* x y)))
	   (not (integerp (* a (/ x) (/ y) b))))
  :hints (("Goal" :use (:instance not-integerp-4a
				  (a (* a b))
				  (x (* x y)))))
  :rule-classes :type-prescription)

(defthm not-integerp-4p-expt-a
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
                (real/rationalp x)
		(integerp n)
		(real/rationalp y)
		(< (* a b) 0)
		(< (- (* a b)) (* (expt x n) y)))
	   (not (integerp (* a (expt x (- n)) (/ y) b))))
  :hints (("Goal" :use (:instance not-integerp-4a
				  (a (* a b))
				  (x (* (expt x n) y)))))
  :rule-classes :type-prescription)

(defthm not-integerp-4p-expt-b
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
                (real/rationalp x)
		(real/rationalp y)
		(integerp n)
		(< (* a b) 0)
		(< (- (* a b)) (* x (expt y n))))
	   (not (integerp (* a (/ x) (expt y (- n)) b))))
  :hints (("Goal" :use (:instance not-integerp-4a
				  (a (* a b))
				  (x (* x (expt y n))))))
  :rule-classes :type-prescription)

(defthm not-integerp-4p-expt-c
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
                (real/rationalp x)
		(integerp n1)
		(real/rationalp y)
		(integerp n2)
		(< (* a b) 0)
		(< (- (* a b)) (* (expt x n1) (expt y n2))))
	   (not (integerp (* a (expt x (- n1)) (expt y (- n2)) b))))
  :hints (("Goal" :use (:instance not-integerp-4a
				  (a (* a b))
				  (x (* (expt x n1) (expt y n2))))))
  :rule-classes :type-prescription)

(local (in-theory (disable not-integerp-4p
                           not-integerp-4p-expt-a
                           not-integerp-4p-expt-b
                           not-integerp-4p-expt-c
                           )))


(defthm not-integerp-4q
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
                (real/rationalp x)
		(real/rationalp y)
		(< (* a b) 0)
		(< (- (* a b)) (* x y)))
	   (not (integerp (* a (/ x) b (/ y)))))
  :hints (("Goal" :use (:instance not-integerp-4a
				  (a (* a b))
				  (x (* x y)))))
  :rule-classes :type-prescription)

(defthm not-integerp-4q-expt-a
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
                (real/rationalp x)
		(integerp n)
		(real/rationalp y)
		(< (* a b) 0)
		(< (- (* a b)) (* (expt x n) y)))
	   (not (integerp (* a (expt x (- n)) b (/ y)))))
  :hints (("Goal" :use (:instance not-integerp-4a
				  (a (* a b))
				  (x (* (expt x n) y)))))
  :rule-classes :type-prescription)

(defthm not-integerp-4q-expt-b
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
                (real/rationalp x)
		(real/rationalp y)
		(integerp n)
		(< (* a b) 0)
		(< (- (* a b)) (* x (expt y n))))
	   (not (integerp (* a (/ x) b (expt y (- n))))))
  :hints (("Goal" :use (:instance not-integerp-4a
				  (a (* a b))
				  (x (* x (expt y n))))))
  :rule-classes :type-prescription)

(defthm not-integerp-4q-expt-c
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
                (real/rationalp x)
		(integerp n1)
		(real/rationalp y)
		(integerp n2)
		(< (* a b) 0)
		(< (- (* a b)) (* (expt x n1) (expt y n2))))
	   (not (integerp (* a (expt x (- n1)) b (expt y (- n2))))))
  :hints (("Goal" :use (:instance not-integerp-4a
				  (a (* a b))
				  (x (* (expt x n1) (expt y n2))))))
  :rule-classes :type-prescription)

(local (in-theory (disable not-integerp-4q
                           not-integerp-4q-expt-a
                           not-integerp-4q-expt-b
                           not-integerp-4q-expt-c
                           )))


(defthm not-integerp-4r
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
                (real/rationalp x)
		(real/rationalp y)
		(< (* a b) 0)
		(< (- (* a b)) (* x y)))
	   (not (integerp (* a b (/ x) (/ y)))))
  :hints (("Goal" :use (:instance not-integerp-4a
				  (a (* a b))
				  (x (* x y)))))
  :rule-classes :type-prescription)

(defthm not-integerp-4r-expt-a
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
                (real/rationalp x)
		(integerp n)
		(real/rationalp y)
		(< (* a b) 0)
		(< (- (* a b)) (* (expt x n) y)))
	   (not (integerp (* a b (expt x (- n)) (/ y)))))
  :hints (("Goal" :use (:instance not-integerp-4a
				  (a (* a b))
				  (x (* (expt x n) y)))))
  :rule-classes :type-prescription)

(defthm not-integerp-4r-expt-b
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
                (real/rationalp x)
		(real/rationalp y)
		(integerp n)
		(< (* a b) 0)
		(< (- (* a b)) (* x (expt y n))))
	   (not (integerp (* a b (/ x) (expt y (- n))))))
  :hints (("Goal" :use (:instance not-integerp-4a
				  (a (* a b))
				  (x (* x (expt y n))))))
  :rule-classes :type-prescription)

(defthm not-integerp-4r-expt-c
  (implies (and ;(real/rationalp a)
                ;(real/rationalp b)
                (real/rationalp x)
		(integerp n1)
		(real/rationalp y)
		(integerp n2)
		(< (* a b) 0)
		(< (- (* a b)) (* (expt x n1) (expt y n2))))
	   (not (integerp (* a b (expt x (- n1)) (expt y (- n2))))))
  :hints (("Goal" :use (:instance not-integerp-4a
				  (a (* a b))
				  (x (* (expt x n1) (expt y n2))))))
  :rule-classes :type-prescription)

(local (in-theory (disable not-integerp-4r
                           not-integerp-4r-expt-a
                           not-integerp-4r-expt-b
                           not-integerp-4r-expt-c
                           )))


(defthm not-integerp-4s
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
                (real/rationalp y)
		(real/rationalp z)
		(< a 0)
		(< (- a) (* x y z)))
	   (not (integerp (* (/ x) (/ y) (/ z) a))))
  :hints (("Goal" :use (:instance not-integerp-4a
                                  (a a)
                                  (x (* x y z)))))
  :rule-classes :type-prescription)

(defthm not-integerp-4s-expt-a
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(integerp n)
                (real/rationalp y)
		(real/rationalp z)
		(< a 0)
		(< (- a) (* (expt x n) y z)))
	   (not (integerp (* (expt x (- n)) (/ y) (/ z) a))))
  :hints (("Goal" :use (:instance not-integerp-4a
                                  (a a)
                                  (x (* (expt x n) y z)))))
  :rule-classes :type-prescription)

(defthm not-integerp-4s-expt-b
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
                (real/rationalp y)
		(integerp n)
		(real/rationalp z)
		(< a 0)
		(< (- a) (* x (expt y n) z)))
	   (not (integerp (* (/ x) (expt y (- n)) (/ z) a))))
  :hints (("Goal" :use (:instance not-integerp-4a
                                  (a a)
                                  (x (* x (expt y n) z)))))
  :rule-classes :type-prescription)

(defthm not-integerp-4s-expt-c
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
                (real/rationalp y)
		(real/rationalp z)
		(integerp n)
		(< a 0)
		(< (- a) (* x y (expt z n))))
	   (not (integerp (* (/ x) (/ y) (expt z (- n)) a))))
  :hints (("Goal" :use (:instance not-integerp-4a
                                  (a a)
                                  (x (* x y (expt z n))))))
  :rule-classes :type-prescription)

(defthm not-integerp-4s-expt-d
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(integerp n1)
                (real/rationalp y)
		(integerp n2)
		(real/rationalp z)
		(< a 0)
		(< (- a) (* (expt x n1) (expt y n2) z)))
	   (not (integerp (* (expt x (- n1)) (expt y (- n2)) (/ z) a))))
  :hints (("Goal" :use (:instance not-integerp-4a
                                  (a a)
                                  (x (* (expt x n1) (expt y n2) z)))))
  :rule-classes :type-prescription)

(defthm not-integerp-4s-expt-e
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(integerp n1)
                (real/rationalp y)
		(real/rationalp z)
		(integerp n2)
		(< a 0)
		(< (- a) (* (expt x n1) y (expt z n2))))
	   (not (integerp (* (expt x (- n1)) (/ y) (expt z (- n2)) a))))
  :hints (("Goal" :use (:instance not-integerp-4a
                                  (a a)
                                  (x (* (expt x n1) y (expt z n2))))))
  :rule-classes :type-prescription)

(defthm not-integerp-4s-expt-f
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
                (real/rationalp y)
		(integerp n1)
		(real/rationalp z)
		(integerp n2)
		(< a 0)
		(< (- a) (* x (expt y n1) (expt z n2))))
	   (not (integerp (* (/ x) (expt y (- n1)) (expt z (- n2)) a))))
  :hints (("Goal" :use (:instance not-integerp-4a
                                  (a a)
                                  (x (* x (expt y n1) (expt z n2))))))
  :rule-classes :type-prescription)

(defthm not-integerp-4s-expt-g
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(integerp n1)
                (real/rationalp y)
		(integerp n2)
		(real/rationalp z)
		(integerp n3)
		(< a 0)
		(< (- a) (* (expt x n1) (expt y n2) (expt z n3))))
	   (not (integerp (* (expt x (- n1)) (expt y (- n2)) (expt z (- n3)) a))))
  :hints (("Goal" :use (:instance not-integerp-4a
                                  (a a)
                                  (x (* (expt x n1) (expt y n2) (expt z n3))))))
  :rule-classes :type-prescription)

(local (in-theory (disable not-integerp-4s
                           not-integerp-4s-expt-a
                           not-integerp-4s-expt-b
                           not-integerp-4s-expt-c
                           not-integerp-4s-expt-d
                           not-integerp-4s-expt-e
                           not-integerp-4s-expt-f
                           not-integerp-4s-expt-g
                           )))


(defthm not-integerp-4t
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
                (real/rationalp y)
		(real/rationalp z)
		(< a 0)
		(< (- a) (* x y z)))
	   (not (integerp (* (/ x) (/ y) a (/ z)))))
  :hints (("Goal" :use not-integerp-4s))
  :rule-classes :type-prescription)

(defthm not-integerp-4t-expt-a
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(integerp n)
                (real/rationalp y)
		(real/rationalp z)
		(< a 0)
		(< (- a) (* (expt x n) y z)))
	   (not (integerp (* (expt x (- n)) (/ y) a (/ z)))))
  :hints (("Goal" :use (:instance not-integerp-4s
				  (x (expt x n)))))
  :rule-classes :type-prescription)

(defthm not-integerp-4t-expt-b
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
                (real/rationalp y)
		(integerp n)
		(real/rationalp z)
		(< a 0)
		(< (- a) (* x (expt y n) z)))
	   (not (integerp (* (/ x) (expt y (- n)) a (/ z)))))
  :hints (("Goal" :use (:instance not-integerp-4s
				  (y (expt y n)))))
  :rule-classes :type-prescription)

(defthm not-integerp-4t-expt-c
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
                (real/rationalp y)
		(real/rationalp z)
		(integerp n)
		(< a 0)
		(< (- a) (* x y (expt z n))))
	   (not (integerp (* (/ x) (/ y) a (expt z (- n))))))
  :hints (("Goal" :use (:instance not-integerp-4s
				  (z (expt z n)))))
  :rule-classes :type-prescription)

(defthm not-integerp-4t-expt-d
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(integerp n1)
                (real/rationalp y)
		(integerp n2)
		(real/rationalp z)
		(< a 0)
		(< (- a) (* (expt x n1) (expt y n2) z)))
	   (not (integerp (* (expt x (- n1)) (expt y (- n2)) a (/ z)))))
  :hints (("Goal" :use (:instance not-integerp-4s
				  (x (expt x n1))
				  (y (expt y n2)))))
  :rule-classes :type-prescription)

(defthm not-integerp-4t-expt-e
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(integerp n1)
                (real/rationalp y)
		(real/rationalp z)
		(integerp n2)
		(< a 0)
		(< (- a) (* (expt x n1) y (expt z n2))))
	   (not (integerp (* (expt x (- n1)) (/ y) a (expt z (- n2))))))
  :hints (("Goal" :use (:instance not-integerp-4s
				  (x (expt x n1))
				  (z (expt z n2)))))
  :rule-classes :type-prescription)

(defthm not-integerp-4t-expt-f
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
                (real/rationalp y)
		(integerp n1)
		(real/rationalp z)
		(integerp n2)
		(< a 0)
		(< (- a) (* x (expt y n1) (expt z n2))))
	   (not (integerp (* (/ x) (expt y (- n1)) a (expt z (- n2))))))
  :hints (("Goal" :use (:instance not-integerp-4s
				  (y (expt y n1))
				  (z (expt z n2)))))
  :rule-classes :type-prescription)

(defthm not-integerp-4t-expt-g
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(integerp n1)
                (real/rationalp y)
		(integerp n2)
		(real/rationalp z)
		(integerp n3)
		(< a 0)
		(< (- a) (* (expt x n1) (expt y n2) (expt z n3))))
	   (not (integerp (* (expt x (- n1)) (expt y (- n2)) a (expt z (- n3))))))
  :hints (("Goal" :use (:instance not-integerp-4s
				  (x (expt x n1))
				  (y (expt y n2))
				  (z (expt z n3)))))
  :rule-classes :type-prescription)

(local (in-theory (disable not-integerp-4t
                           not-integerp-4t-expt-a
                           not-integerp-4t-expt-b
                           not-integerp-4t-expt-c
                           not-integerp-4t-expt-d
                           not-integerp-4t-expt-e
                           not-integerp-4t-expt-f
                           not-integerp-4t-expt-g
                           )))


(defthm not-integerp-4u
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
                (real/rationalp y)
		(real/rationalp z)
		(< a 0)
		(< (- a) (* x y z)))
	   (not (integerp (* (/ x) a (/ y) (/ z)))))
  :hints (("Goal" :use (:instance not-integerp-4s
				  )))
  :rule-classes :type-prescription)

(defthm not-integerp-4u-expt-a
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(integerp n)
                (real/rationalp y)
		(real/rationalp z)
		(< a 0)
		(< (- a) (* (expt x n) y z)))
	   (not (integerp (* (expt x (- n)) a (/ y) (/ z)))))
  :hints (("Goal" :use (:instance not-integerp-4s
				  (x (expt x n)))))
  :rule-classes :type-prescription)

(defthm not-integerp-4u-expt-b
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
                (real/rationalp y)
		(integerp n)
		(real/rationalp z)
		(< a 0)
		(< (- a) (* x (expt y n) z)))
	   (not (integerp (* (/ x) a (expt y (- n)) (/ z)))))
  :hints (("Goal" :use (:instance not-integerp-4s
				  (y (expt y n)))))
  :rule-classes :type-prescription)

(defthm not-integerp-4u-expt-c
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
                (real/rationalp y)
		(real/rationalp z)
		(integerp n)
		(< a 0)
		(< (- a) (* x y (expt z n))))
	   (not (integerp (* (/ x) a (/ y) (expt z (- n))))))
  :hints (("Goal" :use (:instance not-integerp-4s
				  (z (expt z n)))))
  :rule-classes :type-prescription)

(defthm not-integerp-4u-expt-d
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(integerp n1)
                (real/rationalp y)
		(integerp n2)
		(real/rationalp z)
		(< a 0)
		(< (- a) (* (expt x n1) (expt y n2) z)))
	   (not (integerp (* (expt x (- n1)) a (expt y (- n2)) (/ z)))))
  :hints (("Goal" :use (:instance not-integerp-4s
				  (x (expt x n1))
				  (y (expt y n2)))))
  :rule-classes :type-prescription)

(defthm not-integerp-4u-expt-e
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(integerp n1)
                (real/rationalp y)
		(real/rationalp z)
		(integerp n2)
		(< a 0)
		(< (- a) (* (expt x n1) y (expt z n2))))
	   (not (integerp (* (expt x (- n1)) a (/ y) (expt z (- n2))))))
  :hints (("Goal" :use (:instance not-integerp-4s
				  (x (expt x n1))
				  (z (expt z n2)))))
  :rule-classes :type-prescription)

(defthm not-integerp-4u-expt-f
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
                (real/rationalp y)
		(integerp n1)
		(real/rationalp z)
		(integerp n2)
		(< a 0)
		(< (- a) (* x (expt y n1) (expt z n2))))
	   (not (integerp (* (/ x) a (expt y (- n1)) (expt z (- n2))))))
  :hints (("Goal" :use (:instance not-integerp-4s
				  (y (expt y n1))
				  (z (expt z n2)))))
  :rule-classes :type-prescription)

(defthm not-integerp-4u-expt-g
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(integerp n1)
                (real/rationalp y)
		(integerp n2)
		(real/rationalp z)
		(integerp n3)
		(< a 0)
		(< (- a) (* (expt x n1) (expt y n2) (expt z n3))))
	   (not (integerp (* (expt x (- n1)) a (expt y (- n2)) (expt z (- n3))))))
  :hints (("Goal" :use (:instance not-integerp-4s
				  (x (expt x n1))
				  (y (expt y n2))
				  (z (expt z n3)))))
  :rule-classes :type-prescription)

(local (in-theory (disable not-integerp-4u
                           not-integerp-4u-expt-a
                           not-integerp-4u-expt-b
                           not-integerp-4u-expt-c
                           not-integerp-4u-expt-d
                           not-integerp-4u-expt-e
                           not-integerp-4u-expt-f
                           not-integerp-4u-expt-g
                           )))


(defthm not-integerp-4v
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
                (real/rationalp y)
		(real/rationalp z)
		(< a 0)
		(< (- a) (* x y z)))
	   (not (integerp (* a (/ x) (/ y) (/ z)))))
  :hints (("Goal" :use (:instance not-integerp-4s
				  )))
  :rule-classes :type-prescription)

(defthm not-integerp-4v-expt-a
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(integerp n)
                (real/rationalp y)
		(real/rationalp z)
		(< a 0)
		(< (- a) (* (expt x n) y z)))
	   (not (integerp (* a (expt x (- n)) (/ y) (/ z)))))
  :hints (("Goal" :use (:instance not-integerp-4s
				  (x (expt x n)))))
  :rule-classes :type-prescription)

(defthm not-integerp-4v-expt-b
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
                (real/rationalp y)
		(integerp n)
		(real/rationalp z)
		(< a 0)
		(< (- a) (* x (expt y n) z)))
	   (not (integerp (* a (/ x) (expt y (- n)) (/ z)))))
  :hints (("Goal" :use (:instance not-integerp-4s
				  (y (expt y n)))))
  :rule-classes :type-prescription)

(defthm not-integerp-4v-expt-c
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
                (real/rationalp y)
		(real/rationalp z)
		(integerp n)
		(< a 0)
		(< (- a) (* x y (expt z n))))
	   (not (integerp (* a (/ x) (/ y) (expt z (- n))))))
  :hints (("Goal" :use (:instance not-integerp-4s
				  (z (expt z n)))))
  :rule-classes :type-prescription)

(defthm not-integerp-4v-expt-d
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(integerp n1)
                (real/rationalp y)
		(integerp n2)
		(real/rationalp z)
		(< a 0)
		(< (- a) (* (expt x n1) (expt y n2) z)))
	   (not (integerp (* a (expt x (- n1)) (expt y (- n2)) (/ z)))))
  :hints (("Goal" :use (:instance not-integerp-4s
				  (x (expt x n1))
				  (y (expt y n2)))))
  :rule-classes :type-prescription)

(defthm not-integerp-4v-expt-e
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(integerp n1)
                (real/rationalp y)
		(real/rationalp z)
		(integerp n2)
		(< a 0)
		(< (- a) (* (expt x n1) y (expt z n2))))
	   (not (integerp (* a (expt x (- n1)) (/ y) (expt z (- n2))))))
  :hints (("Goal" :use (:instance not-integerp-4s
				  (x (expt x n1))
				  (z (expt z n2)))))
  :rule-classes :type-prescription)

(defthm not-integerp-4v-expt-f
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
                (real/rationalp y)
		(integerp n1)
		(real/rationalp z)
		(integerp n2)
		(< a 0)
		(< (- a) (* x (expt y n1) (expt z n2))))
	   (not (integerp (* a (/ x) (expt y (- n1)) (expt z (- n2))))))
  :hints (("Goal" :use (:instance not-integerp-4s
				  (y (expt y n1))
				  (z (expt z n2)))))
  :rule-classes :type-prescription)

(defthm not-integerp-4v-expt-g
  (implies (and ;(real/rationalp a)
                (real/rationalp x)
		(integerp n1)
                (real/rationalp y)
		(integerp n2)
		(real/rationalp z)
		(integerp n3)
		(< a 0)
		(< (- a) (* (expt x n1) (expt y n2) (expt z n3))))
	   (not (integerp (* a (expt x (- n1)) (expt y (- n2)) (expt z (- n3))))))
  :hints (("Goal" :use (:instance not-integerp-4s
				  (x (expt x n1))
				  (y (expt y n2))
				  (z (expt z n3)))))
  :rule-classes :type-prescription)

(local (in-theory (disable not-integerp-4v
                           not-integerp-4v-expt-a
                           not-integerp-4v-expt-b
                           not-integerp-4v-expt-c
                           not-integerp-4v-expt-d
                           not-integerp-4v-expt-e
                           not-integerp-4v-expt-f
                           not-integerp-4v-expt-g
                           )))

(deftheory not-integerp-type-set-rules
  '(not-integerp-1a
    not-integerp-1a-expt
    not-integerp-1b
    not-integerp-1b-expt
    not-integerp-1d
    not-integerp-1d-expt
    not-integerp-1e
    not-integerp-1e-expt
    not-integerp-1f
    not-integerp-1f-expt-a
    not-integerp-1f-expt-b
    not-integerp-1f-expt-c
    not-integerp-1g
    not-integerp-1g-expt-a
    not-integerp-1g-expt-b
    not-integerp-1g-expt-c
    not-integerp-1h
    not-integerp-1h-expt-a
    not-integerp-1h-expt-b
    not-integerp-1h-expt-c
    not-integerp-1k
    not-integerp-1k-expt
    not-integerp-1l
    not-integerp-1l-expt
    not-integerp-1n
    not-integerp-1n-expt-a
    not-integerp-1n-expt-b
    not-integerp-1n-expt-c
    not-integerp-1o
    not-integerp-1o-expt-a
    not-integerp-1o-expt-b
    not-integerp-1o-expt-c
    not-integerp-1p
    not-integerp-1p-expt-a
    not-integerp-1p-expt-b
    not-integerp-1p-expt-c
    not-integerp-1q
    not-integerp-1q-expt-a
    not-integerp-1q-expt-b
    not-integerp-1q-expt-c
    not-integerp-1r
    not-integerp-1r-expt-a
    not-integerp-1r-expt-b
    not-integerp-1r-expt-c
    not-integerp-1s
    not-integerp-1s-expt-a
    not-integerp-1s-expt-b
    not-integerp-1s-expt-c
    not-integerp-1s-expt-d
    not-integerp-1s-expt-e
    not-integerp-1s-expt-f
    not-integerp-1s-expt-g
    not-integerp-1t
    not-integerp-1t-expt-a
    not-integerp-1t-expt-b
    not-integerp-1t-expt-c
    not-integerp-1t-expt-d
    not-integerp-1t-expt-e
    not-integerp-1t-expt-f
    not-integerp-1t-expt-g
    not-integerp-1u
    not-integerp-1u-expt-a
    not-integerp-1u-expt-b
    not-integerp-1u-expt-c
    not-integerp-1u-expt-d
    not-integerp-1u-expt-e
    not-integerp-1u-expt-f
    not-integerp-1u-expt-g
    not-integerp-1v
    not-integerp-1v-expt-a
    not-integerp-1v-expt-b
    not-integerp-1v-expt-c
    not-integerp-1v-expt-d
    not-integerp-1v-expt-e
    not-integerp-1v-expt-f
    not-integerp-1v-expt-g
    not-integerp-2a
    not-integerp-2a-expt
    not-integerp-2b
    not-integerp-2b-expt
    not-integerp-2d
    not-integerp-2d-expt
    not-integerp-2e
    not-integerp-2e-expt
    not-integerp-2f
    not-integerp-2f-expt-a
    not-integerp-2f-expt-b
    not-integerp-2f-expt-c
    not-integerp-2g
    not-integerp-2g-expt-a
    not-integerp-2g-expt-b
    not-integerp-2g-expt-c
    not-integerp-2h
    not-integerp-2h-expt-a
    not-integerp-2h-expt-b
    not-integerp-2h-expt-c
    not-integerp-2k
    not-integerp-2k-expt
    not-integerp-2l
    not-integerp-2l-expt
    not-integerp-2n
    not-integerp-2n-expt-a
    not-integerp-2n-expt-b
    not-integerp-2n-expt-c
    not-integerp-2o
    not-integerp-2o-expt-a
    not-integerp-2o-expt-b
    not-integerp-2o-expt-c
    not-integerp-2p
    not-integerp-2p-expt-a
    not-integerp-2p-expt-b
    not-integerp-2p-expt-c
    not-integerp-2q
    not-integerp-2q-expt-a
    not-integerp-2q-expt-b
    not-integerp-2q-expt-c
    not-integerp-2r
    not-integerp-2r-expt-a
    not-integerp-2r-expt-b
    not-integerp-2r-expt-c
    not-integerp-2s
    not-integerp-2s-expt-a
    not-integerp-2s-expt-b
    not-integerp-2s-expt-c
    not-integerp-2s-expt-d
    not-integerp-2s-expt-e
    not-integerp-2s-expt-f
    not-integerp-2s-expt-g
    not-integerp-2t
    not-integerp-2t-expt-a
    not-integerp-2t-expt-b
    not-integerp-2t-expt-c
    not-integerp-2t-expt-d
    not-integerp-2t-expt-e
    not-integerp-2t-expt-f
    not-integerp-2t-expt-g
    not-integerp-2u
    not-integerp-2u-expt-a
    not-integerp-2u-expt-b
    not-integerp-2u-expt-c
    not-integerp-2u-expt-d
    not-integerp-2u-expt-e
    not-integerp-2u-expt-f
    not-integerp-2u-expt-g
    not-integerp-2v
    not-integerp-2v-expt-a
    not-integerp-2v-expt-b
    not-integerp-2v-expt-c
    not-integerp-2v-expt-d
    not-integerp-2v-expt-e
    not-integerp-2v-expt-f
    not-integerp-2v-expt-g
    not-integerp-3a
    not-integerp-3a-expt
    not-integerp-3b
    not-integerp-3b-expt
    not-integerp-3d
    not-integerp-3d-expt
    not-integerp-3e
    not-integerp-3e-expt
    not-integerp-3f
    not-integerp-3f-expt-a
    not-integerp-3f-expt-b
    not-integerp-3f-expt-c
    not-integerp-3g
    not-integerp-3g-expt-a
    not-integerp-3g-expt-b
    not-integerp-3g-expt-c
    not-integerp-3h
    not-integerp-3h-expt-a
    not-integerp-3h-expt-b
    not-integerp-3h-expt-c
    not-integerp-3k
    not-integerp-3k-expt
    not-integerp-3l
    not-integerp-3l-expt
    not-integerp-3n
    not-integerp-3n-expt-a
    not-integerp-3n-expt-b
    not-integerp-3n-expt-c
    not-integerp-3o
    not-integerp-3o-expt-a
    not-integerp-3o-expt-b
    not-integerp-3o-expt-c
    not-integerp-3p
    not-integerp-3p-expt-a
    not-integerp-3p-expt-b
    not-integerp-3p-expt-c
    not-integerp-3q
    not-integerp-3q-expt-a
    not-integerp-3q-expt-b
    not-integerp-3q-expt-c
    not-integerp-3r
    not-integerp-3r-expt-a
    not-integerp-3r-expt-b
    not-integerp-3r-expt-c
    not-integerp-3s
    not-integerp-3s-expt-a
    not-integerp-3s-expt-b
    not-integerp-3s-expt-c
    not-integerp-3s-expt-d
    not-integerp-3s-expt-e
    not-integerp-3s-expt-f
    not-integerp-3s-expt-g
    not-integerp-3t
    not-integerp-3t-expt-a
    not-integerp-3t-expt-b
    not-integerp-3t-expt-c
    not-integerp-3t-expt-d
    not-integerp-3t-expt-e
    not-integerp-3t-expt-f
    not-integerp-3t-expt-g
    not-integerp-3u
    not-integerp-3u-expt-a
    not-integerp-3u-expt-b
    not-integerp-3u-expt-c
    not-integerp-3u-expt-d
    not-integerp-3u-expt-e
    not-integerp-3u-expt-f
    not-integerp-3u-expt-g
    not-integerp-3v
    not-integerp-3v-expt-a
    not-integerp-3v-expt-b
    not-integerp-3v-expt-c
    not-integerp-3v-expt-d
    not-integerp-3v-expt-e
    not-integerp-3v-expt-f
    not-integerp-3v-expt-g
    not-integerp-4a
    not-integerp-4a-expt
    not-integerp-4b
    not-integerp-4b-expt
    not-integerp-4d
    not-integerp-4d-expt
    not-integerp-4e
    not-integerp-4e-expt
    not-integerp-4f
    not-integerp-4f-expt-a
    not-integerp-4f-expt-b
    not-integerp-4f-expt-c
    not-integerp-4g
    not-integerp-4g-expt-a
    not-integerp-4g-expt-b
    not-integerp-4g-expt-c
    not-integerp-4h
    not-integerp-4h-expt-a
    not-integerp-4h-expt-b
    not-integerp-4h-expt-c
    not-integerp-4k
    not-integerp-4k-expt
    not-integerp-4l
    not-integerp-4l-expt
    not-integerp-4n
    not-integerp-4n-expt-a
    not-integerp-4n-expt-b
    not-integerp-4n-expt-c
    not-integerp-4o
    not-integerp-4o-expt-a
    not-integerp-4o-expt-b
    not-integerp-4o-expt-c
    not-integerp-4p
    not-integerp-4p-expt-a
    not-integerp-4p-expt-b
    not-integerp-4p-expt-c
    not-integerp-4q
    not-integerp-4q-expt-a
    not-integerp-4q-expt-b
    not-integerp-4q-expt-c
    not-integerp-4r
    not-integerp-4r-expt-a
    not-integerp-4r-expt-b
    not-integerp-4r-expt-c
    not-integerp-4s
    not-integerp-4s-expt-a
    not-integerp-4s-expt-b
    not-integerp-4s-expt-c
    not-integerp-4s-expt-d
    not-integerp-4s-expt-e
    not-integerp-4s-expt-f
    not-integerp-4s-expt-g
    not-integerp-4t
    not-integerp-4t-expt-a
    not-integerp-4t-expt-b
    not-integerp-4t-expt-c
    not-integerp-4t-expt-d
    not-integerp-4t-expt-e
    not-integerp-4t-expt-f
    not-integerp-4t-expt-g
    not-integerp-4u
    not-integerp-4u-expt-a
    not-integerp-4u-expt-b
    not-integerp-4u-expt-c
    not-integerp-4u-expt-d
    not-integerp-4u-expt-e
    not-integerp-4u-expt-f
    not-integerp-4u-expt-g
    not-integerp-4v
    not-integerp-4v-expt-a
    not-integerp-4v-expt-b
    not-integerp-4v-expt-c
    not-integerp-4v-expt-d
    not-integerp-4v-expt-e
    not-integerp-4v-expt-f
    not-integerp-4v-expt-g))



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

(defun reduce-integerp-+-fn-1 (x intp-flag mfc state)
  (declare (xargs :guard (eq (fn-symb x) 'BINARY-+)))

  ;; X is a sum.  We look for the first addend which is proveably an
  ;; integer.  (Or rational if intp-flag is false.)  We return an
  ;; alist binding Z to the negation of the found addend.

  (cond ((and (not (equal (arg1 x) ''0)) ; Prevent possible loops
	      (if intp-flag
		  (proveably-integer 'x `((x . ,(arg1 x))) mfc state)
		(proveably-real/rational 'x `((x . ,(arg1 x))) mfc state))
	      ;; prevent various odd loops
	      (stable-under-rewriting-sums (negate-match (arg1 x))
					   mfc state))
	 (list (cons 'z (negate-match (arg1 x)))))
	((eq (fn-symb (arg2 x)) 'BINARY-+)
	 (reduce-integerp-+-fn-1 (arg2 x) intp-flag mfc state))
	((and (not (equal (arg2 x) ''0))
	      (if intp-flag
		  (proveably-integer 'x `((x . ,(arg2 x))) mfc state)
		(proveably-real/rational 'x `((x . ,(arg2 x))) mfc state))
	      (stable-under-rewriting-sums (negate-match (arg2 x))
					   mfc state))
	 (list (cons 'z (negate-match (arg2 x)))))
	(t
	 nil)))

(defun reduce-integerp-+-fn (x intp-flag mfc state)
  (declare (xargs :guard t))

  (if (eq (fn-symb x) 'BINARY-+)
      (reduce-integerp-+-fn-1 x intp-flag mfc state)
    nil))

(local
 (defthm iff-integerp
     (equal (equal (integerp x)
                   (integerp y))
            (iff (integerp x)
                 (integerp y)))))

(local
 (defthm iff-rationalp
     (equal (equal (real/rationalp x)
                   (real/rationalp y))
            (iff (real/rationalp x)
                 (real/rationalp y)))))

#+non-standard-analysis
(local
 (defthm iff-rationalp
     (equal (equal (real/rationalp x)
                   (real/rationalp y))
            (iff (real/rationalp x)
                 (real/rationalp y)))))

;;; In the right hand side of the conclusion below, if x is a sum and
;;; we can find an addend of x which is proveably an integer, we
;;; remove that addend from the sum.  The finding of the (negation of
;;; the) addend is done by the bind-free hypothesis.

;;; Note: The use of rewriting-goal-literal ensures that we do not use
;;; this while backchaining --- it does not seem worthwhile to go
;;; through all this work unless we can decide the qustion one way or
;;; another, and meta-integerp would have done that if it could.

(defthm reduce-integerp-+
    (implies (and (syntaxp (rewriting-goal-literal x mfc state))
		  (syntaxp (in-term-order-+ x mfc state))
                  (bind-free (reduce-integerp-+-fn x t mfc state)
                             (z))
                  (integerp z)
                  (acl2-numberp x))
             (equal (integerp x)
                    (integerp (+ z x)))))

(defthm reduce-rationalp-+
    (implies (and (syntaxp (rewriting-goal-literal x mfc state))
                  (syntaxp (in-term-order-+ x mfc state))
                  (bind-free (reduce-integerp-+-fn x nil mfc state)
                             (z))
                  (rationalp z)
                  (acl2-numberp x))
             (equal (real/rationalp x)
                    (real/rationalp (+ z x)))))

#+non-standard-analysis
(defthm reduce-real/rationalp-+
    (implies (and (syntaxp (rewriting-goal-literal x mfc state))
                  (syntaxp (in-term-order-+ x mfc state))
                  (bind-free (reduce-integerp-+-fn x nil mfc state)
                             (z))
                  (real/rationalp z)
                  (acl2-numberp x))
             (equal (real/rationalp x)
                    (real/rationalp (+ z x)))))

;;; We repeat the above for removing rational factors from a
;;; product, when we are deciding rationalp.

(defun reduce-rationalp-*-fn-1 (x mfc state)
  (declare (xargs :guard (eq (fn-symb x) 'BINARY-*)))

  (cond ((and (not (equal (arg1 x) ''1)) ; Prevent possible loops
	      (proveably-non-zero-rational 'x `((x . ,(arg1 x))) mfc state)
	      ;; prevent various odd loops
	      (stable-under-rewriting-products (invert-match (arg1 x))
					       mfc state))
	 (list (cons 'z (invert-match (arg1 x)))))
	((eq (fn-symb (arg2 x)) 'BINARY-*)
	 (reduce-rationalp-*-fn-1 (arg2 x) mfc state))
	((and (not (equal (arg2 x) ''1))
	      (proveably-non-zero-rational 'x `((x . ,(arg2 x))) mfc state)
	      (stable-under-rewriting-products (invert-match (arg2 x))
					       mfc state))
	 (list (cons 'z (invert-match (arg2 x)))))
	(t
	 nil)))

#+non-standard-analysis
(defun reduce-real/rationalp-*-fn-1 (x mfc state)
  (declare (xargs :guard (eq (fn-symb x) 'BINARY-*)))

  (cond ((and (not (equal (arg1 x) ''1)) ; Prevent possible loops
	      (proveably-non-zero-real/rational 'x `((x . ,(arg1 x))) mfc state)
	      ;; prevent various odd loops
	      (stable-under-rewriting-products (invert-match (arg1 x))
					       mfc state))
	 (list (cons 'z (invert-match (arg1 x)))))
	((eq (fn-symb (arg2 x)) 'BINARY-*)
	 (reduce-real/rationalp-*-fn-1 (arg2 x) mfc state))
	((and (not (equal (arg2 x) ''1))
	      (proveably-non-zero-rational 'x `((x . ,(arg2 x))) mfc state)
	      (stable-under-rewriting-products (invert-match (arg2 x))
					       mfc state))
	 (list (cons 'z (invert-match (arg2 x)))))
	(t
	 nil)))

(defun reduce-rationalp-*-fn (x mfc state)
  (declare (xargs :guard t))

  (if (eq (fn-symb x) 'BINARY-*)
      (reduce-rationalp-*-fn-1 x mfc state)
    nil))

#+non-standard-analysis
(defun reduce-real/rationalp-*-fn (x mfc state)
  (declare (xargs :guard t))

  (if (eq (fn-symb x) 'BINARY-*)
      (reduce-real/rationalp-*-fn-1 x mfc state)
    nil))

;;; One might want to redo the below, splitting into two rules ---
;;; the first as below but limited to not rewriting-goal-literal,
;;; and the second using a weaker reduce-rationalp-*-fn where
;;; we do not test for zero but rather do a case-split on the
;;; (not (equal z 0)) hyp.  This will probably be too expensive
;;; but might be worth trying some day.

(defthm reduce-rationalp-*
    (implies (and (syntaxp (rewriting-goal-literal x mfc state))
                  (syntaxp (in-term-order-* x mfc state))
                  (bind-free (reduce-rationalp-*-fn x mfc state)
                             (z))
                  (rationalp z)
		  (not (equal z 0))
                  (acl2-numberp x))
             (equal (real/rationalp x)
                    (real/rationalp (* z x)))))

#+non-standard-analysis
(defthm reduce-real/rationalp-*
    (implies (and (syntaxp (rewriting-goal-literal x mfc state))
                  (syntaxp (in-term-order-* x mfc state))
                  (bind-free (reduce-real/rationalp-*-fn x mfc state)
                             (z))
                  (real/rationalp z)
		  (not (equal z 0))
                  (acl2-numberp x))
             (equal (real/rationalp x)
                    (real/rationalp (* z x)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Note that we put rules such as |(integerp (- x))| after rules such
;;; as not-integerp-1a.  ACL2 uses rules ``most recently seen first.''
;;; Thus we place rules that simplify or normalize terms before those
;;; that decide their validity.  This will allow the latter rules to
;;; make certain simple assumptions about the forms of the terms they
;;; see.

;;; The rule integerp-minus-x replaces (integerp (- x)) with
;;; (integerp x) We use negative-addends-p to handle the more general
;;; situation, e.g., (integerp (+ 3 (- x) (* -7 y))).

(defthm integerp-minus-x
    (implies (and (syntaxp (weak-mostly-negative-addends-p x mfc state))
                  (acl2-numberp x))
             (equal (integerp x)
                    (integerp (- x)))))

(defthm rationalp-minus-x
    (implies (and (syntaxp (weak-mostly-negative-addends-p x mfc state))
                  (acl2-numberp x))
             (equal (real/rationalp x)
                    (real/rationalp (- x)))))

#+non-standard-analysis
(defthm real/rationalp-minus-x
    (implies (and (syntaxp (weak-mostly-negative-addends-p x mfc state))
                  (acl2-numberp x))
             (equal (real/rationalp x)
                    (real/rationalp (- x)))))

;;; No longer needed as of ACL2 ... due to improved type-set reasoning.

#|
(defun find-integerp-hyp-1 (type-alist c x)
  (declare (xargs :guard (type-alistp type-alist)))

  ;; We look in the type-alist for a term of the form
  ;; (integerp (* d x)) which is assumed true, where
  ;; c divided by d is an integer.  We return both d
  ;; and (/ c d) in a manner suitable for bind-free.

  (cond ((endp type-alist)
         nil)
        ((let ((typed-term (caar type-alist))
               (type (cadar type-alist)))
           (and (eq (fn-symb typed-term) 'BINARY-*)
                (quotep (arg1 typed-term))
                (equal (arg2 typed-term) x)
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
  (find-integerp-hyp-1 c x (mfc-type-alist mfc)))

;;; Think of |(integerp (* c x))| as the following rule:
;;; (implies (and (integerp (* d x))
;;;               (integerp (/ c d)))
;;;          (integerp (* c x)))
;;;
;;; A couple of examples of its use:
;;;
;;; (implies (integerp (* 1/4 x))
;;;          (integerp (* 3/4 x)))
;;;
;;; (implies (integerp (* 1/4 x))
;;;          (integerp (* 1/2 x)))

(defthm |(integerp (* c x))|
    (implies (and (syntaxp (in-term-order-* `(BINARY-* ,c ,x) mfc state))
                  (bind-free (find-integerp-hyp c x mfc state)
                             (d a))
                  (equal (* d a) c)  ; a = c/d
                  (integerp (* d x))
                  (integerp a))  ; a = c/d
             (integerp (* c x))))
|#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#|
;;; I do not need this rule anymore.  See |(expt (/ x) n)| in
;;; basic.lisp.  I leave it in anyway in case I later change
;;; |(expt (/ x) n)|.

;;; The neccesity of this rule points out a problem with my current
;;; treatment of expt.  I should probably treat expt as ``above'' the
;;; other ``fundamental'' arithmetic operations --- +, -, *, /.  I
;;; have, up till now, been thinking of expt as a fancy or
;;; paramterized multiplication insead of treating it in its own
;;; right.

;;; The form of this rule also points out a flaw in my normalization
;;; procedures with respect to division and expt.  Better would
;;; probably be something like (* x (/ (expt x n))), and then the
;;; above rules would cover this case also.

(defthm nintegerp-extra
    (implies (and (real/rationalp x)
                  (< 0 x)
                  (real/rationalp y)
                  (< 0 y)
                  (integerp n)
                  (< 0 n)
                  (< x (expt y n)))
             (not (integerp (* x (expt (/ y) n))))))
|#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; A couple of neat rules taken from the RTL books.  These are
;;; due to Eric Smith.

;;; Subtract the integer part from any leading constants via
;;; the (- (floor c 1)).  We thus reduce expressions of the form
;;; (integerp (+ c x)), where c is a rational constant, to the
;;; form (integerp (+ d x)) where d is a rational constant
;;; between 0 and 1.

(local
 (defthm integerp-helper
   (implies (integerp x)
	    (equal (integerp (+ y z x))
		   (integerp (+ y z))))))


(defthm integerp-+-reduce-constant
  (implies (and (syntaxp (rational-constant-p c))
                (syntaxp (or (<= 1 (unquote c))
                             (< (unquote c) 0))))
           (equal (integerp (+ c x))
                  (integerp (+ (+ c (- (floor c 1))) x))))
  :hints (("Goal" :in-theory (disable floor))))

;;; Do I want to make something like X-OR-X/2 a forward-chaining rule?
;;; Maybe:
#|
(implies (and (integerp x)
	      (not (integerp (* 1/2 x))))
	 (integerp (+ 1/2 (* 1/2 x))))

(implies (and (integerp x)
	      (not (integerp (+ 1/2 (* 1/2 x)))))
	 (integerp (* 1/2 x)))
|#

;;; Expressions like (integerp (+ 1/2 x)) show up when one is reasoning
;;; about odd and even.

;;; Note1: We do not have to worry about expressions such as
;;; (integerp (+ -1/2 x)) or (integerp (+ 3/2 x)) because of
;;; integerp-+-reduce-leading-constant.

;;; Note 2: We could write a similar rule --- probably a meta rule
;;; --- for expressions such as (integerp (+ 1/3 x)) and
;;; (integerp (+ 3/10 x)).  For (integerp (+ c/d x)), (* n x) is not
;;; an integer for all 0 < n < d.  But this would probably be a messy
;;; proof to do --- it would depend on c/d being in lowest terms ---
;;; but I have not thought about it yet.

(defthm even-and-odd-alternate
  (implies (acl2-numberp x)
	   (equal (integerp (+ 1/2 x))
		  (and (integerp (* 2 x))
		       (not (integerp x))))))

;;; We also see terms such as (INTEGERP (+ (* 1/2 X) (* 1/2 Y)))

;;; Note that the other corollary, when x and y are both even, should
;;; be caught by integerp-meta, and so is not needed.

;;; RBK: The below should probably be generalized for when the
;;; constants are of the form c/2, where c is an odd integer.

(defthm sum-is-even
  (implies (and (syntaxp (rewriting-goal-literal x mfc state))
		(integerp x)
		(integerp y))
	   (equal (integerp (+ (* 1/2 x) (* 1/2 y)))
		  (if (integerp (* 1/2 x))
		      (integerp (* 1/2 y))
		    (not (integerp (* 1/2 y))))))
  :rule-classes ((:rewrite)
		 (:rewrite
		  :corollary
		  (implies (and (integerp x)
				(integerp y)
				(not (integerp (* 1/2 x)))
				(not (integerp (* 1/2 y))))
			   (integerp (+ (* 1/2 x) (* 1/2 y)))))))

