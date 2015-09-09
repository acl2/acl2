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

(defund bvecp (x k)
  (declare (xargs :guard (integerp k)))
  (and (integerp x)
       (<= 0 x)
       (< x (expt 2 k))))

(local ; ACL2 primitive
 (defun natp (x)
   (declare (xargs :guard t))
   (and (integerp x)
        (<= 0 x))))

(defund fl (x)
  (declare (xargs :guard (real/rationalp x)))
  (floor x 1))

(defund bits (x i j)
  (declare (xargs :guard (and (natp x)
                              (natp i)
                              (natp j))
                  :verify-guards nil))
  (mbe :logic (if (or (not (integerp i))
                      (not (integerp j)))
                  0
                (fl (/ (mod x (expt 2 (1+ i))) (expt 2 j))))
       :exec  (if (< i j)
                  0
                (logand (ash x (- j)) (1- (ash 1 (1+ (- i j))))))))

(defund bitn (x n)
  (declare (xargs :guard (and (natp x)
                              (natp n))
                  :verify-guards nil))
  (mbe :logic (bits x n n)
       :exec  (if (evenp (ash x (- n))) 0 1)))

(include-book "cat-def")
(local (include-book "mulcat-proofs"))

(defund mulcat (l n x)

; We introduce mbe not because we want particularly fast execution, but because
; the existing logic definition does not satisfy the guard of cat, which can't
; be changed because of the guard of bits.

  (declare (xargs :guard (and (integerp l)
                              (< 0 l)
                              (acl2-numberp n)
                              (natp x))
                  :verify-guards nil))
  (mbe :logic (if (and (integerp n) (> n 0))
                  (cat (mulcat l (1- n) x)
                       (* l (1- n))
                       x
                       l)
                0)
       :exec  (cond
               ((eql n 1)
                (bits x (1- l) 0))
               ((and (integerp n) (> n 0))
                (cat (mulcat l (1- n) x)
                     (* l (1- n))
                     x
                     l))
               (t 0))))

(defthm mulcat-nonnegative-integer-type
  (and (integerp (mulcat l n x))
       (<= 0 (mulcat l n x)))
  :rule-classes (:type-prescription))

;this rule is no better than mulcat-nonnegative-integer-type and might be worse:
(in-theory (disable (:type-prescription mulcat)))

(defthm mulcat-1
    (implies (natp l)
	     (equal (mulcat l 1 x) 
		    (bits x (1- l) 0))))

(defthm mulcat-bvecp-simple
  (implies (and (= p (* l n))
                (case-split (natp l)))
           (bvecp (mulcat l n x) p))
  :rule-classes ())

(defthm mulcat-bvecp
  (implies (and (>= p (* l n))
                (case-split (integerp p))
                (case-split (natp l)))
           (bvecp (mulcat l n x) p)))

(defthm mulcat-0
  (equal (mulcat l n 0) 
         0))

(defthm mulcat-0-two
  (equal (mulcat l 0 x) 
         0))

(defthm bvecp-mulcat-1
    (implies (natp n)
	     (bvecp (mulcat 1 n 1) n))
  :rule-classes ())

(defthm mulcat-n-1
    (implies (case-split (<= 0 n))
	     (equal (mulcat 1 n 1)
		    (1- (expt 2 n)))))

(defun mulcat-induct (n n2)
  (if (and (integerp n) (> n 0) (integerp n2) (> n2 0))
      (mulcat-induct (1- n) (1- n2))
      0))

;BOZO prove a bits-mulcat? could be used to prove-bitn-mulcat

;BOZO generalize to bits of mulcat when x is larger than 1?
;not general (note the 1 for the l parameter)
;and to when (<= n m)
;add to lib/ ?
(defthm bitn-mulcat-1
  (implies (and (< m n)
                (case-split (bvecp x 1))
                (case-split (natp m))
                (case-split (integerp n)) ;(case-split (natp n))
                )
           (equal (bitn (mulcat 1 n x) m)
                  x)))

(defthm bitn-mulcat-2
  (implies (and (<= (* l n) n2)
                (natp n)
                (natp l)
                (natp n2)
                (case-split (bvecp x l))
                )
           (equal (bitn (mulcat l n x) n2)
                  0)))

(defthmd mulcat-bits
  (implies (and (integerp l)
                (integerp x))
           (equal (mulcat l n (bits x (1- l) 0))
                  (mulcat l n x))))
