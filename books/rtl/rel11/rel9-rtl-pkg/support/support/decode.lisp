; RTL - A Formal Theory of Register-Transfer Logic and Computer Arithmetic
; Copyright (C) 1995-2013 Advanced Mirco Devices, Inc.
;
; Contact:
;   David Russinoff
;   http://www.russinoff.com/
;
; See license file books/rtl/rel9/license.txt.
;
; Author: David M. Russinoff (david@russinoff.com)

(in-package "RTL")

(include-book "ground-zero")

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

(local (include-book "decode-proofs"))


(defund decode (x n)
  (declare (xargs :guard (rationalp n)))
  (if (and (natp x) (< x n))
      (ash 1 x)
    0))

(defthm decode-nonnegative-integer-type
  (and (integerp (decode x n))
       (<= 0 (decode x n)))
  :rule-classes (:type-prescription))

;this rule is no better than decode-nonnegative-integer-type and might be worse:
(in-theory (disable (:type-prescription decode)))

(defthm decode-natp
  (natp (decode x n)))

(defthm decode-bvecp
  (implies (and (<= n k)
                (case-split (integerp k))
                )
           (bvecp (decode x n) k)))

