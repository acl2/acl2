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

(local ; ACL2 primitive
 (defun natp (x)
   (declare (xargs :guard t))
   (and (integerp x)
        (<= 0 x))))

(defund bvecp (x k)
  (declare (xargs :guard (integerp k)))
  (and (integerp x)
       (<= 0 x)
       (< x (expt 2 k))))

(defund fl (x)
  (declare (xargs :guard (real/rationalp x)))
  (floor x 1))


(local (include-book "../../arithmetic/top"))

(defund shft (x s l)
  (declare (xargs :guard (and (integerp s) (rationalp x))))
  (mod (fl (* (expt 2 s) x)) (expt 2 (nfix l))))

(defthm shft-nonnegative-integer-type
  (and (integerp (shft x s l))
       (<= 0 (shft x s l)))
  :rule-classes (:type-prescription))

;(:type-prescription shft) is no better than shft-nonnegative-integer-type and might be worse:
(in-theory (disable (:type-prescription shft)))

(defthm shft-natp
  (natp (shft x s n)))

(defthm shft-bvecp-simple
  (bvecp (shft x s n) n)
  :hints (("Goal" :in-theory (enable bvecp shft))))

(local (include-book "bvecp"))

(defthm shft-bvecp
  (implies (and (<= n k)
                (case-split (integerp k)))
           (bvecp (shft x s n) k))
  :hints (("Goal" :in-theory (disable shft-bvecp-simple)
           :use shft-bvecp-simple)))



