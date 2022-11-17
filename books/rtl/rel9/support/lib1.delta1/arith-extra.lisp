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

(in-package "ACL2")

(include-book "../lib1/arith")
(local (include-book "../../arithmetic/top"))

(defthm expt-positive-integer-type
    (implies (and (integerp a)
		  (integerp i)
		  (>= i 0))
	     (integerp (expt a i)))
  :rule-classes (:type-prescription)
  :hints (("Goal" :in-theory (enable expt))))


