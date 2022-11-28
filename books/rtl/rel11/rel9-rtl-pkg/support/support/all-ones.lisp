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

(defund all-ones (n)
  (declare (xargs :guard (and (integerp n) (<= 0 n))))
  (if (zp n)
      0 ;degenerate case
    (1- (expt 2 n))))

(defthm all-ones-of-non-integer
  (implies (not (integerp n))
           (equal (all-ones n)
                  0))
  :hints (("Goal" :in-theory (enable all-ones))))

(defthm all-ones-of-negative
  (implies (< n 0)
           (equal (all-ones n)
                  0))
  :hints (("Goal" :in-theory (enable all-ones))))
