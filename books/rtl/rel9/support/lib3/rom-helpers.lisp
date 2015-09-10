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

(in-package "ACL2")

(set-enforce-redundancy t)

(local (include-book "../../support/support/rom-helpers"))

(defund bvecp (x k)
  (declare (xargs :guard (integerp k)))
  (and (integerp x)
       (<= 0 x)
       (< x (expt 2 k))))
(local (in-theory (enable bvecp)))

(defun natp (x)
  (declare (xargs :guard t))
  (and (integerp x)
       (<= 0 x)))

(defun check-array (name a dim1 dim2)
  (if (zp dim1)
      t
    (and (bvecp (aref1 name a (1- dim1)) dim2)
	 (check-array name a (1- dim1) dim2))))

(defthm check-array-lemma-1
    (implies (and (not (zp dim1))
		  (check-array name a dim1 dim2)
		  (natp i)
		  (< i dim1))
	     (bvecp (aref1 name a i) dim2))
  :rule-classes ())

(defthm check-array-lemma
    (implies (and (bvecp i n)
		  (not (zp (expt 2 n)))
		  (check-array name a (expt 2 n) dim2))
	     (bvecp (aref1 name a i) dim2))
  :rule-classes ())


