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

(defund fl (x)
  (declare (xargs :guard (real/rationalp x)))
  (floor x 1))

(include-book "ground-zero")
(local (include-book "logior"))
(local (include-book "../../arithmetic/fl"))
(local (include-book "lognot"))

(defthm floor-logorc1-by-2
  (implies (and (case-split (integerp i))
                (case-split (integerp j))
                )
           (equal (floor (logorc1 i j) 2)
                  (logorc1 (floor i 2) (floor j 2))))
  :hints (("Goal" :in-theory (enable logorc1))))

(defthm fl-logorc1-by-2
  (implies (and (case-split (integerp i))
                (case-split (integerp j))
                )
           (equal (fl (* 1/2 (logorc1 i j)))
                  (logorc1 (fl (* 1/2 i)) (fl (* 1/2 j)))))
  :hints (("Goal" :in-theory (enable logorc1))))

#| not true
(defthm mod-LOGORC1
  (implies (and (case-split (integerp i))
                (case-split (integerp j))
                )
           (equal (mod (logorc1 i j) 2)
                  (logorc1 (mod i 2) (mod j 2))))
  :hints (("Goal" :in-theory (enable logorc1))))
|#

#|

(local
(defthm logorc1-mod-1
    (implies (and (integerp i) (integerp j))
	     (iff (= (mod (logorc1 i j) 2) 0)
		  (and (= (mod (lognot i) 2) 0)
		       (= (mod j 2) 0))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable logior lognot)
		  :use ((:instance mod-logior-10 (i (lognot i))))))))

(local(defthm logorc1-mod
    (implies (and (integerp i) (>= i 0)
		  (integerp j))
	     (iff (= (mod (logorc1 i j) 2) 0)
		  (and (= (mod i 2) 1)
		       (= (mod j 2) 0))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable logior lognot)
		  :use ((:instance mod-logior-9)
			(:instance logorc1-mod-1)
			(:instance mod012 (x i)))))))
|#

(defthm logorc1-type
  (implies (and (<= 0 i)
                (<= 0 j))
           (< (logorc1 i j) 0))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable logorc1 lognot))))

