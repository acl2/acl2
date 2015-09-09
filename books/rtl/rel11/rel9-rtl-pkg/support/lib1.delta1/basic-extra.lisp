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

(include-book "../lib1/basic")
(include-book "../../arithmetic/floor")


(local (in-theory (disable mod floor)))
(local (include-book "../../arithmetic/top"))

;;;**********************************************************************
;;;                       FLOOR and CEILING
;;;**********************************************************************

;;; <same>

;;;**********************************************************************
;;;                         MOD
;;;**********************************************************************


(defthm natp-mod-2
  (implies (and (integerp m)
                (integerp n)
                (> n 0))
           (natp (mod m n)))
  :rule-classes ((:type-prescription :typed-term (mod m n))))


(defthm mod-mod-times
    (implies (and (integerp a)
		  (integerp b)
		  (integerp n)
		  (> n 0))
	     (= (mod (* (mod a n) b) n)
		(mod (* a b) n)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance mod-equal-int-reverse (a (* (mod a n) b)) (b (* a b)))
			(:instance mod-does-nothing (m a))
			(:instance mod-bnd-1 (m a))
			(:instance natp-mod-2 (m a))
			(:instance mod-equal-int (b (mod a n)))
			(:instance integerp-prod (x (/ (- a (mod a n)) n)) (y (- b)))))))



(defthm mod-times-mod
    (implies (and (integerp a)
		  (integerp b)
		  (integerp c)
		  (not (zp n))
		  (= (mod a n) (mod b n)))
	     (= (mod (* a c) n) (mod (* b c) n)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance mod-mod-times (b c))
			(:instance mod-mod-times (a b) (b c))))))


(defthm mod-plus-mod
    (implies (and (integerp a)
		  (integerp b)
		  (integerp c)
		  (not (zp n))
		  (= (mod a n) (mod b n)))
	     (= (mod (+ a c) n) (mod (+ b c) n)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance mod-sum (a c))
			(:instance mod-sum (b a) (a c))))))


