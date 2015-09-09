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
(local (include-book "../../arithmetic/top"))
(local (include-book "logior"))
(local (include-book "logand"))
(local (include-book "logorc1"))
(local (include-book "lognot"))


(local (in-theory (enable logorc1))) ;remove

;type?

(defthm logeqv-bound
  (implies (and (<= 0 i)
                (<= 0 j))
           (<= (logeqv i j) -1))
  :hints (("goal" :in-theory (enable logeqv logior))))

(defthm logeqv-with-zero
  (equal (logeqv 0 i)
         (lognot i))
  :hints (("goal" :in-theory (enable lognot logeqv)))
  )

(defthm logeqv-commutative
  (equal (logeqv i j)
         (logeqv j i))
  :hints (("goal" :in-theory (enable lognot logeqv)))
  )

(defthm logeqv-with-minus-1
  (implies (case-split (integerp i))
           (equal (logeqv -1 i)
                  i))
  :hints (("goal" :in-theory (enable logeqv))))

(defthm logeqv-even
  (implies (and (case-split (integerp i))
                (case-split (integerp j)))
           (equal (integerp (* 1/2 (logeqv i j)))
                  (or (and (not (integerp (* 1/2 i)))
                           (integerp (* 1/2 j)))
                      (and (integerp (* 1/2 i))
                           (not (integerp (* 1/2 j)))))))
  :hints (("goal" :in-theory (enable logeqv))))


(defthm logeqv-with-non-integer-arg
  (implies (not (integerp i))
           (and (equal (acl2::binary-logeqv i j)
                       (lognot j))
                (equal (acl2::binary-logeqv j i)
                       (lognot j))))
  :hints (("goal" :in-theory (enable acl2::binary-logeqv))))

(defthm logeqv-self
  (equal (logeqv x x) -1)
  :hints (("goal" :in-theory (enable logeqv))))

(defthm floor-logeqv-by-2
  (implies (and (case-split (integerp i))
                (case-split (integerp j))
                )
           (equal (floor (logeqv i j) 2)
                  (logeqv (floor i 2) (floor j 2))))
  :hints (("goal" :in-theory (enable logeqv))))

(defthm fl-logeqv-by-2
  (implies (and (case-split (integerp i))
                (case-split (integerp j))
                )
           (equal (fl (* 1/2 (logeqv i j)))
                  (logeqv (fl (* 1/2 i)) (fl (* 1/2 j)))))
  :hints (("goal" :in-theory (enable logeqv))))

;i'm not sure which way this rule should go but note that both parts of this rule rewrite to the same rhs
(defthm lognot-logeqv
  (and (equal (logeqv (lognot i) j)
              (lognot (logeqv i j)))
       (equal (logeqv j (lognot i))
              (lognot (logeqv i j))))
  :hints (("goal" :in-theory (enable logeqv logand logior logorc1
                                     evenp ;BOZO prove evenp-lognot and drop this
                                     )
           :induct (log-induct-allows-negatives i j))))



#|


(local(defthm logeqv-mod-1
    (implies (and (integerp i) (>= i 0)
		  (integerp j) (>= j 0))
	     (iff (= (mod (logeqv i j) 2) 0)
		  (or (= (mod (logorc1 i j) 2) 0)
		      (= (mod (logorc1 j i) 2) 0))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable logorc1 logand)
		  :use ((:instance logand-even (i (logorc1 i j)) (j (logorc1 j i))))))))

(local(defthm logeqv-mod
    (implies (and (integerp i) (>= i 0)
		  (integerp j) (>= j 0))
	     (iff (= (mod (logeqv i j) 2) 0)
		  (not (= (logxor (mod i 2) (mod j 2))
			  0))))
  :rule-classes ()
  :hints (("Goal" :in-theory (disable logorc1 logeqv)
		  :use ((:instance logeqv-mod-1)
			(:instance logorc1-mod)
			(:instance logorc1-mod (i j) (j i))
			(:instance mod012 (x i))
			(:instance mod012 (x j)))))))
|#
