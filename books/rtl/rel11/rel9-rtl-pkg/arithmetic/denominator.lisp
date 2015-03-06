; RTL - A Formal Theory of Register-Transfer Logic and Computer Arithmetic 
; Copyright (C) 1995-2013 Advanced Mirco Devices, Inc. 
;
; Contact:
;   David Russinoff
;   1106 W 9th St., Austin, TX 78703
;   http://www.russsinoff.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.
;
; This program is distributed in the hope that it will be useful but WITHOUT ANY
; WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A
; PARTICULAR PURPOSE.  See the GNU General Public License for more details.
;
; You should have received a copy of the GNU General Public License along with
; this program; see the file "gpl.txt" in this directory.  If not, write to the
; Free Software Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA
; 02110-1335, USA.
;
; Author: David M. Russinoff (david@russinoff.com)

(in-package "RTL")

(local (include-book "ground-zero"))
(local (include-book "fp2"))

;denom of non-rat?

(defthm denominator-positive-integer-type-prescription
  (and (< 0 (denominator x))
       (integerp (denominator x)))
  :rule-classes (:type-prescription))

(defthm denominator-positive
  (< 0 (denominator x))
  :rule-classes (:rewrite :linear))

(defthm denominator-integerp
  (integerp (denominator x)))

(defthm denominator-one-means-integer
  (implies (case-split (rationalp x))
           (equal (equal (denominator x) 1)
                  (integerp x)))
  :hints (("goal" :in-theory (disable rational-implies2)
           :use (rational-implies2
                 (:instance lowest-terms 
                            (n (denominator x))
                            (r x) 
                            (q 1))))))

(defthm denominator-of-integer-is-one
  (implies (integerp x)
           (equal (denominator x)
                  1)))
;linear?
(encapsulate
 ()
 (local (include-book "../../../../arithmetic/mod-gcd"))
 (defthm denominator-lower-bound
   (implies (and (< 0 q)
                 (integerp p)
                 (integerp q)
                 )
            (<= (denominator (* p (/ q))) q))
   :hints (("goal" :use (:instance acl2::least-numerator-denominator-<= (n p) (d q))))
   ))
