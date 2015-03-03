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
; cert_param: (non-acl2r)

;These rules may cause case splits, but that's sort of the point.

(local (include-book "predicate"))
(local (include-book "fp2"))

(local (defthm hack2
         (implies
          (and (< y 0)
               (rationalp x)
               (case-split (< x 0))
               )
          (<= 0 (* x y)))
       ))

;BOZO instead of having 2 rules below, consider putting an OR inside the CASE-SPLIT
;make these 2 nicer? ;do we need both?


#| the conclusion of product-less-than-zero used to be this, which didn't mention acl2-numberp of x...
                  (or (and (< x 0) (< 0 y))
                      (and (< y 0) (< 0 x)))
|#

(defthm product-less-than-zero-1
  (implies (case-split (not (complex-rationalp x))) ;can't gen: (* #C(-1 9) #C(-1 9))=#c(-80 -18)
           (equal (< (* x y) 0)
                  (if (< x 0)
                      (< 0 y)
                    (if (equal 0 x)
                        nil
                      (if (not (acl2-numberp x))
                          nil
                        (< y 0))))))
  :otf-flg t
  :hints (("Goal" :cases ((and (rationalp x) (rationalp y))
                          (and (complex-rationalp x) (rationalp y))
                          (and (not (acl2-numberp x)) (rationalp y))
                          (and (rationalp x) (complex-rationalp y))
                          (and (complex-rationalp x) (complex-rationalp y))
                          (and (not (acl2-numberp x)) (complex-rationalp y))
                          ))))

(defthm product-less-than-zero-2
  (implies (case-split (not (complex-rationalp y))) ;(case-split (rationalp y))
           (equal (< (* x y) 0)
                  (or (and (< x 0) (< 0 y))
                      (and (< y 0) (< 0 x)))))
  :hints (("Goal" :in-theory (disable product-less-than-zero-1)
           :use (:instance  product-less-than-zero-1 (x y) (y x)))))

(defthm product-less-than-zero
  (implies (case-split (or (not (complex-rationalp x))
                           (not (complex-rationalp y)))) ;can't gen: (* #C(-1 9) #C(-1 9))=#c(-80 -18)
           (equal (< (* x y) 0)
                  (if (< x 0)
                      (< 0 y)
                    (if (equal 0 x)
                        nil
                      (if (not (acl2-numberp x))
                          nil
                        (< y 0)))))))


;combine the next twp by case-splittin on an OR?
(defthm product-greater-than-zero
  (implies (case-split (not (complex-rationalp y)))
           (equal (< 0 (* x y))
                  (or (and (< 0 x) (< 0 y))
                      (and (< y 0) (< x 0)))))
  :hints (("Goal" :cases (complex-rationalp x))))

(defthm product-greater-than-zero-2
  (implies (case-split (not (complex-rationalp x)))
           (equal (< 0 (* x y))
                  (or (and (< 0 x) (< 0 y))
                      (and (< y 0) (< x 0)))))
  :hints (("Goal" :in-theory (disable product-greater-than-zero)
           :use (:instance  product-greater-than-zero (x y) (y x)))))

;could write the conclusion using an OR...
(defthm product-equal-zero
  (equal (equal 0 (* x y))
         (if (not (acl2-numberp x))
             t
           (if (not (acl2-numberp y))
               t
             (if (equal 0 x)
                 t
               (equal 0 y)))))
  :hints (("Goal" :cases (complex-rationalp x))))


#|
;product-equal-zero is better?
(defthm equal-zero-product
  (implies (and (not (equal 0 x))
                (case-split (acl2-numberp x))
                (case-split (acl2-numberp y))
                )
           (equal (equal 0 (* x y))
                  (equal 0 y))))

;product-equal-zero is better?
(defthm equal-zero-product-2
  (implies (and (case-split (acl2-numberp x))
                (case-split (acl2-numberp y))
                (case-split (not (equal 0 x)))
                )
           (equal (equal 0 (* y x))
                  (equal 0 y))))
|#
