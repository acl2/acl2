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

(local (include-book "predicate"))

(defthm rationalp-product-when-one-arg-is-rational
  (implies (and (rationalp x)
                (case-split (not (equal x 0)))
                (case-split (acl2-numberp y))
                )
           (and (equal (rationalp (* x y))
                       (rationalp y))
                (equal (rationalp (* y x))
                       (rationalp y)))))

(defthm rationalp-sum-when-one-arg-is-rational
  (implies (and (rationalp x)
                (case-split (acl2-numberp y)))
           (and (equal (rationalp (+ x y))
                       (rationalp y))
                (equal (rationalp (+ y x))
                       (rationalp y)))))

(defthm rationalp-unary-divide
  (implies (case-split (acl2-numberp x))
           (equal (rationalp (/ x))
                  (rationalp x))))


                

                
#|

(defthm rationalp-*-when-first-factor-is-rat
  (implies (and (rationalp x)
                (case-split (not (equal x 0))) ;if x is 0, then...
                )
           (equal (rationalp (* x y))
                  (not (complex-rationalp y)))))

(thm
  (implies (and (rationalp x)
                (case-split (not (equal x 0))) ;if x is 0, then...
                )
           (equal (rationalp (* x y))
                  (not (complex-rationalp y)))))

|#


;try

(defthm rationalp-product
  (implies (and (case-split (not (complex-rationalp x)))
                (case-split (not (complex-rationalp y))))
           (rationalp (* x y))))
