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
(local (include-book "fp2"))
(local (include-book "inverted-factor"))

(defthm unary-divide-less-than-zero
  (implies (case-split (not (complex-rationalp x))) ;drop?
           (equal (< (/ x) 0)
                  (< x 0))))

#|
;try
(defthm unary-divide-less-than-zero
  (implies t;(case-split (not (complex-rationalp x))) ;drop?
           (equal (< (/ x) 0)
                  (< x 0))))
|#

;perhaps we don't need these, if we have rules like
;less-than-multiply-through-by-inverted-factor-from-left-hand-side ?
(defthm unary-divide-greater-than-zero
  (implies (case-split (not (complex-rationalp x))) ;drop?
           (equal (< 0 (/ x))
                  (< 0 x))))

(defthm unary-divide-equal-0
  (implies (case-split (acl2-numberp x))
           (equal (equal 0 (/ x))
                  (equal 0 x))))

;BOZO Why do we require the constant to be non-zero?
(defthm unary-divide-equal-non-zero-constant
  (implies (and (syntaxp (and (quotep k)
                              ;(not (equal 0 (cadr k)))
                              ))  ;drop?
                ;(case-split (not (equal 0 k)))
                (case-split (acl2-numberp x))
                (case-split (acl2-numberp k))
                )
           (equal (equal k (/ x))
                  (equal (/ k) x))))

;make a negative case?
(defthm unary-divide-less-than-non-zero-constant
  (implies (and (syntaxp (and (quotep k) (not (equal 0 (cadr k)))))  ;drop?
                (<= 0 k)
                (case-split (<= 0 x))
                (case-split (not (equal 0 k)))
                (case-split (not (equal 0 x)))
                (case-split (rationalp x))
                (case-split (rationalp k))
                )
           (equal (< (/ x) k)
                  (< (/ k) x))))


;once with this msg failed:
;1x (:REWRITE UNARY-DIVIDE-GREATER-THAN-NON-ZERO-CONSTANT) failed because it permutes a big term forward.
;so I changed the conclusion to not use unary-/
(defthm unary-divide-greater-than-non-zero-constant
  (implies (and (syntaxp (and (quotep k) (not (equal 0 (cadr k)))))  ;drop?
                (<= 0 k)
                (case-split (<= 0 x))
                (case-split (not (equal 0 k)))
                (case-split (not (equal 0 x)))
                (case-split (rationalp x))
                (case-split (rationalp k))
                )
           (equal (< k (/ x))
                  (< x (/ 1 k)))))
