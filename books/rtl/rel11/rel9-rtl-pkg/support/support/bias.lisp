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

(local (include-book "bias-proofs"))

(defund bvecp (x k)
  (declare (xargs :guard (integerp k)))
  (and (integerp x)
       (<= 0 x)
       (< x (expt 2 k))))

; bias of a q bit exponent field is 2^(q-1)-1 
(defund bias (q) (- (expt 2 (- q 1)) 1) )

(defthm bias-non-negative-integerp-type-prescription
  (implies (and (case-split (integerp q))
                (case-split (< 0 q))
                )
           (and (integerp (bias q))
                (<= 0 (bias q))))
  :rule-classes :TYPE-PRESCRIPTION)

;BOZO rename q2 to k?
(defthm bias-bvecp
   (implies (and (<= (1- q) q2)
                 (case-split (< 0 q))
                 (case-split (integerp q))
                 (case-split (integerp q2))
                 )
            (bvecp (bias q) q2)))

(defthm bias-integerp-rewrite
  (equal (integerp (bias q))
         (or (and (acl2-numberp q) (not (integerp q)))
             (<= 1 q))))

;where's bias-integerp?
(defthm bias-integerp
  (implies (case-split (< 0 k))
           (integerp (bias k))))

(defthm bias-with-q-an-acl2-number-but-not-an-integer
  (implies (and (not (integerp q))
                (case-split (acl2-numberp q)))
           (equal (bias q)
                  0)))

(defthm bias-with-q-not-an-acl2-number
  (implies (not (acl2-numberp q))
           (equal (bias q)
                  -1/2)))
