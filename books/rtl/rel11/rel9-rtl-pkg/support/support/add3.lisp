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

(include-book "merge") ;BOZO yuck
(local (include-book "add3-proofs"))

(defund add3-measure (x y z)
  (acl2-count (+ x y z)))

(defthm add3-1
  (implies (and (integerp x)
                (> x 0))
           (and (>= (fl (/ x 2)) 0)
                (< (fl (/ x 2)) x)))
  :rule-classes ())

(include-book "land0")
(include-book "lior0")
(include-book "lxor0")

(in-theory (enable bits-tail)) ;BOZO

(defthm add-3-original
  (implies (and (not (zp n))
                (bvecp x n)
                (bvecp y n)
                (bvecp z n))
           (equal (+ x y z)
                  (+ (lxor0 x (lxor0 y z n) n)
                     (* 2 (lior0 (land0 x y n)
                                (lior0 (land0 x z n)
                                      (land0 y z n)
                                      n)
                                n)))))
  :rule-classes ())

(defthm add-2-original
  (implies (and (not (zp n))
                (bvecp x n)
                (bvecp y n))
           (equal (+ x y)
                  (+ (lxor0 x y n)
                     (* 2 (land0 x y n)))))
  :rule-classes ())
