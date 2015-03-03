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

(defthm complex-rationalp-+-when-second-term-is-rational
  (implies (rationalp y)
           (equal (complex-rationalp (+ x y))
                  (complex-rationalp x))))

(defthm complex-rationalp-+-when-second-term-is-not-complex
  (implies (not (complex-rationalp y))
           (equal (complex-rationalp (+ x y))
                  (complex-rationalp x))))

(defthm complex-rationalp-+-when-first-term-is-rational
  (implies (rationalp x)
           (equal (complex-rationalp (+ x y))
                  (complex-rationalp y))))

(defthm complex-rationalp-+-when-first-term-is-not-complex
  (implies (not (complex-rationalp x))
           (equal (complex-rationalp (+ x y))
                  (complex-rationalp y))))

;add more cases
(defthm complex-rationalp-*-drop-first-term-if-rational
  (implies (and (case-split (not (equal y 0)))
                (rationalp y))
           (equal (complex-rationalp (* y x))
                  (complex-rationalp x))))


#|
(defthm complex-rationalp-*-drop-first-term-if-not-complex
  (implies (and (case-split (not (equal y 0)))
                (not (complex-rationalp y))
                )
           (equal (complex-rationalp (* y x))
                  (complex-rationalp x))))
|#

