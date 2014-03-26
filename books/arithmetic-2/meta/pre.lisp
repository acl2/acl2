; Arithmetic-2 Library
; Copyright (C) 1999 Robert Krug <rkrug@cs.utexas.edu>
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.
;
; This program is distributed in the hope that it will be useful but WITHOUT
; ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
; FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more
; details.
;
; You should have received a copy of the GNU General Public License along with
; this program; if not, write to the Free Software Foundation, Inc., 51
; Franklin Street, Suite 500, Boston, MA 02110-1335, USA.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; pre.lisp
;;;
;;;
;;; This is the first book to be loaded.  The capitalized rules
;;; are either copied form axioms.lisp, or are renamed versions
;;; of rules in axioms.lisp.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "../pass1/top"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defthm |Non-numeric x in (+ x y)|
  (implies (not (acl2-numberp x))
           (equal (+ x y)
                  (fix y))))

(defthm |Non-numeric y in (+ x y)|
  (implies (not (acl2-numberp y))
           (equal (+ x y) 
                  (fix x))))

(defthm |Non-numeric x in (- x)|
  (implies (not (acl2-numberp x))
           (equal (- x) 
                  0)))

(defthm |Non-Numeric x in (* x y)|
  (implies (not (acl2-numberp x))
           (equal (* x y)
                  0)))

(defthm |Non-Numeric y in (* x y)|
  (implies (not (acl2-numberp y))
           (equal (* x y)
                  0)))

(defthm |Non-Numeric x in (/ x)|
  (implies (or (not (acl2-numberp x))
               (equal x 0))
           (equal (/ x)
                  0)))

(defthm |Non-Numeric x in (< x y)|
  (implies (not (acl2-numberp x))
           (equal (< x y)
                  (< 0 y))))

(defthm |Non-Numeric y in (< x y)|
  (implies (not (acl2-numberp y))
           (equal (< x y)
                  (< x 0))))

(defthm |Non-Numeric x in (denominator x)|
  (implies (not (rationalp x))
           (equal (denominator x)
                  1)))

(defthm |Non-Numeric x in (numerator x)|
  (implies (not (rationalp x))
           (equal (numerator x)
                  0)))

(defthm |(+ y x)|   ; Commutativity-of-plus
  (equal (+ y x)
         (+ x y)))

(defthm |(+ y (+ x z))|
  (equal (+ y (+ x z))
         (+ x (+ y z))))

(defthm |(* y x)|   ; Commutativity-of-times
  (equal (* y x)
         (* x y)))

(defthm |(* y (* x z))|
   (equal (* y (* x z))
          (* x (* y z))))

