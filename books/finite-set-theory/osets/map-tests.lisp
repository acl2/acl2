; Fully Ordered Finite Sets
; Copyright (C) 2003-2012 by Jared Davis <jared@cs.utexas.edu>
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public Lic-
; ense along with this program; if not, write to the Free Soft- ware
; Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.


; map-tests.lisp
;
; This book should not normally be included; it only exists to make sure that
; the map macro is working.

(in-package "ACL2")
(include-book "map")
(include-book "misc/assert" :dir :system)
(set-verify-guards-eagerness 2)



(SETS::map-function (integerp x))

(assert! (equal (SETS::map<integerp> '(1 2 3)) '(t)))

(assert! (equal (SETS::map-list<integerp> '(1 a 2 b))
                '(t nil t nil)))


(defun square (x)
  (declare (xargs :guard t))
  (* (rfix x) (rfix x)))

(SETS::map-function (square x))

(assert! (equal (SETS::map<square> '(1 2 3)) '(1 4 9)))
(assert! (equal (SETS::map<square> '(a b c)) '(0)))


; Make sure packages in-package works

(SETS::map-function (square x)
                    :in-package-of instance::foo)


; Multi-input test

(defun square-then-add (input offset)
  (declare (xargs :guard t))
  (+ (* (rfix input) (rfix input))
     (rfix offset)))


(SETS::map-function (square-then-add input offset)
                    :in-package-of computed-hints::foo)

(assert! (equal (COMPUTED-HINTS::map<square-then-add> '(1 2 3) 5)
                '(6 9 14)))




(defun plus (x y)
  (declare (xargs :guard (and (integerp x) (rationalp y))))
  (+ x y))

(sets::quantify-predicate (integerp x)
                          :in-package-of defthm)

(sets::map-function (plus arg1 arg2)
                    :in-package-of defthm
                    :set-guard ((all<integerp> ?set))        ; set's name must be ?set
                    :list-guard ((all-list<integerp> ?list)) ; list's name must be ?list
                    :element-guard ((integerp a))            ; element's name must be a
                    :arg-guard ((rationalp arg2)))           ; extra arg names specified above

(assert! (equal (MAP<plus> '(1 2 3) 1) '(2 3 4)))