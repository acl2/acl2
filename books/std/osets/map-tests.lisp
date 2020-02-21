; Fully Ordered Finite Sets
; Copyright (C) 2003-2012 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Jared Davis <jared@kookamara.com>


; map-tests.lisp
;
; This book should not normally be included; it only exists to make sure that
; the map macro is working.

(in-package "ACL2")
(include-book "map")
(include-book "std/testing/assert" :dir :system)
(set-verify-guards-eagerness 2)



(SET::map-function (integerp x))

(assert! (equal (SET::map<integerp> '(1 2 3)) '(t)))

(assert! (equal (SET::map-list<integerp> '(1 a 2 b))
                '(t nil t nil)))


(defun square (x)
  (declare (xargs :guard t))
  (* (rfix x) (rfix x)))

(SET::map-function (square x))

(assert! (equal (SET::map<square> '(1 2 3)) '(1 4 9)))
(assert! (equal (SET::map<square> '(a b c)) '(0)))


; Make sure packages in-package works

(SET::map-function (square x)
                    :in-package-of instance::foo)


; Multi-input test

(defun square-then-add (input offset)
  (declare (xargs :guard t))
  (+ (* (rfix input) (rfix input))
     (rfix offset)))


(SET::map-function (square-then-add input offset)
                    :in-package-of computed-hints::foo)

(assert! (equal (COMPUTED-HINTS::map<square-then-add> '(1 2 3) 5)
                '(6 9 14)))




(defun plus (x y)
  (declare (xargs :guard (and (integerp x) (rationalp y))))
  (+ x y))

(set::quantify-predicate (integerp x)
                          :in-package-of defthm)

(set::map-function (plus arg1 arg2)
                    :in-package-of defthm
                    :set-guard ((all<integerp> ?set))        ; set's name must be ?set
                    :list-guard ((all-list<integerp> ?list)) ; list's name must be ?list
                    :element-guard ((integerp a))            ; element's name must be a
                    :arg-guard ((rationalp arg2)))           ; extra arg names specified above

(assert! (equal (MAP<plus> '(1 2 3) 1) '(2 3 4)))
