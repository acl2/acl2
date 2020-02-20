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

(in-package "ACL2")
(include-book "quantify")
(include-book "std/testing/assert" :dir :system)

(SET::quantify-predicate (integerp x))
(SET::quantify-predicate (symbolp x))
(SET::quantify-predicate (rationalp x))
(SET::quantify-predicate (natp x))

(assert! (SET::all<integerp> '(1 2 3)))
(assert! (SET::all<not-integerp> '(a b c)))
(assert! (equal (SET::find<symbolp> '(1 2 3 a b c)) 'a))

(SET::quantify-predicate (eqlablep x)
                         :in-package-of defthm)

(assert! (exists<eqlablep> '(c (a . b))))

(defun lessp (a b)
  (declare (xargs :guard t))
  (< (rfix a) (rfix b)))

(set::quantify-predicate (lessp a b))

(assert! (set::all<lessp> '(1 2 3) 6))
(assert! (not (set::all<lessp> '(1 2 3) 2)))


(defun fast-lessp (a b)
  (declare (xargs :guard (and (rationalp a)
                              (rationalp b))))
  (< a b))

(SET::quantify-predicate (fast-lessp x max)
                         :set-guard  ((set::all<rationalp> ?set))
                         :list-guard ((set::all-list<rationalp> ?list))
                         :arg-guard  ((rationalp max))
                         :in-package-of defthm)

(assert! (equal (find<fast-lessp> '(-10 -5 0 5 10) 100) -10))

(in-theory (disable set::theory<integerp>))
(in-theory (disable theory<fast-lessp>))

(defun unguarded-morep (a b)
  (> a b))

(set::quantify-predicate (unguarded-morep x max)
                         :verify-guards nil)

(assert! (equal (set::find<unguarded-morep> '(1 2 3 4 5 6 7) 5) 6))
