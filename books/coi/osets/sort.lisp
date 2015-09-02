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

;; COI version, modified by Jared Davis, 2014-10, to include std/osets books
;; and only add the new functions and theorems that had been in COI.

(in-package "SET")
(include-book "outer")
(include-book "std/osets/sort" :dir :system)
(set-verify-guards-eagerness 2)

(local (in-theory (enable weak-insert-induction-helper-1)))
(local (in-theory (enable weak-insert-induction-helper-2)))
(local (in-theory (enable weak-insert-induction-helper-3)))

; A List Membership Function
;
; The current member-equal function has weird semantics, returning a
; list rather than a boolean value.  We provide a convenient
; alternative which always returns t or nil instead.
;
; We don't try to develop a complete theory for this function here,
; but we will provide several useful utility theorems for relating in
; with the common list functions such as cons, append, and reverse.
; In the future we might want to expand this section to include more
; theorems.

(defun in-list (a x)
  (declare (xargs :guard (true-listp x)))
  (if (endp x)
      nil
    (or (equal a (car x))
        (in-list a (cdr x)))))

(defthm in-list-cons
  (equal (in-list a (cons b x))
         (or (equal a b)
             (in-list a x))))

(defthm in-list-append
  (equal (in-list a (append x y))
         (or (in-list a x)
             (in-list a y))))

(encapsulate nil

  (local (defthm lemma
           (implies (in-list a acc)
                    (in-list a (revappend x acc)))))

  (defthm in-list-revappend
    (equal (in-list a (revappend x y))
           (or (in-list a x)
               (in-list a y))))
)

(defthm in-list-reverse
  (equal (in-list a (reverse x))
         (in-list a x)))

(defthm in-list-on-set
  (implies (setp X)
           (equal (in-list a X)
                  (in a X)))
  :hints(("Goal" :in-theory (enable sfix head tail empty setp))))

; We now introduce a naive function to split a list into two.

(defun split-list (x)
  (declare (xargs :guard (true-listp x)))
  (cond ((endp x) (mv nil nil))
        ((endp (cdr x)) (mv (list (car x)) nil))
        (t (mv-let (part1 part2)
                   (split-list (cddr x))
                   (mv (cons (car x) part1)
                       (cons (cadr x) part2))))))

