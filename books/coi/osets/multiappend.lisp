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

;; COI version, modified by Jared Davis, 2014-10, to include std/osets books
;; and only add the new functions and theorems that had been in COI.

;; Multiappend Function
;;
;; map "append" over a set.

(in-package "SET")
(include-book "multicons")
(local (include-book "../util/iff"))

(local (in-theory (enable weak-insert-induction-helper-1)))
(local (in-theory (enable weak-insert-induction-helper-2)))
(local (in-theory (enable weak-insert-induction-helper-3)))

(defund multiappend (list x)
  (if (consp list)
      (set::multicons (car list)
		      (set::multiappend (cdr list) x))
    (set::sfix x)))

(local (in-theory (enable multiappend)))

(defthm multiappend-set
  (setp (multiappend list X)))

(defthm listsetp-of-multiappend
  (equal (listsetp (multiappend a X))
         (all<true-listp> X))
  :hints (("goal" :in-theory (enable listsetp))))


(local
 (include-book "arithmetic/top-with-meta" :dir :system)
 )

(defun multiappend-2-induction (list path x)
  (if (and (consp list)
	   (consp path))
      (set::multicons (car list)
		      (set::multiappend-2-induction (cdr list) (cdr path) x))
    (cons path (set::sfix x))))

(defthm multiappend-in
  (equal (in path (multiappend a X))
         (and (equal (list::firstn (len a) path) (list::fix a))
              (in (list::nthcdr (len a) path) X)))
  :hints(("Goal" :in-theory (enable list::fix)
	  :induct (multiappend-2-induction a path X))))
