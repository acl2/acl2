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
(include-book "membership")
(include-book "std/osets/union" :dir :system)
(include-book "std/osets/intersect" :dir :system)
(include-book "std/osets/difference" :dir :system)
(set-verify-guards-eagerness 2)

(local (in-theory (enable weak-insert-induction-helper-1)))
(local (in-theory (enable weak-insert-induction-helper-2)))
(local (in-theory (enable weak-insert-induction-helper-3)))

;;; First we introduce some basic theory about cons and sets.  Note
;;; that this theory is disabled at the end of this file.  However, if
;;; you are introducing fast versions of new set functions, you can
;;; enable these theorems by enabling cons-theory.

(defthm cons-set
  (equal (setp (cons a X))
         (and (setp X)
              (or (<< a (head X))
                  (empty X))))
  :hints(("Goal" :in-theory (enable primitives-theory))))

(defthm cons-head
  (implies (setp (cons a X))
           (equal (head (cons a X)) a))
  :hints(("Goal" :in-theory (enable primitives-theory))))

(defthm cons-to-insert-empty
  (implies (and (setp X)
                (empty X))
           (equal (cons a X) (insert a X)))
  :hints(("Goal" :in-theory (enable primitives-theory))))

(defthm cons-to-insert-nonempty
  (implies (and (setp X)
                (<< a (head X)))
           (equal (cons a X) (insert a X)))
  :hints(("Goal" :in-theory (enable primitives-theory
                                    primitive-order-theory))))

(defthm cons-in
  (implies (and (setp (cons a X))
                (setp X))
           (equal (in b (cons a X))
                  (or (equal a b)
                      (in b X)))))


(deftheory cons-theory
  '(cons-set
    cons-head
    cons-to-insert-empty
    cons-to-insert-nonempty
    cons-in))

(in-theory (disable cons-theory))
