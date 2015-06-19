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
(set-verify-guards-eagerness 2)

(include-book "std/osets/primitives" :dir :system)

(defmacro emptyset ()
  nil)

(defun list-to-set (list)
  (cond
   ((consp list)
    (insert (car list) (list-to-set (cdr list))))
   (t
    nil)))

(defthmd setp-list-to-set
  (setp (list-to-set X))
  :hints (("Goal" :in-theory (enable insert))))

(defthm head-empty-same
  (implies (and (empty X)
                (empty Y))
           (equal (equal (head X) (head Y)) t)))

(defthm tail-empty-same
  (implies (and (empty X)
                (empty Y))
           (equal (equal (tail X) (tail Y)) t)))

(defthm insert-empty-same
  (implies (and (empty X)
                (empty Y))
           (equal (equal (insert a X) (insert a Y)) t)))

(defthm sfix-empty-same
  (implies (and (empty X)
                (empty Y))
           (equal (equal (sfix X) (sfix Y)) t)))

(defthm tail-preserves-empty
  (implies (empty X)
           (empty (tail X))))

(defthm head-insert-empty
  (implies (empty X)
           (equal (head (insert a X)) a)))

(defthm tail-insert-empty
  (implies (empty X)
           (empty (tail (insert a X)))))

(defthm head-not-whole
  (implies (not (empty X))
           (not (equal (head X) X)))
  :hints(("Goal" :in-theory (enable head empty))))

(deftheory primitives-theory
  '(setp
    empty
    head
    tail
    sfix
    (:definition insert)))

(deftheory primitive-order-theory
  '(<<-irreflexive
    <<-transitive
    <<-asymmetric
    <<-trichotomy
    head-insert
    tail-insert
    head-tail-order
    head-tail-order-contrapositive))

(in-theory (disable primitives-theory
                    primitive-order-theory))

