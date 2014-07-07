; Milawa - A Reflective Theorem Prover
; Copyright (C) 2005-2009 Kookamara LLC
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

(in-package "MILAWA")
(include-book "utilities")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)

(defund clean-update (key val map)
  ;; BOZO move to utilities
  ;;
  ;; This is like (update key val map), but it does the update "in place"
  ;; instead of consing onto the front of the list.
  (declare (xargs :guard (mapp map)))
  (if (consp map)
      (if (equal (car (car map)) key)
          (cons (cons key val) (cdr map))
        (cons (car map) (clean-update key val (cdr map))))
    (list (cons key val))))

(defthm clean-update-when-not-consp
  (implies (not (consp map))
           (equal (clean-update key val map)
                  (list (cons key val))))
  :hints(("Goal" :in-theory (enable clean-update))))

(defthm clean-update-of-cons
  (equal (clean-update key val (cons a map))
         (if (equal (car a) key)
             (cons (cons key val) map)
           (cons a
                 (clean-update key val map))))
  :hints(("Goal" :in-theory (enable clean-update))))