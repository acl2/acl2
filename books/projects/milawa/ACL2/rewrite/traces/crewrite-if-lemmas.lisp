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
(include-book "if-lemmas")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)

(dd.open "crewrite-trace-if-lemmas.tex")


(defderiv rw.disjoined-iff-implies-equal-if-bldr
  :derive (v P (= (equal (if (? a1) (? b1) (? c1)) (if (? a2) (? b2) (? c2))) t))
  :from   ((proof x (v P (= (iff (? a1) (? a2)) t)))
           (proof y (v P (v (!= (not (? a2)) nil) (= (equal (? b1) (? b2)) t))))
           (proof z (v P (v (!= (? a2) nil) (= (equal (? c1) (? c2)) t)))))
  :proof  (@derive
           ((v P (= (iff (? a1) (? a2)) t))                                                  (@given x) *1)
           ((v P (v (!= (not (? a2)) nil) (= (equal (? b1) (? b2)) t)))                      (@given y) *2)
           ((v P (v (!= (? a2) nil) (= (equal (? c1) (? c2)) t)))                            (@given z) *3)
           ((v (!= (iff x1 x2) t)
              (v (! (v (!= (not x2) nil) (= (equal y1 y2) t)))
                 (v (! (v (!= x2 nil) (= (equal z1 z2) t)))
                    (= (equal (if x1 y1 z1) (if x2 y2 z2)) t))))                             (build.theorem (rw.theorem-iff-implies-equal-if-combined)))
           ((v (!= (iff (? a1) (? a2)) t)
               (v (! (v (!= (not (? a2)) nil) (= (equal (? b1) (? b2)) t)))
                  (v (! (v (!= (? a2) nil) (= (equal (? c1) (? c2)) t)))
                     (= (equal (if (? a1) (? b1) (? c1)) (if (? a2) (? b2) (? c2))) t))))    (build.instantiation @- (@sigma (x1 . (? a1)) (x2 . (? a2)) (y1 . (? b1)) (y2 . (? b2)) (z1 . (? c1)) (z2 . (? c2)))))
           ((v P (= (equal (if (? a1) (? b1) (? c1)) (if (? a2) (? b2) (? c2))) t))          (rw.three-disjoined-modus-ponens *1 *2 *3 @-)))
  :minatbl ((if . 3)))

(defderiv rw.disjoined-iff-implies-iff-if-bldr
  :derive (v P (= (iff (if (? a1) (? b1) (? c1)) (if (? a2) (? b2) (? c2))) t))
  :from   ((proof x (v P (= (iff (? a1) (? a2)) t)))
           (proof y (v P (v (!= (not (? a2)) nil) (= (iff (? b1) (? b2)) t))))
           (proof z (v P (v (!= (? a2) nil) (= (iff (? c1) (? c2)) t)))))
  :proof  (@derive
           ((v P (= (iff (? a1) (? a2)) t))                                                (@given x)  *1)
           ((v P (v (!= (not (? a2)) nil) (= (iff (? b1) (? b2)) t)))                      (@given y)  *2)
           ((v P (v (!= (? a2) nil) (= (iff (? c1) (? c2)) t)))                            (@given z)  *3)
           ((v (!= (iff x1 x2) t)
               (v (! (v (!= (not x2) nil) (= (iff y1 y2) t)))
                  (v (! (v (!= x2 nil) (= (iff z1 z2) t)))
                     (= (iff (if x1 y1 z1) (if x2 y2 z2)) t))))                            (build.theorem (rw.theorem-iff-implies-iff-if-combined)))
           ((v (!= (iff (? a1) (? a2)) t)
               (v (! (v (!= (not (? a2)) nil) (= (iff (? b1) (? b2)) t)))
                  (v (! (v (!= (? a2) nil) (= (iff (? c1) (? c2)) t)))
                     (= (iff (if (? a1) (? b1) (? c1)) (if (? a2) (? b2) (? c2))) t))))    (build.instantiation @- (@sigma (x1 . (? a1)) (x2 . (? a2)) (y1 . (? b1)) (y2 . (? b2)) (z1 . (? c1)) (z2 . (? c2)))))
           ((v P (= (iff (if (? a1) (? b1) (? c1)) (if (? a2) (? b2) (? c2))) t))          (rw.three-disjoined-modus-ponens *1 *2 *3 @-)))
  :minatbl ((if . 3)))

(dd.close)
