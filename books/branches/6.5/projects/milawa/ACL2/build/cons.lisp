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
(include-book "pequal-list")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)

(dd.open "cons.tex")

(deftheorem theorem-cons-is-not-nil
  :derive (!= (cons x y) nil)
  :proof  (@derive
           ((v (= (symbolp x) nil)          (= (consp x) nil))              (build.axiom (axiom-disjoint-symbols-and-conses)))
           ((v (= (symbolp (cons x y)) nil) (= (consp (cons x y)) nil))     (build.instantiation @- (@sigma (x . (cons x y)))))
           ((v (= (consp (cons x y)) nil)   (= (symbolp (cons x y)) nil))   (build.commute-or @-)                                 *1)
           ((= (consp (cons x y)) t)                                        (build.axiom (axiom-consp-of-cons)))
           ((!= (consp (cons x y)) nil)                                     (build.not-nil-from-t @-))
           ((= (symbolp (cons x y)) nil)                                    (build.modus-ponens-2 @- *1))
           ((!= (symbolp (cons x y)) t)                                     (build.not-t-from-nil @-))
           ((!= t (symbolp (cons x y)))                                     (build.commute-not-pequal @-))
           ((= (symbolp nil) t)                                             (build.base-eval '(symbolp 'nil)))
           ((!= (symbolp nil) (symbolp (cons x y)))                         (build.substitute-into-not-pequal @-- @-))
           ((!= (symbolp (cons x y)) (symbolp nil))                         (build.commute-not-pequal @-)                         *2)
           ((v (!= (cons x y) nil) (= (cons x y) nil))                      (build.propositional-schema (@formula (= (cons x y) nil))))
           ((v (!= (cons x y) nil) (= (symbolp (cons x y)) (symbolp nil)))  (build.disjoined-pequal-by-args 'symbolp (@formula (!= (cons x y) nil)) (list @-)))
           ((v (= (symbolp (cons x y)) (symbolp nil)) (!= (cons x y) nil))  (build.commute-or @-))
           ((!= (cons x y) nil)                                             (build.modus-ponens-2 *2 @-)))
  :minatbl ((cons . 2)
            (consp . 1)
            (symbolp . 1)))

(dd.close)