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


(dd.open "if.tex")

(dd.section "If manipulation")

(defderiv build.if-when-not-nil
  :derive (= (if (? a) (? b) (? c)) (? b))
  :from   ((proof x (!= (? a) nil))
           (term b (? b))
           (term c (? c)))
  :proof  (@derive ((v (= x nil) (= (if x y z) y))                      (build.axiom (axiom-if-when-not-nil)))
                   ((v (= (? a) nil) (= (if (? a) (? b) (? c)) (? b)))  (build.instantiation @- (@sigma (x . (? a)) (y . (? b)) (z . (? c)))))
                   ((!= (? a) nil)                                      (@given x))
                   ((= (if (? a) (? b) (? c)) (? b))                    (build.modus-ponens-2 @- @--)))
  :minatbl ((if . 3)))

(defderiv build.disjoined-if-when-not-nil
  :derive (v P (= (if (? a) (? b) (? c)) (? b)))
  :from   ((proof x (v P (!= (? a) nil)))
           (term b (? b))
           (term c (? c)))
  :proof  (@derive ((v (= x nil) (= (if x y z) y))                            (build.axiom (axiom-if-when-not-nil)))
                   ((v (= (? a) nil) (= (if (? a) (? b) (? c)) (? b)))        (build.instantiation @- (@sigma (x . (? a)) (y . (? b)) (z . (? c)))))
                   ((v P (v (= (? a) nil) (= (if (? a) (? b) (? c)) (? b))))  (build.expansion (@formula P) @-))
                   ((v P (!= (? a) nil))                                      (@given x))
                   ((v P (= (if (? a) (? b) (? c)) (? b)))                    (build.disjoined-modus-ponens-2 @- @--)))
  :minatbl ((if . 3)))

(defderiv build.if-when-nil
 :derive (= (if (? a) (? b) (? c)) (? c))
 :from   ((proof x (= (? a) nil))
          (term b (? b))
          (term c (? c)))
 :proof  (@derive ((v (!= x nil) (= (if x y z) z))                       (build.axiom (axiom-if-when-nil)))
                  ((v (!= (? a) nil) (= (if (? a) (? b) (? c)) (? c)))   (build.instantiation @- (@sigma (x . (? a)) (y . (? b)) (z . (? c)))))
                  ((= (? a) nil)                                         (@given x))
                  ((= (if (? a) (? b) (? c)) (? c))                      (build.modus-ponens @- @--)))
 :minatbl ((if . 3)))

(defderiv build.disjoined-if-when-nil
 :derive (v P (= (if (? a) (? b) (? c)) (? c)))
 :from   ((proof x (v P (= (? a) nil)))
          (term b (? b))
          (term c (? c)))
 :proof  (@derive ((v (!= x nil) (= (if x y z) z))                           (build.axiom (axiom-if-when-nil)))
                  ((v (!= (? a) nil) (= (if (? a) (? b) (? c)) (? c)))       (build.instantiation @- (@sigma (x . (? a)) (y . (? b)) (z . (? c)))))
                  ((v P (v (!= (? a) nil) (= (if (? a) (? b) (? c)) (? c)))) (build.expansion (@formula P) @-))
                  ((v P (= (? a) nil))                                       (@given x))
                  ((v P (= (if (? a) (? b) (? c)) (? c)))                    (build.disjoined-modus-ponens @- @--)))
 :minatbl ((if . 3)))

(defderiv build.if-of-t
  :derive (= (if t (? b) (? c)) (? b))
  :from   ((term b (? b))
           (term c (? c)))
  :proof  (@derive
           ((!= t nil)                     (build.axiom (axiom-t-not-nil)))
           ((= (if t (? b) (? c)) (? b))   (build.if-when-not-nil @-
                                                                  (@term (? b))
                                                                  (@term (? c)))))
  :minatbl ((if . 3)))

(defderiv build.if-of-nil
  :derive (= (if nil (? b) (? c)) (? c))
  :from   ((term b (? b))
           (term c (? c)))
  :proof  (@derive
           ((= nil nil)                     (build.reflexivity (@term nil)))
           ((= (if nil (? b) (? c)) (? c))  (build.if-when-nil @-
                                                               (@term (? b))
                                                               (@term (? c)))))
  :minatbl ((if . 3)))



(deftheorem theorem-if-redux-same
  :derive (= (if x y y) y)
  :proof  (@derive ((v (= x nil) (= (if x y z) y))         (build.axiom (axiom-if-when-not-nil)))
                   ((v (= x nil) (= (if x y y) y))         (build.instantiation @- (@sigma (z . y)))  *1)
                   ((v (!= x nil) (= (if x y z) z))        (build.axiom (axiom-if-when-nil)))
                   ((v (!= x nil) (= (if x y y) y))        (build.instantiation @- (@sigma (z . y))))
                   ((v (= (if x y y) y) (= (if x y y) y))  (build.cut *1 @-))
                   ((= (if x y y) y)                       (build.contraction @-)))
  :minatbl ((if . 3)))

(deftheorem theorem-if-when-same
  :derive (v (!= y z) (= (if x y z) y))
  :proof (@derive
          ((= x x)                                (build.reflexivity (@term x)))
          ((v (!= y z) (= x x))                   (build.expansion (@formula (!= y z)) @-)          *1a)
          ((= y y)                                (build.reflexivity (@term y)))
          ((v (!= y z) (= y y))                   (build.expansion (@formula (!= y z)) @-)          *1b)
          ((v (!= y z) (= y z))                   (build.propositional-schema (@formula (= y z))))
          ((v (!= y z) (= z y))                   (build.disjoined-commute-pequal @-)               *1c)
          ((v (!= y z) (= (if x y z) (if x y y))) (build.disjoined-pequal-by-args 'if
                                                                                  (@formula (!= y z))
                                                                                  (list *1a *1b *1c))   *1)
          ((= (if x y y) y)                       (build.theorem (theorem-if-redux-same)))
          ((v (!= y z) (= (if x y y) y))          (build.expansion (@formula (!= y z)) @-))
          ((v (!= y z) (= (if x y z) y))          (build.disjoined-transitivity-of-pequal *1 @-)))
  :minatbl ((if . 3)))

(defderiv build.if-when-same
  :derive (= (if (? a) (? b) (? c)) (? b))
  :from ((proof x (= (? b) (? c)))
         (term a (? a)))
  :proof (@derive
          ((v (!= y z) (= (if x y z) y))                           (build.theorem (theorem-if-when-same)))
          ((v (!= (? b) (? c)) (= (if (? a) (? b) (? c)) (? b)))   (build.instantiation @- (@sigma (x . (? a)) (y . (? b)) (z . (? c)))))
          ((= (? b) (? c))                                         (@given x))
          ((= (if (? a) (? b) (? c)) (? b))                        (build.modus-ponens @- @--)))
  :minatbl ((if . 3)))

(defderiv build.disjoined-if-when-same
  :derive (v P (= (if (? a) (? b) (? c)) (? b)))
  :from ((proof x (v P (= (? b) (? c))))
         (term a (? a)))
  :proof (@derive
          ((v (!= y z) (= (if x y z) y))                                 (build.theorem (theorem-if-when-same)))
          ((v (!= (? b) (? c)) (= (if (? a) (? b) (? c)) (? b)))         (build.instantiation @- (@sigma (x . (? a)) (y . (? b)) (z . (? c)))))
          ((v P (v (!= (? b) (? c)) (= (if (? a) (? b) (? c)) (? b))))   (build.expansion (@formula P) @-))
          ((v P (= (? b) (? c)))                                         (@given x))
          ((v P (= (if (? a) (? b) (? c)) (? b)))                        (build.disjoined-modus-ponens @- @--)))
  :minatbl ((if . 3)))




(deftheorem theorem-if-redux-then
 :derive (= (if x (if x y w) z) (if x y z))
 :proof  (@derive ((v (= x nil) (= (if x y z) y))                     (build.axiom (axiom-if-when-not-nil))                        *1)
                  ((v (= x nil) (= (if x y w) y))                     (build.instantiation @- (@sigma (z . w))))
                  ((v (= x nil) (= y (if x y z)))                     (build.disjoined-commute-pequal *1))
                  ((v (= x nil) (= (if x y w) (if x y z)))            (build.disjoined-transitivity-of-pequal @-- @-))
                  ((v (= x nil) (= (if x (if x y w) z) (if x y w)))   (build.instantiation *1 (@sigma (y . (if x y w)))))
                  ((v (= x nil) (= (if x (if x y w) z) (if x y z)))   (build.disjoined-transitivity-of-pequal @- @--)         *2)

                  ((v (!= x nil) (= (if x y z) z))                    (build.axiom (axiom-if-when-nil))                            *3)
                  ((v (!= x nil) (= z (if x y z)))                    (build.disjoined-commute-pequal @-))
                  ((v (!= x nil) (= (if x (if x y w) z) z))           (build.instantiation *3 (@sigma (y . (if x y w)))))
                  ((v (!= x nil) (= (if x (if x y w) z) (if x y z)))  (build.disjoined-transitivity-of-pequal @- @--)         *4)

                  ((v (= (if x (if x y w) z) (if x y z))
                      (= (if x (if x y w) z) (if x y z)))             (build.cut *2 *4))
                  ((= (if x (if x y w) z) (if x y z))                 (build.contraction @-)))
 :minatbl ((if . 3)))

(deftheorem theorem-if-redux-else
 :derive (= (if x y (if x w z)) (if x y z))
 :proof  (@derive ((v (= x nil) (= (if x y z) y))                     (build.axiom (axiom-if-when-not-nil))                     *1)
                  ((v (= x nil) (= (if x y (if x w z)) y))            (build.instantiation @- (@sigma (z . (if x w z)))))
                  ((v (= x nil) (= y (if x y z)))                     (build.disjoined-commute-pequal *1))
                  ((v (= x nil) (= (if x y (if x w z)) (if x y z)))   (build.disjoined-transitivity-of-pequal @-- @-)      *2)

                  ((v (!= x nil) (= (if x y z) z))                    (build.axiom (axiom-if-when-nil))                         *3)
                  ((v (!= x nil) (= (if x w z) z))                    (build.instantiation @- (@sigma (y . w))))
                  ((v (!= x nil) (= x (if x y z)))                    (build.disjoined-commute-pequal *3))
                  ((v (!= x nil) (= (if x w z) (if x y z)))           (build.disjoined-transitivity-of-pequal @-- @-))
                  ((v (!= x nil) (= (if x y (if x w z)) (if x w z)))  (build.instantiation *3 (@sigma (z . (if x w z)))))
                  ((v (!= x nil) (= (if x y (if x w z)) (if x y z)))  (build.disjoined-transitivity-of-pequal @- @--)      *4)

                  ((v (= (if x y (if x w z)) (if x y z))
                      (= (if x y (if x w z)) (if x y z)))             (build.cut *2 *4))
                  ((= (if x y (if x w z)) (if x y z))                 (build.contraction @-)))
 :minatbl ((if . 3)))

(deftheorem theorem-if-redux-test
 :derive (= (if (if x y z) p q) (if x (if y p q) (if z p q)))
 :proof  (@derive ((v (= x nil) (= (if x y z) y))                                        (build.axiom (axiom-if-when-not-nil))      *1a)
                  ((= p p)                                                               (build.reflexivity (@term p))         *p)
                  ((v (= x nil) (= p p))                                                 (build.expansion (@formula (= x nil)) @-)  *1b)
                  ((= q q)                                                               (build.reflexivity (@term q))         *q)
                  ((v (= x nil) (= q q))                                                 (build.expansion (@formula (= x nil)) @-)  *1c)
                  ((v (= x nil) (= (if (if x y z) p q) (if y p q)))                      (build.disjoined-pequal-by-args 'if
                                                                                                                        (@formula (= x nil))
                                                                                                                        (list *1a *1b *1c))      *1)
                  ((v (= x nil) (= (if x (if y p q) (if z p q)) (if y p q)))             (build.instantiation *1a (@sigma (y . (if y p q))
                                                                                                                    (z . (if z p q)))))
                  ((v (= x nil) (= (if y p q) (if x (if y p q) (if z p q))))             (build.disjoined-commute-pequal @-))
                  ((v (= x nil) (= (if (if x y z) p q) (if x (if y p q) (if z p q))))    (build.disjoined-transitivity-of-pequal *1 @-)           **1)

                  ((v (!= x nil) (= (if x y z) z))                                       (build.axiom (axiom-if-when-nil))          *2a)
                  ((v (!= x nil) (= p p))                                                (build.expansion (@formula (!= x nil)) *p) *2b)
                  ((v (!= x nil) (= q q))                                                (build.expansion (@formula (!= x nil)) *q) *2c)
                  ((v (!= x nil) (= (if (if x y z) p q) (if z p q)))                     (build.disjoined-pequal-by-args 'if
                                                                                                                        (@formula (!= x nil))
                                                                                                                        (list *2a *2b *2c))      *2)
                  ((v (!= x nil) (= (if x (if y p q) (if z p q)) (if z p q)))            (build.instantiation *2a (@sigma (y . (if y p q))
                                                                                                                    (z . (if z p q)))))
                  ((v (!= x nil) (= (if z p q) (if x (if y p q) (if z p q))))            (build.disjoined-commute-pequal @-))
                  ((v (!= x nil) (= (if (if x y z) p q) (if x (if y p q) (if z p q))))   (build.disjoined-transitivity-of-pequal *2 @-)           **2)

                  ((v (= (if (if x y z) p q) (if x (if y p q) (if z p q)))
                      (= (if (if x y z) p q) (if x (if y p q) (if z p q))))              (build.cut **1 **2))
                  ((= (if (if x y z) p q) (if x (if y p q) (if z p q)))                  (build.contraction @-)))
 :minatbl ((if . 3)))

(deftheorem theorem-if-redux-nil
 :derive (= (if nil y z) z)
 :proof  (@derive ((= nil nil)         (build.reflexivity (@term nil)))
                  ((= (if nil y z) z)  (build.if-when-nil @- (@term y) (@term z))))
 :minatbl ((if . 3)))

(deftheorem theorem-if-redux-t
 :derive (= (if t y z) y)
 :proof  (@derive ((!= t nil)        (build.axiom (axiom-t-not-nil)))
                  ((= (if t y z) y)  (build.if-when-not-nil @- (@term y) (@term z))))
 :minatbl ((if . 3)))



(dd.close)
