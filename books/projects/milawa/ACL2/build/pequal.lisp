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
(include-book "prop")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)

(dd.open "pequal.tex")

(defderiv build.reflexivity
  :from   ((term a (? a)))
  :derive (= (? a) (? a))
  :proof  (@derive ((= x x)           (build.axiom (axiom-reflexivity)))
                   ((= (? a) (? a))   (build.instantiation @- (@sigma (x . (? a)))))))

(defderiv build.equality
  :from   ((term a1 (? a_1))
           (term b1 (? b_1))
           (term a2 (? a_2))
           (term b2 (? b_2)))
  :derive (v (!= (? a_1) (? b_1)) (v (!= (? a_2) (? b_2)) (v (!= (? a_1) (? a_2)) (= (? b_1) (? b_2)))))
  :proof (@derive ((v (!= x1 y1) (v (!= x2 y2) (v (!= x1 x2) (= y1 y2))))                                          (build.axiom (axiom-equality)))
                  ((v (!= (? a_1) (? b_1)) (v (!= (? a_2) (? b_2)) (v (!= (? a_1) (? a_2)) (= (? b_1) (? b_2)))))  (build.instantiation @- (@sigma (x1 . (? a_1)) (x2 . (? a_2)) (y1 . (? b_1)) (y2 . (? b_2)))))))

(deftheorem theorem-commutativity-of-pequal
  :derive (v (!= x y) (= y x))
  :proof (@derive ((= x x)                                             (build.reflexivity (@term x)))
                  ((v (!= x y) (= x x))                                (build.expansion (@formula (!= x y)) @-)  *1)
                  ((v (!= x y) (v (!= x x) (v (!= x x) (= y x))))      (build.equality (@term x) (@term y) (@term x) (@term x)))
                  ((v (!= x y) (v (!= x x) (= y x)))                   (build.disjoined-modus-ponens *1 @-))
                  ((v (!= x y) (= y x))                                (build.disjoined-modus-ponens *1 @-))))

(defderiv build.commute-pequal
  :derive (= (? b) (? a))
  :from   ((proof x (= (? a) (? b))))
  :proof  (cond ((equal (@term (? a)) (@term (? b)))
                 ;; Optimization.  Just use reflexivity.
                 (@derive ((= (? b) (? a))                             (build.reflexivity (@term (? a))))))
                (t
                 (@derive ((v (!= x y) (= y x))                        (build.theorem (theorem-commutativity-of-pequal)))
                          ((v (!= (? a) (? b)) (= (? b) (? a)))        (build.instantiation @- (@sigma (x . (? a)) (y . (? b)))))
                          ((= (? a) (? b))                             (@given x))
                          ((= (? b) (? a))                             (build.modus-ponens @- @--))))))

(defderiv build.disjoined-commute-pequal
  :derive (v P (= (? b) (? a)))
  :from   ((proof x (v P (= (? a) (? b)))))
  :proof  (cond ((equal (@term (? a)) (@term (? b)))
                 ;; Optimization.  Just use reflexivity and expansion.
                 (@derive ((= (? b) (? a))                             (build.reflexivity (@term (? a))))
                          ((v P (= (? b) (? a)))                       (build.expansion (@formula P) @-))))
                (t
                 (@derive ((v (!= x y) (= y x))                        (build.theorem (theorem-commutativity-of-pequal)))
                          ((v (!= (? a) (? b)) (= (? b) (? a)))        (build.instantiation @- (@sigma (x . (? a)) (y . (? b)))))
                          ((v P (v (!= (? a) (? b)) (= (? b) (? a))))  (build.expansion (@formula P) @-))
                          ((v P (= (? a) (? b)))                       (@given x))
                          ((v P (= (? b) (? a)))                       (build.disjoined-modus-ponens @- @--))))))

(defderiv build.commute-not-pequal
  :derive (!= (? b) (? a))
  :from   ((proof x (!= (? a) (? b))))
  :proof  (@derive ((v (!= x y) (= y x))                               (build.theorem (theorem-commutativity-of-pequal)))
                   ((v (= y x) (!= x y))                               (build.commute-or @-))
                   ((v (= (? a) (? b)) (!= (? b) (? a)))               (build.instantiation @- (@sigma (x . (? b)) (y . (? a)))))
                   ((!= (? a) (? b))                                   (@given x))
                   ((!= (? b) (? a))                                   (build.modus-ponens-2 @- @--))))

(defderiv build.disjoined-commute-not-pequal
  :derive (v P (!= (? b) (? a)))
  :from   ((proof x (v P (!= (? a) (? b)))))
  :proof  (@derive ((v (!= x y) (= y x))                               (build.theorem (theorem-commutativity-of-pequal)))
                   ((v (= y x) (!= x y))                               (build.commute-or @-))
                   ((v (= (? a) (? b)) (!= (? b) (? a)))               (build.instantiation @- (@sigma (x . (? b)) (y . (? a)))))
                   ((v P (v (= (? a) (? b)) (!= (? b) (? a))))         (build.expansion (@formula P) @-))
                   ((v P (!= (? a) (? b)))                             (@given x))
                   ((v P (!= (? b) (? a)))                             (build.disjoined-modus-ponens-2 @- @--))))



(deftheorem theorem-substitute-into-not-pequal
  :derive (v (= x y) (v (!= z x) (!= z y)))
  :proof  (@derive
           ((= y y)                                           (build.reflexivity (@term y)))
           ((v (!= z x) (= y y))                              (build.expansion (@formula (!= z x)) @-))
           ((v (!= z x) (v (!= y y) (v (!= z y) (= x y))))    (build.equality (@term z) (@term x) (@term y) (@term y)))
           ((v (!= z x) (v (!= z y) (= x y)))                 (build.disjoined-modus-ponens @-- @-))
           ((v (v (!= z x) (!= z y)) (= x y))                 (build.associativity @-))
           ((v (= x y) (v (!= z x) (!= z y)))                 (build.commute-or @-))))

(defderiv build.substitute-into-not-pequal
  :derive (!= (? c) (? b))
  :from   ((proof x (!= (? a) (? b)))
           (proof y (= (? c) (? a))))
  :proof  (cond
           ((equal (@term (? a)) (@term (? c)))
            ;; Optimization.  Just use the proof of a != b.
            (@derive ((!= (? c) (? b))                                           (logic.appeal-identity x))))
           (t
            (@derive ((v (= x y) (v (!= z x) (!= z y)))                          (build.theorem (theorem-substitute-into-not-pequal)))
                     ((v (= (? a) (? b)) (v (!= (? c) (? a)) (!= (? c) (? b))))  (build.instantiation @- (@sigma (x . (? a)) (y . (? b)) (z . (? c)))))
                     ((!= (? a) (? b))                                           (@given x))
                     ((v (!= (? c) (? a)) (!= (? c) (? b)))                      (build.modus-ponens-2 @- @--))
                     ((= (? c) (? a))                                            (@given y))
                     ((!= (? c) (? b))                                           (build.modus-ponens @- @--)))))
  :highlevel-override (if (equal (@term (? a)) (@term (? c)))
                          x
                        (logic.appeal 'build.substitute-into-not-pequal
                                      (@formula (!= (? c) (? b)))
                                      (list x y)
                                      nil)))

(defderiv build.disjoined-substitute-into-not-pequal-lemma-1
  :from   ((proof x (v P (!= (? a) (? b))))
           (term c (? c)))
  :derive (v P (v (!= (? c) (? a)) (!= (? c) (? b))))
  :proof  (@derive ((v (= x y) (v (!= z x) (!= z y)))                                (build.theorem (theorem-substitute-into-not-pequal)))
                   ((v (= (? a) (? b)) (v (!= (? c) (? a)) (!= (? c) (? b))))        (build.instantiation @- (@sigma (x . (? a)) (y . (? b)) (z . (? c)))))
                   ((v P (v (= (? a) (? b)) (v (!= (? c) (? a)) (!= (? c) (? b)))))  (build.expansion (@formula P) @-))
                   ((v P (!= (? a) (? b)))                                           (@given x))
                   ((v P (v (!= (? c) (? a)) (!= (? c) (? b))))                      (build.disjoined-modus-ponens-2 @- @--))))

(defderiv build.disjoined-substitute-into-not-pequal
  :derive (v P (!= (? c) (? b)))
  :from   ((proof x (v P (!= (? a) (? b))))
           (proof y (v P (= (? c) (? a)))))
  :proof  (cond ((equal (@term (? a)) (@term (? c)))
                 ;; Optimization.  Just use the proof of P v a != b
                 (@derive ((v P (!= (? c) (? b)))                                           (logic.appeal-identity x))))
                (t
                 (@derive ((v P (v (!= (? c) (? a)) (!= (? c) (? b))))                      (build.disjoined-substitute-into-not-pequal-lemma-1 x (@term (? c))))
                          ((v P (= (? c) (? a)))                                            (@given y))
                          ((v P (!= (? c) (? b)))                                           (build.disjoined-modus-ponens @- @--)))))
  :highlevel-override (if (equal (@term (? a)) (@term (? c)))
                          x
                        (LOGIC.APPEAL 'BUILD.DISJOINED-SUBSTITUTE-INTO-NOT-PEQUAL
                                      (@FORMULA (V P (!= (? C) (? B))))
                                      (LIST X Y)
                                      NIL)))


(deftheorem theorem-transitivity-of-pequal
  :derive (v (!= x y) (v (!= y z) (= x z)))
  :proof  (@derive
           ((v (!= x y) (= y x))                                                       (build.theorem (theorem-commutativity-of-pequal)))
           ((v (!= x y) (v (!= y z) (= y x)))                                          (build.disjoined-left-expansion @- (@formula (!= y z))))
           ((v (v (!= x y) (!= y z)) (= y x))                                          (build.associativity @-)                                         *1)
           ((v (!= y z) (= y z))                                                       (build.propositional-schema (@formula (= y z))))
           ((v (!= x y) (v (!= y z) (= y z)))                                          (build.expansion (@formula (!= x y)) @-))
           ((v (v (!= x y) (!= y z)) (= y z))                                          (build.associativity @-)                                         *2)
           ((= y y)                                                                    (build.reflexivity (@term y)))
           ((v (v (!= x y) (!= y z)) (= y y))                                          (build.expansion (@formula (v (!= x y) (!= y z))) @-)            *3)
           ((v (!= y x) (v (!= y z) (v (!= y y) (= x z))))                             (build.equality (@term y) (@term x) (@term y) (@term z)))
           ((v (v (!= x y) (!= y z)) (v (!= y x) (v (!= y z) (v (!= y y) (= x z)))))   (build.expansion (@formula (v (!= x y) (!= y z))) @-))
           ((v (v (!= x y) (!= y z)) (v (!= y z) (v (!= y y) (= x z))))                (build.disjoined-modus-ponens *1 @-))
           ((v (v (!= x y) (!= y z)) (v (!= y y) (= x z)))                             (build.disjoined-modus-ponens *2 @-))
           ((v (v (!= x y) (!= y z)) (= x z))                                          (build.disjoined-modus-ponens *3 @-))
           ((v (!= x y) (v (!= y z) (= x z)))                                          (build.right-associativity @-))))

(defderiv build.transitivity-of-pequal
  :derive (= (? a) (? c))
  :from   ((proof x (= (? a) (? b)))
           (proof y (= (? b) (? c))))
  :proof  (cond ((equal (@term (? a)) (@term (? c)))
                 ;; Optimization.  Just use reflexivity.
                 (@derive ((= (? a) (? c))                                             (build.reflexivity (@term (? a))))))
                ((equal (@term (? a)) (@term (? b)))
                 ;; Optimization.  Just use the proof that b = c.
                 (@derive ((= (? a) (? c))                                             (logic.appeal-identity y))))
                ((equal (@term (? b)) (@term (? c)))
                 ;; Optimization.  Just use the proof that a = b.
                 (@derive ((= (? a) (? c))                                             (logic.appeal-identity x))))
                (t
                 (@derive ((v (!= x y) (v (!= y z) (= x z)))                           (build.theorem (theorem-transitivity-of-pequal)))
                          ((v (!= (? a) (? b)) (v (!= (? b) (? c)) (= (? a) (? c))))   (build.instantiation @- (@sigma (x . (? a)) (y . (? b)) (z . (? c)))))
                          ((= (? a) (? b))                                             (@given x))
                          ((v (!= (? b) (? c)) (= (? a) (? c)))                        (build.modus-ponens @- @--))
                          ((= (? b) (? c))                                             (@given y))
                          ((= (? a) (? c))                                             (build.modus-ponens @- @--)))))
  :highlevel-override (cond ((equal (@term (? a)) (@term (? c)))
                             (build.reflexivity (@term (? a))))
                            ((equal (@term (? a)) (@term (? b)))
                             y)
                            ((equal (@term (? b)) (@term (? c)))
                             x)
                            (t
                             (LOGIC.APPEAL 'BUILD.TRANSITIVITY-OF-PEQUAL
                                           (@FORMULA (= (? A) (? C)))
                                           (LIST X Y)
                                           NIL))))

(defderiv build.disjoined-transitivity-of-pequal-lemma-1
    :derive (v P (= (? a) (? c)))
    :from   ((proof x (v P (= (? a) (? b))))
             (proof y (v P (= (? b) (? c)))))
    :proof  (@derive ((v (!= x y) (v (!= y z) (= x z)))                                 (build.theorem (theorem-transitivity-of-pequal)))
                     ((v (!= (? a) (? b)) (v (!= (? b) (? c)) (= (? a) (? c))))         (build.instantiation @- (@sigma (x . (? a)) (y . (? b)) (z . (? c)))))
                     ((v P (v (!= (? a) (? b)) (v (!= (? b) (? c)) (= (? a) (? c)))))   (build.expansion (@formula P) @-))
                     ((v P (= (? a) (? b)))                                             (@given x))
                     ((v P (v (!= (? b) (? c)) (= (? a) (? c))))                        (build.disjoined-modus-ponens @- @--))
                     ((v P (= (? b) (? c)))                                             (@given y))
                     ((v P (= (? a) (? c)))                                             (build.disjoined-modus-ponens @- @--))))

(defderiv build.disjoined-transitivity-of-pequal
  :derive (v P (= (? a) (? c)))
  :from   ((proof x (v P (= (? a) (? b))))
           (proof y (v P (= (? b) (? c)))))
  :proof  (cond ((equal (@term (? a)) (@term (? c)))
                 ;; Optimization.  Just use expansion and reflexivity.
                 (@derive ((= (? a) (? c))                          (build.reflexivity (@term (? a))))
                          ((v P (= (? a) (? c)))                    (build.expansion (@formula P) @-))))
                ((equal (@term (? a)) (@term (? b)))
                 ;; Optimization.  Just use the proof of P v b = c.
                 (@derive ((v P (= (? a) (? c)))                    (logic.appeal-identity y))))
                ((equal (@term (? b)) (@term (? c)))
                 ;; Optimization.  Just use the proof of P v a = b.
                 (@derive ((v P (= (? a) (? c)))                    (logic.appeal-identity x))))
                (t
                 (@derive ((v P (= (? a) (? c)))                    (build.disjoined-transitivity-of-pequal-lemma-1 x y)))))
  :highlevel-override (cond ((equal (@term (? a)) (@term (? c)))
                             (@derive ((= (? a) (? c))          (build.reflexivity (@term (? a))))
                                      ((v P (= (? a) (? c)))    (build.expansion (@formula P) @-))))
                            ((equal (@term (? a)) (@term (? b)))
                             y)
                            ((equal (@term (? b)) (@term (? c)))
                             x)
                            (t
                             (LOGIC.APPEAL 'BUILD.DISJOINED-TRANSITIVITY-OF-PEQUAL
                                           (@FORMULA (V P (= (? A) (? C))))
                                           (LIST X Y)
                                           NIL))))

(deftheorem theorem-not-t-or-not-nil
  :derive (v (!= x t) (!= x nil))
  :proof  (@derive ((!= t nil)               (build.axiom (axiom-t-not-nil)))
                   ((v (!= x t) (!= t nil))  (build.expansion (@formula (!= x t)) @-))
                   ((v (!= x t) (= x t))     (build.propositional-schema (@formula (= x t))))
                   ((v (!= x t) (!= x nil))  (build.disjoined-substitute-into-not-pequal @-- @-))))

(defderiv build.not-nil-from-t
  :derive (!= (? a) nil)
  :from   ((proof x (= (? a) t)))
  :proof  (@derive
           ((v (!= x t) (!= x nil))           (build.theorem (theorem-not-t-or-not-nil)))
           ((v (!= (? a) t) (!= (? a) nil))   (build.instantiation @- (@sigma (x . (? a)))))
           ((= (? a) t)                       (@given x))
           ((!= (? a) nil)                    (build.modus-ponens @- @--))))

(defderiv build.disjoined-not-nil-from-t
  :derive (v P (!= (? a) nil))
  :from   ((proof x (v P (= (? a) t))))
  :proof  (@derive ((v (!= x t) (!= x nil))                 (build.theorem (theorem-not-t-or-not-nil)))
                   ((v (!= (? a) t) (!= (? a) nil))         (build.instantiation @- (@sigma (x . (? a)))))
                   ((v P (v (!= (? a) t) (!= (? a) nil)))   (build.expansion (@formula P) @-))
                   ((v P (= (? a) t))                       (@given x))
                   ((v P (!= (? a) nil))                    (build.disjoined-modus-ponens @- @--))))

(defderiv build.not-t-from-nil
  :derive (!= (? a) t)
  :from   ((proof x (= (? a) nil)))
  :proof  (@derive ((v (!= x t) (!= x nil))           (build.theorem (theorem-not-t-or-not-nil)))
                   ((v (!= x nil) (!= x t))           (build.commute-or @-))
                   ((v (!= (? a) nil) (!= (? a) t))   (build.instantiation @- (@sigma (x . (? a)))))
                   ((= (? a) nil)                     (@given x))
                   ((!= (? a) t)                      (build.modus-ponens @- @--))))

(defderiv build.disjoined-not-t-from-nil
  :derive (v P (!= (? a) t))
  :from   ((proof x (v P (= (? a) nil))))
  :proof  (@derive ((v (!= x t) (!= x nil))                 (build.theorem (theorem-not-t-or-not-nil)))
                   ((v (!= x nil) (!= x t))                 (build.commute-or @-))
                   ((v (!= (? a) nil) (!= (? a) t))         (build.instantiation @- (@sigma (x . (? a)))))
                   ((v P (v (!= (? a) nil) (!= (? a) t)))   (build.expansion (@formula P) @-))
                   ((v P (= (? a) nil))                     (@given x))
                   ((v P (!= (? a) t))                      (build.disjoined-modus-ponens @- @--))))

(dd.close)
