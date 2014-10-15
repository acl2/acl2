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
(include-book "lambda")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


(dd.open "equal.tex")

(dd.section "Equal manipulation")


(deftheorem theorem-reflexivity-of-equal
  :derive (= (equal x x) t)
  :proof  (@derive ((v (!= x y) (= (equal x y) t))                                    (build.axiom (axiom-equal-when-same)))
                   ((v (!= x x) (= (equal x x) t))                                    (build.instantiation @- (@sigma (y . x))))
                   ((= x x)                                                           (build.reflexivity (@term x)))
                   ((= (equal x x) t)                                                 (build.modus-ponens @- @--)))
  :minatbl ((equal . 2)))

(defderiv build.equal-reflexivity
  :derive (= (equal (? a) (? a)) t)
  :from   ((term a (? a)))
  :proof  (@derive ((= (equal x x) t)                                                 (build.theorem (theorem-reflexivity-of-equal)))
                   ((= (equal (? a) (? a)) t)                                         (build.instantiation @- (@sigma (x . (? a))))))
  :minatbl ((equal . 2)))



(deftheorem theorem-equal-nil-or-t
  :derive (v (= (equal x y) nil)
             (= (equal x y) t))
  :proof  (@derive ((v (= x y) (= (equal x y) nil))                                   (build.axiom (axiom-equal-when-diff)))
                   ((v (!= x y) (= (equal x y) t))                                    (build.axiom (axiom-equal-when-same)))
                   ((v (= (equal x y) nil) (= (equal x y) t))                         (build.cut @-- @-)))
  :minatbl ((equal . 2)))

(defderiv build.equal-t-from-not-nil
  :derive (= (equal (? a) (? b)) t)
  :from   ((proof x (!= (equal (? a) (? b)) nil)))
  :proof  (@derive ((v (= (equal x y) nil) (= (equal x y) t))                         (build.theorem (theorem-equal-nil-or-t)))
                   ((v (= (equal (? a) (? b)) nil) (= (equal (? a) (? b)) t))         (build.instantiation @- (@sigma (x . (? a)) (y . (? b)))))
                   ((!= (equal (? a) (? b)) nil)                                      (@given x))
                   ((= (equal (? a) (? b)) t)                                         (build.modus-ponens-2 @- @--))))

(defderiv build.disjoined-equal-t-from-not-nil
  :derive (v P (= (equal (? a) (? b)) t))
  :from   ((proof x (v P (!= (equal (? a) (? b)) nil))))
  :proof  (@derive ((v (= (equal x y) nil) (= (equal x y) t))                         (build.theorem (theorem-equal-nil-or-t)))
                   ((v (= (equal (? a) (? b)) nil) (= (equal (? a) (? b)) t))         (build.instantiation @- (@sigma (x . (? a)) (y . (? b)))))
                   ((v P (v (= (equal (? a) (? b)) nil) (= (equal (? a) (? b)) t)))   (build.expansion (@formula P) @-))
                   ((v P (!= (equal (? a) (? b)) nil))                                (@given x))
                   ((v P (= (equal (? a) (? b)) t))                                   (build.disjoined-modus-ponens-2 @- @--))))

(defderiv build.equal-nil-from-not-t
  :derive (= (equal (? a) (? b)) nil)
  :from   ((proof x (!= (equal (? a) (? b)) t)))
  :proof  (@derive ((v (= (equal x y) nil) (= (equal x y) t))                         (build.theorem (theorem-equal-nil-or-t)))
                   ((v (= (equal x y) t) (= (equal x y) nil))                         (build.commute-or @-))
                   ((v (= (equal (? a) (? b)) t) (= (equal (? a) (? b)) nil))         (build.instantiation @- (@sigma (x . (? a)) (y . (? b)))))
                   ((!= (equal (? a) (? b)) t)                                        (@given x))
                   ((= (equal (? a) (? b)) nil)                                       (build.modus-ponens-2 @- @--))))

(defderiv build.disjoined-equal-nil-from-not-t
  :derive (v P (= (equal (? a) (? b)) nil))
  :from   ((proof x (v P (!= (equal (? a) (? b)) t))))
  :proof  (@derive ((v (= (equal x y) nil) (= (equal x y) t))                         (build.theorem (theorem-equal-nil-or-t)))
                   ((v (= (equal x y) t) (= (equal x y) nil))                         (build.commute-or @-))
                   ((v (= (equal (? a) (? b)) t) (= (equal (? a) (? b)) nil))         (build.instantiation @- (@sigma (x . (? a)) (y . (? b)))))
                   ((v P (v (= (equal (? a) (? b)) t) (= (equal (? a) (? b)) nil)))   (build.expansion (@formula P) @-))
                   ((v P (!= (equal (? a) (? b)) t))                                  (@given x))
                   ((v P (= (equal (? a) (? b)) nil))                                 (build.disjoined-modus-ponens-2 @- @--))))

(defderiv build.equal-from-pequal
 :derive (= (equal (? a) (? b)) t)
 :from   ((proof x (= (? a) (? b))))
 :proof  (cond ((equal (@term (? a)) (@term (? b)))
                ;; Optimization.  We can just use reflexivity.
                (@derive ((= (equal (? a) (? b)) t)                               (build.equal-reflexivity (@term (? a))))))
               (t
                (@derive ((v (!= x y) (= (equal x y) t))                          (build.axiom (axiom-equal-when-same)))
                         ((v (!= (? a) (? b)) (= (equal (? a) (? b)) t))          (build.instantiation @- (@sigma (x . (? a)) (y . (? b)))))
                         ((= (? a) (? b))                                         (@given x))
                         ((= (equal (? a) (? b)) t)                               (build.modus-ponens @- @--)))))
 :minatbl ((equal . 2))
 :highlevel-override (if (equal (@term (? a)) (@term (? b)))
                         (build.equal-reflexivity (@term (? a)))
                       (LOGIC.APPEAL 'BUILD.EQUAL-FROM-PEQUAL
                                     (@FORMULA (= (EQUAL (? A) (? B)) T))
                                     (LIST X)
                                     NIL)))

(defderiv build.disjoined-equal-from-pequal
  :derive (v P (= (equal (? a) (? b)) t))
  :from   ((proof x (v P (= (? a) (? b)))))
  :proof  (cond ((equal (@term (? a)) (@term (? b)))
                 ;; Optimization.  Just use reflexivity and expansion.
                 (@derive ((= (equal (? a) (? b)) t)                              (build.equal-reflexivity (@term (? a))))
                          ((v P (= (equal (? a) (? b)) t))                        (build.expansion (@formula P) @-))))
                (t
                 (@derive ((v (!= x y) (= (equal x y) t))                         (build.axiom (axiom-equal-when-same)))
                          ((v (!= (? a) (? b)) (= (equal (? a) (? b)) t))         (build.instantiation @- (@sigma (x . (? a)) (y . (? b)))))
                          ((v P (v (!= (? a) (? b)) (= (equal (? a) (? b)) t)))   (build.expansion (@formula P) @-))
                          ((v P (= (? a) (? b)))                                  (@given x))
                          ((v P (= (equal (? a) (? b)) t))                        (build.disjoined-modus-ponens @- @--)))))
  :minatbl ((equal . 2))
  :highlevel-override (if (equal (@term (? a)) (@term (? b)))
                          (@derive ((= (equal (? a) (? b)) t)         (build.equal-reflexivity (@term (? a))))
                                   ((v P (= (equal (? a) (? b)) t))   (build.expansion (@formula P) @-)))
                        (LOGIC.APPEAL 'BUILD.DISJOINED-EQUAL-FROM-PEQUAL
                                      (@FORMULA (V P (= (EQUAL (? A) (? B)) T)))
                                      (LIST X)
                                      NIL)))

(defderiv build.not-pequal-from-not-equal
 :derive (!= (? a) (? b))
 :from   ((proof x (= (equal (? a) (? b)) nil)))
 :proof  (@derive ((v (!= x y) (= (equal x y) t))                                 (build.axiom (axiom-equal-when-same)))
                  ((v (= (equal x y) t) (!= x y))                                 (build.commute-or @-))
                  ((v (= (equal (? a) (? b)) t) (!= (? a) (? b)))                 (build.instantiation @- (@sigma (x . (? a)) (y . (? b))))  *1)
                  ((= (equal (? a) (? b)) nil)                                    (@given x))
                  ((!= (equal (? a) (? b)) t)                                     (build.not-t-from-nil @-))
                  ((!= (? a) (? b))                                               (build.modus-ponens-2 @- *1))))

(defderiv build.disjoined-not-pequal-from-not-equal
 :derive (v P (!= (? a) (? b)))
 :from   ((proof x (v P (= (equal (? a) (? b)) nil))))
 :proof  (@derive ((v (!= x y) (= (equal x y) t))                                 (build.axiom (axiom-equal-when-same)))
                  ((v (= (equal x y) t) (!= x y))                                 (build.commute-or @-))
                  ((v (= (equal (? a) (? b)) t) (!= (? a) (? b)))                 (build.instantiation @- (@sigma (x . (? a)) (y . (? b)))))
                  ((v P (v (= (equal (? a) (? b)) t) (!= (? a) (? b))))           (build.expansion (@formula P) @-)                           *1)
                  ((v P (= (equal (? a) (? b)) nil))                              (@given x))
                  ((v P (!= (equal (? a) (? b)) t))                               (build.disjoined-not-t-from-nil @-))
                  ((v P (!= (? a) (? b)))                                         (build.disjoined-modus-ponens-2 @- *1))))



(deftheorem theorem-symmetry-of-equal
  :derive (= (equal x y) (equal y x))
  :proof  (@derive ((v (= x y) (= (equal x y) nil))           (build.axiom (axiom-equal-when-diff)) *1)
                   ((v (= y x) (= (equal y x) nil))           (build.instantiation @- (@sigma (x . y) (y . x))))
                   ((v (= y x) (= nil (equal y x)))           (build.disjoined-commute-pequal @-))
                   ((v (= nil (equal y x)) (= y x))           (build.commute-or @-))
                   ((v (= nil (equal y x)) (= x y))           (build.disjoined-commute-pequal @-))
                   ((v (= x y) (= nil (equal y x)))           (build.commute-or @-))
                   ((v (= x y) (= (equal x y) (equal y x)))   (build.disjoined-transitivity-of-pequal *1 @-) *2)
                   ;; ---
                   ((v (!= x y) (= (equal x y) t))            (build.axiom (axiom-equal-when-same)) *3)
                   ((v (!= y x) (= (equal y x) t))            (build.instantiation @- (@sigma (x . y) (y . x))))
                   ((v (!= y x) (= t (equal y x)))            (build.disjoined-commute-pequal @-))
                   ((v (= t (equal y x)) (!= y x))            (build.commute-or @-))
                   ((v (= t (equal y x)) (!= x y))            (build.disjoined-commute-not-pequal @-))
                   ((v (!= x y) (= t (equal y x)))            (build.commute-or @-))
                   ((v (!= x y) (= (equal x y) (equal y x)))  (build.disjoined-transitivity-of-pequal *3 @-) *4)
                   ;; ---
                   ((v (= (equal x y) (equal y x))
                       (= (equal x y) (equal y x)))           (build.cut *2 *4))
                   ((= (equal x y) (equal y x))               (build.contraction @-)))
  :minatbl ((equal . 2)))

(defderiv build.commute-equal
  :derive (= (equal (? b) (? a)) t)
  :from   ((proof x (= (equal (? a) (? b)) t)))
  :proof  (cond ((equal (@term (? a)) (@term (? b)))
                 ;; Optimziation.  Just use reflexivity.
                 (@derive ((= (equal (? b) (? a)) t)                           (build.equal-reflexivity (@term (? a))))))
                (t
                 (@derive ((= (equal x y) (equal y x))                         (build.theorem (theorem-symmetry-of-equal)))
                          ((= (equal (? b) (? a)) (equal (? a) (? b)))         (build.instantiation @- (@sigma (x . (? b)) (y . (? a)))))
                          ((= (equal (? a) (? b)) t)                           (@given x))
                          ((= (equal (? b) (? a)) t)                           (build.transitivity-of-pequal @-- @-)))))
  :highlevel-override (if (equal (@term (? a)) (@term (? b)))
                          (build.equal-reflexivity (@term (? a)))
                        (LOGIC.APPEAL 'BUILD.COMMUTE-EQUAL
                                      (@FORMULA (= (EQUAL (? B) (? A)) T))
                                      (LIST X)
                                      NIL)))

(defderiv build.disjoined-commute-equal
  :derive (v P (= (equal (? b) (? a)) t))
  :from   ((proof x (v P (= (equal (? a) (? b)) t))))
  :proof  (cond ((equal (@term (? a)) (@term (? b)))
                 ;; Optimization.  Just use reflexivity and expansion.
                 (@derive ((= (equal (? b) (? a)) t)                           (build.equal-reflexivity (@term (? a))))
                          ((v P (= (equal (? b) (? a)) t))                     (build.expansion (@formula P) @-))))
                (t
                 (@derive ((= (equal x y) (equal y x))                         (build.theorem (theorem-symmetry-of-equal)))
                          ((= (equal (? b) (? a)) (equal (? a) (? b)))         (build.instantiation @- (@sigma (x . (? b)) (y . (? a)))))
                          ((v P (= (equal (? b) (? a)) (equal (? a) (? b))))   (build.expansion (@formula P) @-))
                          ((v P (= (equal (? a) (? b)) t))                     (@given x))
                          ((v P (= (equal (? b) (? a)) t))                     (build.disjoined-transitivity-of-pequal @-- @-)))))
  :highlevel-override (if (equal (@term (? a)) (@term (? b)))
                          (@derive ((= (equal (? b) (? a)) t)          (build.equal-reflexivity (@term (? a))))
                                   ((v P (= (equal (? b) (? a)) t))    (build.expansion (@formula P) @-)))
                        (LOGIC.APPEAL 'BUILD.DISJOINED-COMMUTE-EQUAL
                                      (@FORMULA (V P (= (EQUAL (? B) (? A)) T)))
                                      (LIST X)
                                      NIL)))


(deftheorem theorem-transitivity-of-equal
  :derive (v (!= (equal x y) t)
             (v (!= (equal y z) t)
                (= (equal x z) t)))
  :proof  (@derive
           ((v (= x y) (= (equal x y) nil))                          (build.axiom (axiom-equal-when-diff)))
           ((v (= x y) (!= (equal x y) t))                           (build.disjoined-not-t-from-nil @-)                   *1)

           ((v (!= (equal y z) t) (v (= x y) (!= (equal x y) t)))    (build.expansion (@formula (!= (equal y z) t)) @-))
           ((v (v (!= (equal y z) t) (= x y)) (!= (equal x y) t))    (build.associativity @-))
           ((v (!= (equal x y) t) (v (!= (equal y z) t) (= x y)))    (build.commute-or @-))
           ((v (v (!= (equal x y) t) (!= (equal y z) t)) (= x y))    (build.associativity @-)                                *2)

           ((v (= y z) (!= (equal y z) t))                           (build.instantiation *1 (@sigma (x . y) (y . z))))
           ((v (!= (equal y z) t) (= y z))                           (build.commute-or @-))
           ((v (!= (equal x y) t) (v (!= (equal y z) t) (= y z)))    (build.expansion (@formula (!= (equal x y) t)) @-))
           ((v (v (!= (equal x y) t) (!= (equal y z) t)) (= y z))    (build.associativity @-))
           ((v (v (!= (equal x y) t) (!= (equal y z) t)) (= x z))    (build.disjoined-transitivity-of-pequal *2 @-)          *3)

           ((v (v (!= (equal x y) t) (!= (equal y z) t))
               (= (equal x z) t))                                    (build.disjoined-equal-from-pequal @-))
           ((v (!= (equal x y) t)
               (v (!= (equal y z) t)
                  (= (equal x z) t)))                                (build.right-associativity @-)))
  :minatbl ((equal . 2)))

(defderiv build.transitivity-of-equal
  :derive (= (equal (? a) (? c)) t)
  :from   ((proof x (= (equal (? a) (? b)) t))
           (proof y (= (equal (? b) (? c)) t)))
  :proof  (cond ((equal (@term (? a)) (@term (? c)))
                 ;; Optimization.  Just use reflexivity.
                 (@derive ((= (equal (? a) (? c)) t)     (build.equal-reflexivity (@term (? a))))))
                ((equal (@term (? a)) (@term (? b)))
                 ;; Optimization.  Just use the proof of (equal b c) = t.
                 (logic.appeal-identity y))
                ((equal (@term (? b)) (@term (? c)))
                 ;; Optimization.  Just use teh proof of (equal a b) = t.
                 (logic.appeal-identity x))
                (t
                 (@derive ((v (!= (equal x y) t) (v (!= (equal y z) t) (= (equal x z) t)))                           (build.theorem (theorem-transitivity-of-equal)))
                          ((v (!= (equal (? a) (? b)) t) (v (!= (equal (? b) (? c)) t) (= (equal (? a) (? c)) t)))   (build.instantiation @- (@sigma (x . (? a)) (y . (? b)) (z . (? c)))))
                          ((= (equal (? a) (? b)) t)                                                                 (@given x))
                          ((v (!= (equal (? b) (? c)) t) (= (equal (? a) (? c)) t))                                  (build.modus-ponens @- @--))
                          ((= (equal (? b) (? c)) t)                                                                 (@given y))
                          ((= (equal (? a) (? c)) t)                                                                 (build.modus-ponens @- @--)))))
  :highlevel-override (cond ((equal (@term (? a)) (@term (? c)))
                             (build.equal-reflexivity (@term (? a))))
                            ((equal (@term (? a)) (@term (? b)))
                             y)
                            ((equal (@term (? b)) (@term (? c)))
                             x)
                            (t
                             (LOGIC.APPEAL 'BUILD.TRANSITIVITY-OF-EQUAL
                                           (@FORMULA (= (EQUAL (? A) (? C)) T))
                                           (LIST X Y)
                                           NIL))))

(defderiv build.disjoined-transitivity-of-equal
  :derive (v P (= (equal (? a) (? c)) t))
  :from   ((proof x (v P (= (equal (? a) (? b)) t)))
           (proof y (v P (= (equal (? b) (? c)) t))))
  :proof  (cond ((equal (@term (? a)) (@term (? c)))
                 ;; Optimization. Just use reflexivity and expansion.
                 (@derive ((= (equal (? a) (? c)) t)                                                                         (build.equal-reflexivity (@term (? a))))
                          ((v P (= (equal (? a) (? c)) t))                                                                   (build.expansion (@formula P) @-))))
                ((equal (@term (? a)) (@term (? b)))
                 ;; Optimization. Just use the proof of P v b = c.
                 (logic.appeal-identity y))
                ((equal (@term (? b)) (@term (? c)))
                 ;; Optimization.  Just use the proof of P v a = b.
                 (logic.appeal-identity x))
                (t
                 (@derive ((v (!= (equal x y) t) (v (!= (equal y z) t) (= (equal x z) t)))                                 (build.theorem (theorem-transitivity-of-equal)))
                          ((v (!= (equal (? a) (? b)) t) (v (!= (equal (? b) (? c)) t) (= (equal (? a) (? c)) t)))         (build.instantiation @- (@sigma (x . (? a)) (y . (? b)) (z . (? c)))))
                          ((v P (v (!= (equal (? a) (? b)) t) (v (!= (equal (? b) (? c)) t) (= (equal (? a) (? c)) t))))   (build.expansion (@formula P) @-))
                          ((v P (= (equal (? a) (? b)) t))                                                                 (@given x))
                          ((v P (v (!= (equal (? b) (? c)) t) (= (equal (? a) (? c)) t)))                                  (build.disjoined-modus-ponens @- @--))
                          ((v P (= (equal (? b) (? c)) t))                                                                 (@given y))
                          ((v P (= (equal (? a) (? c)) t))                                                                 (build.disjoined-modus-ponens @- @--)))))
  :highlevel-override (cond ((equal (@term (? a)) (@term (? c)))
                             (@derive ((= (equal (? a) (? c)) t)         (build.equal-reflexivity (@term (? a))))
                                      ((v P (= (equal (? a) (? c)) t))   (build.expansion (@formula P) @-))))
                            ((equal (@term (? a)) (@term (? b)))
                             y)
                            ((equal (@term (? b)) (@term (? c)))
                             x)
                            (t
                             (LOGIC.APPEAL 'BUILD.DISJOINED-TRANSITIVITY-OF-EQUAL
                                           (@FORMULA (V P (= (EQUAL (? A) (? C)) T)))
                                           (LIST X Y)
                                           NIL))))


(defderiv build.not-pequal-constants
  :derive (!= (? c1) (? c2))
  :from ((term c1 (? c1))
         (term c2 (? c2)))
  :where ((logic.constantp (@term (? c1)))
          (logic.constantp (@term (? c2)))
          (not (equal (@term (? c1)) (@term (? c2)))))
  :proof (@derive
          ((= (equal (? c1) (? c2)) nil)                                          (build.base-eval (@term (equal (? c1) (? c2)))))
          ((!= (? c1) (? c2))                                                     (build.not-pequal-from-not-equal @-)))
  :minatbl ((equal . 2)))

(defund build.equal-from-pequal-list (x)
  (declare (xargs :guard (and (logic.appeal-listp x)
                              (logic.all-atomicp (logic.strip-conclusions x)))))
  (if (consp x)
      (cons (build.equal-from-pequal (car x))
            (build.equal-from-pequal-list (cdr x)))
    nil))

(defobligations build.equal-from-pequal-list
  (build.equal-from-pequal))

(encapsulate
 ()
 (local (in-theory (enable build.equal-from-pequal-list)))

 (defthm len-of-build.equal-from-pequal-list
   (equal (len (build.equal-from-pequal-list x))
          (len x)))

 (defthm forcing-logic.appeal-listp-of-build.equal-from-pequal-list
   (implies (force (and (logic.appeal-listp x)
                        (logic.all-atomicp (logic.strip-conclusions x))))
            (equal (logic.appeal-listp (build.equal-from-pequal-list x))
                   t)))

 (defthm forcing-logic.strip-conclusions-of-build.equal-from-pequal-list
   (implies (force (and (logic.appeal-listp x)
                        (logic.all-atomicp (logic.strip-conclusions x))))
            (equal (logic.strip-conclusions (build.equal-from-pequal-list x))
                   (logic.pequal-list (logic.function-list 'equal (list2-list (logic.=lhses (logic.strip-conclusions x))
                                                                              (logic.=rhses (logic.strip-conclusions x))))
                                      (repeat ''t (len x)))))
   :rule-classes ((:rewrite :backchain-limit-lst 0)))

 (defthm@ forcing-logic.proof-listp-of-build.equal-from-pequal-list
   (implies (force (and (logic.appeal-listp x)
                        (logic.all-atomicp (logic.strip-conclusions x))
                        ;; ---
                        (logic.proof-listp x axioms thms atbl)
                        (equal (cdr (lookup 'equal atbl)) 2)
                        (@obligations build.equal-from-pequal-list)))
            (equal (logic.proof-listp (build.equal-from-pequal-list x) axioms thms atbl)
                   t))))





(defund build.equal-reflexivity-list (x)
  (declare (xargs :guard (logic.term-listp x)))
  (if (consp x)
      (cons (build.equal-reflexivity (car x))
            (build.equal-reflexivity-list (cdr x)))
    nil))

(defobligations build.equal-reflexivity-list
  (build.equal-reflexivity))

(encapsulate
 ()
 (local (in-theory (enable build.equal-reflexivity-list)))

 (defthm len-of-build.equal-reflexivity-list
   (equal (len (build.equal-reflexivity-list x))
          (len x)))

 (defthm forcing-logic.appeal-listp-of-build.equal-reflexivity-list
   (implies (force (logic.term-listp x))
            (equal (logic.appeal-listp (build.equal-reflexivity-list x))
                   t)))

 (defthm forcing-logic.strip-conclusions-of-build.equal-reflexivity-list
   (implies (force (logic.term-listp x))
            (equal (logic.strip-conclusions (build.equal-reflexivity-list x))
                   (logic.pequal-list (logic.function-list 'equal (list2-list x x))
                                      (repeat ''t (len x)))))
   :rule-classes ((:rewrite :backchain-limit-lst 0)))

 (defthm@ forcing-logic.proof-listp-of-build.equal-reflexivity-list
   (implies (force (and (logic.term-listp x)
                        ;; ---
                        (logic.term-list-atblp x atbl)
                        (equal (cdr (lookup 'equal atbl)) 2)
                        (@obligations build.equal-reflexivity-list)))
            (equal (logic.proof-listp (build.equal-reflexivity-list x) axioms thms atbl)
                   t))))



(defund build.disjoined-equal-from-pequal-list (x)
  (declare (xargs :guard (and (logic.appeal-listp x)
                              (logic.all-disjunctionsp (logic.strip-conclusions x))
                              (logic.all-atomicp (logic.vrhses (logic.strip-conclusions x))))))
  (if (consp x)
      (cons (build.disjoined-equal-from-pequal (car x))
            (build.disjoined-equal-from-pequal-list (cdr x)))
    nil))

(defobligations build.disjoined-equal-from-pequal-list
  (build.disjoined-equal-from-pequal))

(encapsulate
 ()
 (local (in-theory (enable build.disjoined-equal-from-pequal-list)))

 (defthm len-of-build.disjoined-equal-from-pequal-list
   (equal (len (build.disjoined-equal-from-pequal-list x))
          (len x)))

 (defthm forcing-logic.appeal-listp-of-build.disjoined-equal-from-pequal-list
   (implies (force (and (logic.appeal-listp x)
                        (logic.all-disjunctionsp (logic.strip-conclusions x))
                        (logic.all-atomicp (logic.vrhses (logic.strip-conclusions x)))))
            (equal (logic.appeal-listp (build.disjoined-equal-from-pequal-list x))
                   t)))

 (defthm forcing-logic.strip-conclusions-of-build.disjoined-equal-from-pequal-list
   (implies (force (and (logic.appeal-listp x)
                        (logic.all-disjunctionsp (logic.strip-conclusions x))
                        (logic.all-atomicp (logic.vrhses (logic.strip-conclusions x)))))
            (equal (logic.strip-conclusions (build.disjoined-equal-from-pequal-list x))
                   (logic.por-list (logic.vlhses (logic.strip-conclusions x))
                                   (logic.pequal-list
                                    (logic.function-list 'equal (list2-list (logic.=lhses (logic.vrhses (logic.strip-conclusions x)))
                                                                            (logic.=rhses (logic.vrhses (logic.strip-conclusions x)))))
                                    (repeat ''t (len x))))))
   :rule-classes ((:rewrite :backchain-limit-lst 0)))

 (defthm@ forcing-logic.proof-listp-of-build.disjoined-equal-from-pequal-list
   (implies (force (and (logic.appeal-listp x)
                        (logic.all-disjunctionsp (logic.strip-conclusions x))
                        (logic.all-atomicp (logic.vrhses (logic.strip-conclusions x)))
                        ;; ---
                        (logic.proof-listp x axioms thms atbl)
                        (force (equal (cdr (lookup 'equal atbl)) 2))
                        (@obligations build.disjoined-equal-from-pequal-list)))
            (equal (logic.proof-listp (build.disjoined-equal-from-pequal-list x) axioms thms atbl)
                   t))))


(dd.subsection "Special conversion rules")

(defderiv build.pequal-from-equal
  :derive (= (? a) (? b))
  :from ((proof x (= (equal (? a) (? b)) t)))
  :proof (cond ((equal (@term (? a)) (@term (? b)))
                ;; Optimization.  Just use reflexivity.
                (@derive ((= (? a) (? b))   (build.reflexivity (@term (? a))))))
               (t
                (@derive ((v (= x y) (= (equal x y) nil))                  (build.axiom (axiom-equal-when-diff)))
                         ((v (= (equal x y) nil) (= x y))                  (build.commute-or @-))
                         ((v (= (equal (? a) (? b)) nil) (= (? a) (? b)))  (build.instantiation @- (@sigma (x . (? a)) (y . (? b))))  *1)
                         ((= (equal (? a) (? b)) t)                        (@given x))
                         ((!= (equal (? a) (? b)) nil)                     (build.not-nil-from-t @-))
                         ((= (? a) (? b))                                  (build.modus-ponens-2 @- *1)))))
  :highlevel-override (if (equal (@term (? a)) (@term (? b)))
                          (build.reflexivity (@term (? a)))
                        (LOGIC.APPEAL 'BUILD.PEQUAL-FROM-EQUAL
                                      (@FORMULA (= (? A) (? B)))
                                      (LIST X)
                                      NIL)))

(defderiv build.disjoined-pequal-from-equal
 :derive (v P (= (? a) (? b)))
 :from   ((proof x (v P (= (equal (? a) (? b)) t))))
 :proof  (@derive ((v (= x y) (= (equal x y) nil))                         (build.axiom (axiom-equal-when-diff)))
                  ((v (= (equal x y) nil) (= x y))                         (build.commute-or @-))
                  ((v (= (equal (? a) (? b)) nil) (= (? a) (? b)))         (build.instantiation @- (@sigma (x . (? a)) (y . (? b)))))
                  ((v P (v (= (equal (? a) (? b)) nil) (= (? a) (? b))))   (build.expansion (@formula P) @-) *1)
                  ((v P (= (equal (? a) (? b)) t))                         (@given x))
                  ((v P (!= (equal (? a) (? b)) nil))                      (build.disjoined-not-nil-from-t @-))
                  ((v P (= (? a) (? b)))                                   (build.disjoined-modus-ponens-2 @- *1))))

(defderiv build.not-equal-from-not-pequal
 :derive (= (equal (? a) (? b)) nil)
 :from   ((proof x (!= (? a) (? b))))
 :proof  (@derive ((v (= x y) (= (equal x y) nil))                  (build.axiom (axiom-equal-when-diff)))
                  ((v (= (? a) (? b)) (= (equal (? a) (? b)) nil))  (build.instantiation @- (@sigma (x . (? a)) (y . (? b)))))
                  ((!= (? a) (? b))                                 (@given x))
                  ((= (equal (? a) (? b)) nil)                      (build.modus-ponens-2 @- @--)))
 :minatbl ((equal . 2)))

(defderiv build.disjoined-not-equal-from-not-pequal
 :derive (v P (= (equal (? a) (? b)) nil))
 :from   ((proof x (v P (!= (? a) (? b)))))
 :proof  (@derive ((v (= x y) (= (equal x y) nil))                        (build.axiom (axiom-equal-when-diff)))
                  ((v (= (? a) (? b)) (= (equal (? a) (? b)) nil))        (build.instantiation @- (@sigma (x . (? a)) (y . (? b)))))
                  ((v P (v (= (? a) (? b)) (= (equal (? a) (? b)) nil)))  (build.expansion (@formula P) @-))
                  ((v P (!= (? a) (? b)))                                 (@given x))
                  ((v P (= (equal (? a) (? b)) nil))                      (build.disjoined-modus-ponens-2 @- @--)))
 :minatbl ((equal . 2)))

(deftheorem theorem-equal-of-equal-and-t
   :derive (= (equal (equal x y) t) (equal x y))
   :proof (@derive
           ((v (= x y) (= (equal x y) nil))                               (build.axiom (axiom-equal-when-diff)) *1a)
           ((v (= x y) (!= (equal x y) t))                                (build.disjoined-not-t-from-nil @-))
           ((v (= x y) (= (equal (equal x y) t) nil))                     (build.disjoined-not-equal-from-not-pequal @-))
           ((v (= x y) (= nil (equal x y)))                               (build.disjoined-commute-pequal *1a))
           ((v (= x y) (= (equal (equal x y) t) (equal x y)))             (build.disjoined-transitivity-of-pequal @-- @-)     *1)
           ;; ---
           ((v (!= x y) (= (equal x y) t))                                (build.axiom (axiom-equal-when-same)))
           ((v (!= x y) (= (equal (equal x y) t) t))                      (build.disjoined-equal-from-pequal @-))
           ((v (!= x y) (= t (equal x y)))                                (build.disjoined-commute-pequal @--))
           ((v (!= x y) (= (equal (equal x y) t) (equal x y)))            (build.disjoined-transitivity-of-pequal @-- @-))
           ;; ---
           ((v (= (equal (equal x y) t) (equal x y))
               (= (equal (equal x y) t) (equal x y)))                     (build.cut *1 @-))
           ((= (equal (equal x y) t) (equal x y))                         (build.contraction @-)))
   :minatbl ((equal . 2)))



;; (dd.subsection "Special equal rules")

(defund build.pequal-from-equal-list (x)
  (declare (xargs :guard (and (logic.appeal-listp x)
                              (let ((concs (logic.strip-conclusions x)))
                                (and (logic.all-atomicp concs)
                                     (let ((lhses (logic.=lhses concs))
                                           (rhses (logic.=rhses concs)))
                                       (and (all-equalp ''t rhses)
                                            (logic.all-functionsp lhses)
                                            (all-equalp 'equal (logic.strip-function-names lhses))
                                            (all-equalp 2 (strip-lens (logic.strip-function-args lhses))))))))))
  (if (consp x)
      (cons (build.pequal-from-equal (car x))
            (build.pequal-from-equal-list (cdr x)))
    nil))

(defobligations build.pequal-from-equal-list
  (build.pequal-from-equal))

(encapsulate
 ()
 (local (in-theory (enable build.pequal-from-equal-list)))

 (defthm len-of-build.pequal-from-equal-list
   (equal (len (build.pequal-from-equal-list x))
          (len x)))

 (defthm forcing-logic.appeal-listp-of-build.pequal-from-equal-list
   (implies (force (and (logic.appeal-listp x)
                        (logic.all-atomicp (logic.strip-conclusions x))
                        (all-equalp ''t (logic.=rhses (logic.strip-conclusions x)))
                        (logic.all-functionsp (logic.=lhses (logic.strip-conclusions x)))
                        (all-equalp 'equal (logic.strip-function-names (logic.=lhses (logic.strip-conclusions x))))
                        (all-equalp 2 (strip-lens (logic.strip-function-args (logic.=lhses (logic.strip-conclusions x)))))))
            (equal (logic.appeal-listp (build.pequal-from-equal-list x))
                   t)))

 (defthm forcing-logic.strip-conclusions-of-build.pequal-from-equal-list
   (implies (force (and (logic.appeal-listp x)
                        (logic.all-atomicp (logic.strip-conclusions x))
                        (all-equalp ''t (logic.=rhses (logic.strip-conclusions x)))
                        (logic.all-functionsp (logic.=lhses (logic.strip-conclusions x)))
                        (all-equalp 'equal (logic.strip-function-names (logic.=lhses (logic.strip-conclusions x))))
                        (all-equalp 2 (strip-lens (logic.strip-function-args (logic.=lhses (logic.strip-conclusions x)))))))
            (equal (logic.strip-conclusions (build.pequal-from-equal-list x))
                   (logic.pequal-list (strip-firsts (logic.strip-function-args (logic.=lhses (logic.strip-conclusions x))))
                                      (strip-seconds (logic.strip-function-args (logic.=lhses (logic.strip-conclusions x)))))))
   :rule-classes ((:rewrite :backchain-limit-lst 0)))

 (defthm@ forcing-logic.proof-listp-of-build.pequal-from-equal-list
   (implies (force (and (logic.appeal-listp x)
                        (logic.all-atomicp (logic.strip-conclusions x))
                        (all-equalp ''t (logic.=rhses (logic.strip-conclusions x)))
                        (logic.all-functionsp (logic.=lhses (logic.strip-conclusions x)))
                        (all-equalp 'equal (logic.strip-function-names (logic.=lhses (logic.strip-conclusions x))))
                        (all-equalp 2 (strip-lens (logic.strip-function-args (logic.=lhses (logic.strip-conclusions x)))))
                        ;; ---
                        (logic.proof-listp x axioms thms atbl)
                        (@obligations build.pequal-from-equal-list)))
            (equal (logic.proof-listp (build.pequal-from-equal-list x) axioms thms atbl)
                   t))))



(defund build.disjoined-pequal-from-equal-list (x)
   (declare (xargs :guard (and (logic.appeal-listp x)
                               (let ((concs (logic.strip-conclusions x)))
                                 (and (logic.all-disjunctionsp concs)
                                      (let ((equals (logic.vrhses concs)))
                                        (and (logic.all-atomicp equals)
                                             (let ((lhses (logic.=lhses equals))
                                                   (rhses (logic.=rhses equals)))
                                               (and (all-equalp ''t rhses)
                                                    (logic.all-functionsp lhses)
                                                    (all-equalp 'equal (logic.strip-function-names lhses))
                                                    (all-equalp 2 (strip-lens (logic.strip-function-args lhses))))))))))))
   (if (consp x)
       (cons (build.disjoined-pequal-from-equal (car x))
             (build.disjoined-pequal-from-equal-list (cdr x)))
     nil))

(defobligations build.disjoined-pequal-from-equal-list
  (build.disjoined-pequal-from-equal))

(encapsulate
 ()
 (local (in-theory (enable build.disjoined-pequal-from-equal-list)))

 (defthm len-of-build.disjoined-pequal-from-equal-list
   (equal (len (build.disjoined-pequal-from-equal-list x))
          (len x)))

 (defthm forcing-logic.appeal-listp-of-build.disjoined-pequal-from-equal-list
   (implies (force (and (logic.appeal-listp x)
                        (logic.all-disjunctionsp (logic.strip-conclusions x))
                        (logic.all-atomicp (logic.vrhses (logic.strip-conclusions x)))
                        (all-equalp ''t (logic.=rhses (logic.vrhses (logic.strip-conclusions x))))
                        (logic.all-functionsp (logic.=lhses (logic.vrhses (logic.strip-conclusions x))))
                        (all-equalp 'equal (logic.strip-function-names (logic.=lhses (logic.vrhses (logic.strip-conclusions x)))))
                        (all-equalp 2 (strip-lens (logic.strip-function-args (logic.=lhses (logic.vrhses (logic.strip-conclusions x))))))))
            (equal (logic.appeal-listp (build.disjoined-pequal-from-equal-list x))
                   t)))

 (defthm forcing-logic.strip-conclusions-of-build.disjoined-pequal-from-equal-list
   (implies (force (and (logic.appeal-listp x)
                        (logic.all-disjunctionsp (logic.strip-conclusions x))
                        (logic.all-atomicp (logic.vrhses (logic.strip-conclusions x)))
                        (all-equalp ''t (logic.=rhses (logic.vrhses (logic.strip-conclusions x))))
                        (logic.all-functionsp (logic.=lhses (logic.vrhses (logic.strip-conclusions x))))
                        (all-equalp 'equal (logic.strip-function-names (logic.=lhses (logic.vrhses (logic.strip-conclusions x)))))
                        (all-equalp 2 (strip-lens (logic.strip-function-args (logic.=lhses (logic.vrhses (logic.strip-conclusions x))))))))
            (equal (logic.strip-conclusions (build.disjoined-pequal-from-equal-list x))
                   (logic.por-list (logic.vlhses (logic.strip-conclusions x))
                                   (logic.pequal-list (strip-firsts (logic.strip-function-args (logic.=lhses (logic.vrhses (logic.strip-conclusions x)))))
                                                      (strip-seconds (logic.strip-function-args (logic.=lhses (logic.vrhses (logic.strip-conclusions x)))))))))
   :rule-classes ((:rewrite :backchain-limit-lst 0)))

 (defthm@ forcing-logic.proof-listp-of-build.disjoined-pequal-from-equal-list
   (implies (force (and (logic.appeal-listp x)
                        (logic.all-disjunctionsp (logic.strip-conclusions x))
                        (logic.all-atomicp (logic.vrhses (logic.strip-conclusions x)))
                        (all-equalp ''t (logic.=rhses (logic.vrhses (logic.strip-conclusions x))))
                        (logic.all-functionsp (logic.=lhses (logic.vrhses (logic.strip-conclusions x))))
                        (all-equalp 'equal (logic.strip-function-names (logic.=lhses (logic.vrhses (logic.strip-conclusions x)))))
                        (all-equalp 2 (strip-lens (logic.strip-function-args (logic.=lhses (logic.vrhses (logic.strip-conclusions x))))))
                        ;; ---
                        (logic.proof-listp x axioms thms atbl)
                        (@obligations build.disjoined-pequal-from-equal-list)))
            (equal (logic.proof-listp (build.disjoined-pequal-from-equal-list x) axioms thms atbl)
                   t))))



(defund build.equal-by-args (f x)
  ;;
  ;;   (equal s1 t1) = t
  ;;   ...
  ;;   (equal sn tn) = t
  ;; -------------------------------------------
  ;;   (equal (f s1 ... sn) (f t1 ... tn)) = t
  ;;
  (declare (xargs :guard (and (logic.function-namep f)
                              (logic.appeal-listp x)
                              (let ((concs (logic.strip-conclusions x)))
                                (and (logic.all-atomicp concs)
                                     (let ((lhses (logic.=lhses concs))
                                           (rhses (logic.=rhses concs)))
                                       (and (all-equalp ''t rhses)
                                            (logic.all-functionsp lhses)
                                            (all-equalp 'equal (logic.strip-function-names lhses))
                                            (all-equalp 2 (strip-lens (logic.strip-function-args lhses))))))))
                  :guard-hints (("Goal" :in-theory (enable axiom-equal-when-same)))))
  (let* ((s-t-tuples (logic.strip-function-args (logic.=lhses (logic.strip-conclusions x))))
         (s*         (strip-firsts  s-t-tuples))
         (t*         (strip-seconds s-t-tuples)))
    (cond ((equal s* t*)
           ;; Optimization.  We can just use reflexivity.
           (build.equal-reflexivity (logic.function f s*)))
          (t
           ;; Derivation.
           ;;
           ;;  1. s1 = t1, ..., sn = tn                                                      = from equal list
           ;;  2. (f s1 ... sn) = (f t1 ... tn)                                              = by args
           ;;  3. x != y v (equal x y) = t                                                   Axiom equal when same
           ;;  4. (f s1 ... sn) != (f t1 ... tn) v (equal (f s1 ... sn) (f t1 ... tn)) = t   Instantiation; 3
           ;;  5. (equal (f s1 ... sn) (f t1 ... tn)) = t                                    Modus Ponens; 2, 4
           ;;
           ;; Q.E.D.
           (let* ((line-1 (build.pequal-from-equal-list x))
                  (line-2 (build.pequal-by-args f line-1))
                  (line-3 (build.axiom (axiom-equal-when-same)))
                  (line-4 (build.instantiation line-3 (list (cons 'x (logic.=lhs (logic.conclusion line-2)))
                                                            (cons 'y (logic.=rhs (logic.conclusion line-2))))))
                  (line-5 (build.modus-ponens line-2 line-4)))
             line-5)))))

(defobligations build.equal-by-args
  (build.equal-reflexivity build.pequal-from-equal-list build.instantiation build.modus-ponens)
  :extra-axioms ((axiom-equal-when-same)))

(encapsulate
 ()
 (local (in-theory (enable build.equal-by-args axiom-equal-when-same)))

 (defthm build.equal-by-args-under-iff
   (iff (build.equal-by-args f x)
        t)
   :hints(("Goal" :in-theory (disable (:executable-counterpart acl2::force)))))

 (defthm forcing-logic.appealp-of-build.equal-by-args
   (implies (force (and (logic.function-namep f)
                        (logic.appeal-listp x)
                        (logic.all-atomicp (logic.strip-conclusions x))
                        (all-equalp ''t (logic.=rhses (logic.strip-conclusions x)))
                        (logic.all-functionsp (logic.=lhses (logic.strip-conclusions x)))
                        (all-equalp 'equal (logic.strip-function-names (logic.=lhses (logic.strip-conclusions x))))
                        (all-equalp 2 (strip-lens (logic.strip-function-args (logic.=lhses (logic.strip-conclusions x)))))))
            (equal (logic.appealp (build.equal-by-args f x))
                   t)))

 (defthm forcing-logic.conclusion-of-build.equal-by-args
   (implies (force (and (logic.function-namep f)
                        (logic.appeal-listp x)
                        (logic.all-atomicp (logic.strip-conclusions x))
                        (all-equalp ''t (logic.=rhses (logic.strip-conclusions x)))
                        (logic.all-functionsp (logic.=lhses (logic.strip-conclusions x)))
                        (all-equalp 'equal (logic.strip-function-names (logic.=lhses (logic.strip-conclusions x))))
                        (all-equalp 2 (strip-lens (logic.strip-function-args (logic.=lhses (logic.strip-conclusions x)))))))
            (equal (logic.conclusion (build.equal-by-args f x))
                   (logic.pequal (logic.function 'equal (list (logic.function f (strip-firsts (logic.strip-function-args (logic.=lhses (logic.strip-conclusions x)))))
                                                              (logic.function f (strip-seconds (logic.strip-function-args (logic.=lhses (logic.strip-conclusions x)))))))
                                 ''t)))
   :rule-classes ((:rewrite :backchain-limit-lst 0)))

 (defthm@ forcing-logic.proofp-of-build.equal-by-args
   (implies (force (and (logic.function-namep f)
                        (logic.appeal-listp x)
                        (logic.all-atomicp (logic.strip-conclusions x))
                        (all-equalp ''t (logic.=rhses (logic.strip-conclusions x)))
                        (logic.all-functionsp (logic.=lhses (logic.strip-conclusions x)))
                        (all-equalp 'equal (logic.strip-function-names (logic.=lhses (logic.strip-conclusions x))))
                        (all-equalp 2 (strip-lens (logic.strip-function-args (logic.=lhses (logic.strip-conclusions x)))))
                        ;; ---
                        (logic.proof-listp x axioms thms atbl)
                        (equal (cdr (lookup 'equal atbl)) 2)
                        (equal (cdr (lookup f atbl)) (len x))
                        (@obligations build.equal-by-args)))
            (equal (logic.proofp (build.equal-by-args f x) axioms thms atbl)
                   t))))



(defund build.equal-by-args-aux-okp (lhses rhses proofs)
  (declare (xargs :guard (and (logic.term-listp lhses)
                              (logic.term-listp rhses)
                              (logic.appeal-listp proofs))
                  :measure (rank proofs)))
  (if (consp proofs)
      (let ((conclusion (logic.conclusion (car proofs))))
        (and (equal 'pequal* (logic.fmtype conclusion))
             (equal (logic.=rhs conclusion) ''t)
             (let ((lhs (logic.=lhs conclusion)))
               (and (logic.functionp lhs)
                    (equal 'equal (logic.function-name lhs))
                    (let ((args (logic.function-args lhs)))
                      (and (equal 2 (fast-len args 0))
                           (equal (first args) (car lhses))
                           (equal (second args) (car rhses))
                           (build.equal-by-args-aux-okp (cdr lhses) (cdr rhses) (cdr proofs))))))))
    t))

(defthm build.equal-by-args-aux-okp-removal
  (implies (force (and (logic.term-listp lhses)
                       (logic.term-listp rhses)
                       (true-listp lhses)
                       (true-listp rhses)
                       (logic.appeal-listp proofs)
                       (equal (len lhses) (len proofs))
                       (equal (len rhses) (len proofs))))
           (equal (build.equal-by-args-aux-okp lhses rhses proofs)
                  (and (logic.all-atomicp (logic.strip-conclusions proofs))
                       (all-equalp ''t (logic.=rhses (logic.strip-conclusions proofs)))
                       (logic.all-functionsp (logic.=lhses (logic.strip-conclusions proofs)))
                       (all-equalp 'equal (logic.strip-function-names (logic.=lhses (logic.strip-conclusions proofs))))
                       (all-equalp 2 (strip-lens (logic.strip-function-args (logic.=lhses (logic.strip-conclusions proofs)))))
                       (equal lhses (strip-firsts (logic.strip-function-args (logic.=lhses (logic.strip-conclusions proofs)))))
                       (equal rhses (strip-seconds (logic.strip-function-args (logic.=lhses (logic.strip-conclusions proofs))))))))
  :hints(("Goal"
          :induct (build.equal-by-args-aux-okp lhses rhses proofs)
          :in-theory (enable build.equal-by-args-aux-okp)
          :expand (build.equal-by-args-aux-okp lhses rhses proofs))))


(defund build.equal-by-args-okp (x atbl)
  (declare (xargs :guard (and (logic.appealp x)
                              (logic.arity-tablep atbl))))
  (let ((method     (logic.method x))
        (conclusion (logic.conclusion x))
        (subproofs  (logic.subproofs x))
        (extras     (logic.extras x)))
    (and (equal method 'build.equal-by-args)
         (logic.formula-atblp conclusion atbl)
         (not extras)
         (equal (logic.fmtype conclusion) 'pequal*)
         (let ((=lhs (logic.=lhs conclusion))
               (=rhs (logic.=rhs conclusion)))
           (and (equal =rhs ''t)
                (logic.functionp =lhs)
                (equal (logic.function-name =lhs) 'equal)
                (let ((args (logic.function-args =lhs)))
                  (and (equal 2 (fast-len args 0))
                       (let ((f-of-lhses (first args))
                             (f-of-rhses (second args)))
                         (and (logic.functionp f-of-lhses)
                              (logic.functionp f-of-rhses)
                              (equal (logic.function-name f-of-lhses) (logic.function-name f-of-rhses))
                              (let ((lhses (logic.function-args f-of-lhses))
                                    (rhses (logic.function-args f-of-rhses)))
                                (and (same-lengthp lhses subproofs)
                                     (same-lengthp rhses subproofs)
                                     (build.equal-by-args-aux-okp lhses rhses subproofs))))))))))))


(defund@ build.equal-by-args-high (f x)
  (declare (xargs :guard (and (logic.function-namep f)
                              (logic.appeal-listp x)
                              (let ((concs (logic.strip-conclusions x)))
                                (and (logic.all-atomicp concs)
                                     (let ((lhses (logic.=lhses concs))
                                           (rhses (logic.=rhses concs)))
                                       (and (all-equalp ''t rhses)
                                            (logic.all-functionsp lhses)
                                            (all-equalp 'equal (logic.strip-function-names lhses))
                                            (all-equalp 2 (strip-lens (logic.strip-function-args lhses))))))))
                  :guard-hints (("Goal"
                                 :in-theory (e/d (logic.strip-conclusions-of-rev
                                                  logic.=lhses-of-rev
                                                  logic.strip-function-args-of-rev
                                                  strip-lens-of-rev)
                                                 (rev-of-logic.strip-conclusions
                                                  rev-of-logic.=lhses
                                                  rev-of-logic.strip-function-args
                                                  rev-of-strip-lens))))))
  (let* ((rev-concs  (logic.fast-strip-conclusions$ x nil))
         (lhses      (logic.fast-=lhses$ rev-concs nil))
         (rev-args   (logic.fast-strip-function-args$ lhses nil))
         (s*         (fast-strip-firsts$ rev-args nil))
         (t*         (fast-strip-seconds$ rev-args nil)))
        (cond ((equal s* t*)
               (build.equal-reflexivity (logic.function f s*)))
              (t
               (logic.appeal 'build.equal-by-args
                             (logic.pequal (logic.function 'equal (list (logic.function f s*)
                                                                        (logic.function f t*)))
                                           ''t)
                             (list-fix x)
                             nil)))))

(encapsulate
 ()
 (local (in-theory (enable build.equal-by-args-okp)))

 (defthm booleanp-of-build.equal-by-args-aux-okp
   (equal (booleanp (build.equal-by-args-aux-okp lhses rhses proofs))
          t)
   :hints(("Goal" :in-theory (e/d (build.equal-by-args-aux-okp)
                                  ((:executable-counterpart ACL2::force))))))

 (defthm booleanp-of-build.equal-by-args-okp
   (equal (booleanp (build.equal-by-args-okp x atbl))
          t)
   :hints(("goal" :in-theory (disable (:executable-counterpart ACL2::force)))))

 (defthm build.equal-by-args-okp-of-logic.appeal-identity
   (equal (build.equal-by-args-okp (logic.appeal-identity x) atbl)
          (build.equal-by-args-okp x atbl))
   :hints(("goal" :in-theory (disable (:executable-counterpart ACL2::force)))))

 (defthmd lemma-1-for-soundness-of-build.equal-by-args-okp
   (implies (and (build.equal-by-args-okp x atbl)
                 (logic.appealp x)
                 (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl))
            (equal (logic.conclusion
                    (build.equal-by-args (logic.function-name (first (logic.function-args (logic.=lhs (logic.conclusion x)))))
                                         (logic.provable-list-witness (logic.strip-conclusions (logic.subproofs x))
                                                                      axioms thms atbl)))
                   (logic.conclusion x))))

 (defthmd@ lemma-2-for-soundness-of-build.equal-by-args-okp
   (implies (and (build.equal-by-args-okp x atbl)
                 (logic.appealp x)
                 (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl)
                 (@obligations build.equal-by-args))
            (equal (logic.proofp
                    (build.equal-by-args (logic.function-name (first (logic.function-args (logic.=lhs (logic.conclusion x)))))
                                         (logic.provable-list-witness (logic.strip-conclusions (logic.subproofs x))
                                                                      axioms thms atbl))
                    axioms thms atbl)
                   t)))

 (defthmd lemma-3-for-soundness-of-build.equal-by-args-okp
   (implies (and (build.equal-by-args-okp x atbl)
                 (logic.appealp x)
                 (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl))
            (equal (logic.appealp
                    (build.equal-by-args (logic.function-name (first (logic.function-args (logic.=lhs (logic.conclusion x)))))
                                         (logic.provable-list-witness (logic.strip-conclusions (logic.subproofs x))
                                                                      axioms thms atbl)))
                   t))
   :hints(("Goal" :in-theory (enable build.equal-by-args-okp))))

 (defthm@ forcing-soundness-of-build.equal-by-args-okp
   (implies (and (build.equal-by-args-okp x atbl)
                 (force (and (logic.appealp x)
                             (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl)
                             (@obligations build.equal-by-args))))
            (equal (logic.provablep (logic.conclusion x) axioms thms atbl)
                   t))
   :hints (("Goal"
            :in-theory (enable lemma-1-for-soundness-of-build.equal-by-args-okp
                               lemma-2-for-soundness-of-build.equal-by-args-okp
                               lemma-3-for-soundness-of-build.equal-by-args-okp)
            :use ((:instance forcing-logic.provablep-when-logic.proofp
                             (x (build.equal-by-args (logic.function-name (first (logic.function-args (logic.=lhs (logic.conclusion x)))))
                                                     (logic.provable-list-witness (logic.strip-conclusions (logic.subproofs x))
                                                                                  axioms thms atbl)))))))))





(defund build.disjoined-equal-by-args (f p x)
   ;;
   ;;   P v (equal s1 t1) = t
   ;;   ...
   ;;   P v (equal sn tn) = t
   ;; -----------------------------------------------
   ;;   P v (equal (f s1 ... sn) (f t1 ... tn)) = t
   ;;
   (declare (xargs :guard (and (logic.function-namep f)
                               (logic.formulap p)
                               (logic.appeal-listp x)
                               (let ((concs (logic.strip-conclusions x)))
                                 (and (logic.all-disjunctionsp concs)
                                      (all-equalp p (logic.vlhses concs))
                                      (let ((equals (logic.vrhses concs)))
                                        (and (logic.all-atomicp equals)
                                             (let ((lhses (logic.=lhses equals))
                                                   (rhses (logic.=rhses equals)))
                                               (and (all-equalp ''t rhses)
                                                    (logic.all-functionsp lhses)
                                                    (all-equalp 'equal (logic.strip-function-names lhses))
                                                    (all-equalp 2 (strip-lens (logic.strip-function-args lhses))))))))))
                   :guard-hints (("Goal" :in-theory (enable axiom-equal-when-same)))))
   (let* ((s-t-tuples  (logic.strip-function-args (logic.=lhses (logic.vrhses (logic.strip-conclusions x)))))
          (s*          (strip-firsts s-t-tuples))
          (t*          (strip-seconds s-t-tuples)))
     (cond ((equal s* t*)
            ;; Optimization.  We can just use reflexivity and expansion.
            (build.expansion p (build.equal-reflexivity (logic.function f s*))))
           (t
            ;; Derivation.
            ;;
            ;;  1. P v s1 = t1, ..., P v sn = tn                                                  DJ = from equal list
            ;;  2. P v (f s1 ... sn) = (f t1 ... tn)                                              DJ = by args
            ;;  3. x != y v (equal x y) = t                                                       Axiom equal when same
            ;;  4. (f s1 ... sn) != (f t1 ... tn) v (equal (f s1 ... sn) (f t1 ... tn)) = t       Instantiation
            ;;  5. P v (f s1 ... sn) != (f t1 ... tn) v (equal (f s1 ... sn) (f t1 ... tn)) = t   Expansion
            ;;  6. P v (equal (f s1 ... sn) (f t1 ... tn)) = t                                    DJ Modus Ponens; 2, 4
            ;;
            ;; Q.E.D.
            (let* ((line-1 (build.disjoined-pequal-from-equal-list x))
                   (line-2 (build.disjoined-pequal-by-args f p line-1))
                   (line-3 (build.axiom (axiom-equal-when-same)))
                   (line-4 (build.instantiation line-3 (list (cons 'x (logic.=lhs (logic.vrhs (logic.conclusion line-2))))
                                                             (cons 'y (logic.=rhs (logic.vrhs (logic.conclusion line-2)))))))
                   (line-5 (build.expansion p line-4))
                   (line-6 (build.disjoined-modus-ponens line-2 line-5)))
              line-6)))))

(defobligations build.disjoined-equal-by-args
  (build.expansion build.equal-reflexivity build.disjoined-pequal-from-equal-list
   build.disjoined-pequal-by-args build.instantiation build.expansion build.disjoined-modus-ponens)
  :extra-axioms ((axiom-equal-when-same)))

(encapsulate
 ()
 (local (in-theory (enable build.disjoined-equal-by-args axiom-equal-when-same)))

 (defthm build.disjoined-equal-by-args-under-iff
   (iff (build.disjoined-equal-by-args f p x)
        t)
   :hints(("Goal" :in-theory (disable (:executable-counterpart acl2::force)))))

 (defthm forcing-logic.appealp-of-build.disjoined-equal-by-args
   (implies (force (and (logic.function-namep f)
                        (logic.formulap p)
                        (logic.appeal-listp x)
                        (logic.all-disjunctionsp (logic.strip-conclusions x))
                        (all-equalp p (logic.vlhses (logic.strip-conclusions x)))
                        (logic.all-atomicp (logic.vrhses (logic.strip-conclusions x)))
                        (all-equalp ''t (logic.=rhses (logic.vrhses (logic.strip-conclusions x))))
                        (logic.all-functionsp (logic.=lhses (logic.vrhses (logic.strip-conclusions x))))
                        (all-equalp 'equal (logic.strip-function-names (logic.=lhses (logic.vrhses (logic.strip-conclusions x)))))
                        (all-equalp 2 (strip-lens (logic.strip-function-args (logic.=lhses (logic.vrhses (logic.strip-conclusions x))))))))
            (equal (logic.appealp (build.disjoined-equal-by-args f p x))
                   t)))

 (defthm forcing-logic.conclusion-of-build.disjoined-equal-by-args
   (implies (force (and (logic.function-namep f)
                        (logic.formulap p)
                        (logic.appeal-listp x)
                        (logic.all-disjunctionsp (logic.strip-conclusions x))
                        (all-equalp p (logic.vlhses (logic.strip-conclusions x)))
                        (logic.all-atomicp (logic.vrhses (logic.strip-conclusions x)))
                        (all-equalp ''t (logic.=rhses (logic.vrhses (logic.strip-conclusions x))))
                        (logic.all-functionsp (logic.=lhses (logic.vrhses (logic.strip-conclusions x))))
                        (all-equalp 'equal (logic.strip-function-names (logic.=lhses (logic.vrhses (logic.strip-conclusions x)))))
                        (all-equalp 2 (strip-lens (logic.strip-function-args (logic.=lhses (logic.vrhses (logic.strip-conclusions x))))))))
            (equal (logic.conclusion (build.disjoined-equal-by-args f p x))
                   (logic.por p (logic.pequal (logic.function 'equal (list (logic.function f (strip-firsts (logic.strip-function-args (logic.=lhses (logic.vrhses (logic.strip-conclusions x))))))
                                                                           (logic.function f (strip-seconds (logic.strip-function-args (logic.=lhses (logic.vrhses (logic.strip-conclusions x))))))))
                                              ''t))))
   :rule-classes ((:rewrite :backchain-limit-lst 0)))

 (defthm@ forcing-logic.proofp-of-build.disjoined-equal-by-args
   (implies (force (and (logic.function-namep f)
                        (logic.formulap p)
                        (logic.appeal-listp x)
                        (logic.all-disjunctionsp (logic.strip-conclusions x))
                        (all-equalp p (logic.vlhses (logic.strip-conclusions x)))
                        (logic.all-atomicp (logic.vrhses (logic.strip-conclusions x)))
                        (all-equalp ''t (logic.=rhses (logic.vrhses (logic.strip-conclusions x))))
                        (logic.all-functionsp (logic.=lhses (logic.vrhses (logic.strip-conclusions x))))
                        (all-equalp 'equal (logic.strip-function-names (logic.=lhses (logic.vrhses (logic.strip-conclusions x)))))
                        (all-equalp 2 (strip-lens (logic.strip-function-args (logic.=lhses (logic.vrhses (logic.strip-conclusions x))))))
                        ;; ---
                        (logic.formula-atblp p atbl)
                        (logic.proof-listp x axioms thms atbl)
                        (equal (cdr (lookup 'equal atbl)) 2)
                        (equal (cdr (lookup f atbl)) (len x))
                        (@obligations build.disjoined-equal-by-args)))
            (equal (logic.proofp (build.disjoined-equal-by-args f p x) axioms thms atbl)
                   t))))

(defund build.disjoined-equal-by-args-aux-okp (p lhses rhses proofs)
  (declare (xargs :guard (and (logic.formulap p)
                              (logic.term-listp lhses)
                              (logic.term-listp rhses)
                              (logic.appeal-listp proofs))
                  :measure (rank proofs)))
  (if (consp proofs)
      (let ((conclusion (logic.conclusion (car proofs))))
        (and (equal 'por* (logic.fmtype conclusion))
             (equal p (logic.vlhs conclusion))
             (let ((rest (logic.vrhs conclusion)))
               (and (equal 'pequal* (logic.fmtype rest))
                    (equal (logic.=rhs rest) ''t)
                    (let ((lhs (logic.=lhs rest)))
                      (and (logic.functionp lhs)
                           (equal 'equal (logic.function-name lhs))
                           (let ((args (logic.function-args lhs)))
                             (and (equal 2 (fast-len args 0))
                                  (equal (first args) (car lhses))
                                  (equal (second args) (car rhses))
                                  (build.disjoined-equal-by-args-aux-okp p (cdr lhses) (cdr rhses) (cdr proofs))))))))))
    t))

(defthm build.disjoined-equal-by-args-aux-okp-removal
  (implies (force (and (logic.formulap p)
                       (logic.term-listp lhses)
                       (logic.term-listp rhses)
                       (true-listp lhses)
                       (true-listp rhses)
                       (logic.appeal-listp proofs)
                       (equal (len lhses) (len proofs))
                       (equal (len rhses) (len proofs))))
           (equal (build.disjoined-equal-by-args-aux-okp p lhses rhses proofs)
                  (and (logic.all-disjunctionsp (logic.strip-conclusions proofs))
                       (all-equalp p (logic.vlhses (logic.strip-conclusions proofs)))
                       (logic.all-atomicp (logic.vrhses (logic.strip-conclusions proofs)))
                       (all-equalp ''t (logic.=rhses (logic.vrhses (logic.strip-conclusions proofs))))
                       (logic.all-functionsp (logic.=lhses (logic.vrhses (logic.strip-conclusions proofs))))
                       (all-equalp 'equal (logic.strip-function-names (logic.=lhses (logic.vrhses (logic.strip-conclusions proofs)))))
                       (all-equalp 2 (strip-lens (logic.strip-function-args (logic.=lhses (logic.vrhses (logic.strip-conclusions proofs))))))
                       (equal lhses (strip-firsts (logic.strip-function-args (logic.=lhses (logic.vrhses (logic.strip-conclusions proofs))))))
                       (equal rhses (strip-seconds (logic.strip-function-args (logic.=lhses (logic.vrhses (logic.strip-conclusions proofs)))))))))
  :hints(("Goal"
          :induct (build.disjoined-equal-by-args-aux-okp p lhses rhses proofs)
          :in-theory (enable build.disjoined-equal-by-args-aux-okp)
          :expand (build.disjoined-equal-by-args-aux-okp p lhses rhses proofs))))

(defund build.disjoined-equal-by-args-okp (x atbl)
  (declare (xargs :guard (and (logic.appealp x)
                              (logic.arity-tablep atbl))))
  (let ((method     (logic.method x))
        (conclusion (logic.conclusion x))
        (subproofs  (logic.subproofs x))
        (extras     (logic.extras x)))
    (and (equal method 'build.disjoined-equal-by-args)
         (logic.formula-atblp conclusion atbl)
         (not extras)
         (equal 'por* (logic.fmtype conclusion))
         (equal 'pequal* (logic.fmtype (logic.vrhs conclusion)))
         (let ((p    (logic.vlhs conclusion))
               (=lhs (logic.=lhs (logic.vrhs conclusion)))
               (=rhs (logic.=rhs (logic.vrhs conclusion))))
           (and (equal =rhs ''t)
                (logic.functionp =lhs)
                (equal (logic.function-name =lhs) 'equal)
                (let ((args (logic.function-args =lhs)))
                  (and (equal 2 (fast-len args 0))
                       (let ((f-of-lhses (first args))
                             (f-of-rhses (second args)))
                         (and (logic.functionp f-of-lhses)
                              (logic.functionp f-of-rhses)
                              (equal (logic.function-name f-of-lhses) (logic.function-name f-of-rhses))
                              (let ((lhses (logic.function-args f-of-lhses))
                                    (rhses (logic.function-args f-of-rhses)))
                                (and (same-lengthp lhses subproofs)
                                     (same-lengthp rhses subproofs)
                                     (build.disjoined-equal-by-args-aux-okp p lhses rhses subproofs))))))))))))


(defund@ build.disjoined-equal-by-args-high (f p x)
  (declare (xargs :guard (and (logic.function-namep f)
                              (logic.formulap p)
                              (logic.appeal-listp x)
                              (let ((concs (logic.strip-conclusions x)))
                                (and (logic.all-disjunctionsp concs)
                                     (all-equalp p (logic.vlhses concs))
                                     (let ((equals (logic.vrhses concs)))
                                       (and (logic.all-atomicp equals)
                                            (let ((lhses (logic.=lhses equals))
                                                  (rhses (logic.=rhses equals)))
                                              (and (all-equalp ''t rhses)
                                                   (logic.all-functionsp lhses)
                                                   (all-equalp 'equal (logic.strip-function-names lhses))
                                                   (all-equalp 2 (strip-lens (logic.strip-function-args lhses))))))))))
                  :guard-hints (("Goal"
                                 :in-theory (e/d (logic.strip-conclusions-of-rev
                                                  logic.vrhses-of-rev
                                                  logic.=lhses-of-rev
                                                  logic.strip-function-args-of-rev
                                                  strip-lens-of-rev)
                                                 (rev-of-logic.strip-conclusions
                                                  rev-of-logic.vrhses
                                                  rev-of-logic.=lhses
                                                  rev-of-logic.strip-function-args
                                                  rev-of-strip-lens))))))
  (let* ((rev-concs  (logic.fast-strip-conclusions$ x nil))
         (vrhses     (logic.fast-vrhses$ rev-concs nil))
         (rev-=lhses (logic.fast-=lhses$ vrhses nil))
         (args       (logic.fast-strip-function-args$ rev-=lhses nil))
         (firsts     (strip-firsts args))
         (seconds    (strip-seconds args)))
    (if (equal firsts seconds)
        (build.expansion p (build.equal-reflexivity (logic.function f firsts)))
      (logic.appeal 'build.disjoined-equal-by-args
                    (logic.por p (logic.pequal (logic.function 'equal (list (logic.function f firsts)
                                                                            (logic.function f seconds)))
                                               ''t))
                    (list-fix x)
                    nil))))


(encapsulate
 ()
 (local (in-theory (enable build.disjoined-equal-by-args-okp)))

 (defthm booleanp-of-build.disjoined-equal-by-args-aux-okp
   (equal (booleanp (build.disjoined-equal-by-args-aux-okp p lhses rhses proofs))
          t)
   :hints(("Goal" :in-theory (e/d (build.disjoined-equal-by-args-aux-okp)
                                  ((:executable-counterpart ACL2::force))))))

 (defthm booleanp-of-build.disjoined-equal-by-args-okp
   (equal (booleanp (build.disjoined-equal-by-args-okp x atbl))
          t)
   :hints(("goal" :in-theory (disable (:executable-counterpart ACL2::force)))))

 (defthm build.disjoined-equal-by-args-okp-of-logic.appeal-identity
   (equal (build.disjoined-equal-by-args-okp (logic.appeal-identity x) atbl)
          (build.disjoined-equal-by-args-okp x atbl))
   :hints(("goal" :in-theory (disable (:executable-counterpart ACL2::force)))))

 (defthmd lemma-1-for-soundness-of-build.disjoined-equal-by-args-okp
   (implies (and (build.disjoined-equal-by-args-okp x atbl)
                 (logic.appealp x)
                 (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl))
            (equal (logic.conclusion
                    (build.disjoined-equal-by-args
                     (logic.function-name (first (logic.function-args (logic.=lhs (logic.vrhs (logic.conclusion x))))))
                     (logic.vlhs (logic.conclusion x))
                     (logic.provable-list-witness (logic.strip-conclusions (logic.subproofs x))
                                                  axioms thms atbl)))
                   (logic.conclusion x))))

 (defthmd@ lemma-2-for-soundness-of-build.disjoined-equal-by-args-okp
   (implies (and (build.disjoined-equal-by-args-okp x atbl)
                 (logic.appealp x)
                 (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl)
                 (@obligations build.disjoined-equal-by-args))
            (equal (logic.proofp
                    (build.disjoined-equal-by-args
                     (logic.function-name (first (logic.function-args (logic.=lhs (logic.vrhs (logic.conclusion x))))))
                     (logic.vlhs (logic.conclusion x))
                     (logic.provable-list-witness (logic.strip-conclusions (logic.subproofs x))
                                                  axioms thms atbl))
                    axioms thms atbl)
                   t)))

 (defthmd lemma-3-for-soundness-of-build.disjoined-equal-by-args-okp
   (implies (and (build.disjoined-equal-by-args-okp x atbl)
                 (logic.appealp x)
                 (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl))
            (equal (logic.appealp
                    (build.disjoined-equal-by-args
                     (logic.function-name (first (logic.function-args (logic.=lhs (logic.vrhs (logic.conclusion x))))))
                     (logic.vlhs (logic.conclusion x))
                     (logic.provable-list-witness (logic.strip-conclusions (logic.subproofs x))
                                                  axioms thms atbl)))
                   t))
   :hints(("Goal" :in-theory (enable build.disjoined-equal-by-args-okp))))

 (defthm@ forcing-soundness-of-build.disjoined-equal-by-args-okp
   (implies (and (build.disjoined-equal-by-args-okp x atbl)
                 (force (and (logic.appealp x)
                             (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl)
                             (@obligations build.disjoined-equal-by-args))))
            (equal (logic.provablep (logic.conclusion x) axioms thms atbl)
                   t))
   :hints (("Goal"
            :in-theory (enable lemma-1-for-soundness-of-build.disjoined-equal-by-args-okp
                               lemma-2-for-soundness-of-build.disjoined-equal-by-args-okp
                               lemma-3-for-soundness-of-build.disjoined-equal-by-args-okp)
            :use ((:instance forcing-logic.provablep-when-logic.proofp
                             (x (build.disjoined-equal-by-args
                                 (logic.function-name (first (logic.function-args (logic.=lhs (logic.vrhs (logic.conclusion x))))))
                                 (logic.vlhs (logic.conclusion x))
                                 (logic.provable-list-witness (logic.strip-conclusions (logic.subproofs x))
                                                              axioms thms atbl)))))))))






(defund build.lambda-equal-by-args (formals body proofs)
  ;;
  ;;   (equal t1 s1) = t
  ;;   ...
  ;;   (equal tn sn) = t
  ;; ---------------------------------------------------------------------------------
  ;;   (equal ((lambda (x1...xn) B) t1 ... tn) ((lambda (x1...xn) B) s1 ... sn)) = t
  ;;
  (declare (xargs :guard (and (true-listp formals)
                              (logic.variable-listp formals)
                              (uniquep formals)
                              (logic.termp body)
                              (subsetp (logic.term-vars body) formals)
                              (logic.appeal-listp proofs)
                              (same-lengthp proofs formals)
                              (logic.all-atomicp (logic.strip-conclusions proofs))
                              (logic.all-functionsp (logic.=lhses (logic.strip-conclusions proofs)))
                              (all-equalp 'equal (logic.strip-function-names (logic.=lhses (logic.strip-conclusions proofs))))
                              (all-equalp 2 (strip-lens (logic.strip-function-args (logic.=lhses (logic.strip-conclusions proofs)))))
                              (all-equalp ''t (logic.=rhses (logic.strip-conclusions proofs))))))
  ;; Derivation.
  ;;
  ;;   1. t1 = s1, ..., tn = sn                                                            = from equal list
  ;;   2. ((lambda (x1...xn) B) t1 ... tn) = ((lambda (x1...xn) B) s1 ... sn)              Lambda = by args
  ;;   3. (equal ((lambda (x1...xn) B) t1 ... tn) ((lambda (x1...xn) B) s1 ... sn) = t     Equal from =
  ;;
  ;; Q.E.D.
  (let* ((line-1 (build.pequal-from-equal-list proofs))
         (line-2 (build.lambda-pequal-by-args formals body line-1))
         (line-3 (build.equal-from-pequal line-2)))
    line-3))

(defobligations build.lambda-equal-by-args
  (build.pequal-from-equal-list build.lambda-pequal-by-args build.equal-from-pequal))

(encapsulate
 ()
 (local (in-theory (enable build.lambda-equal-by-args)))

 (defthm build.lambda-equal-by-args-under-iff
   (iff (build.lambda-equal-by-args formals body proofs)
        t))

 (defthm forcing-logic.appealp-of-build.lambda-equal-by-args
   (implies (force (and (true-listp formals)
                        (logic.variable-listp formals)
                        (uniquep formals)
                        (logic.termp body)
                        (subsetp (logic.term-vars body) formals)
                        (logic.appeal-listp proofs)
                        (same-lengthp proofs formals)
                        (logic.all-atomicp (logic.strip-conclusions proofs))
                        (logic.all-functionsp (logic.=lhses (logic.strip-conclusions proofs)))
                        (all-equalp 'equal (logic.strip-function-names (logic.=lhses (logic.strip-conclusions proofs))))
                        (all-equalp 2 (strip-lens (logic.strip-function-args (logic.=lhses (logic.strip-conclusions proofs)))))
                        (all-equalp ''t (logic.=rhses (logic.strip-conclusions proofs)))))
            (equal (logic.appealp (build.lambda-equal-by-args formals body proofs))
                   t)))

 (defthm forcing-logic.conclusion-of-build.lambda-equal-by-args
   (implies (force (and (true-listp formals)
                        (logic.variable-listp formals)
                        (uniquep formals)
                        (logic.termp body)
                        (subsetp (logic.term-vars body) formals)
                        (logic.appeal-listp proofs)
                        (same-lengthp proofs formals)
                        (logic.all-atomicp (logic.strip-conclusions proofs))
                        (logic.all-functionsp (logic.=lhses (logic.strip-conclusions proofs)))
                        (all-equalp 'equal (logic.strip-function-names (logic.=lhses (logic.strip-conclusions proofs))))
                        (all-equalp 2 (strip-lens (logic.strip-function-args (logic.=lhses (logic.strip-conclusions proofs)))))
                        (all-equalp ''t (logic.=rhses (logic.strip-conclusions proofs)))))
            (equal (logic.conclusion (build.lambda-equal-by-args formals body proofs))
                   (logic.pequal (logic.function 'equal (list (logic.lambda formals body (strip-firsts (logic.strip-function-args (logic.=lhses (logic.strip-conclusions proofs)))))
                                                              (logic.lambda formals body (strip-seconds (logic.strip-function-args (logic.=lhses (logic.strip-conclusions proofs)))))))
                                 ''t)))
   :rule-classes ((:rewrite :backchain-limit-lst 0)))

 (defthm@ forcing-logic.proofp-of-build.lambda-equal-by-args
   (implies (force (and (true-listp formals)
                        (logic.variable-listp formals)
                        (uniquep formals)
                        (logic.termp body)
                        (subsetp (logic.term-vars body) formals)
                        (logic.appeal-listp proofs)
                        (same-lengthp proofs formals)
                        (logic.all-atomicp (logic.strip-conclusions proofs))
                        (logic.all-functionsp (logic.=lhses (logic.strip-conclusions proofs)))
                        (all-equalp 'equal (logic.strip-function-names (logic.=lhses (logic.strip-conclusions proofs))))
                        (all-equalp 2 (strip-lens (logic.strip-function-args (logic.=lhses (logic.strip-conclusions proofs)))))
                        (all-equalp ''t (logic.=rhses (logic.strip-conclusions proofs)))
                        ;; ---
                        (logic.term-atblp body atbl)
                        (logic.proof-listp proofs axioms thms atbl)
                        (equal (cdr (lookup 'equal atbl)) 2)
                        (@obligations build.lambda-equal-by-args)))
            (equal (logic.proofp (build.lambda-equal-by-args formals body proofs) axioms thms atbl)
                   t))))



(defund build.disjoined-lambda-equal-by-args (formals body P proofs)
  ;;
  ;;   P v (equal t1 s1) = t
  ;;   ...
  ;;   P v (equal tn sn) = t
  ;; -------------------------------------------------------------------------------------
  ;;   P v (equal ((lambda (x1...xn) B) t1 ... tn) ((lambda (x1...xn) B) s1 ... sn)) = t
  ;;
  (declare (xargs :guard (and (true-listp formals)
                              (logic.variable-listp formals)
                              (uniquep formals)
                              (logic.termp body)
                              (subsetp (logic.term-vars body) formals)
                              (logic.formulap P)
                              (logic.appeal-listp proofs)
                              (same-lengthp proofs formals)
                              (logic.all-disjunctionsp (logic.strip-conclusions proofs))
                              (all-equalp P (logic.vlhses (logic.strip-conclusions proofs)))
                              (logic.all-atomicp (logic.vrhses (logic.strip-conclusions proofs)))
                              (logic.all-functionsp (logic.=lhses (logic.vrhses (logic.strip-conclusions proofs))))
                              (all-equalp 'equal (logic.strip-function-names (logic.=lhses (logic.vrhses (logic.strip-conclusions proofs)))))
                              (all-equalp 2 (strip-lens (logic.strip-function-args (logic.=lhses (logic.vrhses (logic.strip-conclusions proofs))))))
                              (all-equalp ''t (logic.=rhses (logic.vrhses (logic.strip-conclusions proofs)))))))
  ;; Derivation.
  ;;
  ;;  1. P v t1 = s1, ..., P v tn = sn                                                   DJ = from equal list
  ;;  2. P v ((lambda (x1...xn) B) s1...sn) = ((lambda (x1...xn) B) t1...tn)             DJ lambda = by args
  ;;  3. P v (equal ((lambda (x1...xn) B) s1...sn) ((lambda (x1...xn) B) t1...tn)) = t   DJ equal from =
  ;;
  ;; Q.E.D.
  (let* ((line-1 (build.disjoined-pequal-from-equal-list proofs))
         (line-2 (build.disjoined-lambda-pequal-by-args formals body P line-1))
         (line-3 (build.disjoined-equal-from-pequal line-2)))
    line-3))

(defobligations build.disjoined-lambda-equal-by-args
  (build.disjoined-pequal-from-equal-list build.disjoined-lambda-pequal-by-args
   build.disjoined-equal-from-pequal))

(encapsulate
 ()
 (local (in-theory (enable build.disjoined-lambda-equal-by-args)))

 (defthm build.disjoined-lambda-equal-by-args-under-iff
   (iff (build.disjoined-lambda-equal-by-args formals body P proofs)
        t))

 (defthm forcing-logic.appealp-of-build.disjoined-lambda-equal-by-args
   (implies (force (and (true-listp formals)
                        (logic.variable-listp formals)
                        (uniquep formals)
                        (logic.termp body)
                        (subsetp (logic.term-vars body) formals)
                        (logic.formulap P)
                        (logic.appeal-listp proofs)
                        (same-lengthp proofs formals)
                        (logic.all-disjunctionsp (logic.strip-conclusions proofs))
                        (all-equalp P (logic.vlhses (logic.strip-conclusions proofs)))
                        (logic.all-atomicp (logic.vrhses (logic.strip-conclusions proofs)))
                        (logic.all-functionsp (logic.=lhses (logic.vrhses (logic.strip-conclusions proofs))))
                        (all-equalp 'equal (logic.strip-function-names (logic.=lhses (logic.vrhses (logic.strip-conclusions proofs)))))
                        (all-equalp 2 (strip-lens (logic.strip-function-args (logic.=lhses (logic.vrhses (logic.strip-conclusions proofs))))))
                        (all-equalp ''t (logic.=rhses (logic.vrhses (logic.strip-conclusions proofs))))))
            (equal (logic.appealp (build.disjoined-lambda-equal-by-args formals body P proofs))
                   t)))

 (defthm forcing-logic.conclusion-of-build.disjoined-lambda-equal-by-args
   (implies (force (and (true-listp formals)
                        (logic.variable-listp formals)
                        (uniquep formals)
                        (logic.termp body)
                        (subsetp (logic.term-vars body) formals)
                        (logic.formulap P)
                        (logic.appeal-listp proofs)
                        (same-lengthp proofs formals)
                        (logic.all-disjunctionsp (logic.strip-conclusions proofs))
                        (all-equalp P (logic.vlhses (logic.strip-conclusions proofs)))
                        (logic.all-atomicp (logic.vrhses (logic.strip-conclusions proofs)))
                        (logic.all-functionsp (logic.=lhses (logic.vrhses (logic.strip-conclusions proofs))))
                        (all-equalp 'equal (logic.strip-function-names (logic.=lhses (logic.vrhses (logic.strip-conclusions proofs)))))
                        (all-equalp 2 (strip-lens (logic.strip-function-args (logic.=lhses (logic.vrhses (logic.strip-conclusions proofs))))))
                        (all-equalp ''t (logic.=rhses (logic.vrhses (logic.strip-conclusions proofs))))))
            (equal (logic.conclusion (build.disjoined-lambda-equal-by-args formals body P proofs))
                   (logic.por P (logic.pequal (logic.function 'equal (list (logic.lambda formals body (strip-firsts (logic.strip-function-args (logic.=lhses (logic.vrhses (logic.strip-conclusions proofs))))))
                                                                           (logic.lambda formals body (strip-seconds (logic.strip-function-args (logic.=lhses (logic.vrhses (logic.strip-conclusions proofs))))))))
                                              ''t))))
   :rule-classes ((:rewrite :backchain-limit-lst 0)))

 (defthm@ forcing-logic.proofp-of-build.disjoined-lambda-equal-by-args
   (implies (force (and (true-listp formals)
                        (logic.variable-listp formals)
                        (uniquep formals)
                        (logic.termp body)
                        (subsetp (logic.term-vars body) formals)
                        (logic.formulap P)
                        (logic.appeal-listp proofs)
                        (same-lengthp proofs formals)
                        (logic.all-disjunctionsp (logic.strip-conclusions proofs))
                        (all-equalp P (logic.vlhses (logic.strip-conclusions proofs)))
                        (logic.all-atomicp (logic.vrhses (logic.strip-conclusions proofs)))
                        (logic.all-functionsp (logic.=lhses (logic.vrhses (logic.strip-conclusions proofs))))
                        (all-equalp 'equal (logic.strip-function-names (logic.=lhses (logic.vrhses (logic.strip-conclusions proofs)))))
                        (all-equalp 2 (strip-lens (logic.strip-function-args (logic.=lhses (logic.vrhses (logic.strip-conclusions proofs))))))
                        (all-equalp ''t (logic.=rhses (logic.vrhses (logic.strip-conclusions proofs))))
                        ;; ---
                        (logic.formula-atblp p atbl)
                        (logic.term-atblp body atbl)
                        (logic.proof-listp proofs axioms thms atbl)
                        (equal (cdr (lookup 'equal atbl)) 2)
                        (@obligations build.disjoined-lambda-equal-by-args)))
            (equal (logic.proofp (build.disjoined-lambda-equal-by-args formals body P proofs) axioms thms atbl)
                   t))))


(dd.close)
