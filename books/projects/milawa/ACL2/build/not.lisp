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
(include-book "iff")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)

(dd.open "not.tex")

(defund@ definition-of-not ()
  (declare (xargs :guard t))
  (@formula (= (not x) (if x nil t))))

(in-theory (disable (:executable-counterpart definition-of-not)))

(defthm logic.formulap-of-definition-of-not
  (equal (logic.formulap (definition-of-not))
         t)
  :hints(("Goal" :in-theory (enable definition-of-not))))

(defthm logic.formula-atblp-of-definition-of-not
  (implies (force (and (equal (cdr (lookup 'not atbl)) 1)
                       (equal (cdr (lookup 'if atbl)) 3)))
           (equal (logic.formula-atblp (definition-of-not) atbl)
                  t))
  :hints(("Goal" :in-theory (enable definition-of-not))))



(deftheorem theorem-not-when-nil
  :derive (v (!= x nil) (= (not x) t))
  :proof (@derive
          ((v (!= x nil) (= (if x y z) z))                        (build.axiom (axiom-if-when-nil)))
          ((v (!= x nil) (= (if x nil t) t))                      (build.instantiation @- (@sigma (y . nil) (z . t)))   *1)
          ((= (not x) (if x nil t))                               (build.axiom (definition-of-not)))
          ((v (!= x nil) (= (not x) (if x nil t)))                (build.expansion (@formula (!= x nil)) @-))
          ((v (!= x nil) (= (not x) t))                           (build.disjoined-transitivity-of-pequal @- *1)))
  :minatbl ((if . 3)
            (not . 1)))

(defderiv build.negative-lit-from-pequal-nil
  :derive (!= (not (? a)) nil)
  :from   ((proof x (= (? a) nil)))
  :proof  (@derive
           ((v (!= x nil) (= (not x) t))                          (build.theorem (theorem-not-when-nil)))
           ((v (!= x nil) (!= (not x) nil))                       (build.disjoined-not-nil-from-t @-))
           ((v (!= (? a) nil) (!= (not (? a)) nil))               (build.instantiation @- (@sigma (x . (? a)))))
           ((= (? a) nil)                                         (@given x))
           ((!= (not (? a)) nil)                                  (build.modus-ponens @- @--)))
  :minatbl ((not . 1)))

(defderiv build.disjoined-negative-lit-from-pequal-nil
  :derive (v P (!= (not (? a)) nil))
  :from   ((proof x (v P (= (? a) nil))))
  :proof  (@derive
           ((v (!= x nil) (= (not x) t))                          (build.theorem (theorem-not-when-nil)))
           ((v (!= x nil) (!= (not x) nil))                       (build.disjoined-not-nil-from-t @-))
           ((v (!= (? a) nil) (!= (not (? a)) nil))               (build.instantiation @- (@sigma (x . (? a)))))
           ((v P (v (!= (? a) nil) (!= (not (? a)) nil)))         (build.expansion (@formula P) @-))
           ((v P (= (? a) nil))                                   (@given x))
           ((v P (!= (not (? a)) nil))                            (build.disjoined-modus-ponens @- @--)))
  :minatbl ((not . 1)))



(deftheorem theorem-not-when-not-nil
  :derive (v (= x nil) (= (not x) nil))
  :proof (@derive
          ((v (= x nil) (= (if x y z) y))                         (build.axiom (axiom-if-when-not-nil)))
          ((v (= x nil) (= (if x nil t) nil))                     (build.instantiation @- (@sigma (y . nil) (z . t)))   *1)
          ((= (not x) (if x nil t))                               (build.axiom (definition-of-not)))
          ((v (= x nil) (= (not x) (if x nil t)))                 (build.expansion (@formula (= x nil)) @-))
          ((v (= x nil) (= (not x) nil))                          (build.disjoined-transitivity-of-pequal @- *1)))
  :minatbl ((if . 3)
            (not . 1)))

(defderiv build.pequal-nil-from-negative-lit
  :derive (= (? a) nil)
  :from   ((proof x (!= (not (? a)) nil)))
  :proof  (@derive
           ((v (= x nil) (= (not x) nil))                         (build.theorem (theorem-not-when-not-nil)))
           ((v (= (not x) nil) (= x nil))                         (build.commute-or @-))
           ((v (= (not (? a)) nil) (= (? a) nil))                 (build.instantiation @- (@sigma (x . (? a)))))
           ((!= (not (? a)) nil)                                  (@given x))
           ((= (? a) nil)                                         (build.modus-ponens-2 @- @--)))
  :minatbl ((not . 1)))

(defderiv build.negative-lit-from-not-pequal-nil
  :derive (= (not (? a)) nil)
  :from   ((proof x (!= (? a) nil)))
  :proof  (@derive
           ((v (= x nil) (= (not x) nil))          (build.theorem (theorem-not-when-not-nil)))
           ((v (= (? a) nil) (= (not (? a)) nil))  (build.instantiation @- (@sigma (x . (? a)))))
           ((!= (? a) nil)                         (@given x))
           ((= (not (? a)) nil)                    (build.modus-ponens-2 @- @--)))
  :minatbl ((not . 1)))

(defderiv build.disjoined-pequal-nil-from-negative-lit
  :derive (v P (= (? a) nil))
  :from   ((proof x (v P (!= (not (? a)) nil))))
  :proof  (@derive
           ((v (= x nil) (= (not x) nil))                         (build.theorem (theorem-not-when-not-nil)))
           ((v (= (not x) nil) (= x nil))                         (build.commute-or @-))
           ((v (= (not (? a)) nil) (= (? a) nil))                 (build.instantiation @- (@sigma (x . (? a)))))
           ((v P (v (= (not (? a)) nil) (= (? a) nil)))           (build.expansion (@formula P) @-))
           ((v P (= (? a) nil))                                   (@given x))
           ((v P (= (? a) nil))                                   (build.disjoined-modus-ponens-2 @- @--)))
  :minatbl ((not . 1)))




(deftheorem theorem-not-of-not
  :derive (= (not (not x)) (if x t nil))
  :proof  (@derive
           ((= (not x) (if x nil t))                              (build.axiom (definition-of-not)))
           ((= (not (not x)) (not (if x nil t)))                  (build.pequal-by-args 'not (list @-)))
           ((= (not (if x nil t)) (if (if x nil t) nil t))        (build.instantiation @-- (@sigma (x . (if x nil t)))))
           ((= (not (not x)) (if (if x nil t) nil t))             (build.transitivity-of-pequal @-- @-)                       *1)
           ;; ---
           ((= x x)                                               (build.reflexivity (@term x))                               *2a)
           ((= (if nil y z) z)                                    (build.theorem (theorem-if-redux-nil)))
           ((= (if nil nil t) t)                                  (build.instantiation @- (@sigma (y . nil) (z . t)))         *2b)
           ((= (if t y z) y)                                      (build.theorem (theorem-if-redux-t)))
           ((= (if t nil t) nil)                                  (build.instantiation @- (@sigma (y . nil) (z . t)))         *2c)
           ((= (if x (if nil nil t) (if t nil t)) (if x t nil))   (build.pequal-by-args 'if (list *2a *2b *2c))               *2)
           ;; ---
           ((= (if (if x y z) p q)
               (if x (if y p q) (if z p q)))                      (build.theorem (theorem-if-redux-test)))
           ((= (if (if x nil t) nil t)
               (if x (if nil nil t) (if t nil t)))                (build.instantiation @- (@sigma (y . nil) (z . t) (p . nil) (q . t))))
           ((= (if (if x nil t) nil t) (if x t nil))              (build.transitivity-of-pequal @- *2))
           ((= (not (not x)) (if x t nil))                        (build.transitivity-of-pequal *1 @-)))
  :minatbl ((if . 3)
            (not . 1)))






(deftheorem theorem-iff-of-if-x-t-nil
  :derive (= (iff (if x t nil) x) t)
  :proof  (@derive
           ((v (= x nil) (= (if x y z) y))                       (build.axiom (axiom-if-when-not-nil)))
           ((v (= x nil) (= (if x t nil) t))                     (build.instantiation @- (@sigma (y . t) (z . nil)))                           *1a)
           ((= x x)                                              (build.reflexivity (@term x)))
           ((v (= x nil) (= x x))                                (build.expansion (@formula (= x nil)) @-)                                     *1b)
           ((v (= x nil) (= (iff (if x t nil) x) (iff t x)))     (build.disjoined-pequal-by-args 'iff (@formula (= x nil)) (list *1a *1b))     *1c)
           ((= (iff x y) (iff y x))                              (build.theorem (theorem-symmetry-of-iff)))
           ((= (iff t x) (iff x t))                              (build.instantiation @- (@sigma (x . t) (y . x))))
           ((v (= x nil) (= (iff t x) (iff x t)))                (build.expansion (@formula (= x nil)) @-))
           ((v (= x nil) (= (iff (if x t nil) x) (iff x t)))     (build.disjoined-transitivity-of-pequal *1c @-))
           ((v (= x nil) (= (iff x t) t))                        (build.theorem (theorem-iff-t-when-not-nil)))
           ((v (= x nil) (= (iff (if x t nil) x) t))             (build.disjoined-transitivity-of-pequal @-- @-)                               *1)
           ;; ---
           ((v (!= x nil) (= (if x y z) z))                      (build.axiom (axiom-if-when-nil)))
           ((v (!= x nil) (= (if x t nil) nil))                  (build.instantiation @- (@sigma (y . t) (z . nil)))                           *2a)
           ((= x x)                                              (build.reflexivity (@term x)))
           ((v (!= x nil) (= x x))                               (build.expansion (@formula (!= x nil)) @-)                                    *2b)
           ((v (!= x nil) (= (iff (if x t nil) x) (iff nil x)))  (build.disjoined-pequal-by-args 'iff (@formula (!= x nil)) (list *2a *2b))    *2c)
           ((= (iff x y) (iff y x))                              (build.theorem (theorem-symmetry-of-iff)))
           ((= (iff nil x) (iff x nil))                          (build.instantiation @- (@sigma (x . nil) (y . x))))
           ((v (!= x nil) (= (iff nil x) (iff x nil)))           (build.expansion (@formula (!= x nil)) @-))
           ((v (!= x nil) (= (iff (if x t nil) x) (iff x nil)))  (build.disjoined-transitivity-of-pequal *2c @-))
           ((v (!= x nil) (= (iff x nil) t))                     (build.theorem (theorem-iff-nil-when-nil)))
           ((v (!= x nil) (= (iff (if x t nil) x) t))            (build.disjoined-transitivity-of-pequal @-- @-)                               *2)
           ;; ---
           ((v (= (iff (if x t nil) x) t)
               (= (iff (if x t nil) x) t))                       (build.cut *1 *2))
           ((= (iff (if x t nil) x) t)                           (build.contraction @-)))
  :minatbl ((if . 3)
            (iff . 2)))


(deftheorem theorem-not-of-not-under-iff
  :derive (= (iff (not (not x)) x) t)
  :proof  (@derive
           ((= (not (not x)) (if x t nil))                        (build.theorem (theorem-not-of-not)))
           ((= x x)                                               (build.reflexivity (@term x)))
           ((= (iff (not (not x)) x) (iff (if x t nil) x))        (build.pequal-by-args 'iff (list @-- @-)))
           ((= (iff (if x t nil) x) t)                            (build.theorem (theorem-iff-of-if-x-t-nil)))
           ((= (iff (not (not x)) x) t)                           (build.transitivity-of-pequal @-- @-)))
  :minatbl ((if . 3)
            (iff . 2)
            (not . 1)))



(deftheorem theorem-iff-when-not-nil
  :derive (v (!= (not x) nil) (= (iff x t) t))
  :proof (@derive
          ((v (= x nil) (= (iff x t) t))         (build.theorem (theorem-iff-t-when-not-nil)))
          ((v (= (iff x t) t) (= x nil))         (build.commute-or @-))
          ((v (= (iff x t) t) (!= (not x) nil))  (build.disjoined-negative-lit-from-pequal-nil @-))
          ((v (!= (not x) nil) (= (iff x t) t))  (build.commute-or @-)))
  :minatbl ((iff . 2)
            (not . 1)))

(defderiv build.iff-when-not-nil
  :derive (= (iff (? a) t) t)
  :from   ((proof x (= (not (? a)) nil)))
  :proof  (@derive
           ((v (!= (not x) nil) (= (iff x t) t))          (build.theorem (theorem-iff-when-not-nil)))
           ((v (!= (not (? a)) nil) (= (iff (? a) t) t))  (build.instantiation @- (@sigma (x . (? a)))))
           ((= (not (? a)) nil)                           (@given x))
           ((= (iff (? a) t) t)                           (build.modus-ponens @- @--)))
  :minatbl ((iff . 2)))

(defderiv build.disjoined-iff-when-not-nil
  :derive (v P (= (iff (? a) t) t))
  :from   ((proof x (v P (= (not (? a)) nil))))
  :proof  (@derive
           ((v (!= (not x) nil) (= (iff x t) t))                (build.theorem (theorem-iff-when-not-nil)))
           ((v (!= (not (? a)) nil) (= (iff (? a) t) t))        (build.instantiation @- (@sigma (x . (? a)))))
           ((v P (v (!= (not (? a)) nil) (= (iff (? a) t) t)))  (build.expansion (@formula P) @-))
           ((v P (= (not (? a)) nil))                           (@given x))
           ((v P (= (iff (? a) t) t))                           (build.disjoined-modus-ponens @- @--)))
  :minatbl ((iff . 2)))



(dd.close)
