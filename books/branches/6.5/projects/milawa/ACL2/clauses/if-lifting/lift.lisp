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
(include-book "depth")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


;; (clause.lift-term1 x)
;;
;; This is a single pass of if-lifting.  We collect all the simple tests that
;; occur within unlifted portions of the term, and case-split based on those
;; simple tests.  This makes progress by reducing the maximum if-depth of any
;; unlifted subterm.

(defund clause.lift-term1 (x)
  (declare (xargs :guard (logic.termp x)
                  :verify-guards nil))
  (cond ((logic.constantp x) x)
        ((logic.variablep x) x)
        ((logic.functionp x)
         (let ((name (logic.function-name x))
               (args (logic.function-args x)))
           (if (and (equal name 'if)
                    (equal (len args) 3))
               (logic.function 'if
                      (list (clause.lift-term1 (first args))
                            (clause.lift-term1 (second args))
                            (clause.lift-term1 (third args))))
             (if (clause.simple-term-listp args)
                 x
               (clause.casesplit x (clause.simple-tests x) nil)))))
        ((logic.lambdap x)
         (let ((actuals (logic.lambda-actuals x)))
           (if (clause.simple-term-listp actuals)
               x
             (clause.casesplit x (clause.simple-tests x) nil))))
        (t x)))

(defthm forcing-logic.termp-of-clause.lift-term1
  (implies (force (logic.termp x))
           (equal (logic.termp (clause.lift-term1 x))
                  t))
  :hints(("Goal" :in-theory (enable clause.lift-term1))))

(verify-guards clause.lift-term1)

(defthm forcing-logic.term-atblp-of-clause.lift-term1
  (implies (and (force (logic.termp x))
                (force (logic.term-atblp x atbl))
                (force (equal (cdr (lookup 'if atbl)) 3)))
           (equal (logic.term-atblp (clause.lift-term1 x) atbl)
                  t))
  :hints(("Goal" :in-theory (enable clause.lift-term1))))

(defthm clause.lift-term1-when-no-clause.unlifted-subterms
  (implies (and (clause.lifted-termp x)
                (force (logic.termp x)))
           (equal (clause.lift-term1 x)
                  x))
  :hints(("Goal" :in-theory (enable clause.lift-term1))))



(defthmd forcing-clause.depth-of-clause.factor-strong
  (implies (and (force (logic.termp x))
                (force (not (clause.simple-termp x)))
                (force (clause.simple-term-listp (domain assignment)))
                (force (disjoint-from-nonep (domain assignment) (clause.term-paths x))))
           (equal (< (clause.depth (clause.factor x assignment))
                     (clause.depth x))
                  t)))

(local (in-theory (enable forcing-clause.depth-of-clause.factor-strong)))


(encapsulate
 ()
 (defthmd lemma-for-clause.depth-decreases-in-lambda-case
   (implies (and (logic.lambdap x)
                 (logic.termp x)
                 (not (clause.simple-term-listp (logic.lambda-actuals x)))
                 (clause.simple-term-listp (domain assignment))
                 (disjoint-from-nonep (domain assignment) (clause.term-paths-list (logic.lambda-actuals x))))
            (< (clause.depth (clause.factor (clause.deepest-after-factoring (logic.lambda-actuals x) assignment) assignment))
               (clause.depth (clause.deepest (logic.lambda-actuals x)))))
   :hints(("Goal"
           :in-theory (disable clause.deepest-weakly-deeper-than-any-member)
           :use ((:instance clause.deepest-weakly-deeper-than-any-member
                            (x (logic.lambda-actuals x))
                            (a (clause.deepest-after-factoring (logic.lambda-actuals x) assignment)))))))

 (defthmd lemma2-for-clause.depth-decreases-in-lambda-case
   (implies (and (logic.lambdap x)
                 (logic.termp x)
                 (not (clause.simple-term-listp (logic.lambda-actuals x))))
            (< (clause.depth
                (clause.factor
                 (clause.deepest-after-factoring
                  (logic.lambda-actuals x)
                  (clause.special-assignment x (clause.cases (clause.simple-tests-list (logic.lambda-actuals x)) nil)))
                 (clause.special-assignment x (clause.cases (clause.simple-tests-list (logic.lambda-actuals x)) nil))))
               (clause.depth (clause.deepest (logic.lambda-actuals x)))))
   :hints(("Goal"
           :in-theory (disable clause.simple-term-listp-of-domain-of-clause.cases
                               disjoint-from-nonep-of-domain-of-clause.cases
                               lemma-for-clause.depth-decreases-in-lambda-case)
           :use ((:instance lemma-for-clause.depth-decreases-in-lambda-case
                            (assignment (clause.special-assignment x (clause.cases (clause.simple-tests-list (logic.lambda-actuals x)) nil))))
                 (:instance clause.simple-term-listp-of-domain-of-clause.cases
                            (x     (clause.special-assignment x (clause.cases (clause.simple-tests-list (logic.lambda-actuals x)) nil)))
                            (cases (clause.simple-tests-list (logic.lambda-actuals x)))
                            (assignment nil))
                 (:instance disjoint-from-nonep-of-domain-of-clause.cases
                            (x     (clause.special-assignment x (clause.cases (clause.simple-tests-list (logic.lambda-actuals x)) nil)))
                            (cases (clause.simple-tests-list (logic.lambda-actuals x)))
                            (set   (clause.term-paths-list (logic.lambda-actuals x)))
                            (assignment nil))))))

 (defthmd clause.depth-decreases-in-lambda-case
   (implies (and (logic.lambdap x)
                 (not (clause.simple-term-listp (logic.lambda-actuals x)))
                 (logic.termp x))
            (< (clause.depth-list (clause.unlifted-subterms-list (clause.multifactor x (clause.cases (clause.simple-tests-list (logic.lambda-actuals x)) nil))))
               (clause.depth-list (logic.lambda-actuals x))))
   :hints(("Goal" :in-theory (enable lemma2-for-clause.depth-decreases-in-lambda-case
                                     clause.depth-list-redefinition)))))


(encapsulate
 ()
 (defthmd lemma-for-clause.depth-decreases-in-logic.functionp-case
   (implies (and (logic.functionp x)
                 (logic.termp x)
                 (not (clause.simple-term-listp (logic.function-args x)))
                 (clause.simple-term-listp (domain assignment))
                 (disjoint-from-nonep (domain assignment) (clause.term-paths-list (logic.function-args x))))
            (< (clause.depth (clause.factor (clause.deepest-after-factoring (logic.function-args x) assignment) assignment))
               (clause.depth (clause.deepest (logic.function-args x)))))
   :hints(("Goal"
           :in-theory (disable clause.deepest-weakly-deeper-than-any-member)
           :use ((:instance clause.deepest-weakly-deeper-than-any-member
                            (x (logic.function-args x))
                            (a (clause.deepest-after-factoring (logic.function-args x) assignment)))))))

 (defthmd lemma2-for-clause.depth-decreases-in-logic.functionp-case
   (implies (and (logic.functionp x)
                 (logic.termp x)
                 (not (clause.simple-term-listp (logic.function-args x))))
            (< (clause.depth
                (clause.factor
                 (clause.deepest-after-factoring (logic.function-args x) (clause.special-assignment x (clause.cases (clause.simple-tests-list (logic.function-args x)) nil)))
                 (clause.special-assignment x (clause.cases (clause.simple-tests-list (logic.function-args x)) nil))))
               (clause.depth (clause.deepest (logic.function-args x)))))
   :hints(("Goal"
           :in-theory (disable clause.simple-term-listp-of-domain-of-clause.cases
                               disjoint-from-nonep-of-domain-of-clause.cases
                               lemma-for-clause.depth-decreases-in-logic.functionp-case)
           :use ((:instance lemma-for-clause.depth-decreases-in-logic.functionp-case
                            (assignment (clause.special-assignment x (clause.cases (clause.simple-tests-list (logic.function-args x)) nil))))
                 (:instance clause.simple-term-listp-of-domain-of-clause.cases
                            (x     (clause.special-assignment x (clause.cases (clause.simple-tests-list (logic.function-args x)) nil)))
                            (cases (clause.simple-tests-list (logic.function-args x)))
                            (assignment nil))
                 (:instance disjoint-from-nonep-of-domain-of-clause.cases
                            (x     (clause.special-assignment x (clause.cases (clause.simple-tests-list (logic.function-args x)) nil)))
                            (cases (clause.simple-tests-list (logic.function-args x)))
                            (set   (clause.term-paths-list (logic.function-args x)))
                            (assignment nil))))))

 (defthmd clause.depth-decreases-in-non-if-logic.functionp-case
   (implies (and (not (equal (logic.function-name x) 'if))
                 (not (clause.simple-term-listp (logic.function-args x)))
                 (logic.functionp x)
                 (logic.termp x))
            (< (clause.depth-list (clause.unlifted-subterms-list (clause.multifactor x (clause.cases (clause.simple-tests-list (logic.function-args x)) nil))))
               (clause.depth-list (logic.function-args x))))
   :hints(("Goal" :in-theory (e/d (clause.depth-list-redefinition
                                   lemma2-for-clause.depth-decreases-in-logic.functionp-case)
                                  (clause.simple-termp-when-bad-args-logic.functionp
                                   clause.unlifted-subterms-when-bad-args-logic.functionp)))))

 (defthmd clause.depth-decreases-in-bad-args-logic.functionp-case
   (implies (and (not (equal (len (logic.function-args x)) 3))
                 (not (clause.simple-term-listp (logic.function-args x)))
                 (logic.functionp x)
                 (logic.termp x))
            (< (clause.depth-list (clause.unlifted-subterms-list (clause.multifactor x (clause.cases (clause.simple-tests-list (logic.function-args x)) nil))))
               (clause.depth-list (logic.function-args x))))
   :hints(("Goal" :in-theory (enable clause.depth-list-redefinition
                                     lemma2-for-clause.depth-decreases-in-logic.functionp-case)))))

(defthm clause.lift-term1-makes-progress
  (implies (and (logic.termp x)
                (clause.unlifted-subterms x))
           (equal (< (clause.depth-list (clause.unlifted-subterms (clause.lift-term1 x)))
                     (clause.depth-list (clause.unlifted-subterms x)))
                  t))
  :hints(("Goal"
          :expand (clause.depth x)
          :in-theory (enable clause.lift-term1
                             clause.depth-decreases-in-bad-args-logic.functionp-case
                             clause.depth-decreases-in-non-if-logic.functionp-case
                             clause.depth-decreases-in-lambda-case)
          :induct (clause.lift-term1 x))))




;; (clause.lift-term x)
;;
;; This is full, multi-pass if-lifting.  We repeatedly call if-lift1 to bring
;; up tests to the top of a term, until the term is in lifted form.

(defund clause.lift-term (x)
  (declare (xargs :guard (logic.termp x)
                  :measure (clause.depth-list (clause.unlifted-subterms x))))
  (if (and (logic.termp x)
           (not (clause.lifted-termp x)))
      (clause.lift-term (clause.lift-term1 x))
    x))

(defthm forcing-logic.termp-of-clause.lift-term
  (implies (force (logic.termp x))
           (equal (logic.termp (clause.lift-term x))
                  t))
  :hints(("Goal" :in-theory (enable clause.lift-term))))

(defthm forcing-logic.term-atblp-of-clause.lift-term
  (implies (and (force (logic.termp x))
                (force (logic.term-atblp x atbl))
                (force (equal (cdr (lookup 'if atbl)) 3)))
           (equal (logic.term-atblp (clause.lift-term x) atbl)
                  t))
  :hints(("Goal" :in-theory (enable clause.lift-term))))

(defthm forcing-clause.lifted-termp-of-clause.lift-term
  (implies (force (logic.termp x))
           (equal (clause.lifted-termp (clause.lift-term x))
                  t))
  :hints(("Goal" :in-theory (enable clause.lift-term))))

(defthm clause.lift-term-when-clause.simple-termp
  (implies (clause.simple-termp x)
           (equal (clause.lift-term x)
                  x))
  :hints(("Goal" :in-theory (enable clause.lift-term))))

(defthm clause.lift-term-when-clause.lifted-termp
  (implies (clause.lifted-termp x)
           (equal (clause.lift-term x)
                  x))
  :hints(("Goal" :in-theory (enable clause.lift-term))))



(defprojection :list (clause.lift-term-list x)
               :element (clause.lift-term x)
               :guard (logic.term-listp x)
               :nil-preservingp t)

(defthm forcing-logic.term-listp-of-clause.lift-term-list
  (implies (force (logic.term-listp x))
           (equal (logic.term-listp (clause.lift-term-list x))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-logic.term-list-atblp-of-clause.lift-term-list
  (implies (and (force (logic.term-listp x))
                (force (logic.term-list-atblp x atbl))
                (force (equal (cdr (lookup 'if atbl)) 3)))
           (equal (logic.term-list-atblp (clause.lift-term-list x) atbl)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm clause.lift-term-list-when-clause.simple-term-listp
  (implies (clause.simple-term-listp x)
           (equal (clause.lift-term-list x)
                  (list-fix x)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm clause.lift-term-list-when-clause.lifted-term-listp
  (implies (clause.lifted-term-listp x)
           (equal (clause.lift-term-list x)
                  (list-fix x)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-clause.lifted-term-listp-of-clause.lift-term-list
  (implies (force (logic.term-listp x))
           (equal (clause.lifted-term-listp (clause.lift-term-list x))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))




(defprojection :list (clause.lift-term-list-list x)
               :element (clause.lift-term-list x)
               :guard (logic.term-list-listp x)
               :nil-preservingp t)

(defthm forcing-logic.term-listp-of-clause.lift-term-list-list
  (implies (force (logic.term-list-listp x))
           (equal (logic.term-list-listp (clause.lift-term-list-list x))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-logic.term-list-atblp-of-clause.lift-term-list-list
  (implies (and (force (logic.term-list-listp x))
                (force (logic.term-list-list-atblp x atbl))
                (force (equal (cdr (lookup 'if atbl)) 3)))
           (equal (logic.term-list-list-atblp (clause.lift-term-list-list x) atbl)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm clause.lift-term-list-list-when-clause.simple-term-list-listp
  (implies (clause.simple-term-list-listp x)
           (equal (clause.lift-term-list-list x)
                  (list-list-fix x)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-cons-listp-of-clause.lift-term-list-list
  (implies (force (cons-listp x))
           (equal (cons-listp (clause.lift-term-list-list x))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))