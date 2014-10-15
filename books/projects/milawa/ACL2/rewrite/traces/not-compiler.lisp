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
(include-book "trace-okp")
(include-book "if-lemmas")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)



(defund@ rw.compile-negative-if-trace (x)
  (declare (xargs :guard (and (rw.tracep x)
                              (rw.negative-if-tracep x))
                  :verify-guards nil))
  (let* ((hypbox   (rw.trace->hypbox x))
         (iffp     (rw.trace->iffp x))
         (lhs      (rw.trace->lhs x))
         (guts     (first (logic.function-args lhs)))
         (lemma    (@derive
                    ((= (not x) (if x nil t))       (build.axiom (definition-of-not)))
                    ((= (if x nil t) (not x))       (build.commute-pequal @-))
                    ((= (if guts nil t) (not guts)) (build.instantiation @- (list (cons 'x guts))))))
         (lemma2   (if iffp
                       (build.iff-from-pequal lemma)
                     (build.equal-from-pequal lemma))))
    (if (or (rw.hypbox->left hypbox)
            (rw.hypbox->right hypbox))
        (build.expansion (rw.hypbox-formula hypbox) lemma2)
      lemma2)))

(defobligations rw.compile-negative-if-trace
  (build.commute-pequal
   build.iff-from-pequal
   build.equal-from-pequal)
  :extra-axioms ((definition-of-not)))

(encapsulate
 ()
 (local (in-theory (enable rw.compile-negative-if-trace
                           rw.negative-if-tracep
                           logic.term-formula
                           rw.assms-formula
                           rw.hypbox-formula)))

 (local (in-theory (enable definition-of-not)))

 (local (in-theory (enable rw.trace-conclusion-formula
                           rw.trace-formula)))

 (defthm rw.compile-negative-if-trace-under-iff
   (iff (rw.compile-negative-if-trace x)
        t))

 (defthm forcing-logic.appealp-of-rw.compile-negative-if-trace
   (implies (force (and (rw.tracep x)
                        (rw.negative-if-tracep x)))
            (equal (logic.appealp (rw.compile-negative-if-trace x))
                   t)))

 (defthm logic.conclusion-of-rw.compile-negative-if-trace
   (implies (force (and (rw.tracep x)
                        (rw.negative-if-tracep x)))
            (equal (logic.conclusion (rw.compile-negative-if-trace x))
                   (rw.trace-formula x)))
   :rule-classes ((:rewrite :backchain-limit-lst 0)))

 (defthm@ logic.proofp-of-rw.compile-negative-if-trace
   (implies (force (and (rw.tracep x)
                        (rw.negative-if-tracep x)
                        ;; ---
                        (rw.trace-atblp x atbl)
                        (logic.proof-listp proofs axioms thms atbl)
                        (equal (cdr (lookup 'iff atbl)) 2)
                        (equal (cdr (lookup 'equal atbl)) 2)
                        (@obligations rw.compile-negative-if-trace)))
            (equal (logic.proofp (rw.compile-negative-if-trace x) axioms thms atbl)
                   t)))

 (verify-guards rw.compile-negative-if-trace))







(deftheorem rw.compile-not-lemma1
  :derive (v (!= (iff x y) t) (= (not x) (not y)))
  :proof  (@derive

           ((v (!= (iff x1 x2) t) (= (if x1 y z) (if x2 y z)))     (build.theorem (rw.theorem-iff-implies-pequal-if-1)))
           ((v (!= (iff x y) t) (= (if x nil t) (if y nil t)))     (build.instantiation @- (@sigma (x1 . x) (x2 . y) (y . nil) (z . t))) *1)

           ((= (not x) (if x nil t))                               (build.axiom (definition-of-not)))
           ((= (if x nil t) (not x))                               (build.commute-pequal @-)  *2)

           ((= (if y nil t) (not y))                               (build.instantiation @- (@sigma (x . y))))
           ((v (!= (iff x y) t) (= (if y nil t) (not y)))          (build.expansion (@formula (!= (iff x y) t)) @-))
           ((v (!= (iff x y) t) (= (if x nil t) (not y)))          (build.disjoined-transitivity-of-pequal *1 @-))
           ((v (!= (iff x y) t) (= (not y) (if x nil t)))          (build.disjoined-commute-pequal @-))

           ((v (!= (iff x y) t) (= (if x nil t) (not x)))          (build.expansion (@formula (!= (iff x y) t)) *2))
           ((v (!= (iff x y) t) (= (not y) (not x)))               (build.disjoined-transitivity-of-pequal @-- @-))
           ((v (!= (iff x y) t) (= (not x) (not y)))               (build.disjoined-commute-pequal @-)))

  :minatbl ((iff . 2)
            (not . 1)
            (if . 3)))

(defderiv rw.compile-not-trace-lemma-0a
  ;; Assumptions; general case
  :from   ((proof x (v P (= (iff (? lhs) (? rhs)) t))))
  :derive (v P (= (not (? lhs)) (not (? rhs))))
  :proof  (@derive
           ((v (!= (iff x y) t) (= (not x) (not y)))                                 (build.theorem (rw.compile-not-lemma1)))
           ((v (!= (iff (? lhs) (? rhs)) t) (= (not (? lhs)) (not (? rhs))))         (build.instantiation @- (@sigma (x . (? lhs)) (y . (? rhs)))))
           ((v P (v (!= (iff (? lhs) (? rhs)) t) (= (not (? lhs)) (not (? rhs)))))   (build.expansion (@formula P) @-))
           ((v P (= (iff (? lhs) (? rhs)) t))                                        (@given x))
           ((v P (= (not (? lhs)) (not (? rhs))))                                    (build.disjoined-modus-ponens @- @--)))
  :minatbl ((not . 1)))

(defderiv rw.compile-not-trace-lemma-1a
  ;; Assumptions; special case when rhs is T
  :from   ((proof x (v P (= (iff (? lhs) t) t))))
  :derive (v P (= (not (? lhs)) nil))
  :proof  (@derive
           ((v (= x nil) (= (not x) nil))      (build.theorem (theorem-not-when-not-nil)))
           ((v (= t nil) (= (not t) nil))      (build.instantiation @- (@sigma (x . t))))
           ((!= t nil)                         (build.axiom (axiom-t-not-nil)))
           ((= (not t) nil)                    (build.modus-ponens-2 @- @--))
           ((v P (= (not t) nil))              (build.expansion (@formula P) @-)    *1)
           ((v P (= (iff (? lhs) t) t))        (@given x))
           ((v P (= (not (? lhs)) (not t)))    (rw.compile-not-trace-lemma-0a @-))
           ((v P (= (not (? lhs)) nil))        (build.disjoined-transitivity-of-pequal @- *1)))
  :minatbl ((not . 1)))

(defderiv rw.compile-not-trace-lemma-2a
  ;; Assumptions; special case when rhs is NIL
  :from   ((proof x (v P (= (iff (? lhs) nil) t))))
  :derive (v P (= (not (? lhs)) t))
  :proof  (@derive
           ((v (!= x nil) (= (not x) t))              (build.theorem (theorem-not-when-nil)))
           ((v (!= nil nil) (= (not nil) t))          (build.instantiation @- (@sigma (x . nil))))
           ((= nil nil)                               (build.reflexivity ''nil))
           ((= (not nil) t)                           (build.modus-ponens @- @--))
           ((v P (= (not nil) t))                     (build.expansion (@formula P) @-) *1)
           ((v P (= (iff (? lhs) nil) t))             (@given x))
           ((v P (= (not (? lhs)) (not nil)))         (rw.compile-not-trace-lemma-0a @-))
           ((v P (= (not (? lhs)) t))                 (build.disjoined-transitivity-of-pequal @- *1)))
  :minatbl ((not . 1)))

(defderiv rw.compile-not-trace-lemma-0b
  ;; No assumptions; general case
  :from   ((proof x (= (iff (? lhs) (? rhs)) t)))
  :derive (= (not (? lhs)) (not (? rhs)))
  :proof  (@derive
           ((v (!= (iff x y) t) (= (not x) (not y)))                          (build.theorem (rw.compile-not-lemma1)))
           ((v (!= (iff (? lhs) (? rhs)) t) (= (not (? lhs)) (not (? rhs))))  (build.instantiation @- (@sigma (x . (? lhs)) (y . (? rhs)))))
           ((= (iff (? lhs) (? rhs)) t)                                       (@given x))
           ((= (not (? lhs)) (not (? rhs)))                                   (build.modus-ponens @- @--)))
  :minatbl ((not . 1)))

(defderiv rw.compile-not-trace-lemma-1b
  ;; No assumptions; special case when rhs is T
  :from   ((proof x (= (iff (? lhs) t) t)))
  :derive (= (not (? lhs)) nil)
  :proof  (@derive
           ((v (= x nil) (= (not x) nil))      (build.theorem (theorem-not-when-not-nil)))
           ((v (= t nil) (= (not t) nil))      (build.instantiation @- (@sigma (x . t))))
           ((!= t nil)                         (build.axiom (axiom-t-not-nil)))
           ((= (not t) nil)                    (build.modus-ponens-2 @- @--) *1)
           ((= (iff (? lhs) t) t)              (@given x))
           ((= (not (? lhs)) (not t))          (rw.compile-not-trace-lemma-0b @-))
           ((= (not (? lhs)) nil)              (build.transitivity-of-pequal @- *1)))
  :minatbl ((not . 1)))

(defderiv rw.compile-not-trace-lemma-2b
  ;; No assumptions; special case when rhs is NIL
  :from   ((proof x (= (iff (? lhs) nil) t)))
  :derive (= (not (? lhs)) t)
  :proof  (@derive
           ((v (!= x nil) (= (not x) t))       (build.theorem (theorem-not-when-nil)))
           ((v (!= nil nil) (= (not nil) t))   (build.instantiation @- (@sigma (x . nil))))
           ((= nil nil)                        (build.reflexivity ''nil))
           ((= (not nil) t)                    (build.modus-ponens @- @--) *1)
           ((= (iff (? lhs) nil) t)            (@given x))
           ((= (not (? lhs)) (not nil))        (rw.compile-not-trace-lemma-0b @-))
           ((= (not (? lhs)) t)                (build.transitivity-of-pequal @- *1)))
  :minatbl ((not . 1)))

(defund@ rw.compile-not-trace (x proofs)
  (declare (xargs :guard (and (rw.tracep x)
                              (rw.not-tracep x)
                              (logic.appeal-listp proofs)
                              (equal (logic.strip-conclusions proofs)
                                     (rw.trace-list-formulas (rw.trace->subtraces x))))
                  :verify-guards nil))
  (let* ((hypbox  (rw.trace->hypbox x))
         (iffp    (rw.trace->iffp x))
         (sub1    (first (rw.trace->subtraces x)))
         (rhs     (rw.trace->rhs sub1))
         (proof1  (first proofs)))
    (if (or (rw.hypbox->left hypbox)
            (rw.hypbox->right hypbox))
        (let ((lemma (cond ((equal rhs ''t)
                            (rw.compile-not-trace-lemma-1a proof1))
                           ((equal rhs ''nil)
                            (rw.compile-not-trace-lemma-2a proof1))
                           (t
                            (rw.compile-not-trace-lemma-0a proof1)))))
          (if iffp
              (build.disjoined-iff-from-pequal lemma)
            (build.disjoined-equal-from-pequal lemma)))
      (let ((lemma (cond ((equal rhs ''t)
                          (rw.compile-not-trace-lemma-1b proof1))
                         ((equal rhs ''nil)
                          (rw.compile-not-trace-lemma-2b proof1))
                         (t
                          (rw.compile-not-trace-lemma-0b proof1)))))
        (if iffp
            (build.iff-from-pequal lemma)
          (build.equal-from-pequal lemma))))))

(defobligations rw.compile-not-trace
  (rw.compile-not-trace-lemma-1a
   rw.compile-not-trace-lemma-2a
   rw.compile-not-trace-lemma-0a
   build.disjoined-iff-from-pequal
   build.disjoined-equal-from-pequal
   rw.compile-not-trace-lemma-1b
   rw.compile-not-trace-lemma-2b
   rw.compile-not-trace-lemma-0b
   build.iff-from-pequal
   build.equal-from-pequal))


(encapsulate
 ()
 (local (in-theory (enable rw.compile-not-trace
                           rw.not-tracep
                           logic.term-formula
                           rw.hypbox-formula)))

 (local (in-theory (enable rw.trace-conclusion-formula
                           rw.trace-formula)))

 (defthmd lemma-1-for-rw.compile-not-trace
   (implies (and (equal (rw.trace-list-formulas (rw.trace->subtraces x)) (logic.strip-conclusions proofs))
                 (equal (len (rw.trace->subtraces x)) 1))
            (equal (consp proofs)
                   t)))

 (defthmd lemma-2-for-rw.compile-not-trace
   (implies (and (equal (rw.trace-list-formulas (rw.trace->subtraces x)) (logic.strip-conclusions proofs))
                 (equal (len (rw.trace->subtraces x)) 1))
            (equal (logic.conclusion (first proofs))
                   (rw.trace-formula (first (rw.trace->subtraces x)))))
   :hints(("Goal" :in-theory (disable rw.trace-formula))))

 (local (in-theory (enable lemma-1-for-rw.compile-not-trace
                           lemma-2-for-rw.compile-not-trace)))

 (defthm rw.compile-not-trace-under-iff
   (iff (rw.compile-not-trace x proofs)
        t))

 (defthm forcing-logic.appealp-of-rw.compile-not-trace
   (implies (force (and (rw.tracep x)
                        (rw.not-tracep x)
                        (logic.appeal-listp proofs)
                        (equal (logic.strip-conclusions proofs) (rw.trace-list-formulas (rw.trace->subtraces x)))))
            (equal (logic.appealp (rw.compile-not-trace x proofs))
                   t)))

 (defthm logic.conclusion-of-rw.compile-not-trace
   (implies (force (and (rw.tracep x)
                        (rw.not-tracep x)
                        (logic.appeal-listp proofs)
                        (equal (logic.strip-conclusions proofs) (rw.trace-list-formulas (rw.trace->subtraces x)))))
            (equal (logic.conclusion (rw.compile-not-trace x proofs))
                   (rw.trace-formula x)))
   :rule-classes ((:rewrite :backchain-limit-lst 0)))

 (defthm@ logic.proofp-of-rw.compile-not-trace
   (implies (force (and (rw.tracep x)
                        (rw.not-tracep x)
                        (logic.appeal-listp proofs)
                        (equal (logic.strip-conclusions proofs) (rw.trace-list-formulas (rw.trace->subtraces x)))
                        ;; ---
                        (rw.trace-atblp x atbl)
                        (logic.proof-listp proofs axioms thms atbl)
                        (@obligations rw.compile-not-trace)
                        (equal (cdr (lookup 'iff atbl)) 2)
                        (equal (cdr (lookup 'equal atbl)) 2)
                        (equal (cdr (lookup 'not atbl)) 1)
                        (equal (cdr (lookup 'if atbl)) 3)))
            (equal (logic.proofp (rw.compile-not-trace x proofs) axioms thms atbl)
                   t)))

 (verify-guards rw.compile-not-trace))

