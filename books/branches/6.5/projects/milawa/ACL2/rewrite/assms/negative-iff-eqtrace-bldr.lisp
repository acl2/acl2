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
(include-book "eqtrace-okp")
(include-book "../../clauses/basic-bldrs")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


(defderiv rw.negative-iff-eqtrace-nhyp-bldr-lemma-1
  :from   ((proof x (= (? a) (not (? b)))))
  :derive (v (!= (? a) nil) (= (iff (? b) t) t))
  :proof  (@derive
           ((v (!= x nil) (= (not x) t))                  (build.theorem (theorem-not-when-nil)))
           ((v (!= (? b) nil) (= (not (? b)) t))          (build.instantiation @- (@sigma (x . (? b)))) *1a)
           ((= (? a) (not (? b)))                         (@given x))
           ((v (!= (? b) nil) (= (? a) (not (? b))))      (build.expansion (@formula (!= (? b) nil)) @-))
           ((v (!= (? b) nil) (= (? a) t))                (build.disjoined-transitivity-of-pequal @- *1a))
           ((v (!= (? b) nil) (!= (? a) nil))             (build.disjoined-not-nil-from-t @-) *1)
           ((v (= x nil) (= (iff x t) t))                 (build.theorem (theorem-iff-t-when-not-nil)))
           ((v (= (? b) nil) (= (iff (? b) t) t))         (build.instantiation @- (@sigma (x . (? b)))))
           ((v (= (iff (? b) t) t) (!= (? a) nil))        (build.cut @- *1))
           ((v (!= (? a) nil) (= (iff (? b) t) t))        (build.commute-or @-)))
  :minatbl ((iff . 2)))

(defund@ rw.negative-iff-eqtrace-nhyp-bldr (nhyp)
  ;; Given an nhyp that matches a negative-iff eqtrace, prove:
  ;;   nhyp != nil v (equal lhs rhs) = t
  (declare (xargs :guard (and (logic.termp nhyp)
                              (rw.negative-iff-eqtrace t nhyp))
                  :verify-guards nil))
  ;; Let nhyp be (not* (equal a b)).
  (let* ((guts (clause.negative-term-guts nhyp))
         (main-proof (@derive
                      ((= nhyp (not guts))                           (clause.standardize-negative-term-bldr nhyp))
                      ((v (!= nhyp nil) (= (iff guts t) t))          (rw.negative-iff-eqtrace-nhyp-bldr-lemma-1 @-)))))
    (if (logic.term-< ''t guts)
        (build.disjoined-commute-iff main-proof)
      main-proof)))

(defobligations rw.negative-iff-eqtrace-nhyp-bldr
  (clause.standardize-negative-term-bldr
   rw.negative-iff-eqtrace-nhyp-bldr-lemma-1
   build.disjoined-commute-iff))

(encapsulate
 ()
 (local (in-theory (enable rw.negative-iff-eqtrace
                           rw.negative-iff-eqtrace-nhyp-bldr
                           theorem-not-when-nil
                           theorem-iff-t-when-not-nil
                           logic.term-formula)))

 (local (in-theory (disable forcing-equal-of-logic.pequal-rewrite-two
                            forcing-equal-of-logic.pequal-rewrite
                            forcing-equal-of-logic.por-rewrite-two
                            forcing-equal-of-logic.por-rewrite
                            forcing-equal-of-logic.pnot-rewrite-two
                            forcing-equal-of-logic.pnot-rewrite)))

 (defthm rw.negative-iff-eqtrace-nhyp-bldr-under-iff
   (iff (rw.negative-iff-eqtrace-nhyp-bldr nhyp)
        t))

 (defthm forcing-logic.appealp-of-rw.negative-iff-eqtrace-nhyp-bldr
   (implies (force (and (logic.termp nhyp)
                        (rw.negative-iff-eqtrace t nhyp)))
            (equal (logic.appealp (rw.negative-iff-eqtrace-nhyp-bldr nhyp))
                   t)))

 (defthm forcing-logic.conclusion-of-rw.negative-iff-eqtrace-nhyp-bldr
   (implies (force (and (logic.termp nhyp)
                        (rw.negative-iff-eqtrace t nhyp)))
            (equal (logic.conclusion (rw.negative-iff-eqtrace-nhyp-bldr nhyp))
                   (logic.por (logic.term-formula nhyp)
                              (logic.pequal (logic.function 'iff
                                                            (list (rw.eqtrace->lhs (rw.negative-iff-eqtrace t nhyp))
                                                                  (rw.eqtrace->rhs (rw.negative-iff-eqtrace t nhyp))))
                                            ''t))))
   :rule-classes ((:rewrite :backchain-limit-lst 0)))

 (defthm@ forcing-logic.proofp-of-rw.negative-iff-eqtrace-nhyp-bldr
   (implies (force (and (logic.termp nhyp)
                        (rw.negative-iff-eqtrace t nhyp)
                        ;; ---
                        (logic.term-atblp nhyp atbl)
                        (equal (cdr (lookup 'not atbl)) 1)
                        (equal (cdr (lookup 'iff atbl)) 2)
                        (@obligations rw.negative-iff-eqtrace-nhyp-bldr)))
            (equal (logic.proofp (rw.negative-iff-eqtrace-nhyp-bldr nhyp) axioms thms atbl)
                   t)))

 (verify-guards rw.negative-iff-eqtrace-nhyp-bldr))



(defund rw.negative-iff-eqtrace-bldr (x box)
  ;; Given a negative-iff eqtrace that is box-okp, prove
  ;;   hypbox-formula v (equal lhs rhs) = t
  (declare (xargs :guard (and (rw.eqtracep x)
                              (rw.hypboxp box)
                              (rw.negative-iff-eqtrace-okp x box))
                  :verify-guards nil))
  (let* ((left      (rw.hypbox->left box))
         (right     (rw.hypbox->right box))
         (nhyp-left (rw.find-nhyp-for-negative-iff-eqtracep left x)))
    ;; First search for a working hyp on the left.
    (if nhyp-left
        ;; 1. nhyp-left v (iff lhs rhs) = t      Negative-Iff eqtrace nhyp bldr
        ;; 2. Left v (iff lhs rhs) = t           Multi assoc expansion
        (let* ((line-1 (rw.negative-iff-eqtrace-nhyp-bldr nhyp-left))
               (line-2 (build.multi-assoc-expansion line-1 (logic.term-list-formulas left))))
          (if right
              ;; 3. Left v (Right v (iff lhs rhs) = t)    DJ Left Expansion
              ;; 4. (Left v Right) v (iff lhs rhs) = t    Associativity
              (build.associativity (build.disjoined-left-expansion line-2 (clause.clause-formula right)))
            ;; Else we're done already
            line-2))
      ;; Else we know there must be a matching hyp on the right, since our guard
      ;; requires we are a box-okp negative-iff eqtrace.
      ;;
      ;; 1. nhyp-right v (equal lhs rhs) = t       Negative-Iff eqtrace nhyp bldr
      ;; 2. Right v (equal lhs rhs) = t            Multi assoc expansion.
      (let* ((nhyp-right (rw.find-nhyp-for-negative-iff-eqtracep right x))
             (line-1     (rw.negative-iff-eqtrace-nhyp-bldr nhyp-right))
             (line-2     (build.multi-assoc-expansion line-1 (logic.term-list-formulas right))))
        (if left
            ;; 3. Left v (Right v (iff lhs rhs) = t)    Expansion
            ;; 4. (Left v Right) v (iff lhs rhs) = t    Associativity
            (build.associativity
             (build.expansion (clause.clause-formula left) line-2))
          ;; Else we're done already.
          line-2)))))

(defobligations rw.negative-iff-eqtrace-bldr
  (rw.negative-iff-eqtrace-nhyp-bldr
   build.multi-assoc-expansion
   build.disjoined-left-expansion))

(encapsulate
 ()
 (local (in-theory (enable rw.negative-iff-eqtrace-bldr
                           rw.negative-iff-eqtrace-okp
                           rw.hypbox-formula
                           rw.eqtrace-formula
                           )))

 (defthm rw.negative-iff-eqtrace-bldr-under-iff
   (iff (rw.negative-iff-eqtrace-bldr x box)
        t))

 (defthm forcing-logic.appealp-of-rw.negative-iff-eqtrace-bldr
   (implies (force (and (rw.eqtracep x)
                        (rw.hypboxp box)
                        (rw.negative-iff-eqtrace-okp x box)))
            (equal (logic.appealp (rw.negative-iff-eqtrace-bldr x box))
                   t)))

 (defthm forcing-logic.conclusion-of-rw.negative-iff-eqtrace-bldr
   (implies (force (and (rw.eqtracep x)
                        (rw.hypboxp box)
                        (rw.negative-iff-eqtrace-okp x box)))
            (equal (logic.conclusion (rw.negative-iff-eqtrace-bldr x box))
                   (rw.eqtrace-formula x box)))
   :rule-classes ((:rewrite :backchain-limit-lst 0)))

 (defthm@ forcing-logic.proofp-of-rw.negative-iff-eqtrace-bldr
   (implies (force (and (rw.eqtracep x)
                        (rw.hypboxp box)
                        (rw.negative-iff-eqtrace-okp x box)
                        ;; ---
                        (equal (cdr (lookup 'not atbl)) 1)
                        (equal (cdr (lookup 'iff atbl)) 2)
                        (rw.hypbox-atblp box atbl)
                        (@obligations rw.negative-iff-eqtrace-bldr)))
            (equal (logic.proofp (rw.negative-iff-eqtrace-bldr x box) axioms thms atbl)
                   t)))

 (verify-guards rw.negative-iff-eqtrace-bldr))

