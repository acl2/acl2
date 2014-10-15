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



(defund@ rw.secondary-eqtrace-nhyp-bldr (nhyp x)
  ;; Given an nhyp that matches a secondary eqtrace, prove:
  ;;   nhyp != nil v (equal lhs rhs) = t
  (declare (xargs :guard (and (logic.termp nhyp)
                              (rw.eqtracep x)
                              (equal (rw.secondary-eqtrace t nhyp) x))
                  :verify-guards nil))
  (if (equal (rw.eqtrace->lhs x) nhyp)
      ;; The args are already in order.
      (@derive
       ((v (!= nhyp nil) (= nhyp nil))                (build.propositional-schema (logic.pequal nhyp ''nil)))
       ((v (!= nhyp nil) (= (equal nhyp nil) t))      (build.disjoined-equal-from-pequal @-)))
    ;; The args are out of order.
    (@derive
     ((v (!= nhyp nil) (= nhyp nil))                  (build.propositional-schema (logic.pequal nhyp ''nil)))
     ((v (!= nhyp nil) (= nil nhyp))                  (build.disjoined-commute-pequal @-))
     ((v (!= nhyp nil) (= (equal nil nhyp) t))        (build.disjoined-equal-from-pequal @-)))))

(defobligations rw.secondary-eqtrace-nhyp-bldr
  (build.propositional-schema
   build.disjoined-equal-from-pequal
   build.disjoined-commute-pequal))

(encapsulate
 ()
 (local (in-theory (enable rw.secondary-eqtrace
                           rw.secondary-eqtrace-nhyp-bldr
                           logic.term-formula)))

 (local (in-theory (disable forcing-equal-of-logic.pequal-rewrite-two
                            forcing-equal-of-logic.pequal-rewrite
                            forcing-equal-of-logic.por-rewrite-two
                            forcing-equal-of-logic.por-rewrite
                            forcing-equal-of-logic.pnot-rewrite-two
                            forcing-equal-of-logic.pnot-rewrite)))

 (defthm rw.secondary-eqtrace-nhyp-bldr-under-iff
   (iff (rw.secondary-eqtrace-nhyp-bldr nhyp x)
        t))

 (defthm forcing-logic.appealp-of-rw.secondary-eqtrace-nhyp-bldr
   (implies (force (and (logic.termp nhyp)
                        (rw.eqtracep x)
                        (equal (rw.secondary-eqtrace t nhyp) x)))
            (equal (logic.appealp (rw.secondary-eqtrace-nhyp-bldr nhyp x))
                   t)))

 (defthm forcing-logic.conclusion-of-rw.secondary-eqtrace-nhyp-bldr
   (implies (force (and (logic.termp nhyp)
                        (rw.eqtracep x)
                        (equal (rw.secondary-eqtrace t nhyp) x)))
            (equal (logic.conclusion (rw.secondary-eqtrace-nhyp-bldr nhyp x))
                   (logic.por (logic.term-formula nhyp)
                              (logic.pequal (logic.function 'equal
                                                            (list (rw.eqtrace->lhs x)
                                                                  (rw.eqtrace->rhs x)))
                                            ''t))))
   :rule-classes ((:rewrite :backchain-limit-lst 0)))

 (defthm@ forcing-logic.proofp-of-rw.secondary-eqtrace-nhyp-bldr
   (implies (force (and (logic.termp nhyp)
                        (rw.eqtracep x)
                        (equal (rw.secondary-eqtrace t nhyp) x)
                        ;; ---
                        (logic.term-atblp nhyp atbl)
                        (equal (cdr (lookup 'equal atbl)) 2)
                        (@obligations rw.secondary-eqtrace-nhyp-bldr)))
            (equal (logic.proofp (rw.secondary-eqtrace-nhyp-bldr nhyp x) axioms thms atbl)
                   t)))

 (verify-guards rw.secondary-eqtrace-nhyp-bldr))




(defund rw.secondary-eqtrace-bldr (x box)
  ;; Given a secondary eqtrace that is box-okp, prove
  ;;   hypbox-formula v (equal lhs rhs) = t
  ;;
  ;; This is basically identical to the primary-eqtrace bldr.
  (declare (xargs :guard (and (rw.eqtracep x)
                              (rw.hypboxp box)
                              (rw.secondary-eqtrace-okp x box))
                  :verify-guards nil))
  (let* ((left      (rw.hypbox->left box))
         (right     (rw.hypbox->right box))
         (nhyp-left (rw.find-nhyp-for-secondary-eqtracep left x)))
    (if nhyp-left
        (let* ((line-1 (rw.secondary-eqtrace-nhyp-bldr nhyp-left x))
               (line-2 (build.multi-assoc-expansion line-1 (logic.term-list-formulas left))))
          (if right
              (build.associativity (build.disjoined-left-expansion line-2 (clause.clause-formula right)))
            line-2))
      (let* ((nhyp-right (rw.find-nhyp-for-secondary-eqtracep right x))
             (line-1 (rw.secondary-eqtrace-nhyp-bldr nhyp-right x))
             (line-2 (build.multi-assoc-expansion line-1 (logic.term-list-formulas right))))
        (if left
            (build.associativity (build.expansion (clause.clause-formula left) line-2))
          line-2)))))

(defobligations rw.secondary-eqtrace-bldr
  (rw.secondary-eqtrace-nhyp-bldr
   build.multi-assoc-expansion
   build.disjoined-left-expansion))

(encapsulate
 ()
 (local (in-theory (enable rw.secondary-eqtrace-bldr
                           rw.secondary-eqtrace-okp
                           rw.hypbox-formula
                           rw.eqtrace-formula)))

 (defthm rw.secondary-eqtrace-bldr-under-iff
   (iff (rw.secondary-eqtrace-bldr x box)
        t))

 (defthm forcing-logic.appealp-of-rw.secondary-eqtrace-bldr
   (implies (force (and (rw.eqtracep x)
                        (rw.hypboxp box)
                        (rw.secondary-eqtrace-okp x box)))
            (equal (logic.appealp (rw.secondary-eqtrace-bldr x box))
                   t)))

 (defthm forcing-logic.conclusion-of-rw.secondary-eqtrace-bldr
   (implies (force (and (rw.eqtracep x)
                        (rw.hypboxp box)
                        (rw.secondary-eqtrace-okp x box)))
            (equal (logic.conclusion (rw.secondary-eqtrace-bldr x box))
                   (rw.eqtrace-formula x box)))
   :rule-classes ((:rewrite :backchain-limit-lst 0)))

 (defthm@ forcing-logic.proofp-of-rw.secondary-eqtrace-bldr
   (implies (force (and (rw.eqtracep x)
                        (rw.hypboxp box)
                        (rw.secondary-eqtrace-okp x box)
                        ;; ---
                        (equal (cdr (lookup 'equal atbl)) 2)
                        (rw.hypbox-atblp box atbl)
                        (@obligations rw.secondary-eqtrace-bldr)))
            (equal (logic.proofp (rw.secondary-eqtrace-bldr x box) axioms thms atbl)
                   t)))

 (verify-guards rw.secondary-eqtrace-bldr))


