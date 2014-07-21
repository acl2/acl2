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
(include-book "basic")
(include-book "../build/pequal")
(include-book "../build/disjoined-subset")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)




;; We introduce (clause.update-clause-bldr x proof t-proofs).
;;
;;   T1' v ... v Tn'            (clause x, proven in proof)
;;   T1 = T1'
;;   ...                        (proofs from t-proofs)
;;   Tn = Tn'
;; --------------------------------------------------------
;;   T1 v ... v Tn
;;
;; Our goal is to prove T1 v ... v Tn.  (Or, if you prefer, our goal is to
;; prove T1 != nil v ... v Tn != nil, where x is actually T1' != nil v ...  Tn'
;; != nil.
;;
;; We could have just used equal-consequence-bldr for this, giving it the goal
;; clause [t1 = nil, t2 != nil, ...], proof, and t-proofs as inputs.  But our
;; customized builder seems to produce proofs which are smaller by over 3
;; orders of magnitude better; see the tests at the end of this file.





;; The core of our routine is a tail recursive builder which is similar to the
;; build.revappend-disjunction.  Our auxilliary builder reverses the list in
;; the process, so this has to be repaired with build.rev-disjunction
;; afterwards.
;;
;; Instead of accumulating "to the back", we accumulated "to the front" because
;; this looked like it would make smaller proofs.  The specification for our
;; auxilliary builder is the following:
;;
;;      (D1 v ... v Dm) v (T1' v ... v Tn')
;;      T1.term = T1'.term
;;      ...
;;      Tn.term = TN'.term
;;   -------------------------------------------
;;      Tn v ... v T1 v D1 v ... v Dm
;;
;; Here we think of D1..m as the "done" literals which don't need to be
;; processed anymore, and T1' ... Tn' as the "todo" literals which we still
;; need to process.  At each step, our task is to process T1' by replacing it
;; with T1 and moving it to the front of the done list.

(defderiv clause.aux-update-clause-lemma1-bldr
  :derive (v (!= (? a) nil) P)
  :from   ((proof x (v P (!= (? b) nil)))
           (proof y (= (? a) (? b))))
  :proof  (@derive
           ((= (? a) (? b))                  (@given y))
           ((v P (= (? a) (? b)))            (build.expansion (@formula P) @-))
           ((v P (!= (? b) nil))             (@given x))
           ((v P (!= (? a) nil))             (build.disjoined-substitute-into-not-pequal @- @--))
           ((v (!= (? a) nil) P)             (build.commute-or @-))))

(defderiv clause.aux-update-clause-lemma2-bldr
  :derive (v (v (!= (? a) nil) P) Q)
  :from   ((proof x (v P (v (!= (? b) nil) Q)))
           (proof y (= (? a) (? b))))
  :proof  (@derive
           ((v P (v (!= (? b) nil) Q))       (@given x))
           ((v (v P (!= (? b) nil)) Q)       (build.associativity @-))
           ((v Q (v P (!= (? b) nil)))       (build.commute-or @-))
           ((v (v Q P) (!= (? b) nil))       (build.associativity @-))
           ((= (? a) (? b))                  (@given y))
           ((v (!= (? a) nil) (v Q P))       (clause.aux-update-clause-lemma1-bldr @-- @-))
           ((v (!= (? a) nil) (v P Q))       (build.disjoined-commute-or @-))
           ((v (v (!= (? a) nil) P) Q)       (build.associativity @-))))


(defund@ clause.aux-update-clause-bldr (todo done t-proofs proof)
  (declare (xargs :guard (and (logic.term-listp todo)
                              (logic.term-listp done)
                              (or (consp todo) (consp done))
                              (logic.appealp proof)
                              (logic.appeal-listp t-proofs)
                              (equal (logic.conclusion proof)
                                     (cond ((and (consp done) (consp todo))
                                            (logic.por (clause.clause-formula done)
                                                       (clause.clause-formula todo)))
                                           ((consp done)
                                            (clause.clause-formula done))
                                           (t
                                            (clause.clause-formula todo))))
                              (logic.all-atomicp (logic.strip-conclusions t-proofs))
                              (equal (logic.=rhses (logic.strip-conclusions t-proofs)) todo))
                  :verify-guards nil))
  (if (consp todo)
      (let ((new-term (logic.=lhs (logic.conclusion (car t-proofs)))))
        (if (consp (cdr todo))
            (if (consp done)
                (clause.aux-update-clause-bldr (cdr todo)
                                              (cons new-term done)
                                              (cdr t-proofs)
                                              ;; D1..m v (T1' != nil v T2..n')
                                              ;; T1 = T1'
                                              ;; ----------------------------------
                                              ;; (T1 != nil v D1..m) v T2..n'
                                              (clause.aux-update-clause-lemma2-bldr proof (car t-proofs)))
              (clause.aux-update-clause-bldr (cdr todo)
                                             (cons new-term done)
                                             (cdr t-proofs)
                                             ;; T1' != nil v T2..n'
                                             ;; T1 = T1'
                                             ;; ------------------------
                                             ;; T1 != nil v T2..n'
                                             (clause.aux-update-clause-lemma1-bldr (build.commute-or proof) (car t-proofs))))
          (if (consp done)
              ;; D1..m v T1' != nil
              ;; T1 = T1'
              ;; -----------------------
              ;; T1 != nil v D1..m
              (clause.aux-update-clause-lemma1-bldr proof (car t-proofs))
            ;; T1' != nil
            ;; T1 = T1'
            ;; ------------------
            ;; T1' != nil
            (build.substitute-into-not-pequal proof (car t-proofs)))))
    ;; Degenerate case.
    (logic.appeal-identity proof)))










(defund clause.aux-update-clause-bldr (todo done t-proofs proof)
  (declare (xargs :guard (and (logic.term-listp todo)
                              (logic.term-listp done)
                              (or (consp todo) (consp done))
                              (logic.appealp proof)
                              (logic.appeal-listp t-proofs)
                              (equal (logic.conclusion proof)
                                     (cond ((and (consp done) (consp todo))
                                            (logic.por (clause.clause-formula done)
                                                       (clause.clause-formula todo)))
                                           ((consp done)
                                            (clause.clause-formula done))
                                           (t
                                            (clause.clause-formula todo))))
                              (logic.all-atomicp (logic.strip-conclusions t-proofs))
                              (equal (logic.=rhses (logic.strip-conclusions t-proofs)) todo))
                  :verify-guards nil))
  (if (consp todo)
      (let ((new-term (logic.=lhs (logic.conclusion (car t-proofs)))))
        (if (consp (cdr todo))
            (if (consp done)
                (clause.aux-update-clause-bldr (cdr todo)
                                              (cons new-term done)
                                              (cdr t-proofs)
                                              ;; D1..m v (T1' != nil v T2..n')
                                              ;; T1 = T1'
                                              ;; ----------------------------------
                                              ;; (T1 != nil v D1..m) v T2..n'
                                              (clause.aux-update-clause-lemma2-bldr proof (car t-proofs)))
              (clause.aux-update-clause-bldr (cdr todo)
                                            (cons new-term done)
                                            (cdr t-proofs)
                                            ;; T1' != nil v T2..n'
                                            ;; T1 = T1'
                                            ;; ------------------------
                                            ;; T1 != nil v T2..n'
                                            (clause.aux-update-clause-lemma1-bldr (build.commute-or proof) (car t-proofs))))
          (if (consp done)
              ;; D1..m v T1' != nil
              ;; T1 = T1'
              ;; -----------------------
              ;; T1 != nil v D1..m
              (clause.aux-update-clause-lemma1-bldr proof (car t-proofs))
            ;; T1' != nil
            ;; T1 = T1'
            ;; ------------------
            ;; T1' != nil
            (build.substitute-into-not-pequal proof (car t-proofs)))))
    ;; Degenerate case.
    (logic.appeal-identity proof)))

(defobligations clause.aux-update-clause-bldr
  (clause.aux-update-clause-lemma1-bldr
   clause.aux-update-clause-lemma2-bldr
   build.substitute-into-not-pequal))

(encapsulate
 ()
 (local (in-theory (enable clause.aux-update-clause-bldr logic.term-formula)))

 (defthm clause.aux-update-clause-bldr-under-iff
   (iff (clause.aux-update-clause-bldr todo done t-proofs proof)
        t))

 (local (defthm lemma
          (implies (and (logic.term-listp todo)
                        (logic.term-listp done)
                        (or (consp todo) (consp done))
                        (logic.appealp proof)
                        (logic.appeal-listp t-proofs)
                        (equal (logic.conclusion proof)
                               (cond ((and (consp done) (consp todo))
                                      (logic.por (clause.clause-formula done)
                                                 (clause.clause-formula todo)))
                                     ((consp done)
                                      (clause.clause-formula done))
                                     (t
                                      (clause.clause-formula todo))))
                        (logic.all-atomicp (logic.strip-conclusions t-proofs))
                        (equal (logic.=rhses (logic.strip-conclusions t-proofs)) todo))
                   (and (logic.appealp (clause.aux-update-clause-bldr todo done t-proofs proof))
                        (equal (logic.conclusion (clause.aux-update-clause-bldr todo done t-proofs proof))
                               (clause.clause-formula (app (rev (logic.=lhses (logic.strip-conclusions t-proofs)))
                                                           done)))))
          :hints(("Goal"
                  :induct (clause.aux-update-clause-bldr todo done t-proofs proof)))))

 (defthm forcing-logic.appealp-of-clause.aux-update-clause-bldr
   (implies (force (and (logic.term-listp todo)
                        (logic.term-listp done)
                        (or (consp todo) (consp done))
                        (logic.appealp proof)
                        (logic.appeal-listp t-proofs)
                        (equal (logic.conclusion proof)
                               (cond ((and (consp done) (consp todo))
                                      (logic.por (clause.clause-formula done)
                                                 (clause.clause-formula todo)))
                                     ((consp done)
                                      (clause.clause-formula done))
                                     (t
                                      (clause.clause-formula todo))))
                        (logic.all-atomicp (logic.strip-conclusions t-proofs))
                        (equal (logic.=rhses (logic.strip-conclusions t-proofs)) todo)))
            (equal (logic.appealp (clause.aux-update-clause-bldr todo done t-proofs proof))
                   t)))

 (defthm forcing-logic.conclusion-of-clause.aux-update-clause-bldr
   (implies (force (and (logic.term-listp todo)
                        (logic.term-listp done)
                        (or (consp todo) (consp done))
                        (logic.appealp proof)
                        (logic.appeal-listp t-proofs)
                        (equal (logic.conclusion proof)
                               (cond ((and (consp done) (consp todo))
                                      (logic.por (clause.clause-formula done)
                                                 (clause.clause-formula todo)))
                                     ((consp done)
                                      (clause.clause-formula done))
                                     (t
                                      (clause.clause-formula todo))))
                        (logic.all-atomicp (logic.strip-conclusions t-proofs))
                        (equal (logic.=rhses (logic.strip-conclusions t-proofs)) todo)))
            (equal (logic.conclusion (clause.aux-update-clause-bldr todo done t-proofs proof))
                   (clause.clause-formula (app (rev (logic.=lhses (logic.strip-conclusions t-proofs)))
                                               done))))
   :rule-classes ((:rewrite :backchain-limit-lst 0)))

 (defthm@ forcing-logic.proofp-of-clause.aux-update-clause-bldr
   (implies (force (and (logic.term-listp todo)
                        (logic.term-listp done)
                        (or (consp todo) (consp done))
                        (logic.appealp proof)
                        (logic.appeal-listp t-proofs)
                        (equal (logic.conclusion proof)
                               (cond ((and (consp done) (consp todo))
                                      (logic.por (clause.clause-formula done)
                                                 (clause.clause-formula todo)))
                                     ((consp done)
                                      (clause.clause-formula done))
                                     (t
                                      (clause.clause-formula todo))))
                        (logic.all-atomicp (logic.strip-conclusions t-proofs))
                        (equal (logic.=rhses (logic.strip-conclusions t-proofs)) todo)
                        ;; ---
                        (force (logic.term-list-atblp todo atbl))
                        (force (logic.term-list-atblp done atbl))
                        (force (logic.proofp proof axioms thms atbl))
                        (force (logic.proof-listp t-proofs axioms thms atbl))
                        (@obligations clause.aux-update-clause-bldr)))
            (equal (logic.proofp (clause.aux-update-clause-bldr todo done t-proofs proof) axioms thms atbl)
                   t))
   :hints(("Goal" :induct (clause.aux-update-clause-bldr todo done t-proofs proof))))

 (verify-guards clause.aux-update-clause-bldr))




(defund clause.update-clause-bldr (x proof t-proofs)
  (declare (xargs :guard (and (logic.term-listp x)
                              (consp x)
                              (logic.appealp proof)
                              (logic.appeal-listp t-proofs)
                              (equal (logic.conclusion proof) (clause.clause-formula x))
                              (logic.all-atomicp (logic.strip-conclusions t-proofs))
                              (equal (logic.=rhses (logic.strip-conclusions t-proofs)) x))))
  (let ((lhses (logic.=lhses-of-strip-conclusions t-proofs)))
    (if (equal lhses x)
        ;; Important optimization!  If nothing has changed, just reuse the input proof.
        (logic.appeal-identity proof)
      (build.rev-disjunction
       (logic.fast-term-list-formulas$ lhses nil)
       (clause.aux-update-clause-bldr x nil t-proofs proof)))))

(defobligations clause.update-clause-bldr
  (clause.aux-update-clause-bldr
   build.rev-disjunction))


(encapsulate
 ()
 (local (in-theory (enable clause.update-clause-bldr)))

 (defthm clause.update-clause-bldr-under-iff
   (iff (clause.update-clause-bldr x proof t-proofs)
        t))

 (defthm forcing-logic.appealp-of-clause.update-clause-bldr
   (implies (force (and (logic.term-listp x)
                        (consp x)
                        (logic.appealp proof)
                        (logic.appeal-listp t-proofs)
                        (equal (logic.conclusion proof) (clause.clause-formula x))
                        (logic.all-atomicp (logic.strip-conclusions t-proofs))
                        (equal (logic.=rhses (logic.strip-conclusions t-proofs)) x)))
            (equal (logic.appealp (clause.update-clause-bldr x proof t-proofs))
                   t)))

 (defthm forcing-logic.conclusion-of-clause.update-clause-bldr
   (implies (force (and (logic.term-listp x)
                        (consp x)
                        (logic.appealp proof)
                        (logic.appeal-listp t-proofs)
                        (equal (logic.conclusion proof) (clause.clause-formula x))
                        (logic.all-atomicp (logic.strip-conclusions t-proofs))
                        (equal (logic.=rhses (logic.strip-conclusions t-proofs)) x)))
            (equal (logic.conclusion (clause.update-clause-bldr x proof t-proofs))
                   (clause.clause-formula (logic.=lhses (logic.strip-conclusions t-proofs))))))

 (defthm@ forcing-logic.proofp-of-clause.update-clause-bldr
   (implies (force (and (logic.term-listp x)
                        (consp x)
                        (logic.appealp proof)
                        (logic.appeal-listp t-proofs)
                        (equal (logic.conclusion proof) (clause.clause-formula x))
                        (logic.all-atomicp (logic.strip-conclusions t-proofs))
                        (equal (logic.=rhses (logic.strip-conclusions t-proofs)) x)
                        ;; ---
                        (logic.term-list-atblp x atbl)
                        (logic.proof-listp t-proofs axioms thms atbl)
                        (logic.proofp proof axioms thms atbl)
                        (@obligations clause.update-clause-bldr)))
            (equal (logic.proofp (clause.update-clause-bldr x proof t-proofs) axioms thms atbl)
                   t))))




;; Here's how clause.update-clause compares against the generic equal-consequence
;; builder.
;;
;;    n    equal-consequence   clause.update-clause   savings
;;   -------------------------------------------------------------
;;     1          1,165,951            312            99.97%
;;     2          4,187,075          2,419            99.94%
;;     3         17,511,319          7,127            99.96%
;;     4         66,176,366         14,215            99.98%
;;     5        209,545,630         23,683            99.99%
;;   ------------------------------------------------------------
;;
;; This table was generated by commenting out the appropriate parts of this test code:
;;
;; (include-book "clausep")
;; (include-book "../classic/equal-substitution")
;;
;; (let* ((goal-clause (list 'T1
;;                           'T2
;;                           'T3
;;                           'T4
;;                           'T5
;;                           ))
;;        (t-proofs (list
;;                   (build.axiom (logic.pequal 'T1 'T1-Prime))
;;                   (build.axiom (logic.pequal 'T2 'T2-Prime))
;;                   (build.axiom (logic.pequal 'T3 'T3-Prime))
;;                   (build.axiom (logic.pequal 'T4 'T4-Prime))
;;                   (build.axiom (logic.pequal 'T5 'T5-Prime))
;;                   ))
;;        (orig-clause   (logic.=rhses (logic.strip-conclusions t-proofs)))
;;        (input-proof   (build.axiom (clause.clause-formula orig-clause)))
;;        (classic-proof (equal-consequence-bldr (clause.clause-formula goal-clause) input-proof t-proofs))
;;        (new-proof     (clause.update-clause-bldr orig-clause input-proof t-proofs))
;;        )
;;   (list (list 'input-proof  (logic.conclusion input-proof))
;;         (list 't-proofs     (logic.strip-conclusions t-proofs))
;;         (list 'classic-rank (rank classic-proof))
;;         (list 'classic-conc (logic.conclusion classic-proof))
;;         (list 'new-rank     (rank new-proof))
;;         (list 'new-conc     (logic.conclusion new-proof))
;;         (list 'ok           (equal (logic.conclusion classic-proof)
;;                                    (logic.conclusion new-proof))))
;;         )




(defund clause.update-clause-bldr-okp (x)
  (declare (xargs :guard (logic.appealp x)))
  (let ((method     (logic.method x))
        (conclusion (logic.conclusion x))
        (subproofs  (logic.subproofs x))
        (extras     (logic.extras x)))
    (and (equal method 'clause.update-clause-bldr)
         ;; In the builder's parlance, we want to build from a term list, proof, and t-proofs.
         ;; The term list is exactly the same as the rhses of the strip-conclusions of t-proofs,
         ;; so we take it from there directly.
         (not extras)
         (consp subproofs)
         (let ((proof    (car subproofs))
               (t-proofs (cdr subproofs)))
           (and (consp t-proofs)
                (logic.all-atomicp-of-strip-conclusions t-proofs)
                (equal conclusion (clause.clause-formula (logic.=lhses-of-strip-conclusions t-proofs)))
                (equal (logic.conclusion proof)
                       (clause.clause-formula (logic.=rhses-of-strip-conclusions t-proofs))))))))

(defund clause.update-clause-bldr-high (x proof t-proofs)
  (declare (xargs :guard (and (logic.term-listp x)
                              (consp x)
                              (logic.appealp proof)
                              (logic.appeal-listp t-proofs)
                              (equal (logic.conclusion proof) (clause.clause-formula x))
                              (logic.all-atomicp (logic.strip-conclusions t-proofs))
                              (equal (logic.=rhses (logic.strip-conclusions t-proofs)) x)))
           (ignore x))
  (logic.appeal 'clause.update-clause-bldr
                (clause.clause-formula (logic.=lhses-of-strip-conclusions t-proofs))
                (cons proof (list-fix t-proofs))
                nil))

(encapsulate
 ()
 (local (in-theory (enable clause.update-clause-bldr-okp)))

 (defthm booleanp-of-clause.update-clause-bldr-okp
   (equal (booleanp (clause.update-clause-bldr-okp x))
          t)
   :hints(("goal" :in-theory (disable (:executable-counterpart ACL2::force)))))

 (defthm clause.update-clause-bldr-okp-of-logic.appeal-identity
   (equal (clause.update-clause-bldr-okp (logic.appeal-identity x))
          (clause.update-clause-bldr-okp x))
   :hints(("goal" :in-theory (disable (:executable-counterpart ACL2::force)))))

 (local (in-theory (e/d (backtracking-logic.formula-atblp-rules)
                        (forcing-logic.formula-atblp-rules
                         forcing-lookup-of-logic.function-name-free))))

 (defthmd lemma-1-for-soundness-of-clause.update-clause-bldr-okp
   (implies (and (clause.update-clause-bldr-okp x)
                 (logic.appealp x)
                 (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl))
            (equal (logic.conclusion (clause.update-clause-bldr
                                      (logic.=rhses
                                       (logic.strip-conclusions
                                        (logic.provable-list-witness (logic.strip-conclusions (cdr (logic.subproofs x)))
                                                                     axioms thms atbl)))
                                      (logic.provable-witness (logic.conclusion (car (logic.subproofs x))) axioms thms atbl)
                                      (logic.provable-list-witness (logic.strip-conclusions (cdr (logic.subproofs x)))
                                                                   axioms thms atbl)))
                   (logic.conclusion x))))

 (defthmd@ lemma-2-for-soundness-of-clause.update-clause-bldr-okp
   (implies (and (clause.update-clause-bldr-okp x)
                 (logic.appealp x)
                 (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl)
                 (@obligations clause.update-clause-bldr))
            (equal (logic.proofp (clause.update-clause-bldr
                                  (logic.=rhses
                                   (logic.strip-conclusions
                                    (logic.provable-list-witness (logic.strip-conclusions (cdr (logic.subproofs x)))
                                                                 axioms thms atbl)))
                                  (logic.provable-witness (logic.conclusion (car (logic.subproofs x))) axioms thms atbl)
                                  (logic.provable-list-witness (logic.strip-conclusions (cdr (logic.subproofs x)))
                                                               axioms thms atbl))
                                 axioms thms atbl)
                   t)))

 (defthm@ forcing-soundness-of-clause.update-clause-bldr-okp
   (implies (and (clause.update-clause-bldr-okp x)
                 (force (and (logic.appealp x)
                             (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl)
                             (@obligations clause.update-clause-bldr))))
            (equal (logic.provablep (logic.conclusion x) axioms thms atbl)
                   t))
   :hints (("Goal"
            :in-theory (enable lemma-1-for-soundness-of-clause.update-clause-bldr-okp
                               lemma-2-for-soundness-of-clause.update-clause-bldr-okp)
            :use ((:instance forcing-logic.provablep-when-logic.proofp
                             (x (clause.update-clause-bldr
                                 (logic.=rhses
                                  (logic.strip-conclusions
                                   (logic.provable-list-witness (logic.strip-conclusions (cdr (logic.subproofs x)))
                                                                axioms thms atbl)))
                                 (logic.provable-witness (logic.conclusion (car (logic.subproofs x))) axioms thms atbl)
                                 (logic.provable-list-witness (logic.strip-conclusions (cdr (logic.subproofs x)))
                                                              axioms thms atbl)))))))))


