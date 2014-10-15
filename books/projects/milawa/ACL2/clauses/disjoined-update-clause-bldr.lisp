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
(include-book "../build/disjoined-rev-disjunction")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)




;; We introduce (clause.disjoined-update-clause-bldr x proof t-proofs).  This
;; is just a disjoined version of update-clause-bldr.
;;
;; X is a non-empty clause, say [T1, ..., Tn]
;; Proof is a proof of P v T1' v ... v Tn'
;; T-Proofs are of P v T1 = T1', ..., P v Tn = Tn'
;; We prove P v T1 v ... v Tn.
;;
;; That is:
;;
;;   P v T1' v ... v Tn'
;;   P v T1 = T1'
;;   ...
;;   P v Tn = Tn'
;; --------------------------------------------------------
;;   P v T1 v ... v Tn
;;
;; We again use a tail recursive auxilliary builder which reverses the list in
;; the process.  This has to be repaired with build.rev-disjunction afterwards.
;;
;; The specification for our auxilliary builder is the following:
;;
;;      P v (D1 v ... v Dm) v (T1' v ... v Tn')
;;      P v T1.term = T1'.term
;;      ...
;;      P v Tn.term = TN'.term
;;   -------------------------------------------
;;      P v Tn v ... v T1 v D1 v ... v Dm
;;
;; We think of D1..m as the "done" literals which don't need to be processed
;; anymore, and T1' ... Tn' as the "todo" literals which we still need to
;; process.  At each step, our task is to process T1' by replacing it with T1
;; and moving it to the front of the done list.

(defderiv clause.aux-disjoined-update-clause-twiddle
  :derive (v P (v (v S Q) R))
  :from   ((proof x (v R (v (v P Q) S))))
  :proof  (@derive
           ((v R (v (v P Q) S))    (@given x))
           ((v R (v P (v Q S)))    (build.disjoined-right-associativity @-))
           ((v (v R P) (v Q S))    (build.associativity @-))
           ((v (v R P) (v S Q))    (build.disjoined-commute-or @-))
           ((v (v S Q) (v R P))    (build.commute-or @-))
           ((v (v (v S Q) R) P)    (build.associativity @-))
           ((v P (v (v S Q) R))    (build.commute-or @-))))

(defderiv clause.aux-disjoined-update-clause-lemma1-bldr
  ;; Case 1: We still have more todo literals beyond the first (R) and
  ;;         there are already some done literals (Q)
  :derive (v P (v (v (!= (? a) nil) Q) R))
  :from   ((proof x (v P (v Q (v (!= (? b) nil) R))))
           (proof y (v P (= (? a) (? b)))))
  :proof  (@derive
           ((v P (v Q (v (!= (? b) nil) R)))    (@given x))
           ((v (v P Q) (v (!= (? b) nil) R))    (build.associativity @-))
           ((v (v (v P Q) (!= (? b) nil)) R)    (build.associativity @-))
           ((v R (v (v P Q) (!= (? b) nil)))    (build.commute-or @-))
           ((v (v R (v P Q)) (!= (? b) nil))    (build.associativity @-) *1)
           ;; ---
           ((v P (= (? a) (? b)))               (@given y))
           ((v P (v Q (= (? a) (? b))))         (build.disjoined-left-expansion @- (@formula Q)))
           ((v (v P Q) (= (? a) (? b)))         (build.associativity @-))
           ((v R (v (v P Q) (= (? a) (? b))))   (build.expansion (@formula R) @-))
           ((v (v R (v P Q)) (= (? a) (? b)))   (build.associativity @-))
           ((v (v R (v P Q)) (!= (? a) nil))    (build.disjoined-substitute-into-not-pequal *1 @-))
           ((v R (v (v P Q) (!= (? a) nil)))    (build.right-associativity @-))
           ((v P (v (v (!= (? a) nil) Q) R))    (clause.aux-disjoined-update-clause-twiddle @-))))

(defderiv clause.aux-disjoined-update-clause-lemma2-bldr
  ;; Case 2: We still have more todo literals beyond the first (R) but
  ;;         there are not yet any done literals.
  :derive (v P (v (!= (? a) nil) R))
  :from   ((proof x (v P (v (!= (? b) nil) R)))
           (proof y (v P (= (? a) (? b)))))
  :proof  (@derive
           ((v P (v (!= (? b) nil) R))    (@given x))
           ((v (v P (!= (? b) nil)) R)    (build.associativity @-))
           ((v R (v P (!= (? b) nil)))    (build.commute-or @-))
           ((v (v R P) (!= (? b) nil))    (build.associativity @-)   *1)
           ;; ---
           ((v P (= (? a) (? b)))         (@given y))
           ((v R (v P (= (? a) (? b))))   (build.expansion (@formula R) @-))
           ((v (v R P) (= (? a) (? b)))   (build.associativity @-))
           ((v (v R P) (!= (? a) nil))    (build.disjoined-substitute-into-not-pequal *1 @-))
           ((v (!= (? a) nil) (v R P))    (build.commute-or @-))
           ((v (v (!= (? a) nil) R) P)    (build.associativity @-))
           ((v P (v (!= (? a) nil) R))    (build.commute-or @-))))

(defderiv clause.aux-disjoined-update-clause-lemma3-bldr
  ;; Case 3: We have no todo literals beyond the first, but we have some
  ;;         done literals (Q).
  :derive (v P (v (!= (? a) nil) Q))
  :from   ((proof x (v P (v Q (!= (? b) nil))))
           (proof y (v P (= (? a) (? b)))))
  :proof  (@derive
           ((v P (v Q (!= (? b) nil)))   (@given x))
           ((v P (v (!= (? b) nil) Q))   (build.disjoined-commute-or @-))
           ((v P (= (? a) (? b)))        (@given y))
           ((v P (v (!= (? a) nil) Q))   (clause.aux-disjoined-update-clause-lemma2-bldr @-- @-))))



(defund@ clause.aux-disjoined-update-clause-bldr (p todo done t-proofs proof)
  (declare (xargs :guard (and (logic.formulap p)
                              (logic.term-listp todo)
                              (logic.term-listp done)
                              (or (consp todo) (consp done))
                              (logic.appealp proof)
                              (logic.appeal-listp t-proofs)
                              (equal (logic.conclusion proof)
                                     (cond ((and (consp done) (consp todo))
                                            (logic.por p (logic.por (clause.clause-formula done)
                                                                    (clause.clause-formula todo))))
                                           ((consp done)
                                            (logic.por p (clause.clause-formula done)))
                                           (t
                                            (logic.por p (clause.clause-formula todo)))))
                              (logic.all-disjunctionsp (logic.strip-conclusions t-proofs))
                              (all-equalp p (logic.vlhses (logic.strip-conclusions t-proofs)))
                              (logic.all-atomicp (logic.vrhses (logic.strip-conclusions t-proofs)))
                              (equal (logic.=rhses (logic.vrhses (logic.strip-conclusions t-proofs))) todo))
                  :verify-guards nil))
  (if (consp todo)
      (let ((new-term (logic.=lhs (logic.vrhs (logic.conclusion (car t-proofs))))))
        (if (consp (cdr todo))
            (if (consp done)
                ;; Case 1: We still have more todo literals beyond the first (R) and
                ;;         there are already some done literals (Q)
                (clause.aux-disjoined-update-clause-bldr p
                                                         (cdr todo)
                                                         (cons new-term done)
                                                         (cdr t-proofs)
                                                         ;; P v (D1..m v (T1' != nil v T2..n'))
                                                         ;; P v T1 = T1'
                                                         ;; ----------------------------------
                                                         ;; P v ((T1 != nil v D1..m) v T2..n')
                                                         (clause.aux-disjoined-update-clause-lemma1-bldr proof (car t-proofs)))
              ;; Case 2: We still have more todo literals beyond the first (R) but
              ;;         there are not yet any done literals.
              (clause.aux-disjoined-update-clause-bldr p
                                                       (cdr todo)
                                                       (cons new-term done)
                                                       (cdr t-proofs)
                                                       ;; P v (T1' != nil v T2..n')
                                                       ;; P v T1 = T1'
                                                       ;; ------------------------
                                                       ;; P v (T1 != nil v T2..n')
                                                       (clause.aux-disjoined-update-clause-lemma2-bldr proof (car t-proofs))))
          (if (consp done)
              ;; Case 3: We have no todo literals beyond the first, but we have some
              ;;         done literals (Q).
              ;; P v (D1..m v T1' != nil)
              ;; P v T1 = T1'
              ;; -----------------------
              ;; P v (T1 != nil v D1..m)
              (clause.aux-disjoined-update-clause-lemma3-bldr proof (car t-proofs))
            ;; Case 4: We have no todo literals beyond the first, and no done literals.
            ;; P v T1' != nil
            ;; P v T1 = T1'
            ;; ------------------
            ;; P v T1' != nil
            (build.disjoined-substitute-into-not-pequal proof (car t-proofs)))))
    ;; Degenerate case.
    (logic.appeal-identity proof)))

(defobligations clause.aux-disjoined-update-clause-bldr
  (clause.aux-disjoined-update-clause-lemma1-bldr
   clause.aux-disjoined-update-clause-lemma2-bldr
   clause.aux-disjoined-update-clause-lemma3-bldr
   build.disjoined-substitute-into-not-pequal))

(encapsulate
 ()
 (local (in-theory (enable clause.aux-disjoined-update-clause-bldr
                           logic.term-formula)))

 (defthm clause.aux-disjoined-update-clause-bldr-under-iff
   (iff (clause.aux-disjoined-update-clause-bldr p todo done t-proofs proof)
        t))

 (local (defthm lemma
          (implies (and (logic.formulap p)
                        (logic.term-listp todo)
                        (logic.term-listp done)
                        (or (consp todo) (consp done))
                        (logic.appealp proof)
                        (logic.appeal-listp t-proofs)
                        (equal (logic.conclusion proof)
                               (cond ((and (consp done) (consp todo))
                                      (logic.por p (logic.por (clause.clause-formula done)
                                                              (clause.clause-formula todo))))
                                     ((consp done)
                                      (logic.por p (clause.clause-formula done)))
                                     (t
                                      (logic.por p (clause.clause-formula todo)))))
                        (logic.all-disjunctionsp (logic.strip-conclusions t-proofs))
                        (all-equalp p (logic.vlhses (logic.strip-conclusions t-proofs)))
                        (logic.all-atomicp (logic.vrhses (logic.strip-conclusions t-proofs)))
                        (equal (logic.=rhses (logic.vrhses (logic.strip-conclusions t-proofs))) todo))
                   (and (logic.appealp (clause.aux-disjoined-update-clause-bldr p todo done t-proofs proof))
                        (equal (logic.conclusion (clause.aux-disjoined-update-clause-bldr p todo done t-proofs proof))
                               (logic.por p (clause.clause-formula (app (rev (logic.=lhses (logic.vrhses (logic.strip-conclusions t-proofs)))) done))))))
          :hints(("Goal"
                  :induct (clause.aux-disjoined-update-clause-bldr p todo done t-proofs proof)))))

 (defthm forcing-logic.appealp-of-clause.aux-disjoined-update-clause-bldr
   (implies (force (and (logic.formulap p)
                        (logic.term-listp todo)
                        (logic.term-listp done)
                        (or (consp todo) (consp done))
                        (logic.appealp proof)
                        (logic.appeal-listp t-proofs)
                        (equal (logic.conclusion proof)
                               (cond ((and (consp done) (consp todo))
                                      (logic.por p (logic.por (clause.clause-formula done)
                                                              (clause.clause-formula todo))))
                                     ((consp done)
                                      (logic.por p (clause.clause-formula done)))
                                     (t
                                      (logic.por p (clause.clause-formula todo)))))
                        (logic.all-disjunctionsp (logic.strip-conclusions t-proofs))
                        (all-equalp p (logic.vlhses (logic.strip-conclusions t-proofs)))
                        (logic.all-atomicp (logic.vrhses (logic.strip-conclusions t-proofs)))
                        (equal (logic.=rhses (logic.vrhses (logic.strip-conclusions t-proofs))) todo)))
            (equal (logic.appealp (clause.aux-disjoined-update-clause-bldr p todo done t-proofs proof))
                   t)))

 (defthm forcing-logic.conclusion-of-clause.aux-disjoined-update-clause-bldr
   (implies (force (and (logic.formulap p)
                        (logic.term-listp todo)
                        (logic.term-listp done)
                        (or (consp todo) (consp done))
                        (logic.appealp proof)
                        (logic.appeal-listp t-proofs)
                        (equal (logic.conclusion proof)
                               (cond ((and (consp done) (consp todo))
                                      (logic.por p (logic.por (clause.clause-formula done)
                                                              (clause.clause-formula todo))))
                                     ((consp done)
                                      (logic.por p (clause.clause-formula done)))
                                     (t
                                      (logic.por p (clause.clause-formula todo)))))
                        (logic.all-disjunctionsp (logic.strip-conclusions t-proofs))
                        (all-equalp p (logic.vlhses (logic.strip-conclusions t-proofs)))
                        (logic.all-atomicp (logic.vrhses (logic.strip-conclusions t-proofs)))
                        (equal (logic.=rhses (logic.vrhses (logic.strip-conclusions t-proofs))) todo)))
            (equal (logic.conclusion (clause.aux-disjoined-update-clause-bldr p todo done t-proofs proof))
                   (logic.por p (clause.clause-formula (app (rev (logic.=lhses (logic.vrhses (logic.strip-conclusions t-proofs)))) done)))))
   :rule-classes ((:rewrite :backchain-limit-lst 0)))

 (defthm@ forcing-logic.proofp-of-clause.aux-disjoined-update-clause-bldr
   (implies (force (and (logic.formulap p)
                        (logic.term-listp todo)
                        (logic.term-listp done)
                        (or (consp todo) (consp done))
                        (logic.appealp proof)
                        (logic.appeal-listp t-proofs)
                        (equal (logic.conclusion proof)
                               (cond ((and (consp done) (consp todo))
                                      (logic.por p (logic.por (clause.clause-formula done)
                                                              (clause.clause-formula todo))))
                                     ((consp done)
                                      (logic.por p (clause.clause-formula done)))
                                     (t
                                      (logic.por p (clause.clause-formula todo)))))
                        (logic.all-disjunctionsp (logic.strip-conclusions t-proofs))
                        (all-equalp p (logic.vlhses (logic.strip-conclusions t-proofs)))
                        (logic.all-atomicp (logic.vrhses (logic.strip-conclusions t-proofs)))
                        (equal (logic.=rhses (logic.vrhses (logic.strip-conclusions t-proofs))) todo)
                        ;; ---
                        (logic.proofp proof axioms thms atbl)
                        (logic.proof-listp t-proofs axioms thms atbl)
                        (@obligations clause.aux-disjoined-update-clause-bldr)
                        ))
            (equal (logic.proofp (clause.aux-disjoined-update-clause-bldr p todo done t-proofs proof) axioms thms atbl)
                   t))
   :hints(("Goal" :induct (clause.aux-disjoined-update-clause-bldr p todo done t-proofs proof))))

 (verify-guards clause.aux-disjoined-update-clause-bldr))




(defund clause.disjoined-update-clause-bldr (x proof t-proofs)
  (declare (xargs :guard (and (logic.term-listp x)
                              (consp x)
                              (logic.appealp proof)
                              (logic.appeal-listp t-proofs)
                              (equal (logic.fmtype (logic.conclusion proof)) 'por*)
                              (equal (logic.vrhs (logic.conclusion proof)) (clause.clause-formula x))
                              (logic.all-disjunctionsp (logic.strip-conclusions t-proofs))
                              (all-equalp (logic.vlhs (logic.conclusion proof)) (logic.vlhses (logic.strip-conclusions t-proofs)))
                              (logic.all-atomicp (logic.vrhses (logic.strip-conclusions t-proofs)))
                              (equal (logic.=rhses (logic.vrhses (logic.strip-conclusions t-proofs))) x))))
  (build.disjoined-rev-disjunction
   ;; this is probably pretty expensive.  having a compiler that folded these would be a huge win.
   (logic.term-list-formulas (fast-rev (logic.=lhses (logic.vrhses (logic.strip-conclusions t-proofs)))))
   (clause.aux-disjoined-update-clause-bldr (logic.vlhs (logic.conclusion proof)) x nil t-proofs proof)))

(defobligations clause.disjoined-update-clause-bldr
  (clause.aux-disjoined-update-clause-bldr
   build.disjoined-rev-disjunction))

(encapsulate
 ()
 (local (in-theory (enable clause.disjoined-update-clause-bldr)))

 (defthm clause.disjoined-update-clause-bldr-under-iff
   (iff (clause.disjoined-update-clause-bldr x proof t-proofs)
        t))

 (defthm forcing-logic.appealp-of-clause.disjoined-update-clause-bldr
   (implies (force (and (logic.term-listp x)
                        (consp x)
                        (logic.appealp proof)
                        (logic.appeal-listp t-proofs)
                        (equal (logic.fmtype (logic.conclusion proof)) 'por*)
                        (equal (logic.vrhs (logic.conclusion proof)) (clause.clause-formula x))
                        (logic.all-disjunctionsp (logic.strip-conclusions t-proofs))
                        (all-equalp (logic.vlhs (logic.conclusion proof)) (logic.vlhses (logic.strip-conclusions t-proofs)))
                        (logic.all-atomicp (logic.vrhses (logic.strip-conclusions t-proofs)))
                        (equal (logic.=rhses (logic.vrhses (logic.strip-conclusions t-proofs))) x)))
            (equal (logic.appealp (clause.disjoined-update-clause-bldr x proof t-proofs))
                   t)))

 (defthm forcing-logic.conclusion-of-clause.disjoined-update-clause-bldr
   (implies (force (and (logic.term-listp x)
                        (consp x)
                        (logic.appealp proof)
                        (logic.appeal-listp t-proofs)
                        (equal (logic.fmtype (logic.conclusion proof)) 'por*)
                        (equal (logic.vrhs (logic.conclusion proof)) (clause.clause-formula x))
                        (logic.all-disjunctionsp (logic.strip-conclusions t-proofs))
                        (all-equalp (logic.vlhs (logic.conclusion proof)) (logic.vlhses (logic.strip-conclusions t-proofs)))
                        (logic.all-atomicp (logic.vrhses (logic.strip-conclusions t-proofs)))
                        (equal (logic.=rhses (logic.vrhses (logic.strip-conclusions t-proofs))) x)))
            (equal (logic.conclusion (clause.disjoined-update-clause-bldr x proof t-proofs))
                   (logic.por (logic.vlhs (logic.conclusion proof))
                              (clause.clause-formula (logic.=lhses (logic.vrhses (logic.strip-conclusions t-proofs))))))))

 (defthm@ forcing-logic.proofp-of-clause.disjoined-update-clause-bldr
   (implies (force (and (logic.term-listp x)
                        (consp x)
                        (logic.appealp proof)
                        (logic.appeal-listp t-proofs)
                        (equal (logic.fmtype (logic.conclusion proof)) 'por*)
                        (equal (logic.vrhs (logic.conclusion proof)) (clause.clause-formula x))
                        (logic.all-disjunctionsp (logic.strip-conclusions t-proofs))
                        (all-equalp (logic.vlhs (logic.conclusion proof)) (logic.vlhses (logic.strip-conclusions t-proofs)))
                        (logic.all-atomicp (logic.vrhses (logic.strip-conclusions t-proofs)))
                        (equal (logic.=rhses (logic.vrhses (logic.strip-conclusions t-proofs))) x)
                        ;; ---
                        (logic.term-list-atblp x atbl)
                        (logic.proof-listp t-proofs axioms thms atbl)
                        (logic.proofp proof axioms thms atbl)
                        (@obligations clause.disjoined-update-clause-bldr)))
            (equal (logic.proofp (clause.disjoined-update-clause-bldr x proof t-proofs) axioms thms atbl)
                   t))))



(defund clause.disjoined-update-clause-bldr-okp (x)
  (declare (xargs :guard (logic.appealp x)))
  (let ((method     (logic.method x))
        (conclusion (logic.conclusion x))
        (subproofs  (logic.subproofs x))
        (extras     (logic.extras x)))
    (and (equal method 'clause.disjoined-update-clause-bldr)
         ;; In the builder's parlance, we want to build from a term list, proof, and t-proofs.
         ;; The term list is exactly the same as the rhses of the strip-conclusions of t-proofs,
         ;; so we take it from there directly.
         (not extras)
         (consp subproofs)
         (let ((proof    (car subproofs))
               (t-proofs (cdr subproofs)))
           (and (consp t-proofs)
                (equal (logic.fmtype (logic.conclusion proof)) 'por*)
                (logic.all-disjunctionsp-of-strip-conclusions t-proofs)
                (let ((p (logic.vlhs (logic.conclusion proof))))
                  (and
                   (equal (logic.fmtype (logic.conclusion proof)) 'por*)
                   (all-equalp p (logic.vlhses-of-strip-conclusions t-proofs))
                   (logic.all-atomicp-of-vrhses-of-strip-conclusions t-proofs)
                   (let ((x (logic.=rhses-of-vrhses-of-strip-conclusions t-proofs)))
                     (and (equal (logic.vrhs (logic.conclusion proof))
                                 (clause.clause-formula x))
                          (equal conclusion
                                 (logic.por
                                  p
                                  (clause.clause-formula
                                   (logic.=lhses-of-vrhses-of-strip-conclusions t-proofs)))))))))))))

(defund clause.disjoined-update-clause-bldr-high (x proof t-proofs)
  (declare (xargs :guard (and (logic.term-listp x)
                              (consp x)
                              (logic.appealp proof)
                              (logic.appeal-listp t-proofs)
                              (equal (logic.fmtype (logic.conclusion proof))
                                     'por*)
                              (equal (logic.vrhs (logic.conclusion proof))
                                     (clause.clause-formula x))
                              (logic.all-disjunctionsp
                               (logic.strip-conclusions t-proofs))
                              (all-equalp
                               (logic.vlhs (logic.conclusion proof))
                               (logic.vlhses (logic.strip-conclusions t-proofs)))
                              (logic.all-atomicp
                               (logic.vrhses (logic.strip-conclusions t-proofs)))
                              (equal
                               (logic.=rhses
                                (logic.vrhses (logic.strip-conclusions t-proofs)))
                               x)))
           (ignore x))
  (logic.appeal 'clause.disjoined-update-clause-bldr
                (logic.por (logic.vlhs (logic.conclusion proof))
                           (clause.clause-formula (logic.=lhses-of-vrhses-of-strip-conclusions t-proofs)))
                (cons proof (list-fix t-proofs))
                nil))

(encapsulate
 ()
 (local (in-theory (enable clause.disjoined-update-clause-bldr-okp)))

 (defthm booleanp-of-clause.disjoined-update-clause-bldr-okp
   (equal (booleanp (clause.disjoined-update-clause-bldr-okp x))
          t)
   :hints(("goal" :in-theory (disable (:executable-counterpart ACL2::force)))))

 (defthm clause.disjoined-update-clause-bldr-okp-of-logic.appeal-identity
   (equal (clause.disjoined-update-clause-bldr-okp (logic.appeal-identity x))
          (clause.disjoined-update-clause-bldr-okp x))
   :hints(("goal" :in-theory (disable (:executable-counterpart ACL2::force)))))

 (local (in-theory (e/d (backtracking-logic.formula-atblp-rules)
                        (forcing-logic.formula-atblp-rules
                         forcing-lookup-of-logic.function-name-free))))

 (defthmd lemma-1-for-soundness-of-clause.disjoined-update-clause-bldr-okp
   (implies (and (clause.disjoined-update-clause-bldr-okp x)
                 (logic.appealp x)
                 (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl))
            (equal (logic.conclusion (clause.disjoined-update-clause-bldr

                                      (logic.=rhses
                                       (logic.vrhses
                                        (logic.strip-conclusions
                                         (logic.provable-list-witness (logic.strip-conclusions (cdr (logic.subproofs x)))
                                                                      axioms thms atbl))))

                                      (logic.provable-witness
                                       (logic.conclusion (car (logic.subproofs x))) axioms thms atbl)
                                      (logic.provable-list-witness
                                       (logic.strip-conclusions (cdr (logic.subproofs x)))
                                       axioms thms atbl)))
                   (logic.conclusion x))))

 (defthmd@ lemma-2-for-soundness-of-clause.disjoined-update-clause-bldr-okp
   (implies (and (clause.disjoined-update-clause-bldr-okp x)
                 (logic.appealp x)
                 (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl)
                 (@obligations clause.disjoined-update-clause-bldr))
            (equal (logic.proofp (clause.disjoined-update-clause-bldr
                                  (logic.=rhses
                                   (logic.vrhses
                                    (logic.strip-conclusions
                                     (logic.provable-list-witness (logic.strip-conclusions (cdr (logic.subproofs x)))
                                                                  axioms thms atbl))))
                                  (logic.provable-witness
                                   (logic.conclusion (car (logic.subproofs x)))
                                   axioms thms atbl)
                                  (logic.provable-list-witness
                                   (logic.strip-conclusions (cdr (logic.subproofs x)))
                                   axioms thms atbl))
                                 axioms thms atbl)
                   t)))

 (defthm@ forcing-soundness-of-clause.disjoined-update-clause-bldr-okp
   (implies (and (clause.disjoined-update-clause-bldr-okp x)
                 (force (and (logic.appealp x)
                             (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl)
                             (@obligations clause.disjoined-update-clause-bldr))))
            (equal (logic.provablep (logic.conclusion x) axioms thms atbl)
                   t))
   :hints (("Goal"
            :in-theory (enable lemma-1-for-soundness-of-clause.disjoined-update-clause-bldr-okp
                               lemma-2-for-soundness-of-clause.disjoined-update-clause-bldr-okp)
            :use ((:instance forcing-logic.provablep-when-logic.proofp
                             (x (clause.disjoined-update-clause-bldr
                                 (logic.=rhses
                                  (logic.vrhses
                                   (logic.strip-conclusions
                                    (logic.provable-list-witness (logic.strip-conclusions (cdr (logic.subproofs x)))
                                                                 axioms thms atbl))))
                                 (logic.provable-witness (logic.conclusion (car (logic.subproofs x))) axioms thms atbl)
                                 (logic.provable-list-witness (logic.strip-conclusions (cdr (logic.subproofs x)))
                                                              axioms thms atbl)))))))))

