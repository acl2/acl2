;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;           __    __        __    __                                        ;;
;;          /  \  /  \      (__)  |  |    ____   ___      __    ____         ;;
;;         /    \/    \      __   |  |   / _  |  \  \ __ /  /  / _  |        ;;
;;        /  /\    /\  \    |  |  |  |  / / | |   \  '  '  /  / / | |        ;;
;;       /  /  \__/  \  \   |  |  |  |  \ \_| |    \  /\  /   \ \_| |        ;;
;;      /__/          \__\  |__|  |__|   \____|     \/  \/     \____|        ;;
;; ~ ~~ \  ~ ~  ~_~~ ~/~ /~ | ~|~ | ~| ~ /~_ ~|~ ~  ~\  ~\~ ~  ~ ~  |~~    ~ ;;
;;  ~ ~  \~ \~ / ~\~ / ~/ ~ |~ | ~|  ~ ~/~/ | |~ ~~/ ~\/ ~~ ~ / / | |~   ~   ;;
;; ~ ~  ~ \ ~\/ ~  \~ ~/ ~~ ~__|  |~ ~  ~ \_~  ~  ~  .__~ ~\ ~\ ~_| ~  ~ ~~  ;;
;;  ~~ ~  ~\  ~ /~ ~  ~ ~  ~ __~  |  ~ ~ \~__~| ~/__~   ~\__~ ~~___~| ~ ~    ;;
;; ~  ~~ ~  \~_/  ~_~/ ~ ~ ~(__~ ~|~_| ~  ~  ~~  ~  ~ ~~    ~  ~   ~~  ~  ~  ;;
;;                                                                           ;;
;;            A   R e f l e c t i v e   P r o o f   C h e c k e r            ;;
;;                                                                           ;;
;;       Copyright (C) 2005-2009 by Jared Davis <jared@cs.utexas.edu>        ;;
;;                                                                           ;;
;; This program is free software; you can redistribute it and/or modify it   ;;
;; under the terms of the GNU General Public License as published by the     ;;
;; Free Software Foundation; either version 2 of the License, or (at your    ;;
;; option) any later version.                                                ;;
;;                                                                           ;;
;; This program is distributed in the hope that it will be useful, but       ;;
;; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABIL-  ;;
;; ITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public      ;;
;; License for more details.                                                 ;;
;;                                                                           ;;
;; You should have received a copy of the GNU General Public License along   ;;
;; with this program (see the file COPYING); if not, write to the Free       ;;
;; Software Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA    ;;
;; 02110-1301, USA.                                                          ;;
;;                                                                           ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "MILAWA")
(include-book "basic-bldrs")
(include-book "../build/iff")
(include-book "../build/disjoined-subset")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)



;; We now introduce clause.update-clause-iff-bldr, which is almost the same as
;; clause.update-clause-bldr.  Here, instead of taking proofs that ti = ti', we
;; take proofs that (iff ti ti') = t.  This allows us to rewrite each literal
;; under iff, and then use those results to create a new clause.  This is also
;; relatively cheap.

;; (defderiv clause.aux-update-clause-iff-lemma-0-bldr
;;   :derive (!= (? a) nil)
;;   :from   ((proof x (!= (? b) nil))
;;            (proof y (= (iff (? a) (? b)) t)))
;;   :proof  (@derive
;;            ((!= (? b) nil)              (@given x))
;;            ((= (iff (? b) t) t)         (build.iff-t-from-not-pequal-nil @-))
;;            ((= (iff (? a) (? b)) t)     (@given y))
;;            ((= (iff (? a) t) t)         (build.transitivity-of-iff @- @--))
;;            ((!= (iff (? a) t) nil)      (build.not-nil-from-t @-))
;;            ((!= (? a) nil)              (build.not-pequal-nil-from-iff-t @-))))

(defderiv clause.aux-update-clause-iff-lemma1-bldr
  :derive (v (!= (? a) nil) P)
  :from   ((proof x (v P (!= (? b) nil)))
           (proof y (= (iff (? a) (? b)) t)))
  :proof  (@derive
           ((= (iff (? a) (? b)) t)          (@given y))
           ((v P (= (iff (? a) (? b)) t))    (build.expansion (@formula P) @-))
           ((v P (!= (? b) nil))             (@given x))
           ((v P (!= (? a) nil))             (clause.disjoined-substitute-iff-into-literal-bldr @- @--))
           ((v (!= (? a) nil) P)             (build.commute-or @-))))

;;   :proof  (@derive
;;            ((= (iff (? a) (? b)) t)          (@given y))
;;            ((v P (= (iff (? a) (? b)) t))    (build.expansion (@formula P) @-)   *1)
;;            ((v P (!= (? b) nil))             (@given x))
;;            ((v P (= (iff (? b) t) t))        (build.disjoined-iff-t-from-not-pequal-nil @-))
;;            ((v P (= (iff (? a) t) t))        (build.disjoined-transitivity-of-iff *1 @-))
;;            ((v P (!= (iff (? a) t) nil))     (build.disjoined-not-nil-from-t @-))
;;            ((v P (!= (? a) nil))             (build.disjoined-not-pequal-nil-from-iff-t @-))
;;            ((v (!= (? a) nil) P)             (build.commute-or @-))))

(defderiv clause.aux-update-clause-iff-lemma2-bldr
  :derive (v (v (!= (? a) nil) P) Q)
  :from   ((proof x (v P (v (!= (? b) nil) Q)))
           (proof y (= (iff (? a) (? b)) t)))
  :proof  (@derive
           ((v P (v (!= (? b) nil) Q))       (@given x))
           ((v (v P (!= (? b) nil)) Q)       (build.associativity @-))
           ((v Q (v P (!= (? b) nil)))       (build.commute-or @-))
           ((v (v Q P) (!= (? b) nil))       (build.associativity @-)       *1)
           ((= (? a) (? b))                  (@given y))
           ((v (!= (? a) nil) (v Q P))       (clause.aux-update-clause-iff-lemma1-bldr @-- @-))
           ((v (!= (? a) nil) (v P Q))       (build.disjoined-commute-or @-))
           ((v (v (!= (? a) nil) P) Q)       (build.associativity @-))))


(defund clause.aux-update-clause-iff-bldr (todo done t-proofs proof)
  (declare (xargs :guard (and (logic.term-listp todo)
                              (logic.term-listp done)
                              (or (consp todo) (consp done))
                              ;; (D1 v ... v Dm) v (L1' v ... v Ln')
                              (logic.appealp proof)
                              (equal (logic.conclusion proof)
                                     (cond ((and (consp done)
                                                 (consp todo))
                                            (logic.por (clause.clause-formula done)
                                                       (clause.clause-formula todo)))
                                           ((consp done)
                                            (clause.clause-formula done))
                                           (t
                                            (clause.clause-formula todo))))
                              ;; (iff L1 L1') = t, ..., (iff Ln Ln') = t
                              (logic.appeal-listp t-proofs)
                              (logic.all-atomicp (logic.strip-conclusions t-proofs))
                              (all-equalp ''t (logic.=rhses (logic.strip-conclusions t-proofs)))
                              (logic.all-functionsp (logic.=lhses (logic.strip-conclusions t-proofs)))
                              (all-equalp 'iff (logic.strip-function-names (logic.=lhses (logic.strip-conclusions t-proofs))))
                              (all-equalp 2 (strip-lens (logic.strip-function-args (logic.=lhses (logic.strip-conclusions t-proofs)))))
                              (equal (strip-seconds (logic.strip-function-args (logic.=lhses (logic.strip-conclusions t-proofs))))
                                     todo))
                  :verify-guards nil))
  (if (consp todo)
      (let ((new-term (first (logic.function-args (logic.=lhs (logic.conclusion (car t-proofs)))))))
        (if (consp (cdr todo))
            (if (consp done)
                (clause.aux-update-clause-iff-bldr (cdr todo)
                                                  (cons new-term done)
                                                  (cdr t-proofs)
                                                  ;; D1..m v (L1' != nil v L2..n')
                                                  ;; (iff L1 L1') = t
                                                  ;; ----------------------------------
                                                  ;; (L1 != nil v D1..m) v L2..n
                                                  (clause.aux-update-clause-iff-lemma2-bldr proof (car t-proofs)))
              (clause.aux-update-clause-iff-bldr (cdr todo)
                                                (cons new-term done)
                                                (cdr t-proofs)
                                                ;; L1' != nil v L2..n'
                                                ;; (iff L1 L1') = t
                                                ;; --------------------------
                                                ;; L1 != nil v L2..n'
                                                (clause.aux-update-clause-iff-lemma1-bldr (build.commute-or proof) (car t-proofs))))
          (if (consp done)
              (clause.aux-update-clause-iff-bldr (cdr todo)
                                                (cons new-term done)
                                                (cdr t-proofs)
                                                ;; D1..m v L1' != nil
                                                ;; (iff L1 L1') = t
                                                ;; --------------------------
                                                ;; L1 != nil v D1..m
                                                (clause.aux-update-clause-iff-lemma1-bldr proof (car t-proofs)))
            ;; L1' != nil
            ;; (iff L1 L1') = t
            ;; --------------------------
            ;; L1 != nil
            (clause.substitute-iff-into-literal-bldr proof (car t-proofs)))))
    ;; Degenerate case.
    (logic.appeal-identity proof)))

(defobligations clause.aux-update-clause-iff-bldr
  (clause.aux-update-clause-iff-lemma2-bldr
   clause.aux-update-clause-iff-lemma1-bldr
   ;; BOZO this isn't needed
   clause.aux-update-clause-iff-lemma0-bldr))


(encapsulate
 ()
 (local (in-theory (enable clause.aux-update-clause-iff-bldr logic.term-formula)))

 (defthm clause.aux-update-clause-iff-bldr-under-iff
   (iff (clause.aux-update-clause-iff-bldr todo done t-proofs proof)
        t))

 (local (defthm crock
          ;; Ugh what an ugly pit
          (implies (and (all-equalp 2 (strip-lens (logic.strip-function-args (logic.=lhses (logic.strip-conclusions x)))))
                        (force (and (logic.appeal-listp x)
                                    (logic.all-atomicp (logic.strip-conclusions x))
                                    (logic.all-functionsp (logic.=lhses (logic.strip-conclusions x))))))
                   (equal (consp (cdr (logic.function-args (logic.=lhs (logic.conclusion (car x))))))
                          (consp x)))))

 (local (defthm lemma
          (implies (and (logic.term-listp todo)
                        (logic.term-listp done)
                        (or (consp todo) (consp done))
                        (logic.appealp proof)
                        (equal (logic.conclusion proof)
                               (cond ((and (consp done) (consp todo))
                                      (logic.por (clause.clause-formula done) (clause.clause-formula todo)))
                                     ((consp done)
                                      (clause.clause-formula done))
                                     (t
                                      (clause.clause-formula todo))))
                        (logic.appeal-listp t-proofs)
                        (logic.all-atomicp (logic.strip-conclusions t-proofs))
                        (all-equalp ''t (logic.=rhses (logic.strip-conclusions t-proofs)))
                        (logic.all-functionsp (logic.=lhses (logic.strip-conclusions t-proofs)))
                        (all-equalp 'iff (logic.strip-function-names (logic.=lhses (logic.strip-conclusions t-proofs))))
                        (all-equalp 2 (strip-lens (logic.strip-function-args (logic.=lhses (logic.strip-conclusions t-proofs)))))
                        (equal (strip-seconds (logic.strip-function-args (logic.=lhses (logic.strip-conclusions t-proofs)))) todo))
                   (and (logic.appealp (clause.aux-update-clause-iff-bldr todo done t-proofs proof))
                        (equal (logic.conclusion (clause.aux-update-clause-iff-bldr todo done t-proofs proof))
                               (clause.clause-formula
                                (app (rev (strip-firsts (logic.strip-function-args (logic.=lhses (logic.strip-conclusions t-proofs)))))
                                     done)))))
          :hints(("Goal" :induct (clause.aux-update-clause-iff-bldr todo done t-proofs proof)))))

 (defthm forcing-logic.appealp-of-clause.aux-update-clause-iff-bldr
   (implies (force (and (logic.term-listp todo)
                        (logic.term-listp done)
                        (or (consp todo) (consp done))
                        (logic.appealp proof)
                        (equal (logic.conclusion proof)
                               (cond ((and (consp done) (consp todo))
                                      (logic.por (clause.clause-formula done) (clause.clause-formula todo)))
                                     ((consp done)
                                      (clause.clause-formula done))
                                     (t
                                      (clause.clause-formula todo))))
                        (logic.appeal-listp t-proofs)
                        (logic.all-atomicp (logic.strip-conclusions t-proofs))
                        (all-equalp ''t (logic.=rhses (logic.strip-conclusions t-proofs)))
                        (logic.all-functionsp (logic.=lhses (logic.strip-conclusions t-proofs)))
                        (all-equalp 'iff (logic.strip-function-names (logic.=lhses (logic.strip-conclusions t-proofs))))
                        (all-equalp 2 (strip-lens (logic.strip-function-args (logic.=lhses (logic.strip-conclusions t-proofs)))))
                        (equal (strip-seconds (logic.strip-function-args (logic.=lhses (logic.strip-conclusions t-proofs)))) todo)))
            (equal (logic.appealp (clause.aux-update-clause-iff-bldr todo done t-proofs proof))
                   t)))

 (defthm forcing-logic.conclusion-of-clause.aux-update-clause-iff-bldr
   (implies (force (and (logic.term-listp todo)
                        (logic.term-listp done)
                        (or (consp todo) (consp done))
                        (logic.appealp proof)
                        (equal (logic.conclusion proof)
                               (cond ((and (consp done) (consp todo))
                                      (logic.por (clause.clause-formula done) (clause.clause-formula todo)))
                                     ((consp done)
                                      (clause.clause-formula done))
                                     (t
                                      (clause.clause-formula todo))))
                        (logic.appeal-listp t-proofs)
                        (logic.all-atomicp (logic.strip-conclusions t-proofs))
                        (all-equalp ''t (logic.=rhses (logic.strip-conclusions t-proofs)))
                        (logic.all-functionsp (logic.=lhses (logic.strip-conclusions t-proofs)))
                        (all-equalp 'iff (logic.strip-function-names (logic.=lhses (logic.strip-conclusions t-proofs))))
                        (all-equalp 2 (strip-lens (logic.strip-function-args (logic.=lhses (logic.strip-conclusions t-proofs)))))
                        (equal (strip-seconds (logic.strip-function-args (logic.=lhses (logic.strip-conclusions t-proofs)))) todo)))
            (equal (logic.conclusion (clause.aux-update-clause-iff-bldr todo done t-proofs proof))
                   (clause.clause-formula
                    (app (rev (strip-firsts (logic.strip-function-args (logic.=lhses (logic.strip-conclusions t-proofs)))))
                         done))))
   :rule-classes ((:rewrite :backchain-limit-lst 0)))

 (defthm@ forcing-logic.proofp-of-clause.aux-update-clause-iff-bldr
   (implies (force (and (logic.term-listp todo)
                        (logic.term-listp done)
                        (or (consp todo) (consp done))
                        (logic.appealp proof)
                        (equal (logic.conclusion proof)
                               (cond ((and (consp done) (consp todo))
                                      (logic.por (clause.clause-formula done) (clause.clause-formula todo)))
                                     ((consp done)
                                      (clause.clause-formula done))
                                     (t
                                      (clause.clause-formula todo))))
                        (logic.appeal-listp t-proofs)
                        (logic.all-atomicp (logic.strip-conclusions t-proofs))
                        (all-equalp ''t (logic.=rhses (logic.strip-conclusions t-proofs)))
                        (logic.all-functionsp (logic.=lhses (logic.strip-conclusions t-proofs)))
                        (all-equalp 'iff (logic.strip-function-names (logic.=lhses (logic.strip-conclusions t-proofs))))
                        (all-equalp 2 (strip-lens (logic.strip-function-args (logic.=lhses (logic.strip-conclusions t-proofs)))))
                        (equal (strip-seconds (logic.strip-function-args (logic.=lhses (logic.strip-conclusions t-proofs)))) todo)
                        ;; ---
                        (logic.term-list-atblp todo atbl)
                        (logic.term-list-atblp done atbl)
                        (logic.proofp proof axioms thms atbl)
                        (logic.proof-listp t-proofs axioms thms atbl)
                        (@obligations clause.aux-update-clause-iff-bldr)))
            (equal (logic.proofp (clause.aux-update-clause-iff-bldr todo done t-proofs proof) axioms thms atbl)
                   t))
   :hints(("Goal" :induct (clause.aux-update-clause-iff-bldr todo done t-proofs proof))))

 (verify-guards clause.aux-update-clause-iff-bldr))





(local (in-theory (e/d (strip-lens-of-rev)
                       (rev-of-logic.strip-conclusions
                        rev-of-logic.=lhses
                        rev-of-logic.strip-function-args
                        rev-of-strip-lens))))

(defund clause.update-clause-iff-bldr (x proof t-proofs)
  (declare (xargs :guard (and (logic.term-listp x)
                              (consp x)
                              (logic.appealp proof)
                              (equal (logic.conclusion proof) (clause.clause-formula x))
                              (logic.appeal-listp t-proofs)
                              (logic.all-atomicp (logic.strip-conclusions t-proofs))
                              (all-equalp ''t (logic.=rhses (logic.strip-conclusions t-proofs)))
                              (logic.all-functionsp (logic.=lhses (logic.strip-conclusions t-proofs)))
                              (all-equalp 'iff (logic.strip-function-names (logic.=lhses (logic.strip-conclusions t-proofs))))
                              (all-equalp 2 (strip-lens (logic.strip-function-args (logic.=lhses (logic.strip-conclusions t-proofs)))))
                              (equal (strip-seconds (logic.strip-function-args (logic.=lhses (logic.strip-conclusions t-proofs)))) x))))
  (let ((lhses (strip-firsts (logic.strip-function-args (logic.=lhses (logic.strip-conclusions t-proofs))))))
    (if (equal lhses x)
        ;; Important optimization!  If nothing has changed, just reuse the original proof.
        (logic.appeal-identity proof)
      (build.rev-disjunction
       (logic.term-list-formulas (fast-rev lhses))
       (clause.aux-update-clause-iff-bldr x nil t-proofs proof)))))

(defobligations clause.update-clause-iff-bldr
  (build.rev-disjunction clause.aux-update-clause-iff-bldr))

(encapsulate
 ()
 (local (in-theory (enable clause.update-clause-iff-bldr)))

 (defthm clause.update-clause-iff-bldr-under-iff
   (iff (clause.update-clause-iff-bldr x proof t-proofs)
        t))

 (defthm forcing-logic.appealp-of-clause.update-clause-iff-bldr
   (implies (force (and (logic.term-listp x)
                        (consp x)
                        (logic.appealp proof)
                        (equal (logic.conclusion proof) (clause.clause-formula x))
                        (logic.appeal-listp t-proofs)
                        (logic.all-atomicp (logic.strip-conclusions t-proofs))
                        (all-equalp ''t (logic.=rhses (logic.strip-conclusions t-proofs)))
                        (logic.all-functionsp (logic.=lhses (logic.strip-conclusions t-proofs)))
                        (all-equalp 'iff (logic.strip-function-names (logic.=lhses (logic.strip-conclusions t-proofs))))
                        (all-equalp 2 (strip-lens (logic.strip-function-args (logic.=lhses (logic.strip-conclusions t-proofs)))))
                        (equal (strip-seconds (logic.strip-function-args (logic.=lhses (logic.strip-conclusions t-proofs)))) x)))
            (equal (logic.appealp (clause.update-clause-iff-bldr x proof t-proofs))
                   t)))

 (defthm forcing-logic.conclusion-of-clause.update-clause-iff-bldr
   (implies (force (and (logic.term-listp x)
                        (consp x)
                        (logic.appealp proof)
                        (equal (logic.conclusion proof) (clause.clause-formula x))
                        (logic.appeal-listp t-proofs)
                        (logic.all-atomicp (logic.strip-conclusions t-proofs))
                        (all-equalp ''t (logic.=rhses (logic.strip-conclusions t-proofs)))
                        (logic.all-functionsp (logic.=lhses (logic.strip-conclusions t-proofs)))
                        (all-equalp 'iff (logic.strip-function-names (logic.=lhses (logic.strip-conclusions t-proofs))))
                        (all-equalp 2 (strip-lens (logic.strip-function-args (logic.=lhses (logic.strip-conclusions t-proofs)))))
                        (equal (strip-seconds (logic.strip-function-args (logic.=lhses (logic.strip-conclusions t-proofs)))) x)))
            (equal (logic.conclusion (clause.update-clause-iff-bldr x proof t-proofs))
                   (clause.clause-formula (strip-firsts (logic.strip-function-args (logic.=lhses (logic.strip-conclusions t-proofs)))))))
   :rule-classes ((:rewrite :backchain-limit-lst 0)))

 (defthm@ forcing-logic.proofp-of-clause.update-clause-iff-bldr
   (implies (force (and (and (logic.term-listp x)
                             (consp x)
                             (logic.appealp proof)
                             (equal (logic.conclusion proof) (clause.clause-formula x))
                             (logic.appeal-listp t-proofs)
                             (logic.all-atomicp (logic.strip-conclusions t-proofs))
                             (all-equalp ''t (logic.=rhses (logic.strip-conclusions t-proofs)))
                             (logic.all-functionsp (logic.=lhses (logic.strip-conclusions t-proofs)))
                             (all-equalp 'iff (logic.strip-function-names (logic.=lhses (logic.strip-conclusions t-proofs))))
                             (all-equalp 2 (strip-lens (logic.strip-function-args (logic.=lhses (logic.strip-conclusions t-proofs)))))
                             (equal (strip-seconds (logic.strip-function-args (logic.=lhses (logic.strip-conclusions t-proofs)))) x)
                             ;; ---
                             (logic.term-list-atblp x atbl)
                             (logic.proofp proof axioms thms atbl)
                             (logic.proof-listp t-proofs axioms thms atbl)
                             (@obligations clause.update-clause-iff-bldr))))
            (equal (logic.proofp (clause.update-clause-iff-bldr x proof t-proofs) axioms thms atbl)
                   t))))




;; Rudimentary Size Testing
;;
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
;; (include-book "update-clause-bldr")
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
;;
;;
;; And here's how clause.update-clause-iff compares to clause.update-clause.
;;
;;    n    clause.update-clause   clause.update-clause-iff
;;   ---------------------------------------------------------
;;     1              313                 1,370
;;     2            2,419                 9,307
;;     3            7,127                20,159
;;     4           14,215                35,191
;;     5           26,683                54,403
;;   ---------------------------------------------------------
;;
;; This table was generated by commenting out the appropriate parts of this test code:
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
;;        (t-proofs-iff (list
;;                       (build.axiom (logic.pequal '(iff T1 T1-Prime) ''t))
;;                       (build.axiom (logic.pequal '(iff T2 T2-Prime) ''t))
;;                       (build.axiom (logic.pequal '(iff T3 T3-Prime) ''t))
;;                       (build.axiom (logic.pequal '(iff T4 T4-Prime) ''t))
;;                       (build.axiom (logic.pequal '(iff T5 T5-Prime) ''t))
;;                       ))
;;        (orig-clause   (logic.=rhses (logic.strip-conclusions t-proofs)))
;;        (input-proof   (build.axiom (clause.clause-formula orig-clause)))
;;        (pequal-proof  (clause.update-clause-bldr orig-clause input-proof t-proofs))
;;        (iff-proof     (clause.update-clause-iff-bldr orig-clause input-proof t-proofs-iff)))
;;   (list (list 'input-proof  (logic.conclusion input-proof))
;;         (list 't-proofs     (logic.strip-conclusions t-proofs))
;;         (list 't-proofs-iff (logic.strip-conclusions t-proofs-iff))
;;         (list 'pequal-rank  (rank pequal-proof))
;;         (list 'iff-rank     (rank iff-proof))
;;         (list 'pequal-conc  (logic.conclusion pequal-proof))
;;         (list 'iff-conc     (logic.conclusion iff-proof))
;;         (list 'pequal-okp   (equal (logic.conclusion pequal-proof) (clause.clause-formula goal-clause)))
;;         (list 'iff-okp      (equal (logic.conclusion iff-proof) (clause.clause-formula goal-clause)))))




(defund clause.update-clause-iff-bldr-okp (x)
  (declare (xargs :guard (logic.appealp x)))
  (let ((method     (logic.method x))
        (conclusion (logic.conclusion x))
        (subproofs  (logic.subproofs x))
        (extras     (logic.extras x)))
    (and (equal method 'clause.update-clause-iff-bldr)
         (not extras)
         (consp subproofs)
         (let ((proof    (car subproofs))
               (t-proofs (cdr subproofs)))
           (and (consp t-proofs)
                (logic.all-atomicp-of-strip-conclusions t-proofs)
                (logic.all-functionsp (logic.=lhses-of-strip-conclusions t-proofs))
                (all-equalp 'iff (logic.strip-function-names (logic.=lhses-of-strip-conclusions t-proofs)))
                (all-equalp 2 (strip-lens (logic.strip-function-args (logic.=lhses-of-strip-conclusions t-proofs))))
                (all-equalp ''t (logic.=rhses-of-strip-conclusions t-proofs))
                ;; BOZO efficiency -- we could do a ton with folding/deforestation here
                (equal conclusion
                       (clause.clause-formula (strip-firsts (logic.strip-function-args (logic.=lhses-of-strip-conclusions t-proofs)))))
                (equal (logic.conclusion proof)
                       (clause.clause-formula (strip-seconds (logic.strip-function-args (logic.=lhses-of-strip-conclusions t-proofs)))))
                )))))

(defund clause.update-clause-iff-bldr-high (x proof t-proofs)
  (declare (xargs :guard (and (logic.term-listp x)
                              (consp x)
                              (logic.appealp proof)
                              (equal (logic.conclusion proof) (clause.clause-formula x))
                              (logic.appeal-listp t-proofs)
                              (logic.all-atomicp (logic.strip-conclusions t-proofs))
                              (all-equalp ''t (logic.=rhses (logic.strip-conclusions t-proofs)))
                              (logic.all-functionsp (logic.=lhses (logic.strip-conclusions t-proofs)))
                              (all-equalp 'iff (logic.strip-function-names (logic.=lhses (logic.strip-conclusions t-proofs))))
                              (all-equalp 2 (strip-lens (logic.strip-function-args (logic.=lhses (logic.strip-conclusions t-proofs)))))
                              (equal (strip-seconds (logic.strip-function-args (logic.=lhses (logic.strip-conclusions t-proofs)))) x)))
           (ignore x))
  (logic.appeal 'clause.update-clause-iff-bldr
                (clause.clause-formula (strip-firsts (logic.strip-function-args (logic.=lhses (logic.strip-conclusions t-proofs)))))
                (cons proof (list-fix t-proofs))
                nil))



(encapsulate
 ()
 (local (in-theory (enable clause.update-clause-iff-bldr-okp)))

 (defthm booleanp-of-clause.update-clause-iff-bldr-okp
   (equal (booleanp (clause.update-clause-iff-bldr-okp x))
          t)
   :hints(("goal" :in-theory (disable (:executable-counterpart ACL2::force)))))

 (defthm clause.update-clause-iff-bldr-okp-of-logic.appeal-identity
   (equal (clause.update-clause-iff-bldr-okp (logic.appeal-identity x))
          (clause.update-clause-iff-bldr-okp x))
   :hints(("goal" :in-theory (disable (:executable-counterpart ACL2::force)))))

 (local (in-theory (e/d (backtracking-logic.formula-atblp-rules)
                        (forcing-logic.formula-atblp-rules
                         forcing-lookup-of-logic.function-name-free))))

 (defthmd lemma-1-for-soundness-of-clause.update-clause-iff-bldr-okp
   (implies (and (clause.update-clause-iff-bldr-okp x)
                 (logic.appealp x)
                 (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl))
            (equal (logic.conclusion (clause.update-clause-iff-bldr
                                      (strip-seconds
                                       (logic.strip-function-args
                                        (logic.=lhses
                                         (logic.strip-conclusions
                                          (logic.provable-list-witness (logic.strip-conclusions (cdr (logic.subproofs x)))
                                                                       axioms thms atbl)))))
                                      (logic.provable-witness (logic.conclusion (car (logic.subproofs x))) axioms thms atbl)
                                      (logic.provable-list-witness (logic.strip-conclusions (cdr (logic.subproofs x)))
                                                                   axioms thms atbl)))
                   (logic.conclusion x))))

 (defthmd@ lemma-2-for-soundness-of-clause.update-clause-iff-bldr-okp
   (implies (and (clause.update-clause-iff-bldr-okp x)
                 (logic.appealp x)
                 (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl)
                 (@obligations clause.update-clause-iff-bldr))
            (equal (logic.proofp (clause.update-clause-iff-bldr
                                  (strip-seconds
                                   (logic.strip-function-args
                                    (logic.=lhses
                                     (logic.strip-conclusions
                                      (logic.provable-list-witness (logic.strip-conclusions (cdr (logic.subproofs x)))
                                                                   axioms thms atbl)))))
                                  (logic.provable-witness (logic.conclusion (car (logic.subproofs x))) axioms thms atbl)
                                  (logic.provable-list-witness (logic.strip-conclusions (cdr (logic.subproofs x)))
                                                               axioms thms atbl))
                                 axioms thms atbl)
                   t)))

 (defthm@ forcing-soundness-of-clause.update-clause-iff-bldr-okp
   (implies (and (clause.update-clause-iff-bldr-okp x)
                 (force (and (logic.appealp x)
                             (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl)
                             (@obligations clause.update-clause-iff-bldr))))
            (equal (logic.provablep (logic.conclusion x) axioms thms atbl)
                   t))
   :hints (("Goal"
            :in-theory (enable lemma-1-for-soundness-of-clause.update-clause-iff-bldr-okp
                               lemma-2-for-soundness-of-clause.update-clause-iff-bldr-okp)
            :use ((:instance forcing-logic.provablep-when-logic.proofp
                             (x (clause.update-clause-iff-bldr
                                 (strip-seconds
                                  (logic.strip-function-args
                                   (logic.=lhses
                                    (logic.strip-conclusions
                                     (logic.provable-list-witness (logic.strip-conclusions (cdr (logic.subproofs x)))
                                                                  axioms thms atbl)))))
                                 (logic.provable-witness (logic.conclusion (car (logic.subproofs x))) axioms thms atbl)
                                 (logic.provable-list-witness (logic.strip-conclusions (cdr (logic.subproofs x)))
                                                              axioms thms atbl)))))))))
