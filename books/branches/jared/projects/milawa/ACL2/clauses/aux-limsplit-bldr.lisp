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
(include-book "prop")
(include-book "../build/disjoined-subset")
(include-book "aux-split-support")
(include-book "aux-limsplit")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)



(defund clause.aux-limsplit-cutoff-bldr (as bs proof)
  ;;    (A1 v ... v An v B1 v ... v Bm) v Q
  ;;  ---------------------------------------
  ;;   (B1 v ... v Bm) v (An v ... v A1 v Q)
  ;;
  ;; This is just the repeated application of aux-limsplit-cutoff-step-bldr.
  (declare (xargs :guard (and (logic.formula-listp as)
                              (logic.formula-listp bs)
                              (consp bs)
                              (logic.appealp proof)
                              (equal (logic.fmtype (logic.conclusion proof)) 'por*)
                              (equal (logic.vlhs (logic.conclusion proof))
                                     (logic.disjoin-formulas (app as bs))))
                  :verify-guards nil))
  (if (consp as)
      (clause.aux-limsplit-cutoff-bldr (cdr as) bs
                                       (clause.aux-limsplit-cutoff-step-bldr proof))
    (logic.appeal-identity proof)))

(encapsulate
 ()
 (local (in-theory (enable clause.aux-limsplit-cutoff-bldr)))

 (defthm clause.aux-limsplit-cutoff-bldr-under-iff
   (iff (clause.aux-limsplit-cutoff-bldr as bs proof)
        t))

 (defthm forcing-logic.appealp-of-clause.aux-limsplit-cutoff-bldr
   (implies (force (and (logic.formula-listp as)
                        (logic.formula-listp bs)
                        (consp bs)
                        (logic.appealp proof)
                        (equal (logic.fmtype (logic.conclusion proof)) 'por*)
                        (equal (logic.vlhs (logic.conclusion proof))
                               (logic.disjoin-formulas (app as bs)))))
            (equal (logic.appealp (clause.aux-limsplit-cutoff-bldr as bs proof))
                   t)))

 (defthmd lemma-for-forcing-logic.conclusion-of-clause.aux-limsplit-cutoff-bldr
   (implies (force (and (logic.formulap b)
                        (logic.formulap c)))
            (equal (logic.disjoin-formulas (app a (list b c)))
                   (logic.disjoin-formulas (app a (list (logic.por b c))))))
   :hints(("Goal"
           :induct (cdr-induction a)
           :in-theory (enable logic.disjoin-formulas))))

 (defthm forcing-logic.conclusion-of-clause.aux-limsplit-cutoff-bldr
   (implies (force (and (logic.formula-listp as)
                        (logic.formula-listp bs)
                        (consp bs)
                        (logic.appealp proof)
                        (equal (logic.fmtype (logic.conclusion proof)) 'por*)
                        (equal (logic.vlhs (logic.conclusion proof))
                               (logic.disjoin-formulas (app as bs)))))
            (equal (logic.conclusion (clause.aux-limsplit-cutoff-bldr as bs proof))
                   (logic.por (logic.disjoin-formulas bs)
                              (logic.disjoin-formulas (app (rev as) (list (logic.vrhs (logic.conclusion proof))))))))
   :rule-classes ((:rewrite :backchain-limit-lst 0))
   :hints(("Goal"
           :in-theory (enable lemma-for-forcing-logic.conclusion-of-clause.aux-limsplit-cutoff-bldr))))

 (verify-guards clause.aux-limsplit-cutoff-bldr)

 (defthm forcing-logic.proofp-of-clause.aux-limsplit-cutoff-bldr
   (implies (force (and (logic.formula-listp as)
                        (logic.formula-listp bs)
                        (consp bs)
                        (logic.appealp proof)
                        (equal (logic.fmtype (logic.conclusion proof)) 'por*)
                        (equal (logic.vlhs (logic.conclusion proof))
                               (logic.disjoin-formulas (app as bs)))
                        ;; ---
                        (logic.proofp proof axioms thms atbl)))
            (equal (logic.proofp (clause.aux-limsplit-cutoff-bldr as bs proof) axioms thms atbl)
                   t))))


(defund clause.limsplit-cutoff-bldr (as bs proof)
  ;;    (A1 v ... v An v B1 v ... v Bm)
  ;;  -----------------------------------
  ;;   (B1 v ... v Bm) v (An v ... v A1)
  (declare (xargs :guard (and (logic.formula-listp as)
                              (logic.formula-listp bs)
                              (logic.appealp proof)
                              (or (consp as) (consp bs))
                              (equal (logic.conclusion proof)
                                     (logic.disjoin-formulas (app as bs))))
                  :verify-guards nil))
  (if (consp as)
      (if (consp bs)
          (if (consp (cdr as))
              ;; The usual case.  We have a proof of A1 v (A2 v ... v B1...Bm).  We rotate the A1 to
              ;; the right with a commute-or and it becomes Q.  Then, we handle the rest with our
              ;; aux-cutoff-builder.
              (clause.aux-limsplit-cutoff-bldr (cdr as) bs (build.commute-or proof))
            ;; An unusual case.  We have A1 v B1...Bm.  This is super easy -- we just need to commute
            ;; the or.
            (build.commute-or proof))
        ;; An unusual case.  We have A1...An all by itself.  We can just reverse it.
        (build.rev-disjunction as proof))
    ;; An unusual case.  We have B1...Bm all by itself.  We don't need to do anything.
    (logic.appeal-identity proof)))

(encapsulate
 ()
 (local (in-theory (enable clause.limsplit-cutoff-bldr)))

 (defthm forcing-logic.appealp-of-clause.limsplit-cutoff-bldr
   (implies (force (and (logic.formula-listp as)
                        (logic.formula-listp bs)
                        (logic.appealp proof)
                        (or (consp as) (consp bs))
                        (equal (logic.conclusion proof)
                               (logic.disjoin-formulas (app as bs)))))
            (equal (logic.appealp (clause.limsplit-cutoff-bldr as bs proof))
                   t)))

 (defthm forcing-logic.conclusion-of-clause.limsplit-cutoff-bldr
   (implies (force (and (logic.formula-listp as)
                        (logic.formula-listp bs)
                        (logic.appealp proof)
                        (or (consp as) (consp bs))
                        (equal (logic.conclusion proof)
                               (logic.disjoin-formulas (app as bs)))))
            (equal (logic.conclusion (clause.limsplit-cutoff-bldr as bs proof))
                   (cond ((and (consp as)
                               (consp bs))
                          (logic.por (logic.disjoin-formulas bs)
                                     (logic.disjoin-formulas (rev as))))
                         ((consp as)
                          (logic.disjoin-formulas (rev as)))
                         (t
                          (logic.disjoin-formulas bs)))))
   :rule-classes ((:rewrite :backchain-limit-lst 0)))

 (verify-guards clause.limsplit-cutoff-bldr)

 (defthm forcing-logic.proofp-of-clause.limsplit-cutoff-bldr
   (implies (force (and (logic.formula-listp as)
                        (logic.formula-listp bs)
                        (logic.appealp proof)
                        (or (consp as) (consp bs))
                        (equal (logic.conclusion proof)
                               (logic.disjoin-formulas (app as bs)))
                        ;; ---
                        (logic.proofp proof axioms thms atbl)))
            (equal (logic.proofp (clause.limsplit-cutoff-bldr as bs proof) axioms thms atbl)
                   t))))





(defund clause.limsplit-cutoff-bldr-nice (todo done proof)
  (declare (xargs :guard (and (logic.term-listp todo)
                              (true-listp todo)
                              (logic.term-listp done)
                              (logic.appealp proof)
                              (or (consp todo) (consp done))
                              (equal (logic.conclusion proof)
                                     (clause.clause-formula (revappend done todo))))))
  (clause.limsplit-cutoff-bldr (logic.term-list-formulas (fast-rev done))
                               (logic.term-list-formulas todo)
                               proof))

(defthm forcing-logic.appealp-of-clause.limsplit-cutoff-bldr-nice
  (implies (force (and (logic.term-listp todo)
                       (logic.term-listp done)
                       (logic.appealp proof)
                       (or (consp todo) (consp done))
                       (equal (logic.conclusion proof)
                              (clause.clause-formula (app (rev done) todo)))))
           (equal (logic.appealp (clause.limsplit-cutoff-bldr-nice todo done proof))
                  t))
  :hints(("Goal" :in-theory (enable clause.limsplit-cutoff-bldr-nice))))

(defthm forcing-logic.conclusion-of-clause.limsplit-cutoff-bldr-nice
  (implies (force (and (logic.term-listp todo)
                       (logic.term-listp done)
                       (logic.appealp proof)
                       (or (consp todo) (consp done))
                       (equal (logic.conclusion proof)
                              (clause.clause-formula (app (rev done) todo)))))
           (equal (logic.conclusion (clause.limsplit-cutoff-bldr-nice todo done proof))
                  (clause.aux-split-goal todo done)))
  :rule-classes ((:rewrite :backchain-limit-lst 0))
  :hints(("Goal" :in-theory (enable clause.limsplit-cutoff-bldr-nice
                                    clause.aux-split-goal))))

(defthm forcing-logic.proofp-of-clause.limsplit-cutoff-bldr-nice
  (implies (force (and (logic.term-listp todo)
                       (logic.term-listp done)
                       (logic.appealp proof)
                       (or (consp todo) (consp done))
                       (equal (logic.conclusion proof)
                              (clause.clause-formula (app (rev done) todo)))
                       (logic.proofp proof axioms thms atbl)))
           (equal (logic.proofp (clause.limsplit-cutoff-bldr-nice todo done proof) axioms thms atbl)
                  t))
  :hints(("Goal" :in-theory (enable clause.limsplit-cutoff-bldr-nice
                                    clause.aux-split-goal))))






(defund clause.limsplit-cutoff-bldr-nice-okp (x)
  (declare (xargs :guard (logic.appealp x)))
  (let ((method     (logic.method x))
        (conclusion (logic.conclusion x))
        (subproofs  (logic.subproofs x))
        (extras     (logic.extras x)))
    (and (equal method 'clause.limsplit-cutoff-bldr-nice)
         (tuplep 2 extras)
         (equal (len subproofs) 1)
         (let ((todo (first extras))
               (done (second extras))
               (proof (first subproofs)))
           (and (logic.term-listp todo)
                (true-listp todo)
                (logic.term-listp done)
                (or (consp todo) (consp done))
                (equal conclusion (clause.aux-split-goal todo done))
                (equal (logic.conclusion proof)
                       (clause.clause-formula (revappend done todo))))))))

(defund clause.limsplit-cutoff-bldr-nice-high (todo done proof)
  (declare (xargs :guard (and (logic.term-listp todo)
                              (true-listp todo)
                              (logic.term-listp done)
                              (logic.appealp proof)
                              (or (consp todo) (consp done))
                              (equal (logic.conclusion proof)
                                     (clause.clause-formula (revappend done todo))))))
  (logic.appeal 'clause.limsplit-cutoff-bldr-nice
                (clause.clause-formula (revappend done todo))
                (list proof)
                (list todo done)))

(defobligations clause.limsplit-cutoff-bldr-nice-okp
  (clause.limsplit-cutoff-bldr-nice))

(encapsulate
 ()
 (local (in-theory (enable clause.limsplit-cutoff-bldr-nice-okp
                           clause.limsplit-cutoff-bldr-nice-high)))

 (defthm booleanp-of-clause.limsplit-cutoff-bldr-nice-okp
   (equal (booleanp (clause.limsplit-cutoff-bldr-nice-okp x))
          t))

 (defthm clause.limsplit-cutoff-bldr-nice-okp-of-logic.appeal-identity
   (equal (clause.limsplit-cutoff-bldr-nice-okp (logic.appeal-identity x))
          (clause.limsplit-cutoff-bldr-nice-okp x)))

 (defthmd lemma-1-for-soundness-of-clause.limsplit-cutoff-bldr-nice-okp
   (implies (and (clause.limsplit-cutoff-bldr-nice-okp x)
                 (logic.appealp x)
                 (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl))
            (equal (logic.conclusion
                    (clause.limsplit-cutoff-bldr-nice (first (logic.extras x))
                                                      (second (logic.extras x))
                                                      (logic.provable-witness (logic.conclusion (first (logic.subproofs x)))
                                                                              axioms thms atbl)))
                   (logic.conclusion x))))

 (defthmd@ lemma-2-for-soundness-of-clause.limsplit-cutoff-bldr-nice-okp
   (implies (and (clause.limsplit-cutoff-bldr-nice-okp x)
                 (logic.appealp x)
                 (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl)
                 (@obligations clause.limsplit-cutoff-bldr-nice-okp))
            (equal (logic.proofp
                    (clause.limsplit-cutoff-bldr-nice (first (logic.extras x))
                                                      (second (logic.extras x))
                                                      (logic.provable-witness (logic.conclusion (first (logic.subproofs x)))
                                                                              axioms thms atbl))
                    axioms thms atbl)
                   t)))

 (defthm@ forcing-soundness-of-clause.limsplit-cutoff-bldr-nice-okp
   (implies (and (clause.limsplit-cutoff-bldr-nice-okp x)
                 (force (and (logic.appealp x)
                             (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl)
                             (@obligations clause.limsplit-cutoff-bldr-nice-okp))))
            (equal (logic.provablep (logic.conclusion x) axioms thms atbl)
                   t))
   :hints (("Goal"
            :in-theory (enable lemma-1-for-soundness-of-clause.limsplit-cutoff-bldr-nice-okp
                               lemma-2-for-soundness-of-clause.limsplit-cutoff-bldr-nice-okp)
            :use ((:instance forcing-logic.provablep-when-logic.proofp
                             (x (clause.limsplit-cutoff-bldr-nice (first (logic.extras x))
                                                                  (second (logic.extras x))
                                                                  (logic.provable-witness (logic.conclusion (first (logic.subproofs x)))
                                                                                          axioms thms atbl)))))))))





(defund clause.aux-limsplit-bldr (todo done proofs n)
  (declare (xargs :guard (and (logic.term-listp todo)
                              (logic.term-listp done)
                              (true-listp todo)
                              (or (consp todo) (consp done))
                              (natp n)
                              (logic.appeal-listp proofs)
                              (subsetp (clause.clause-list-formulas (clause.aux-limsplit todo done n))
                                       (logic.strip-conclusions proofs)))
                  :verify-guards nil
                  :measure (clause.split-count-list todo)))
  (if (zp n)
      (clause.limsplit-cutoff-bldr-nice todo done
                                        (logic.find-proof (clause.clause-formula (revappend done todo)) proofs))
    (if (consp todo)
        (let ((t1 (car todo)))
          (if (clause.negative-termp t1)
              (let ((guts (clause.negative-term-guts t1)))
                (if (clause.negative-termp guts)
                    (clause.aux-split-double-negate t1 (cdr todo) done
                                                    (clause.aux-limsplit-bldr (cons (clause.negative-term-guts guts) (cdr todo))
                                                                              done proofs n))
                  (if (and (logic.functionp guts)
                           (equal (logic.function-name guts) 'if)
                           (equal (len (logic.function-args guts)) 3))
                      (let ((args (logic.function-args guts)))
                        (let ((a      (first args))
                              (not-a  (logic.function 'not (list (first args))))
                              (not-b  (logic.function 'not (list (second args))))
                              (not-c  (logic.function 'not (list (third args))))
                              (rest   (cdr todo)))
                          (let ((triv1 (clause.aux-split-trivial-branchp not-a not-b rest done))
                                (triv2 (clause.aux-split-trivial-branchp a not-c rest done)))
                            (cond ((and triv1 triv2)
                                   (clause.aux-split-negated-if t1 rest done
                                                                (clause.aux-split-trivial-branch-bldr not-a not-b rest done)
                                                                (clause.aux-split-trivial-branch-bldr a not-c rest done)))
                                  (triv1
                                   (clause.aux-split-negated-if t1 rest done
                                                                (clause.aux-split-trivial-branch-bldr not-a not-b rest done)
                                                                (clause.aux-limsplit-bldr (cons a (cons not-c rest)) done proofs n)))
                                  (triv2
                                   (clause.aux-split-negated-if t1 rest done
                                                                (clause.aux-limsplit-bldr (cons not-a (cons not-b rest)) done proofs n)
                                                                (clause.aux-split-trivial-branch-bldr a not-c rest done)))
                                  (t
                                   (clause.aux-split-negated-if t1 rest done
                                                                (clause.aux-limsplit-bldr (cons not-a (cons not-b rest)) done proofs (- n 1))
                                                                (clause.aux-limsplit-bldr (cons a (cons not-c rest)) done proofs (- n 1))))))))

                    (clause.aux-split-negative-default t1 (cdr todo) done
                                                       (clause.aux-limsplit-bldr (cdr todo)
                                                                                 (cons (logic.function 'not (list guts)) done)
                                                                                 proofs n)))))
            (if (and (logic.functionp t1)
                     (equal (logic.function-name t1) 'if)
                     (equal (len (logic.function-args t1)) 3))
                (let ((args (logic.function-args t1)))
                  (let ((a     (first args))
                        (not-a (logic.function 'not (list (first args))))
                        (b     (second args))
                        (c     (third args))
                        (rest  (cdr todo)))
                    (let ((triv1 (clause.aux-split-trivial-branchp not-a b rest done))
                          (triv2 (clause.aux-split-trivial-branchp a c rest done)))
                      (cond ((and triv1 triv2)
                             (clause.aux-split-positive-if t1 rest done
                                                           (clause.aux-split-trivial-branch-bldr not-a b rest done)
                                                           (clause.aux-split-trivial-branch-bldr a c rest done)))
                            (triv1
                             (clause.aux-split-positive-if t1 rest done
                                                           (clause.aux-split-trivial-branch-bldr not-a b rest done)
                                                           (clause.aux-limsplit-bldr (cons a (cons c rest)) done proofs n)))
                            (triv2
                             (clause.aux-split-positive-if t1 rest done
                                                           (clause.aux-limsplit-bldr (cons not-a (cons b rest)) done proofs n)
                                                           (clause.aux-split-trivial-branch-bldr a c rest done)))
                            (t
                             (clause.aux-split-positive-if t1 rest done
                                                           (clause.aux-limsplit-bldr (cons not-a (cons b rest)) done proofs (- n 1))
                                                           (clause.aux-limsplit-bldr (cons a (cons c rest)) done proofs (- n 1))))))))

              (clause.aux-split-positive-default t1 (cdr todo) done
                                                 (clause.aux-limsplit-bldr (cdr todo) (cons t1 done) proofs n)))))

      (logic.find-proof (clause.clause-formula done) proofs))))

(defobligations clause.aux-limsplit-bldr
  (clause.aux-split-double-negate
   clause.aux-split-negated-if
   clause.aux-split-negative-default
   clause.aux-split-positive-if
   clause.aux-split-positive-default
   clause.aux-split-trivial-branch-bldr))


(encapsulate
 ()
 (local (in-theory (enable clause.aux-limsplit-bldr
                           clause.aux-split-goal-when-not-consp-of-todo
                           )))

 (defthm lemma-for-forcing-logic.appealp-of-clause.aux-limsplit-bldr
   (implies (and (logic.term-listp todo)
                 (logic.term-listp done)
                 (true-listp todo)
                 (or (consp todo) (consp done))
                 (logic.appeal-listp proofs)
                 (subsetp (clause.clause-list-formulas (clause.aux-limsplit todo done n))
                          (logic.strip-conclusions proofs)))
            (and (logic.appealp (clause.aux-limsplit-bldr todo done proofs n))
                 (equal (logic.conclusion (clause.aux-limsplit-bldr todo done proofs n))
                        (clause.aux-split-goal todo done))))
   :rule-classes nil
   :hints(("Goal"
           :induct (clause.aux-limsplit-bldr todo done proofs n)
           :expand ((clause.aux-limsplit todo done n)
                    (clause.aux-limsplit nil done n))
           )))

 (defthm forcing-logic.appealp-of-clause.aux-limsplit-bldr
   (implies (force (and (logic.term-listp todo)
                        (logic.term-listp done)
                        (true-listp todo)
                        (or (consp todo) (consp done))
                        (logic.appeal-listp proofs)
                        (subsetp (clause.clause-list-formulas (clause.aux-limsplit todo done n))
                                 (logic.strip-conclusions proofs))))
            (equal (logic.appealp (clause.aux-limsplit-bldr todo done proofs n))
                   t))
   :hints(("Goal" :use ((:instance lemma-for-forcing-logic.appealp-of-clause.aux-limsplit-bldr)))))

 ;; We want to keep working with clause.aux-limsplit-goal, for now.
 (defthmd lemma-for-forcing-logic.proofp-of-clause.aux-limsplit-bldr
   (implies (force (and (logic.term-listp todo)
                        (logic.term-listp done)
                        (true-listp todo)
                        (or (consp todo) (consp done))
                        (logic.appeal-listp proofs)
                        (subsetp (clause.clause-list-formulas (clause.aux-limsplit todo done n))
                                 (logic.strip-conclusions proofs))))
            (equal (logic.conclusion (clause.aux-limsplit-bldr todo done proofs n))
                   (clause.aux-split-goal todo done)))
   :rule-classes ((:rewrite :backchain-limit-lst 0))
   :hints(("Goal" :use ((:instance lemma-for-forcing-logic.appealp-of-clause.aux-limsplit-bldr)))))

 (verify-guards clause.aux-limsplit-bldr
                :hints(("Goal"
                        :in-theory (enable lemma-for-forcing-logic.proofp-of-clause.aux-limsplit-bldr)
                        :expand ((clause.aux-limsplit todo done n)
                                 (clause.aux-limsplit nil done n))
                        )))

 (defthm@ forcing-logic.proofp-of-clause.aux-limsplit-bldr
   (implies (force (and (logic.term-listp todo)
                        (logic.term-listp done)
                        (true-listp todo)
                        (or (consp todo) (consp done))
                        (logic.appeal-listp proofs)
                        (subsetp (clause.clause-list-formulas (clause.aux-limsplit todo done n))
                                 (logic.strip-conclusions proofs))
                        ;; ---
                        (logic.term-list-atblp todo atbl)
                        (logic.term-list-atblp done atbl)
                        (logic.proof-listp proofs axioms thms atbl)
                        (equal (cdr (lookup 'not atbl)) 1)
                        (equal (cdr (lookup 'iff atbl)) 2)
                        (equal (cdr (lookup 'equal atbl)) 2)
                        (equal (cdr (lookup 'if atbl)) 3)
                        (@obligations clause.aux-limsplit-bldr)
                        ))
            (equal (logic.proofp (clause.aux-limsplit-bldr todo done proofs n) axioms thms atbl)
                   t))
   :hints(("Goal"
           :induct (clause.aux-limsplit-bldr todo done proofs n)
           :in-theory (enable lemma-for-forcing-logic.proofp-of-clause.aux-limsplit-bldr)
           :expand ((clause.aux-limsplit todo done n)
                    (clause.aux-limsplit nil done n))
           )))

 (defthm forcing-logic.conclusion-of-clause.aux-limsplit-bldr
   (implies (force (and (logic.term-listp todo)
                        (logic.term-listp done)
                        (true-listp todo)
                        (or (consp todo) (consp done))
                        (logic.appeal-listp proofs)
                        (subsetp (clause.clause-list-formulas (clause.aux-limsplit todo done n))
                                 (logic.strip-conclusions proofs))))
            (equal (logic.conclusion (clause.aux-limsplit-bldr todo done proofs n))
                   (cond ((and (consp todo)
                               (consp done))
                          (logic.por (clause.clause-formula todo)
                                     (clause.clause-formula done)))
                         ((consp todo)
                          (clause.clause-formula todo))
                         (t
                          (clause.clause-formula done)))))
   :hints(("Goal"
           :in-theory (enable clause.aux-split-goal)
           :use ((:instance lemma-for-forcing-logic.proofp-of-clause.aux-limsplit-bldr))
           :expand (clause.aux-limsplit nil done n)
           ))))






(defund clause.simple-limsplit-bldr (clause proofs n)
  (declare (xargs :guard (and (logic.term-listp clause)
                              (consp clause)
                              (true-listp clause)
                              (natp n)
                              (logic.appeal-listp proofs)
                              (equal (clause.clause-list-formulas (clause.simple-limsplit clause n))
                                     (logic.strip-conclusions proofs)))
                  :guard-hints (("Goal" :in-theory (enable clause.simple-limsplit)))))
  (clause.aux-limsplit-bldr clause nil proofs n))

(defobligations clause.simple-limsplit-bldr
  (clause.aux-limsplit-bldr))

(defthm forcing-logic.appealp-of-clause.simple-limsplit-bldr
   (implies (force (and (logic.term-listp clause)
                        (consp clause)
                        (true-listp clause)
                        (logic.appeal-listp proofs)
                        (equal (clause.clause-list-formulas (clause.simple-limsplit clause n))
                               (logic.strip-conclusions proofs))))
            (equal (logic.appealp (clause.simple-limsplit-bldr clause proofs n))
                   t))
   :hints(("Goal" :in-theory (enable clause.simple-limsplit
                                     clause.simple-limsplit-bldr))))

(defthm forcing-logic.conclusion-of-clause.simple-limsplit-bldr
   (implies (force (and (logic.term-listp clause)
                        (true-listp clause)
                        (consp clause)
                        (logic.appeal-listp proofs)
                        (equal (clause.clause-list-formulas (clause.simple-limsplit clause n))
                               (logic.strip-conclusions proofs))))
            (equal (logic.conclusion (clause.simple-limsplit-bldr clause proofs n))
                   (clause.clause-formula clause)))
   :rule-classes ((:rewrite :backchain-limit-lst 0))
   :hints(("Goal" :in-theory (enable clause.simple-limsplit
                                     clause.simple-limsplit-bldr))))

(defthm@ forcing-logic.proofp-of-clause.simple-limsplit-bldr
   (implies (force (and (logic.term-listp clause)
                        (true-listp clause)
                        (consp clause)
                        (logic.appeal-listp proofs)
                        (equal (clause.clause-list-formulas (clause.simple-limsplit clause n))
                               (logic.strip-conclusions proofs))
                        ;; ---
                        (logic.term-list-atblp clause atbl)
                        (logic.proof-listp proofs axioms thms atbl)
                        (equal (cdr (lookup 'not atbl)) 1)
                        (equal (cdr (lookup 'iff atbl)) 2)
                        (equal (cdr (lookup 'equal atbl)) 2)
                        (equal (cdr (lookup 'if atbl)) 3)
                        (@obligations clause.simple-limsplit-bldr)
                        ))
            (equal (logic.proofp (clause.simple-limsplit-bldr clause proofs n) axioms thms atbl)
                   t))
   :hints(("Goal" :in-theory (enable clause.simple-limsplit
                                     clause.simple-limsplit-bldr))))



(defund clause.simple-limsplit-bldr-okp (x atbl)
  (declare (xargs :guard (and (logic.appealp x)
                              (logic.arity-tablep atbl))))
  (let ((method     (logic.method x))
        (conclusion (logic.conclusion x))
        (subproofs  (logic.subproofs x))
        (extras     (logic.extras x)))
    (and (equal method 'clause.simple-limsplit-bldr)
         (tuplep 2 extras)
         (let ((clause (first extras))
               (n      (second extras)))
           (and (consp clause)
                (true-listp clause)
                (logic.term-listp clause)
                (logic.term-list-atblp clause atbl)
                (natp n)
                (equal (clause.clause-list-formulas (clause.simple-limsplit clause n))
                       (logic.strip-conclusions subproofs))
                (equal conclusion
                       (clause.clause-formula clause)))))))

(defund clause.simple-limsplit-bldr-high (clause proofs n)
  (declare (xargs :guard (and (logic.term-listp clause)
                              (consp clause)
                              (true-listp clause)
                              (natp n)
                              (logic.appeal-listp proofs)
                              (equal (clause.clause-list-formulas (clause.simple-limsplit clause n))
                                     (logic.strip-conclusions proofs)))))
  (logic.appeal 'clause.simple-limsplit-bldr
                (clause.clause-formula clause)
                (list-fix proofs)
                (list clause n)))

(defobligations clause.simple-limsplit-bldr-okp
  (clause.simple-limsplit-bldr))

(encapsulate
 ()
 (local (in-theory (enable clause.simple-limsplit-bldr-okp)))

 (defthm booleanp-of-clause.simple-limsplit-bldr-okp
   (equal (booleanp (clause.simple-limsplit-bldr-okp x atbl))
          t))

 (defthm clause.simple-limsplit-bldr-okp-of-logic.appeal-identity
   (equal (clause.simple-limsplit-bldr-okp (logic.appeal-identity x) atbl)
          (clause.simple-limsplit-bldr-okp x atbl)))

 (defthmd lemma-1-for-soundness-of-clause.simple-limsplit-bldr-okp
   (implies (and (clause.simple-limsplit-bldr-okp x atbl)
                 (logic.appealp x)
                 (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl))
            (equal (logic.conclusion
                    (clause.simple-limsplit-bldr (first (logic.extras x))
                                                 (logic.provable-list-witness (logic.strip-conclusions (logic.subproofs x))
                                                                              axioms thms atbl)
                                                 (second (logic.extras x))))
                   (logic.conclusion x))))

 (defthmd@ lemma-2-for-soundness-of-clause.simple-limsplit-bldr-okp
   (implies (and (clause.simple-limsplit-bldr-okp x atbl)
                 (logic.appealp x)
                 (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl)
                 (@obligations clause.simple-limsplit-bldr-okp)
                 (equal (cdr (lookup 'not atbl)) 1)
                 (equal (cdr (lookup 'iff atbl)) 2)
                 (equal (cdr (lookup 'equal atbl)) 2)
                 (equal (cdr (lookup 'if atbl)) 3))
            (equal (logic.proofp
                    (clause.simple-limsplit-bldr (first (logic.extras x))
                                                 (logic.provable-list-witness (logic.strip-conclusions (logic.subproofs x))
                                                                              axioms thms atbl)
                                                 (second (logic.extras x)))
                    axioms thms atbl)
                   t)))

 (defthm@ forcing-soundness-of-clause.simple-limsplit-bldr-okp
   (implies (and (clause.simple-limsplit-bldr-okp x atbl)
                 (force (and (logic.appealp x)
                             (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl)
                             (@obligations clause.simple-limsplit-bldr-okp)
                             (equal (cdr (lookup 'not atbl)) 1)
                             (equal (cdr (lookup 'iff atbl)) 2)
                             (equal (cdr (lookup 'equal atbl)) 2)
                             (equal (cdr (lookup 'if atbl)) 3))))
            (equal (logic.provablep (logic.conclusion x) axioms thms atbl)
                   t))
   :hints (("Goal"
            :in-theory (enable lemma-1-for-soundness-of-clause.simple-limsplit-bldr-okp
                               lemma-2-for-soundness-of-clause.simple-limsplit-bldr-okp)
            :use ((:instance forcing-logic.provablep-when-logic.proofp
                             (x (clause.simple-limsplit-bldr
                                 (first (logic.extras x))
                                 (logic.provable-list-witness (logic.strip-conclusions (logic.subproofs x))
                                                              axioms thms atbl)
                                 (second (logic.extras x))))))))))
