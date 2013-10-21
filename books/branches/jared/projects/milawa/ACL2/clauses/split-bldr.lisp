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
(include-book "split")
(include-book "aux-split-bldr")
(include-book "aux-limsplit-bldr")
(include-book "update-clause-bldr")
(include-book "if-lifting/lift-bldr")
(include-book "if-lifting/limlift-bldr")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)



(defund clause.split-bldr (liftp liftlimit splitlimit x proofs)
  ;; Suppose x is a clause and we have proofs of all the clauses x splits
  ;; into.  Then, build a proof of x.
  (declare (xargs :guard (and (logic.term-listp x)
                              (true-listp x)
                              (consp x)
                              (natp liftlimit)
                              (natp splitlimit)
                              (logic.appeal-listp proofs)
                              (equal (clause.clause-list-formulas (cdr (clause.split liftp liftlimit splitlimit x)))
                                     (logic.strip-conclusions proofs)))
                  :verify-guards nil))
  (let* ((lifted-clause     (if liftp
                                (if (equal liftlimit 0)
                                    (clause.fast-lift-term-list$ x nil)
                                  (clause.fast-limlift-term-list$ x liftlimit nil))
                              x))
         (split-clauses     (if (equal splitlimit 0)
                                (clause.simple-split lifted-clause)
                              (clause.simple-limsplit lifted-clause splitlimit)))
         (clean-proofs      (clause.clean-clauses-bldr split-clauses proofs))
         (split-proof       (if (equal splitlimit 0)
                                (clause.simple-split-bldr lifted-clause clean-proofs)
                              (clause.simple-limsplit-bldr lifted-clause clean-proofs splitlimit))))
    (if liftp
        (let* ((lit-proofs   (if (equal liftlimit 0)
                                 (clause.fast-lift-term-list-bldr$ x nil)
                               (clause.fast-limlift-term-list-bldr$ x liftlimit nil)))
               (update-proof (clause.update-clause-bldr lifted-clause split-proof lit-proofs))
               (rev-proof    (build.rev-disjunction (logic.fast-term-list-formulas$ x nil) update-proof)))
          (ACL2::prog2$
           (ACL2::cw! ";; Split step: ~s0~|"
                      (STR::ncat "Inputs " (unbounded-rank proofs) "; "
                                "Unclean " (- (unbounded-rank clean-proofs) (unbounded-rank proofs)) "; "
                                "Unsplit " (- (unbounded-rank split-proof) (unbounded-rank clean-proofs)) "; "
                                "Unlift " (unbounded-rank lit-proofs) "; "
                                "Update " (- (unbounded-rank update-proof)
                                             (ACL2::+ (unbounded-rank split-proof) (unbounded-rank lit-proofs))) "; "
                                "Rev " (- (unbounded-rank rev-proof) (unbounded-rank update-proof)) "; "
                                "Outputs " (unbounded-rank rev-proof) "."))
           rev-proof))
      (ACL2::prog2$
       (ACL2::cw! ";; Split step: ~s0~|"
                  (STR::ncat "Inputs " (unbounded-rank proofs) "; "
                            "Unclean " (- (unbounded-rank clean-proofs) (unbounded-rank proofs)) "; "
                            "Unsplit " (- (unbounded-rank split-proof) (unbounded-rank clean-proofs)) "; "
                            "Outputs " (unbounded-rank split-proof) "."))
       split-proof))))

(defobligations clause.split-bldr
  (clause.lift-term-list-bldr
   clause.limlift-term-list-bldr
   clause.simple-split-bldr
   clause.simple-limsplit-bldr
   clause.update-clause-bldr
   clause.clean-clauses-bldr
   build.rev-disjunction))

(encapsulate
 ()
 (local (in-theory (enable clause.split clause.split-bldr)))

 (verify-guards clause.split-bldr)

 (defthm forcing-logic.appealp-of-clause.split-bldr
   (implies (force (and (logic.term-listp x)
                        (true-listp x)
                        (consp x)
                        (logic.appeal-listp proofs)
                        (equal (clause.clause-list-formulas (cdr (clause.split liftp liftlimit splitlimit x)))
                               (logic.strip-conclusions proofs))))
            (equal (logic.appealp (clause.split-bldr liftp liftlimit splitlimit x proofs))
                   t)))

 (defthm forcing-logic.conclusion-of-clause.split-bldr
   (implies (force (and (logic.term-listp x)
                        (true-listp x)
                        (consp x)
                        (logic.appeal-listp proofs)
                        (equal (clause.clause-list-formulas (cdr (clause.split liftp liftlimit splitlimit x)))
                               (logic.strip-conclusions proofs))
                        ))
            (equal (logic.conclusion (clause.split-bldr liftp liftlimit splitlimit x proofs))
                   (clause.clause-formula x))))

 (defthm@ forcing-logic.proofp-of-clause.split-bldr
   (implies (force (and (logic.term-listp x)
                        (true-listp x)
                        (consp x)
                        (logic.appeal-listp proofs)
                        (equal (clause.clause-list-formulas (cdr (clause.split liftp liftlimit splitlimit x)))
                               (logic.strip-conclusions proofs))
                        ;; ---
                        (logic.term-list-atblp x atbl)
                        (logic.proof-listp proofs axioms thms atbl)
                        (equal (cdr (lookup 'if atbl)) 3)
                        (equal (cdr (lookup 'iff atbl)) 2)
                        (equal (cdr (lookup 'not atbl)) 1)
                        (equal (cdr (lookup 'equal atbl)) 2)
                        (@obligations clause.split-bldr)))
            (equal (logic.proofp (clause.split-bldr liftp liftlimit splitlimit x proofs) axioms thms atbl)
                   t))))



(deflist logic.appeal-list-listp (x)
  ;; BOZO find me a home
  (logic.appeal-listp x)
  :elementp-of-nil t)

(defprojection
  ;; BOZO find me a home
  :list (logic.strip-conclusions-list x)
  :element (logic.strip-conclusions x)
  :guard (logic.appeal-list-listp x)
  :nil-preservingp t)

(encapsulate
 ()
 ;; BOZO find me a home
 (local (in-theory (disable redefinition-of-clause.clause-list-formulas)))
 (defprojection
   :list (clause.clause-list-list-formulas x)
   :element (clause.clause-list-formulas x)
   :guard (and (logic.term-list-list-listp x)
               (cons-list-listp x))
   :nil-preservingp t))

(deflist logic.proof-list-listp (x axioms thms atbl)
  ;; BOZO find me a home
  (logic.proof-listp x axioms thms atbl)
  :guard (and (logic.appeal-list-listp x)
              (logic.formula-listp axioms)
              (logic.formula-listp thms)
              (logic.arity-tablep atbl))
  :elementp-of-nil t)

(defund clause.split-list-bldr (liftp liftlimit splitlimit x proofs)
  (declare (xargs :guard (and (logic.term-list-listp x)
                              (true-list-listp x)
                              (cons-listp x)
                              (natp liftlimit)
                              (natp splitlimit)
                              (logic.appeal-list-listp proofs)
                              (equal (clause.clause-list-list-formulas (cdr (clause.split-list liftp liftlimit splitlimit x)))
                                     (logic.strip-conclusions-list proofs)))))
  (if (consp x)
      (cons (ACL2::prog2$ (ACL2::cw "; Building proof of clause #~x0.~%" (fast-len x 0))
                          (clause.split-bldr liftp liftlimit splitlimit (car x) (car proofs)))
            (clause.split-list-bldr liftp liftlimit splitlimit (cdr x) (cdr proofs)))
    nil))

(defobligations clause.split-list-bldr
  (clause.split-bldr))

(defthm forcing-logic.appeal-listp-of-clause.split-list-bldr
   (implies (force (and (logic.term-list-listp x)
                        (true-list-listp x)
                        (cons-listp x)
                        (logic.appeal-list-listp proofs)
                        (equal (clause.clause-list-list-formulas (cdr (clause.split-list liftp liftlimit splitlimit x)))
                               (logic.strip-conclusions-list proofs))
                        ))
            (equal (logic.appeal-listp (clause.split-list-bldr liftp liftlimit splitlimit x proofs))
                   t))
   :hints(("Goal" :in-theory (enable clause.split-list clause.split-list-bldr))))

(defthm forcing-logic.strip-conclusions-of-clause.split-list-bldr
   (implies (force (and (logic.term-list-listp x)
                        (true-list-listp x)
                        (cons-listp x)
                        (logic.appeal-list-listp proofs)
                        (equal (clause.clause-list-list-formulas (cdr (clause.split-list liftp liftlimit splitlimit x)))
                               (logic.strip-conclusions-list proofs))
                        ))
            (equal (logic.strip-conclusions (clause.split-list-bldr liftp liftlimit splitlimit x proofs))
                   (clause.clause-list-formulas x)))
   :rule-classes ((:rewrite :backchain-limit-lst 0))
   :hints(("Goal"  :in-theory (enable clause.split-list clause.split-list-bldr))))

(defthm@ forcing-logic.proof-listp-of-clause.split-list-bldr
   (implies (force (and (logic.term-list-listp x)
                        (true-list-listp x)
                        (cons-listp x)
                        (logic.appeal-list-listp proofs)
                        (equal (clause.clause-list-list-formulas (cdr (clause.split-list liftp liftlimit splitlimit x)))
                               (logic.strip-conclusions-list proofs))
                        ;; ---
                        (logic.term-list-list-atblp x atbl)
                        (logic.proof-list-listp proofs axioms thms atbl)
                        (equal (cdr (lookup 'if atbl)) 3)
                        (equal (cdr (lookup 'iff atbl)) 2)
                        (equal (cdr (lookup 'not atbl)) 1)
                        (equal (cdr (lookup 'equal atbl)) 2)
                        (@obligations clause.split-list-bldr)
                        ))
            (equal (logic.proof-listp (clause.split-list-bldr liftp liftlimit splitlimit x proofs) axioms thms atbl)
                   t))
   :hints(("Goal" :in-theory (enable clause.split-list clause.split-list-bldr))))




(defund clause.split-bldr-okp (x atbl)
  (declare (xargs :guard (and (logic.appealp x)
                              (logic.arity-tablep atbl))))
  (let ((method     (logic.method x))
        (conclusion (logic.conclusion x))
        (subproofs  (logic.subproofs x))
        (extras     (logic.extras x)))
    (and (equal method 'clause.split-bldr)
         (tuplep 4 extras)
         (let ((liftp      (first extras))
               (liftlimit  (second extras))
               (splitlimit (third extras))
               (clause     (fourth extras)))
           (and (natp liftlimit)
                (natp splitlimit)
                (logic.term-listp clause)
                (logic.term-list-atblp clause atbl)
                (true-listp clause)
                (consp clause)
                (equal conclusion (clause.clause-formula clause))
                (equal (clause.clause-list-formulas (cdr (clause.split liftp liftlimit splitlimit clause)))
                       (logic.strip-conclusions subproofs)))))))

(defund clause.split-bldr-high (liftp liftlimit splitlimit x proofs)
  (declare (xargs :guard (and (logic.term-listp x)
                              (true-listp x)
                              (consp x)
                              (natp liftlimit)
                              (natp splitlimit)
                              (logic.appeal-listp proofs)
                              (equal (clause.clause-list-formulas (cdr (clause.split liftp liftlimit splitlimit x)))
                                     (logic.strip-conclusions proofs)))))
  (logic.appeal 'clause.split-bldr
                (clause.clause-formula x)
                (list-fix proofs)
                (list liftp liftlimit splitlimit x)))

(defobligations clause.split-bldr-okp
  (clause.split-bldr))

(encapsulate
 ()
 (local (in-theory (enable clause.split-bldr-okp)))

 (defthm booleanp-of-clause.split-bldr-okp
   (equal (booleanp (clause.split-bldr-okp x atbl))
          t))

 (defthm clause.split-bldr-okp-of-logic.appeal-identity
   (equal (clause.split-bldr-okp (logic.appeal-identity x) atbl)
          (clause.split-bldr-okp x atbl)))

 (defthmd lemma-1-for-soundness-of-clause.split-bldr-okp
   (implies (and (clause.split-bldr-okp x atbl)
                 (logic.appealp x)
                 (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl))
            (equal (logic.conclusion
                    (clause.split-bldr (first (logic.extras x))
                                       (second (logic.extras x))
                                       (third (logic.extras x))
                                       (fourth (logic.extras x))
                                       (logic.provable-list-witness (logic.strip-conclusions (logic.subproofs x))
                                                                    axioms thms atbl)))
                   (logic.conclusion x))))

 (defthmd@ lemma-2-for-soundness-of-clause.split-bldr-okp
   (implies (and (clause.split-bldr-okp x atbl)
                 (logic.appealp x)
                 (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl)
                 (@obligations clause.split-bldr-okp)
                 (equal (cdr (lookup 'not atbl)) 1)
                 (equal (cdr (lookup 'equal atbl)) 2)
                 (equal (cdr (lookup 'iff atbl)) 2)
                 (equal (cdr (lookup 'if atbl)) 3))
            (equal (logic.proofp
                    (clause.split-bldr (first (logic.extras x))
                                       (second (logic.extras x))
                                       (third (logic.extras x))
                                       (fourth (logic.extras x))
                                       (logic.provable-list-witness (logic.strip-conclusions (logic.subproofs x))
                                                                    axioms thms atbl))
                    axioms thms atbl)
                   t)))

 (defthm@ forcing-soundness-of-clause.split-bldr-okp
   (implies (and (clause.split-bldr-okp x atbl)
                 (force (and (logic.appealp x)
                             (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl)
                             (@obligations clause.split-bldr-okp)
                             (equal (cdr (lookup 'not atbl)) 1)
                             (equal (cdr (lookup 'iff atbl)) 2)
                             (equal (cdr (lookup 'equal atbl)) 2)
                             (equal (cdr (lookup 'if atbl)) 3))))
            (equal (logic.provablep (logic.conclusion x) axioms thms atbl)
                   t))
   :hints (("Goal"
            :in-theory (enable lemma-1-for-soundness-of-clause.split-bldr-okp
                               lemma-2-for-soundness-of-clause.split-bldr-okp)
            :use ((:instance forcing-logic.provablep-when-logic.proofp
                             (x (clause.split-bldr (first (logic.extras x))
                                                   (second (logic.extras x))
                                                   (third (logic.extras x))
                                                   (fourth (logic.extras x))
                                                   (logic.provable-list-witness (logic.strip-conclusions (logic.subproofs x))
                                                                                axioms thms atbl)))))))))


