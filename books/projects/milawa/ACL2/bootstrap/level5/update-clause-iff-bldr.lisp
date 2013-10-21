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
(include-book "update-clause-bldr") ;; BOZO needed for rev-disjunction for now, stupid.
(%interactive)

(local (%enable default build.rev-disjunction))

(%autoadmit clause.aux-update-clause-iff-bldr)

(defmacro %clause.aux-update-clause-iff-bldr-induction (todo done t-proofs proof)
  `(%induct (rank ,todo)
            ((not (consp ,todo))
             nil)
            ((and (consp ,todo)
                  (not (consp (cdr ,todo)))
                  (not (consp ,done)))
             nil)
            ((and (consp ,todo)
                  (not (consp (cdr ,todo)))
                  (consp ,done))
             (((,todo (cdr ,todo))
               (,done (cons (first (logic.function-args (logic.=lhs (logic.conclusion (car ,t-proofs)))))
                            ,done))
               (,t-proofs (cdr ,t-proofs))
               (,proof (clause.aux-update-clause-iff-lemma1-bldr ,proof (car ,t-proofs))))))
            ((and (consp ,todo)
                  (consp (cdr ,todo))
                  (not (consp ,done)))
             (((,todo (cdr ,todo))
               (,done (cons (first (logic.function-args (logic.=lhs (logic.conclusion (car ,t-proofs)))))
                            ,done))
               (,t-proofs (cdr ,t-proofs))
               (,proof (clause.aux-update-clause-iff-lemma1-bldr (build.commute-or ,proof) (car ,t-proofs))))))
            ((and (consp ,todo)
                  (consp (cdr ,todo))
                  (consp ,done))
             (((,todo (cdr ,todo))
               (,done (cons (first (logic.function-args (logic.=lhs (logic.conclusion (car ,t-proofs)))))
                            ,done))
               (,t-proofs (cdr ,t-proofs))
               (,proof (clause.aux-update-clause-iff-lemma2-bldr ,proof (car ,t-proofs))))))))

(%autoprove clause.aux-update-clause-iff-bldr-under-iff
            (%clause.aux-update-clause-iff-bldr-induction todo done t-proofs proof)
            (%restrict default clause.aux-update-clause-iff-bldr (equal todo 'todo))
            (%enable default logic.term-formula))

(defthm lemma-1-for-forcing-logic.appealp-of-clause.aux-update-clause-iff-bldr
  ;; BOZO unlocalize this
  (implies (and (all-equalp 2 (strip-lens (logic.strip-function-args (logic.=lhses (logic.strip-conclusions x)))))
                (force (and (logic.appeal-listp x)
                            (logic.all-atomicp (logic.strip-conclusions x))
                            (logic.all-functionsp (logic.=lhses (logic.strip-conclusions x))))))
           (equal (consp (cdr (logic.function-args (logic.=lhs (logic.conclusion (car x))))))
                  (consp x))))

(%autoprove lemma-1-for-forcing-logic.appealp-of-clause.aux-update-clause-iff-bldr
           (%forcingp nil))

(defthm lemma-for-forcing-logic.appealp-of-clause.aux-update-clause-iff-bldr
  ;; BOZO unlocalize this
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
  ;; Gonna need a different theory hint.
  :rule-classes nil)

(%autoprove lemma-for-forcing-logic.appealp-of-clause.aux-update-clause-iff-bldr
            (%clause.aux-update-clause-iff-bldr-induction todo done t-proofs proof)
            (%auto :strategy (cleanup urewrite split))
            (%restrict default clause.aux-update-clause-iff-bldr (equal todo 'todo))
            (%enable default logic.term-formula)
            (%auto :strategy (cleanup urewrite split))
            (%forcingp nil)
            (%auto) ;; out of steps
            (%forcingp t)
            (%auto))

(%autoprove forcing-logic.appealp-of-clause.aux-update-clause-iff-bldr
            (%use (%instance (%thm lemma-for-forcing-logic.appealp-of-clause.aux-update-clause-iff-bldr))))

(%autoprove forcing-logic.conclusion-of-clause.aux-update-clause-iff-bldr
            (%use (%instance (%thm lemma-for-forcing-logic.appealp-of-clause.aux-update-clause-iff-bldr))))

(%autoprove forcing-logic.proofp-of-clause.aux-update-clause-iff-bldr
            (%clause.aux-update-clause-iff-bldr-induction todo done t-proofs proof)
            (%auto :strategy (cleanup urewrite split))
            (%restrict default clause.aux-update-clause-iff-bldr (equal todo 'todo))
            (%enable default logic.term-formula)
            (%auto :strategy (cleanup urewrite split))
            (%forcingp nil)
            (%auto)
            (%forcingp t)
            (%auto))





(defsection clause.update-clause-iff-bldr
  (%autoadmit clause.update-clause-iff-bldr)
  (local (%enable default
                  strip-lens-of-rev
                  clause.update-clause-iff-bldr))
  (local (%disable default
                   rev-of-logic.strip-conclusions
                   rev-of-logic.=lhses
                   rev-of-logic.strip-function-args
                   rev-of-strip-lens))
  (%autoprove clause.update-clause-iff-bldr-under-iff)
  (%autoprove forcing-logic.appealp-of-clause.update-clause-iff-bldr)
  (%autoprove forcing-logic.conclusion-of-clause.update-clause-iff-bldr)
  (%autoprove forcing-logic.proofp-of-clause.update-clause-iff-bldr))




(defsection clause.update-clause-iff-bldr-okp

  (%autoadmit clause.update-clause-iff-bldr-okp)

  (%autoprove booleanp-of-clause.update-clause-iff-bldr-okp
              (%enable default clause.update-clause-iff-bldr-okp))

  (%autoprove clause.update-clause-iff-bldr-okp-of-logic.appeal-identity
              (%enable default clause.update-clause-iff-bldr-okp))

  (local (%enable default backtracking-logic.formula-atblp-rules))
  (local (%disable default
                   forcing-logic.formula-atblp-rules
                   forcing-lookup-of-logic.function-name-free))

  (%autoprove lemma-1-for-soundness-of-clause.update-clause-iff-bldr-okp
              (%enable default clause.update-clause-iff-bldr-okp))

  (%autoprove lemma-2-for-soundness-of-clause.update-clause-iff-bldr-okp
              (%enable default clause.update-clause-iff-bldr-okp))

  (%autoprove forcing-soundness-of-clause.update-clause-iff-bldr-okp
              (%enable default
                       lemma-1-for-soundness-of-clause.update-clause-iff-bldr-okp
                       lemma-2-for-soundness-of-clause.update-clause-iff-bldr-okp
                       clause.update-clause-iff-bldr-okp)
              (%use (%instance (%thm forcing-logic.provablep-when-logic.proofp)
                               (x (clause.update-clause-iff-bldr
                                   (strip-seconds
                                    (logic.strip-function-args
                                     (logic.=lhses
                                      (logic.strip-conclusions
                                       (logic.provable-list-witness (logic.strip-conclusions (cdr (logic.subproofs x)))
                                                                    axioms thms atbl)))))
                                   (logic.provable-witness (logic.conclusion (car (logic.subproofs x))) axioms thms atbl)
                                   (logic.provable-list-witness (logic.strip-conclusions (cdr (logic.subproofs x)))
                                                                axioms thms atbl)))))))

