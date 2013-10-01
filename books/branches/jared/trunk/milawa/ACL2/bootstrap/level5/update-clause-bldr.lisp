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
(include-book "fuse")
(%interactive)



(defthm lemma-for-forcing-logic.appealp-of-clause.aux-update-clause-bldr
  ;; BOZO unlocalize in update-clause.lisp
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
  :rule-classes nil)



(%autoadmit clause.aux-update-clause-bldr)

(defmacro %clause.aux-update-clause-bldr-induction (todo done t-proofs proof)
  `(%induct (rank ,todo)
            ((not (consp ,todo))
             nil)
            ((and (consp ,todo)
                  (not (consp (cdr ,todo))))
             nil)
            ((and (consp ,todo)
                  (consp (cdr ,todo))
                  (not (consp ,done)))
             (((,todo (cdr ,todo))
               (,done (cons (logic.=lhs (logic.conclusion (car ,t-proofs))) ,done))
               (,t-proofs (cdr ,t-proofs))
               (,proof (clause.aux-update-clause-lemma1-bldr (build.commute-or ,proof) (car ,t-proofs))))))
            ((and (consp ,todo)
                  (consp (cdr ,todo))
                  (consp ,done))
             (((,todo (cdr ,todo))
               (,done (cons (logic.=lhs (logic.conclusion (car ,t-proofs))) ,done))
               (,t-proofs (cdr ,t-proofs))
               (,proof (clause.aux-update-clause-lemma2-bldr ,proof (car ,t-proofs))))))))

(%autoprove clause.aux-update-clause-bldr-under-iff
            (%clause.aux-update-clause-bldr-induction todo done t-proofs proof)
            (%restrict default clause.aux-update-clause-bldr (equal todo 'todo))
            (%enable default logic.term-formula))

(%autoprove lemma-for-forcing-logic.appealp-of-clause.aux-update-clause-bldr
            (%clause.aux-update-clause-bldr-induction todo done t-proofs proof)
            (%restrict default clause.aux-update-clause-bldr (memberp todo '(todo 'nil)))
            (%enable default logic.term-formula))

(%autoprove forcing-logic.appealp-of-clause.aux-update-clause-bldr
            (%use (%instance (%thm lemma-for-forcing-logic.appealp-of-clause.aux-update-clause-bldr))))

(%autoprove forcing-logic.conclusion-of-clause.aux-update-clause-bldr
            (%use (%instance (%thm lemma-for-forcing-logic.appealp-of-clause.aux-update-clause-bldr))))

(%autoprove forcing-logic.proofp-of-clause.aux-update-clause-bldr
            (%clause.aux-update-clause-bldr-induction todo done t-proofs proof)
            (%restrict default clause.aux-update-clause-bldr (memberp todo '(todo 'nil)))
            (%enable default logic.term-formula)
            (%auto :strategy (cleanup split urewrite crewrite dist))
            ;; Oh my, why do we have to do this ?!?  I guess ACL2's expansion heuristics are taking
            ;; care of this for us, but I'm still surprised we need to consider these cases and
            ;; can't just address the proof using one-level expansion of aux-update-clause-bldr.
            ;; Maybe the induction scheme is somehow flawed?
            (%restrict default clause.aux-update-clause-bldr
                       (memberp todo
                                '((cons (logic.=rhs (logic.conclusion (car t-proofs))) (logic.=rhses (logic.strip-conclusions (cdr t-proofs))))
                                  (cons (logic.=rhs (logic.conclusion (car t-proofs))) (logic.=rhses (logic.strip-conclusions (cdr t-proofs))))
                                  (cons (logic.=lhs (logic.~arg (logic.conclusion proof))) 'nil)
                                  (cons (logic.=rhs (logic.conclusion (car t-proofs))) 'nil)))))



(defsection clause.update-clause-bldr
  (%autoadmit clause.update-clause-bldr)
  ;; BOZO have to enable rev-disjunction becuase we never bothered to prove
  ;; anything about it, and we just made it an alias for generic-subset
  ;; instead.  we should consider globally enabling this and the other
  ;; functions like it.
  (local (%enable default clause.update-clause-bldr build.rev-disjunction))
  (%autoprove clause.update-clause-bldr-under-iff)
  (%autoprove forcing-logic.appealp-of-clause.update-clause-bldr)
  (%autoprove forcing-logic.conclusion-of-clause.update-clause-bldr)
  (%autoprove forcing-logic.proofp-of-clause.update-clause-bldr))


(%autoprove logic.formula-list-atblp-of-logic.strip-conclusions-of-cdr-when-logic.provable-listp)

(defsection clause.update-clause-bldr-okp

  (%autoadmit clause.update-clause-bldr-okp)

  (%autoprove booleanp-of-clause.update-clause-bldr-okp
              (%enable default clause.update-clause-bldr-okp))

  (%autoprove clause.update-clause-bldr-okp-of-logic.appeal-identity
              (%enable default clause.update-clause-bldr-okp))

  (local (%enable default backtracking-logic.formula-atblp-rules))
  (local (%disable default
                   forcing-logic.formula-atblp-rules
                   forcing-lookup-of-logic.function-name-free))

  (%autoprove lemma-1-for-soundness-of-clause.update-clause-bldr-okp
              (%enable default clause.update-clause-bldr-okp))

  (%autoprove lemma-2-for-soundness-of-clause.update-clause-bldr-okp
              (%enable default clause.update-clause-bldr-okp))

  (%autoprove forcing-soundness-of-clause.update-clause-bldr-okp
              (%disable default [OUTSIDE]CONSP-OF-LOGIC.STRIP-CONCLUSIONS) ;; why is this a problem??
              (%enable default
                       lemma-1-for-soundness-of-clause.update-clause-bldr-okp
                       lemma-2-for-soundness-of-clause.update-clause-bldr-okp)
              (%use (%instance (%thm forcing-logic.provablep-when-logic.proofp)
                               (x (clause.update-clause-bldr
                                   (logic.=rhses
                                    (logic.strip-conclusions
                                     (logic.provable-list-witness (logic.strip-conclusions (cdr (logic.subproofs x)))
                                                                  axioms thms atbl)))
                                   (logic.provable-witness (logic.conclusion (car (logic.subproofs x))) axioms thms atbl)
                                   (logic.provable-list-witness (logic.strip-conclusions (cdr (logic.subproofs x)))
                                                                axioms thms atbl)))))
              (%forcingp nil)
              (%auto :strategy (cleanup split crewrite))
              (%enable default clause.update-clause-bldr-okp)
              (%auto)))
