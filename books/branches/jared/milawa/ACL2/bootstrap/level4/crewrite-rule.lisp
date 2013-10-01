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
(include-book "clause-basics")
(include-book "rulep")
(%interactive)


(defthm LOGIC.PEQUAL-LIST-OF-CONS-AND-CONS-gross-right
  (implies (syntaxp (logic.constantp y))
           (equal (logic.pequal-list (cons a x) y)
                  (if (consp y)
                      (CONS (LOGIC.PEQUAL a (CAR Y))
                            (LOGIC.PEQUAL-LIST x (CDR Y)))
                    nil)))
  :hints(("Goal" :expand (logic.pequal-list (cons a x) y))))

(%autoprove LOGIC.PEQUAL-LIST-OF-CONS-AND-CONS-gross-right)

;(local (%disable default LOGIC.FUNCTION-OF-CONS-WITH-DEFECTIVELY-MERGED-CONSTANT))



(%deftheorem rw.crewrite-rule-lemma)

(encapsulate
 ()
 (local (%enable default bust-up-cdr-of-logic.function-args-expensive))
 (%defderiv rw.crewrite-rule-lemma-bldr)
 (%defderiv rw.disjoined-crewrite-rule-lemma-bldr))

(defsection rw.crewrite-rule-lemma-list-bldr
  (%autoadmit rw.crewrite-rule-lemma-list-bldr)
  (%autoprove forcing-logic.appeal-listp-of-rw.crewrite-rule-lemma-list-bldr
              (%cdr-induction x)
              (%restrict default rw.crewrite-rule-lemma-list-bldr (equal x 'x)))
  (%autoprove forcing-logic.strip-conclusions-of-rw.crewrite-rule-lemma-list-bldr
              (%cdr-induction x)
              (%restrict default rw.crewrite-rule-lemma-list-bldr (equal x 'x))
              (%enable default logic.negate-term)
              (%disable default
                        formula-decomposition
                        expensive-term/formula-inference))
  (%autoprove forcing-logic.proof-listp-of-rw.crewrite-rule-lemma-list-bldr
              (%cdr-induction x)
              (%restrict default rw.crewrite-rule-lemma-list-bldr (equal x 'x))))

(defsection rw.disjoined-crewrite-rule-lemma-list-bldr
  (%autoadmit rw.disjoined-crewrite-rule-lemma-list-bldr)
  (%autoprove forcing-logic.appeal-listp-of-rw.disjoined-crewrite-rule-lemma-list-bldr
              (%cdr-induction x)
              (%restrict default rw.disjoined-crewrite-rule-lemma-list-bldr (equal x 'x)))
  (%autoprove forcing-logic.strip-conclusions-of-rw.disjoined-crewrite-rule-lemma-list-bldr
              (%cdr-induction x)
              (%restrict default rw.disjoined-crewrite-rule-lemma-list-bldr (equal x 'x))
              (%enable default logic.negate-term))
  (%autoprove forcing-logic.proof-listp-of-rw.disjoined-crewrite-rule-lemma-list-bldr
              (%cdr-induction x)
              (%restrict default rw.disjoined-crewrite-rule-lemma-list-bldr (equal x 'x))))




(defsection rw.compile-crewrite-rule-trace-lemma1

  (defthmd lemma-for-logic.appealp-of-rw.compile-crewrite-rule-trace-lemma1
    ;; BOZO unlocalize in ACL2 model
    (implies (and (logic.all-negationsp a)
                  (logic.all-negationsp c)
                  (force (equal (len a) (len c))) ;; not always true, we force anyway
                  (force (equal (len b) (len d))) ;; not always true, we force anyway
                  (force (logic.formula-listp a))
                  (force (logic.formula-listp b))
                  (force (logic.formula-listp c))
                  (force (logic.formula-listp d)))
             (equal (equal (logic.disjoin-formulas (app a b))
                           (logic.disjoin-formulas (app c d)))
                    (and (equal (list-fix a) (list-fix c))
                         (equal (list-fix b) (list-fix d))))))

  (defthmd lemma2-for-logic.appealp-of-rw.compile-crewrite-rule-trace-lemma1
    ;; BOZO unlocalize in ACL2 model
    (implies (equal (logic.substitute-list (rw.hyp-list-terms (rw.rule->hyps rule)) sigma)
                    (strip-firsts (logic.strip-function-args (logic.=lhses (logic.strip-conclusions proofs)))))
             (equal (len proofs)
                    (len (rw.rule->hyps rule))))
    :hints(("Goal"
            :in-theory (disable len-of-strip-firsts len-of-logic.substitute-list)
            :use ((:instance len-of-strip-firsts
                             (x (logic.strip-function-args (logic.=lhses (logic.strip-conclusions proofs)))))
                  (:instance len-of-logic.substitute-list
                             (x (rw.hyp-list-terms (rw.rule->hyps rule))))))))

  (%autoadmit rw.compile-crewrite-rule-trace-lemma1)
  (local (%enable default
                  rw.compile-crewrite-rule-trace-lemma1
                  rw.rule-clause
                  redefinition-of-logic.term-list-formulas))

  (%autoprove lemma-for-logic.appealp-of-rw.compile-crewrite-rule-trace-lemma1)

  (%autoprove lemma2-for-logic.appealp-of-rw.compile-crewrite-rule-trace-lemma1
              (%disable default
                        len-of-strip-firsts
                        len-of-logic.substitute-list
                        [outside]len-of-strip-firsts
                        [outside]len-of-logic.substitute-list)
              (%use (%instance (%thm len-of-strip-firsts)
                               (x (logic.strip-function-args (logic.=lhses (logic.strip-conclusions proofs))))))
              (%use (%instance (%thm len-of-logic.substitute-list)
                               (x (rw.hyp-list-terms (rw.rule->hyps rule))))))
  (local (%enable default
                  lemma-for-logic.appealp-of-rw.compile-crewrite-rule-trace-lemma1
                  lemma2-for-logic.appealp-of-rw.compile-crewrite-rule-trace-lemma1))
  ;; Speed hack
  (local (%disable default
                   consp-when-memberp-of-logic.sigmap
                   consp-when-memberp-of-logic.sigma-atblp
                   all-equalp-of-subsetp-when-all-equalp))
  (%autoprove logic.appealp-of-rw.compile-crewrite-rule-trace-lemma1)
  (%autoprove logic.conclusion-of-rw.compile-crewrite-rule-trace-lemma1)
  (%autoprove logic.proofp-of-rw.compile-crewrite-rule-trace-lemma1
              (%enable default rw.rule-env-okp)))


(defsection rw.compile-crewrite-rule-trace-lemma2

  (defthmd lemma-2-for-logic.appealp-of-rw.compile-crewrite-rule-trace-lemma2
    ;; BOZO unlocalize.  We use lemma-1 from lemma1.
    (implies (equal (logic.substitute-list (rw.hyp-list-terms (rw.rule->hyps rule)) sigma)
                    (strip-firsts (logic.strip-function-args (logic.=lhses (logic.vrhses (logic.strip-conclusions proofs))))))
             (equal (len proofs)
                    (len (rw.rule->hyps rule))))
    :hints(("Goal"
            :in-theory (disable len-of-strip-firsts len-of-logic.substitute-list)
            :use ((:instance len-of-strip-firsts
                             (x (logic.strip-function-args (logic.=lhses (logic.vrhses (logic.strip-conclusions proofs))))))
                  (:instance len-of-logic.substitute-list
                             (x (rw.hyp-list-terms (rw.rule->hyps rule))))))))

  (%autoadmit rw.compile-crewrite-rule-trace-lemma2)

  (local (%enable default
                  rw.compile-crewrite-rule-trace-lemma2
                  rw.rule-clause
                  redefinition-of-logic.term-list-formulas))

  (%autoprove lemma-2-for-logic.appealp-of-rw.compile-crewrite-rule-trace-lemma2
              (%disable default
                        len-of-strip-firsts
                        len-of-logic.substitute-list
                        [outside]len-of-strip-firsts
                        [outside]len-of-logic.substitute-list)
              (%use (%instance (%thm len-of-strip-firsts)
                               (x (logic.strip-function-args (logic.=lhses (logic.vrhses (logic.strip-conclusions proofs)))))))
              (%use (%instance (%thm len-of-logic.substitute-list)
                               (x (rw.hyp-list-terms (rw.rule->hyps rule))))))

  (local (%enable default
                  lemma-for-logic.appealp-of-rw.compile-crewrite-rule-trace-lemma1
                  lemma-2-for-logic.appealp-of-rw.compile-crewrite-rule-trace-lemma2))

  (local (%disable default
                   consp-when-memberp-of-logic.sigmap
                   consp-when-memberp-of-logic.sigma-atblp
                   all-equalp-of-subsetp-when-all-equalp))

  (%autoprove forcing-logic.appealp-of-rw.compile-crewrite-rule-trace-lemma2)
  (%autoprove forcing-logic.conclusion-of-rw.compile-crewrite-rule-trace-lemma2)
  (%autoprove forcing-logic.proofp-of-rw.compile-crewrite-rule-trace-lemma2
              (%enable default rw.rule-env-okp)))



(defsection rw.compile-crewrite-rule-trace-lemma1-okp
  (%autoadmit rw.compile-crewrite-rule-trace-lemma1-okp)
  (%autoprove booleanp-of-rw.compile-crewrite-rule-trace-lemma1-okp
              (%enable default rw.compile-crewrite-rule-trace-lemma1-okp))
  (%autoprove rw.compile-crewrite-rule-trace-lemma1-okp-of-logic.appeal-identity
              (%enable default rw.compile-crewrite-rule-trace-lemma1-okp))
  (local (%enable default backtracking-logic.formula-atblp-rules))
  (local (%disable default
                   forcing-logic.formula-atblp-rules
                   forcing-lookup-of-logic.function-name-free))
  (%autoprove lemma-1-for-soundness-of-rw.compile-crewrite-rule-trace-lemma1-okp
              (%enable default rw.compile-crewrite-rule-trace-lemma1-okp))
  (%autoprove lemma-2-for-soundness-of-rw.compile-crewrite-rule-trace-lemma1-okp
              (%enable default rw.compile-crewrite-rule-trace-lemma1-okp))
  (%autoprove forcing-soundness-of-rw.compile-crewrite-rule-trace-lemma1-okp
              (%enable default
                       lemma-1-for-soundness-of-rw.compile-crewrite-rule-trace-lemma1-okp
                       lemma-2-for-soundness-of-rw.compile-crewrite-rule-trace-lemma1-okp)
              (%use (%instance (%thm forcing-logic.provablep-when-logic.proofp)
                               (x (rw.compile-crewrite-rule-trace-lemma1 (first (logic.extras x))
                                                                         (second (logic.extras x))
                                                                         (logic.provable-list-witness
                                                                          (logic.strip-conclusions (logic.subproofs x))
                                                                          axioms thms atbl)))))
              (%auto :strategy (cleanup split crewrite))
              (%enable default rw.compile-crewrite-rule-trace-lemma1-okp)
              (%auto :strategy (cleanup split crewrite))))


(defsection rw.compile-crewrite-rule-trace-lemma2-okp
  (%autoadmit rw.compile-crewrite-rule-trace-lemma2-okp)
  (%autoprove booleanp-of-rw.compile-crewrite-rule-trace-lemma2-okp
              (%enable default rw.compile-crewrite-rule-trace-lemma2-okp))
  (%autoprove rw.compile-crewrite-rule-trace-lemma2-okp-of-logic.appeal-identity
              (%enable default rw.compile-crewrite-rule-trace-lemma2-okp))
  (%autoprove lemma-1-for-soundness-of-rw.compile-crewrite-rule-trace-lemma2-okp
              (%enable default rw.compile-crewrite-rule-trace-lemma2-okp))
  (%autoprove lemma-2-for-soundness-of-rw.compile-crewrite-rule-trace-lemma2-okp
              (%enable default rw.compile-crewrite-rule-trace-lemma2-okp))
  (%autoprove forcing-soundness-of-rw.compile-crewrite-rule-trace-lemma2-okp
              (%enable default
                       lemma-1-for-soundness-of-rw.compile-crewrite-rule-trace-lemma2-okp
                       lemma-2-for-soundness-of-rw.compile-crewrite-rule-trace-lemma2-okp)
              (%use (%instance (%thm forcing-logic.provablep-when-logic.proofp)
                               (x (rw.compile-crewrite-rule-trace-lemma2 (first (logic.extras x))
                                                                         (second (logic.extras x))
                                                                         (third (logic.extras x))
                                                                         (logic.provable-list-witness
                                                                          (logic.strip-conclusions (logic.subproofs x))
                                                                          axioms thms atbl)))))
              (%auto :strategy (cleanup split crewrite))
              (%enable default rw.compile-crewrite-rule-trace-lemma2-okp)
              (%auto :strategy (cleanup split crewrite))))

