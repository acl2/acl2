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
(include-book "skeletonp")
(include-book "replace-subterm")
(%interactive)

(%autoadmit tactic.conditional-eqsubst-okp)
(%autoadmit tactic.conditional-eqsubst-env-okp)

(%autoprove booleanp-of-tactic.conditional-eqsubst-okp
            (%enable default tactic.conditional-eqsubst-okp))

(%autoprove booleanp-of-tactic.conditional-eqsubst-env-okp
            (%enable default tactic.conditional-eqsubst-env-okp))



(%autoadmit tactic.conditional-eqsubst-tac)

(%autoprove forcing-tactic.skeletonp-of-tactic.conditional-eqsubst-tac
            (%enable default tactic.conditional-eqsubst-tac))

(%autoprove forcing-tactic.conditional-eqsubst-okp-of-tactic.conditional-eqsubst-tac
            (%enable default
                     tactic.conditional-eqsubst-tac
                     tactic.conditional-eqsubst-okp))

(%autoprove forcing-tactic.conditional-eqsubst-env-okp-of-tactic.conditional-eqsubst-tac
            (%enable default
                     tactic.conditional-eqsubst-tac
                     tactic.conditional-eqsubst-env-okp))


;; BOZO consider moving to level4 or something?
(%defderiv tactic.conditional-eqsubst-lemma1)




(%autoadmit tactic.conditional-eqsubst-bldr)

(encapsulate
 ()
 (local (%enable default tactic.conditional-eqsubst-bldr))
 (%autoprove tactic.conditional-eqsubst-bldr-under-iff)
 (%autoprove forcing-logic.appealp-of-tactic.conditional-eqsubst-bldr)
 (%autoprove forcing-logic.conclusion-of-tactic.conditional-eqsubst-bldr)
 (%autoprove forcing-logic.proofp-of-tactic.conditional-eqsubst-bldr))






;; BOZO unlocalize/rename these in tactics/conditional-eqsubst.lisp

(defthmd crock1-for-tactic.conditional-eqsubst-compile
  (implies (equal (clause.clause-list-formulas goals) (logic.strip-conclusions proofs))
           (equal (logic.conclusion (first proofs))
                  (clause.clause-formula (first goals)))))

(defthmd crock2-for-tactic.conditional-eqsubst-compile
  (implies (equal (clause.clause-list-formulas goals) (logic.strip-conclusions proofs))
           (equal (logic.conclusion (second proofs))
                  (clause.clause-formula (second goals)))))

(defthmd crock3-for-tactic.conditional-eqsubst-compile
  (implies (equal (clause.clause-list-formulas goals) (logic.strip-conclusions proofs))
           (equal (logic.conclusion (third proofs))
                  (clause.clause-formula (third goals)))))

(defthmd crock4-for-tactic.conditional-eqsubst-compile
  ;; NOTE reordered equality to match term order
  (implies (not (cdr x))
           (equal (equal 1 (len x))
                  (consp x)))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(%autoprove crock1-for-tactic.conditional-eqsubst-compile)
(%autoprove crock2-for-tactic.conditional-eqsubst-compile)
(%autoprove crock3-for-tactic.conditional-eqsubst-compile)
(%autoprove crock4-for-tactic.conditional-eqsubst-compile)


(%autoadmit tactic.conditional-eqsubst-compile)

(local (%enable default
                tactic.conditional-eqsubst-okp
                tactic.conditional-eqsubst-env-okp
                tactic.conditional-eqsubst-compile
                logic.term-formula))

(local (%enable default
                crock1-for-tactic.conditional-eqsubst-compile
                crock2-for-tactic.conditional-eqsubst-compile
                crock3-for-tactic.conditional-eqsubst-compile
                crock4-for-tactic.conditional-eqsubst-compile))

(%autoprove forcing-logic.appeal-listp-of-tactic.conditional-eqsubst-compile

            (%disable default
                      expensive-arithmetic-rules
                      expensive-arithmetic-rules-two
                      type-set-like-rules
                      unusual-memberp-rules
                      unusual-consp-rules
                      unusual-subsetp-rules
                      expensive-term/formula-inference
                      formula-decomposition
                      same-length-prefixes-equal-cheap)

            (%waterfall default 40)

            (%restrict default logic.strip-conclusions
                       (or (equal x 'proofs)
                           (equal x '(cdr proofs))
                           (equal x '(cdr (cdr proofs)))))

            (%restrict default definition-of-logic.appeal-listp
                       (or (equal x 'proofs)
                           (equal x '(cdr proofs))
                           (equal x '(cdr (cdr proofs)))))

            (%waterfall default 40)

            (%enable default
                     formula-decomposition
                     expensive-term/formula-inference
                     unusual-consp-rules)
            (%auto :strategy (cleanup split urewrite crewrite)))


(%autoprove forcing-logic.strip-conclusions-of-tactic.conditional-eqsubst-compile

            (%disable default
                      expensive-arithmetic-rules
                      expensive-arithmetic-rules-two
                      type-set-like-rules
                      unusual-memberp-rules
                      unusual-consp-rules
                      unusual-subsetp-rules
                      expensive-term/formula-inference
                      formula-decomposition
                      same-length-prefixes-equal-cheap)

            (%waterfall default 40)

            (%restrict default logic.strip-conclusions
                       (or (equal x 'proofs)
                           (equal x '(cdr proofs))
                           (equal x '(cdr (cdr proofs)))))

            (%restrict default definition-of-logic.appeal-listp
                       (or (equal x 'proofs)
                           (equal x '(cdr proofs))
                           (equal x '(cdr (cdr proofs)))))

            (%waterfall default 40)

            (%enable default
                     formula-decomposition
                     expensive-term/formula-inference
                     unusual-consp-rules)
            (%auto :strategy (cleanup split urewrite crewrite)))



(%autoprove forcing-logic.proof-listp-of-tactic.conditional-eqsubst-compile

            (%disable default
                      expensive-arithmetic-rules
                      expensive-arithmetic-rules-two
                      type-set-like-rules
                      unusual-memberp-rules
                      unusual-consp-rules
                      unusual-subsetp-rules
                      expensive-term/formula-inference
                      formula-decomposition
                      same-length-prefixes-equal-cheap)

            (%waterfall default 40)

            (%restrict default logic.strip-conclusions
                       (or (equal x 'proofs)
                           (equal x '(cdr proofs))
                           (equal x '(cdr (cdr proofs)))))

            (%restrict default definition-of-logic.appeal-listp
                       (or (equal x 'proofs)
                           (equal x '(cdr proofs))
                           (equal x '(cdr (cdr proofs)))))

            (%restrict default definition-of-logic.proof-listp
                       (or (equal x 'proofs)
                           (equal x '(cdr proofs))
                           (equal x '(cdr (cdr proofs)))))

            (%waterfall default 40)

            (%enable default
                     formula-decomposition
                     expensive-term/formula-inference
                     unusual-consp-rules)
            (%auto :strategy (cleanup split urewrite crewrite)))

(%ensure-exactly-these-rules-are-missing "../../tactics/conditional-eqsubst")

