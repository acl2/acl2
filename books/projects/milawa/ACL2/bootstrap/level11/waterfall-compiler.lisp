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
(include-book "waterfall-steps")
(%interactive)


(%autoadmit rw.stop-waterstep-compiler)
(encapsulate
 ()
 (local (%enable default
                 rw.stop-waterstep-compiler
                 rw.stop-waterstep-okp))
 (local (%restrict default definition-of-rw.waterfall-subgoals (equal x 'x)))
 (%autoprove logic.appealp-of-rw.stop-waterstep-compiler)
 (%autoprove logic.conclusion-of-rw.stop-waterstep-compiler)
 (%autoprove logic.proofp-of-rw.stop-waterstep-compiler))


(%autoadmit rw.urewrite-waterstep-compiler)
(encapsulate
 ()
 (local (%enable default
                 rw.urewrite-waterstep-compiler
                 rw.urewrite-waterstep-okp))
 (local (%restrict default definition-of-rw.waterfall-subgoals (equal x 'x)))
 (local (%disable default
                  formula-decomposition
                  expensive-term/formula-inference
                  type-set-like-rules
                  unusual-memberp-rules
                  unusual-subsetp-rules
                  expensive-arithmetic-rules
                  expensive-arithmetic-rules-two
                  MEMBERP-WHEN-MEMBERP-OF-CDR
                  MEMBERP-WHEN-NOT-CONSP
                  same-length-prefixes-equal-cheap
                  CAR-WHEN-MEMBERP-OF-SINGLETON-LIST-CHEAP
                  CAR-WHEN-MEMBERP-AND-NOT-MEMBERP-OF-CDR-CHEAP
                  ))
 (%autoprove logic.appealp-of-rw.urewrite-waterstep-compiler)
 (%autoprove logic.conclusion-of-rw.urewrite-waterstep-compiler)
 (%autoprove logic.proofp-of-rw.urewrite-waterstep-compiler))


(%autoadmit rw.crewrite-waterstep-compiler)
(encapsulate
 ()
 (local (%enable default
                 rw.crewrite-waterstep-compiler
                 rw.crewrite-waterstep-okp))
 (local (%restrict default definition-of-rw.waterfall-subgoals (equal x 'x)))
 (local (%disable default
                  formula-decomposition
                  expensive-term/formula-inference
                  type-set-like-rules
                  unusual-memberp-rules
                  unusual-subsetp-rules
                  expensive-arithmetic-rules
                  expensive-arithmetic-rules-two
                  MEMBERP-WHEN-MEMBERP-OF-CDR
                  MEMBERP-WHEN-NOT-CONSP
                  same-length-prefixes-equal-cheap
                  CAR-WHEN-MEMBERP-OF-SINGLETON-LIST-CHEAP
                  CAR-WHEN-MEMBERP-AND-NOT-MEMBERP-OF-CDR-CHEAP
                  ))
 (%autoprove logic.appealp-of-rw.crewrite-waterstep-compiler)
 (%autoprove logic.conclusion-of-rw.crewrite-waterstep-compiler)
 (%autoprove logic.proofp-of-rw.crewrite-waterstep-compiler))


(%autoadmit rw.split-waterstep-compiler)
(encapsulate
 ()
 (local (%enable default
                 rw.split-waterstep-okp
                 rw.split-waterstep-compiler))
 (local (%restrict default definition-of-rw.waterfall-subgoals (equal x 'x)))
 (%autoprove logic.appealp-of-rw.split-waterstep-compiler)
 (%autoprove logic.conclusion-of-rw.split-waterstep-compiler)
 (%autoprove logic.proofp-of-rw.split-waterstep-compiler))



(%autoadmit rw.flag-waterstep-compiler)
(%autoadmit rw.waterstep-compiler)
(%autoadmit rw.waterstep-list-compiler)
(%autoprove definition-of-rw.waterstep-compiler
            (%restrict default rw.flag-waterstep-compiler (equal x 'x))
            (%enable default rw.waterstep-list-compiler rw.waterstep-compiler))
(%autoprove definition-of-rw.waterstep-list-compiler
            (%restrict default rw.flag-waterstep-compiler (equal x 'x))
            (%enable default rw.waterstep-list-compiler rw.waterstep-compiler))
(%autoprove rw.flag-waterstep-compiler-of-clause
            (%enable default rw.waterstep-compiler))
(%autoprove rw.flag-waterstep-compiler-of-list
            (%enable default rw.waterstep-list-compiler))

(%autoprove rw.waterstep-compiler-of-nil
            (%restrict default definition-of-rw.waterstep-compiler (equal x ''nil)))

(%autoprove rw.waterstep-list-compiler-when-not-consp
            (%restrict default definition-of-rw.waterstep-list-compiler (equal x 'x)))

(%autoprove rw.waterstep-list-compiler-of-cons
            (%restrict default definition-of-rw.waterstep-list-compiler (equal x '(cons a x))))

(%defprojection
 :list (rw.waterstep-list-compiler x world rproofs)
 :element (rw.waterstep-compiler x world rproofs)
 :nil-preservingp t)

(%autoprove lemma-for-logic.appealp-of-rw.waterstep-compiler
            (%autoinduct rw.waterstep-induction flag x)
            (%disable default
                      formula-decomposition
                      expensive-term/formula-inference
                      type-set-like-rules
                      unusual-memberp-rules
                      unusual-subsetp-rules
                      expensive-arithmetic-rules
                      expensive-arithmetic-rules-two
                      same-length-prefixes-equal-cheap)
            (%forcingp nil)
            (%waterfall default 40)

            (%restrict default definition-of-rw.waterstep-compiler (equal x 'x))
            (%restrict default definition-of-rw.waterfall-subgoals (equal x 'x))
            (%restrict default definition-of-rw.waterstep-okp (equal x 'x))
            (%waterfall default 40)

            (%enable default
                     formula-decomposition
                     expensive-term/formula-inference
                     type-set-like-rules
                     unusual-memberp-rules
                     unusual-subsetp-rules
                     expensive-arithmetic-rules
                     expensive-arithmetic-rules-two
                     same-length-prefixes-equal-cheap)

            (%waterfall default 40)
            (%auto))

(%autoprove logic.appealp-of-rw.waterstep-compiler
            (%use (%instance (%thm lemma-for-logic.appealp-of-rw.waterstep-compiler)
                             (flag 'clause))))

(%autoprove logic.conclusion-of-rw.waterstep-compiler
            (%use (%instance (%thm lemma-for-logic.appealp-of-rw.waterstep-compiler)
                             (flag 'clause))))

(%autoprove logic.appeal-listp-of-rw.waterstep-list-compiler
            (%use (%instance (%thm lemma-for-logic.appealp-of-rw.waterstep-compiler)
                             (flag 'list))))

(%autoprove logic.strip-conclusions-of-rw.waterstep-list-compiler
            (%use (%instance (%thm lemma-for-logic.appealp-of-rw.waterstep-compiler)
                             (flag 'list))))

(%autoprove lemma-for-logic.proofp-of-rw.waterstep-compiler
            (%autoinduct rw.waterstep-induction flag x)
            (%disable default
                      formula-decomposition
                      expensive-term/formula-inference
                      type-set-like-rules
                      unusual-memberp-rules
                      unusual-subsetp-rules
                      expensive-arithmetic-rules
                      expensive-arithmetic-rules-two
                      same-length-prefixes-equal-cheap
                      MEMBERP-WHEN-MEMBERP-OF-CDR
                      MEMBERP-WHEN-NOT-CONSP
                      CAR-WHEN-MEMBERP-AND-NOT-MEMBERP-OF-CDR-CHEAP
                      CAR-WHEN-MEMBERP-OF-SINGLETON-LIST-CHEAP
                      SUBSETP-TRANSITIVE-TWO
                      SUBSETP-OF-REMOVE-DUPLICATES-ONE-INDIRECT
                      SUBSETP-OF-LOGIC.DISJOIN-EACH-FORMULA-LISTS-WHEN-SUBSETP
                      SUBSETP-OF-LOGIC.TERM-LIST-LIST-FORMULASS-WHEN-SUBSETP)
            (%forcingp nil)
            (%liftlimit 2)
            (%splitlimit 5)
            (%waterfall default 40)

            (%restrict default definition-of-rw.waterstep-compiler (equal x 'x))
            (%restrict default definition-of-rw.waterfall-subgoals (equal x 'x))
            (%restrict default definition-of-rw.waterstep-okp (equal x 'x))
            (%waterfall default 40)

            (%enable default
                     formula-decomposition
                     expensive-term/formula-inference
                     type-set-like-rules
                     unusual-memberp-rules
                     unusual-subsetp-rules
                     expensive-arithmetic-rules
                     expensive-arithmetic-rules-two
                     same-length-prefixes-equal-cheap)

            (%waterfall default 40)
            (%auto))

(%autoprove logic.proofp-of-rw.waterstep-compiler
            (%use (%instance (%thm lemma-for-logic.proofp-of-rw.waterstep-compiler)
                             (flag 'clause))))

(%autoprove logic.proof-listp-of-rw.waterstep-list-compiler
            (%use (%instance (%thm lemma-for-logic.proofp-of-rw.waterstep-compiler)
                             (flag 'list))))
