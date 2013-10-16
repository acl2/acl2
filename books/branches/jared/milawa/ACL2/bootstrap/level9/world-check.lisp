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
(include-book "worldp")
(%interactive)

(%autoadmit tactic.slow-world-arities)
(%autoadmit tactic.world-arities)

(%autoprove true-listp-of-tactic.world-arities
            (%enable default tactic.world-arities))

(%autoprove tactic.world-arities-removal
            (%enable default tactic.world-arities)
            (%enable default tactic.slow-world-arities))

(%autoprove tactic.slow-world-arities-correct
            (%forcingp nil)
            (%enable default tactic.slow-world-arities tactic.world-atblp))


(%autoadmit tactic.slow-world-list-arities)
(%autoadmit tactic.world-list-arities)

(%autoprove true-listp-of-tactic.world-list-arities
            (%autoinduct tactic.world-list-arities)
            (%restrict default tactic.world-list-arities (equal x 'x)))

(%autoprove tactic.world-list-arities-removal
            (%autoinduct tactic.world-list-arities)
            (%restrict default tactic.world-list-arities (equal x 'x))
            (%restrict default tactic.slow-world-list-arities (equal x 'x)))

(%autoprove tactic.slow-world-list-arities-correct
            (%autoinduct tactic.slow-world-list-arities)
            (%restrict default tactic.slow-world-list-arities (equal x 'x))
            (%restrict default tactic.world-list-atblp (equal x 'x)))


(%autoadmit tactic.slow-world-partial-arities)
(%autoadmit tactic.world-partial-arities)

(%autoprove true-listp-of-tactic.world-partial-arities
            (%enable default tactic.world-partial-arities))

(%autoprove tactic.world-partial-arities-removal
            (%enable default tactic.world-partial-arities)
            (%enable default tactic.slow-world-partial-arities))

(%autoprove tactic.slow-world-partial-arities-correct
            (%forcingp nil)
            (%enable default tactic.world-atblp)
            (%enable default tactic.slow-world-partial-arities))


(%autoadmit tactic.slow-world-list-partial-arities)
(%autoadmit tactic.world-list-partial-arities)

(%autoprove true-listp-of-tactic.world-list-partial-arities
            (%autoinduct tactic.world-list-partial-arities)
            (%restrict default tactic.world-list-partial-arities (equal x 'x)))

(%autoprove tactic.world-list-partial-arities-removal
            (%autoinduct tactic.world-list-partial-arities)
            (%restrict default tactic.world-list-partial-arities (equal x 'x))
            (%restrict default tactic.slow-world-list-partial-arities (equal x 'x)))

(%autoadmit tactic.world-list-compatiblep-hack)

(%autoprove tactic.slow-world-list-partial-arities-correct
            (%cdr-induction x)
            (%forcingp nil)
            (%restrict default tactic.world-list-compatiblep-hack (or (equal x 'x) (equal x '(cdr x))))
            (%restrict default tactic.slow-world-list-partial-arities (or (equal x 'x) (equal x '(cdr x)))))


(%autoadmit tactic.fast-world-list-atblp)

(%autoprove tactic.fast-world-list-atblp-is-tactic.world-list-atblp
            (%enable default tactic.fast-world-list-atblp)
            (%forcingp nil))


(%autoadmit tactic.world-thms-okp)
(%autoadmit tactic.world-axioms-okp)

(%autoprove booleanp-of-tactic.world-thms-okp
            (%enable default tactic.world-thms-okp))

(%autoprove booleanp-of-tactic.world-axioms-okp
            (%enable default tactic.world-axioms-okp))

(%deflist tactic.world-list-thms-okp (x thms)
          (tactic.world-thms-okp x thms))

(%deflist tactic.world-list-axioms-okp (x axioms)
          (tactic.world-axioms-okp x axioms))

(%autoprove tactic.world-env-okp-redefinition
            (%enable default
                     tactic.world-env-okp
                     tactic.world-thms-okp
                     tactic.world-axioms-okp))

(%autoprove tactic.world-list-env-okp-redefinition
            (%cdr-induction x)
            (%enable default tactic.world-env-okp-redefinition))


(%autoadmit tactic.slow-world-thms)
(%autoadmit tactic.world-thms)

(%autoprove true-listp-of-tactic.world-thms
            (%enable default tactic.world-thms))

(%autoprove tactic.world-thms-removal
            (%enable default tactic.world-thms tactic.slow-world-thms))

(%autoprove tactic.slow-world-thms-correct
            (%enable default tactic.slow-world-thms tactic.world-thms-okp))


(%autoadmit tactic.slow-world-list-thms)
(%autoadmit tactic.world-list-thms)

(%autoprove true-listp-of-tactic.world-list-thms
            (%autoinduct tactic.world-list-thms)
            (%restrict default tactic.world-list-thms (equal x 'x)))

(%autoprove tactic.world-list-thms-removal
            (%autoinduct tactic.world-list-thms)
            (%restrict default tactic.world-list-thms (equal x 'x))
            (%restrict default tactic.slow-world-list-thms (equal x 'x)))

(%autoprove tactic.slow-world-list-thms-correct
            (%cdr-induction x)
            (%restrict default tactic.slow-world-list-thms (equal x 'x)))


(%autoadmit tactic.slow-world-partial-thms)
(%autoadmit tactic.world-partial-thms)

(%autoprove true-listp-of-tactic.world-partial-thms
            (%enable default tactic.world-partial-thms))

(%autoprove tactic.world-partial-thms-removal
            (%enable default tactic.world-partial-thms tactic.slow-world-partial-thms))

(%autoprove tactic.slow-world-partial-thms-correct
            (%enable default tactic.slow-world-partial-thms tactic.world-thms-okp))

(%autoadmit tactic.slow-world-list-partial-thms)
(%autoadmit tactic.world-list-partial-thms)

(%autoprove true-listp-of-tactic.world-list-partial-thms
            (%autoinduct tactic.world-list-partial-thms)
            (%restrict default tactic.world-list-partial-thms (equal x 'x)))

(%autoprove tactic.world-list-partial-thms-removal
            (%autoinduct tactic.world-list-partial-thms)
            (%restrict default tactic.world-list-partial-thms (equal x 'x))
            (%restrict default tactic.slow-world-list-partial-thms (equal x 'x)))

(%autoprove tactic.slow-world-list-partial-thms-correct
            (%cdr-induction x)
            (%restrict default tactic.world-list-compatiblep-hack
                       (or (equal x 'x) (equal x '(cdr x))))
            (%restrict default tactic.slow-world-list-partial-thms
                       (or (equal x 'x) (equal x '(cdr x))))
            (%restrict default tactic.world-list-thms-okp
                       (or (equal x 'x) (equal x '(cdr x)))))


(%autoadmit tactic.world-list-defs)

(%autoprove true-listp-of-tactic.world-list-defs
            (%cdr-induction x)
            (%restrict default tactic.world-list-defs (equal x 'x)))

(%autoprove tactic.world-list-defs-correct
            (%cdr-induction x)
            (%restrict default tactic.world-list-defs (equal x 'x))
            (%enable default tactic.world-axioms-okp))

(%autoprove tactic.world-list-partial-defs-correct
            (%cdr-induction x)
            (%enable default tactic.world-axioms-okp)
            (%restrict default tactic.world-list-compatiblep-hack
                       (or (equal x 'x) (equal x '(cdr x))))
            (%restrict default tactic.world-list-defs
                       (or (equal x 'x) (equal x '(cdr x)))))


(%autoadmit tactic.fast-world-list-env-okp)

(%autoprove lemma-1-for-tactic.fast-world-list-env-okp-lemma
            (%cdr-induction x)
            (%enable default
                     tactic.world-thms-okp
                     tactic.slow-world-partial-thms)
            (%restrict default tactic.world-list-compatiblep-hack
                       (or (equal x 'x) (equal x '(cdr x))))
            (%restrict default tactic.slow-world-list-partial-thms
                       (or (equal x 'x) (equal x '(cdr x)))))

(%autoprove lemma-2-for-tactic.fast-world-list-env-okp-lemma
            (%cdr-induction x)
            (%enable default tactic.world-thms-okp))

(%autoprove tactic.fast-world-list-env-okp-lemma
            (%restrict default tactic.fast-world-list-env-okp (equal x 'x))
            (%enable default
                     lemma-1-for-tactic.fast-world-list-env-okp-lemma
                     lemma-2-for-tactic.fast-world-list-env-okp-lemma))


(%autoprove tactic.fast-world-list-env-okp-correct
            ;; BOZO move to world-check eventually
            (%enable default
                     tactic.fast-world-list-env-okp-lemma
                     tactic.world-list-env-okp-redefinition))
