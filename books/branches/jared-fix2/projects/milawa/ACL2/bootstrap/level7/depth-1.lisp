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
(%interactive)



;; BOZO move these to utilities or wherever max is defined
(defthm max-of-nfix-left
  (equal (max (nfix a) b)
         (max a b)))

(defthm max-of-nfix-right
  (equal (max a (nfix b))
         (max a b)))

(%autoprove max-of-nfix-left)
(%autoprove max-of-nfix-right)


(%autoadmit clause.flag-depth)
(%autoadmit clause.depth)
(%autoadmit clause.depth-list)

(%autoprove definition-of-clause.depth
            (%restrict default clause.flag-depth (equal x 'x))
            (%enable default clause.depth clause.depth-list))

(%autoprove definition-of-clause.depth-list
            (%restrict default clause.flag-depth (equal x 'x))
            (%enable default clause.depth clause.depth-list))

(%autoprove clause.flag-depth-of-term
            (%enable default clause.depth))

(%autoprove clause.flag-depth-of-list
            (%enable default clause.depth-list))



(%autoprove forcing-clause.depth-of-logic.function
            (%restrict default definition-of-clause.depth (memberp x '((logic.function fn args)
                                                                       (logic.function 'if args))))
            (%forcingp nil))

(%autoprove forcing-clause.depth-of-logic.lambda
            (%restrict default definition-of-clause.depth (equal x '(logic.lambda formals body actuals)))
            (%forcingp nil))

(%autoprove clause.depth-list-when-not-consp
            (%restrict default definition-of-clause.depth-list (equal x 'x)))

(%autoprove clause.depth-list-of-cons
            (%restrict default definition-of-clause.depth-list (equal x '(cons a x))))



(%autoprove clause.depth-list-when-length-three
            (%disable default max))


(%autoprove lemma-for-natp-of-clause.depth
            (%clause.simple-term-induction flag x)
            (%restrict default definition-of-clause.depth (equal x 'x)))

(%autoprove natp-of-clause.depth
            (%use (%instance (%thm lemma-for-natp-of-clause.depth) (flag 'term))))

(%autoprove natp-of-clause.depth-list
            (%use (%instance (%thm lemma-for-natp-of-clause.depth) (flag 'list))))


(%autoprove clause.depth-list-of-list-fix
            (%cdr-induction x))

(%autoprove clause.depth-list-of-app
            (%cdr-induction x))

(%autoprove clause.depth-list-of-rev
            (%cdr-induction x))



(%autoprove lemma-for-clause.depth-zero
            (%clause.simple-term-induction flag x)
            (%restrict default definition-of-clause.depth (equal x 'x)))

(%autoprove clause.depth-zero
            (%use (%instance (%thm lemma-for-clause.depth-zero) (flag 'term))))

(%autoprove clause.depth-list-zero
            (%use (%instance (%thm lemma-for-clause.depth-zero) (flag 'list))))



(%autoprove clause.depth-when-clause.simple-termp)

(%autoprove clause.depth-list-when-clause.simple-term-listp)

(%autoprove clause.depth-positive-when-non-clause.simple-termp)

(%autoprove clause.depth-list-positive-when-non-clause.simple-term-listp)




