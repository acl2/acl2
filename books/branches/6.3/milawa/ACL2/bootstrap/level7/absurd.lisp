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


(%autoadmit clause.absurd-termp)

(%autoprove booleanp-of-clause.absurd-termp
            (%enable default clause.absurd-termp))


(%autoadmit clause.remove-absurd-terms-from-list)

(%autoprove clause.remove-absurd-terms-from-list-when-not-consp
            (%restrict default clause.remove-absurd-terms-from-list (equal x 'x)))

(%autoprove clause.remove-absurd-terms-from-list-of-cons
            (%restrict default clause.remove-absurd-terms-from-list (equal x '(cons a x))))

(%autoprove true-listp-of-clause.remove-absurd-terms-from-list
            (%cdr-induction x))

(%autoprove clause.remove-absurd-terms-from-list-of-list-fix
            (%cdr-induction x))

(%autoprove clause.remove-absurd-terms-from-list-of-app
            (%cdr-induction x))

(%autoprove rev-of-clause.remove-absurd-terms-from-list
            (%cdr-induction x))

(%autoprove subsetp-of-clause.remove-absurd-terms-from-list
            (%cdr-induction x))

(%autoprove forcing-logic.term-listp-of-clause.remove-absurd-terms-from-list
            (%cdr-induction x))



(%defprojection :list (clause.remove-absurd-terms-from-clauses x)
                :element (clause.remove-absurd-terms-from-list x))

(%autoprove all-superset-of-somep-of-clause.remove-absurd-terms-from-clauses
            (%cdr-induction x))

(%autoprove all-subset-of-somep-of-clause.remove-absurd-terms-from-clauses
            (%cdr-induction x))

(%autoprove forcing-logic.term-list-listp-of-clause.remove-absurd-terms-from-clauses
            (%cdr-induction x))




(%autoadmit clause.fast-remove-absurd-terms-from-list$)

(%autoprove clause.fast-remove-absurd-terms-from-list$-removal
            (%induct (rank x)
                     ((not (consp x))
                      nil)
                     ((and (consp x)
                           (clause.absurd-termp (car x)))
                      (((x (cdr x)) (acc acc))))
                     ((and (consp x)
                           (not (clause.absurd-termp (car x))))
                      (((x (cdr x)) (acc (cons (car x) acc))))))
            (%restrict default clause.fast-remove-absurd-terms-from-list$ (equal x 'x)))


