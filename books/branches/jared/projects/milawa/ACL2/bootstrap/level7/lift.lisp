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
(include-book "lift-term1")
(%interactive)

(%autoadmit clause.lift-term)

(defmacro %clause.lift-term-induction (x)
  `(%induct (clause.depth-list (clause.unlifted-subterms ,x))
            ((not (logic.termp ,x))
             nil)
            ((clause.lifted-termp ,x)
             nil)
            ((and (logic.termp ,x)
                  (not (clause.lifted-termp ,x)))
             (((x (clause.lift-term1 ,x)))))))

(%autoprove forcing-logic.termp-of-clause.lift-term
            (%clause.lift-term-induction x)
            (%restrict default clause.lift-term (equal x 'x)))

(%autoprove forcing-logic.term-atblp-of-clause.lift-term
            (%clause.lift-term-induction x)
            (%restrict default clause.lift-term (equal x 'x)))

(%autoprove forcing-clause.lifted-termp-of-clause.lift-term
            (%clause.lift-term-induction x)
            (%restrict default clause.lift-term (equal x 'x)))

(%autoprove clause.lift-term-when-clause.simple-termp
            (%clause.lift-term-induction x)
            (%restrict default clause.lift-term (equal x 'x)))




(%defprojection :list (clause.lift-term-list x)
                :element (clause.lift-term x))

(%autoprove forcing-logic.term-listp-of-clause.lift-term-list
            (%cdr-induction x))

(%autoprove forcing-logic.term-list-atblp-of-clause.lift-term-list
            (%cdr-induction x))

(%autoprove clause.lift-term-list-when-clause.simple-term-listp
            (%cdr-induction x))

(%autoprove forcing-clause.lifted-term-listp-of-clause.lift-term-list
            (%cdr-induction x))



(%defprojection :list (clause.lift-term-list-list x)
                :element (clause.lift-term-list x))

(%autoprove forcing-logic.term-listp-of-clause.lift-term-list-list
            (%cdr-induction x))

(%autoprove forcing-logic.term-list-atblp-of-clause.lift-term-list-list
            (%cdr-induction x))

(%autoprove clause.lift-term-list-list-when-clause.simple-term-list-listp
            (%cdr-induction x))

(%autoprove forcing-cons-listp-of-clause.lift-term-list-list
            (%cdr-induction x))

