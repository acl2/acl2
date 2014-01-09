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
(include-book "lift")
(include-book "limlift")
(include-book "clean-clauses")
(%interactive)


(%autoprove true-listp-of-clause.clean-clauses
            (%enable default clause.clean-clauses))

(%autoprove forcing-logic.term-list-list-atblp-of-remove-supersets1
            (%autoinduct remove-supersets1 x acc)
            (%restrict default remove-supersets1 (equal todo 'x)))

(%autoprove forcing-logic.term-list-list-atblp-of-remove-supersets
            (%enable default remove-supersets))

(%autoprove forcing-logic.term-list-list-atblp-of-remove-duplicates-list
            (%cdr-induction x))

(%autoprove forcing-logic.term-list-list-atblp-of-clause.remove-absurd-terms-from-clauses
            (%cdr-induction x))

(%autoprove logic.term-list-list-atblp-of-third-of-clause.clean-clauses
            (%enable default clause.clean-clauses))

(%autoprove forcing-clause.simple-term-list-listp-of-remove-supersets1
            (%autoinduct remove-supersets1 x acc)
            (%restrict default remove-supersets1 (equal todo 'x)))

(%autoprove forcing-clause.simple-term-list-listp-of-remove-supersets
            (%enable default remove-supersets))

(%autoprove forcing-clause.simple-term-list-listp-of-remove-duplicates-list
            (%cdr-induction x))

(%autoprove forcing-clause.simple-term-list-listp-of-clause.remove-absurd-terms-from-clauses
            (%cdr-induction x))

(%autoprove forcing-clause.simple-term-list-listp-of-clause.remove-complement-clauses
            (%cdr-induction x))

(%autoprove forcing-clause.simple-term-list-listp-of-clause.remove-obvious-clauses
            (%cdr-induction x))

(%autoprove forcing-clause.simple-termp-of-clause.negative-term-guts
            (%enable default
                     clause.negative-termp
                     clause.negative-term-guts))

(%autoprove forcing-clause.simple-termp-of-clause.normalize-nots-term
            (%autoinduct clause.normalize-nots-term)
            (%restrict default clause.normalize-nots-term (equal x 'x)))

(%autoprove forcing-clause.simple-term-listp-of-clause.normalize-nots-term-list
            (%cdr-induction x))

(%autoprove forcing-clause.simple-term-list-listp-of-clause.normalize-nots-clauses
            (%cdr-induction x))

(%autoprove clause.simple-term-list-listp-of-third-of-clause.clean-clauses
            (%enable default clause.clean-clauses))



(%autoadmit clause.split)

(%autoprove true-listp-of-clause.split
            ;; BOZO we don't want this theorem.  We want true-listp of cdr.  Oh well,
            ;; I'll prove this one anyway.
            (%enable default clause.split))

(%autoprove forcing-logic.term-list-listp-of-cdr-of-clause.split
            (%enable default clause.split))

(%autoprove forcing-logic.term-list-list-atblp-of-cdr-of-clause.split
            (%enable default clause.split))

(%autoprove forcing-cons-listp-of-cdr-of-clause.split
            (%enable default clause.split))


;; We don't bother to prove this.  Maybe we should, eventually.
;; (%autoprove forcing-clause.simple-term-list-listp-of-clause.split-of-cdr-of--clause.lift-clause
;;            (%enable default clause.split))


(%autoadmit clause.split-list)

(%autoprove clause.split-list-when-not-consp
            (%restrict default clause.split-list (equal x 'x)))

(%autoprove clause.split-list-of-cons
            (%restrict default clause.split-list (equal x '(cons a x))))

(%autoprove true-listp-of-cdr-of-clause.split-list
            (%cdr-induction x))

(%deflist logic.term-list-list-listp (x)
  (logic.term-list-listp x))

(%deflist logic.term-list-list-list-atblp (x atbl)
  (logic.term-list-list-atblp x atbl))

(%autoprove forcing-logic.term-list-list-listp-of-cdr-of-clause.split-list
            (%cdr-induction x))

(%autoprove forcing-logic.term-list-list-list-atblp-of-cdr-of-clause.split-list
            (%cdr-induction x))

(%deflist cons-list-listp (x)
          (cons-listp x))

(%autoprove forcing-cons-list-listp-of-cdr-of-clause.split-list
            (%cdr-induction x))