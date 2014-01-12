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
(include-book "simple-negativep")
(%interactive)

(local (%enable default lemma-split-up-list-of-quoted-nil))

(%autoadmit clause.complement-term)

(%autoprove logic.termp-of-clause.complement-term
            (%enable default clause.complement-term))

(%autoprove clause.complement-term-of-clause.complement-term
            (%enable default clause.complement-term))




(%autoadmit clause.find-complementary-literal)

(%autoprove clause.find-complementary-literal-when-not-consp
            (%restrict default clause.find-complementary-literal (equal x 'x)))

(%autoprove clause.find-complementary-literal-of-cons
            (%restrict default clause.find-complementary-literal (equal x '(cons a x))))

(%autoprove forcing-memberp-of-clause.find-complementary-literal
            (%cdr-induction x))

(%autoprove forcing-memberp-of-not-of-clause.find-complementary-literal
            (%cdr-induction x))

(%autoprove clause.find-complementary-literal-of-list-fix
            (%cdr-induction x))

(%autoprove forcing-clause.find-complementary-literal-of-app-one
            (%cdr-induction x))

(%autoprove lemma-for-clause.find-complementary-literal-of-rev
            (%cdr-induction x))

(%autoprove clause.find-complementary-literal-of-rev
            (%cdr-induction x)
            (%enable default lemma-for-clause.find-complementary-literal-of-rev))



(%autoadmit clause.remove-complement-clauses)

(%autoprove clause.remove-complement-clauses-when-not-consp
            (%restrict default clause.remove-complement-clauses (equal x 'x)))

(%autoprove clause.remove-complement-clauses-of-cons
            (%restrict default clause.remove-complement-clauses (equal x '(cons a x))))

(%autoprove forcing-logic.term-list-listp-of-clause.remove-complement-clauses
            (%cdr-induction x))

(%autoprove forcing-logic.term-list-list-atblp-of-clause.remove-complement-clauses
            (%cdr-induction x))

(%autoprove cons-listp-of-clause.remove-complement-clauses
            (%cdr-induction x))

(%autoprove true-listp-of-clause.remove-complement-clauses
            (%cdr-induction x))

(%autoprove clause.remove-complement-clauses-of-list-fix
            (%cdr-induction x))

(%autoprove clause.remove-complement-clauses-of-app
            (%cdr-induction x))

(%autoprove rev-of-clause.remove-complement-clauses
            (%cdr-induction x))

(%autoprove clause.remove-complement-clauses-of-rev)




(defsection clause.complement-clause-bldr
  (%autoadmit clause.complement-clause-bldr)
  (local (%enable default
                  clause.complement-clause-bldr
                  clause.complement-term
                  theorem-not-when-nil))
  (%autoprove forcing-logic.appealp-of-clause.complement-clause-bldr)
  (%autoprove forcing-logic.conclusion-of-clause.complement-clause-bldr)
  (%autoprove forcing-logic.proofp-of-clause.complement-clause-bldr))




(%autoadmit clause.remove-complement-clauses-bldr)

(%autoprove forcing-logic.appeal-listp-of-clause.remove-complement-clauses-bldr
            (%autoinduct clause.remove-complement-clauses-bldr)
            (%restrict default clause.remove-complement-clauses (equal x 'x))
            (%restrict default clause.remove-complement-clauses-bldr (equal x 'x)))

(%autoprove forcing-logic.strip-conclusions-of-clause.remove-complement-clauses-bldr
            (%autoinduct clause.remove-complement-clauses-bldr)
            (%restrict default clause.remove-complement-clauses (equal x 'x))
            (%restrict default clause.remove-complement-clauses-bldr (equal x 'x)))

(%autoprove forcing-logic.proof-listp-of-clause.remove-complement-clauses-bldr
            (%autoinduct clause.remove-complement-clauses-bldr)
            (%restrict default clause.remove-complement-clauses (equal x 'x))
            (%restrict default clause.remove-complement-clauses-bldr (equal x 'x)))
