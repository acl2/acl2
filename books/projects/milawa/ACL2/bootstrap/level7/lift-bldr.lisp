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
(include-book "casesplit-bldr")
(%interactive)

(%autoadmit clause.lift-term1-bldr)

(%autoprove lemma-for-forcing-logic.appealp-of-clause.lift-term1-bldr
            (%clause.lift-term1-induction x)
            (%disable default
                      expensive-arithmetic-rules
                      type-set-like-rules
                      logic.termp-when-logic.formulap)
            (%auto)
            (%restrict default clause.lift-term1-bldr (equal x 'x))
            (%restrict default clause.lift-term1 (equal x 'x)))

(%autoprove forcing-logic.appealp-of-clause.lift-term1-bldr
            (%use (%instance (%thm lemma-for-forcing-logic.appealp-of-clause.lift-term1-bldr))))

(%autoprove forcing-logic.conclusion-of-clause.lift-term1-bldr
            (%use (%instance (%thm lemma-for-forcing-logic.appealp-of-clause.lift-term1-bldr))))

(%autoprove forcing-logic.proofp-of-clause.lift-term1-bldr
            (%clause.lift-term1-induction x)
            (%disable default
                      expensive-arithmetic-rules
                      type-set-like-rules
                      logic.termp-when-logic.formulap)
            (%auto)
            (%restrict default clause.lift-term1-bldr (equal x 'x))
            (%restrict default clause.lift-term1 (equal x 'x)))



(%autoadmit clause.lift-term-bldr)

(defthmd clause.lift-term-when-clause.lifted-termp
  (implies (clause.lifted-termp x)
           (equal (clause.lift-term x)
                  x))
  :hints(("Goal" :in-theory (enable clause.lift-term))))

(%autoprove clause.lift-term-when-clause.lifted-termp
            (%restrict default clause.lift-term (equal x 'x)))

(local (%enable default clause.lift-term-when-clause.lifted-termp))

(%autoprove lemma-for-forcing-logic.appealp-of-clause.lift-term-bldr
            (%clause.lift-term-induction x)
            (%auto)
            (%restrict default clause.lift-term-bldr (equal x 'x))
            (%restrict default clause.lift-term (equal x 'x)))

(%autoprove forcing-logic.appealp-of-clause.lift-term-bldr
            (%use (%instance (%thm lemma-for-forcing-logic.appealp-of-clause.lift-term-bldr))))

(%autoprove forcing-logic.conclusion-of-clause.lift-term-bldr
            (%use (%instance (%thm lemma-for-forcing-logic.appealp-of-clause.lift-term-bldr))))

(%autoprove forcing-logic.proofp-of-clause.lift-term-bldr
            (%clause.lift-term-induction x)
            (%auto)
            (%restrict default clause.lift-term-bldr (equal x 'x))
            (%restrict default clause.lift-term (equal x 'x)))


(%defprojection :list (clause.lift-term-list-bldr x)
                :element (clause.lift-term-bldr x))

(%autoprove forcing-logic.appeal-listp-of-clause.lift-term-list-bldr
            (%cdr-induction x))

(%autoprove forcing-logic.strip-conclusions-of-clause.lift-term-list-bldr
            (%cdr-induction x))

(%autoprove forcing-logic.proof-listp-of-clause.lift-term-list-bldr
            (%cdr-induction x))



(%autoadmit clause.lift-clauses-bldr)

(%autoprove forcing-logic.appeal-listp-of-clause.lift-clauses-bldr
            (%cdr-cdr-induction x proofs)
            (%restrict default clause.lift-clauses-bldr (equal x 'x)))

(%autoprove forcing-logic.strip-conclusions-of-clause.lift-clauses-bldr
            (%cdr-cdr-induction x proofs)
            (%restrict default clause.lift-clauses-bldr (equal x 'x)))

(%autoprove forcing-logic.proof-listp-of-clause.lift-clauses-bldr
            (%cdr-cdr-induction x proofs)
            (%restrict default clause.lift-clauses-bldr (equal x 'x)))
