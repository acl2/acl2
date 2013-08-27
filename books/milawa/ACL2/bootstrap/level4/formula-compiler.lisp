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

;; BOZO these don't go here -- need them for compile lemmas.
;; but we apparently don't introduce them anywhere else?  should we be using
;; other rules, perhaps?

(%defderiv build.disjoined-if-when-nil)
(%defderiv build.disjoined-if-when-not-nil)

(%deftheorem theorem-if-when-same)
(%defderiv build.disjoined-if-when-same)

;; </BOZO>


(%autoadmit logic.compile-formula)

(%autoprove forcing-logic.termp-of-logic.compile-formula
            (%autoinduct logic.compile-formula)
            (%restrict default logic.compile-formula (equal x 'x)))

(%autoprove forcing-logic.term-atblp-of-logic.compile-formula
            (%autoinduct logic.compile-formula)
            (%restrict default logic.compile-formula (equal x 'x)))

(%defderiv build.compile-formula-lemma-1)
(%defderiv build.compile-formula-lemma-2)


(%autoadmit build.compile-formula)

;; BOZO unlocalize+rename in clauses/compile-formula
(encapsulate
 ()
 (local (in-theory (acl2::current-theory 'build.compile-formula)))
 (defthm lemma-for-forcing-logic.appealp-of-first-of-build.compile-formula
   (implies (logic.formulap x)
            (let ((result (logic.compile-formula x))
                  (proofs (build.compile-formula x)))
              (and (logic.appealp (first proofs))
                   (logic.appealp (second proofs))
                   (equal (logic.conclusion (first proofs)) (logic.por (logic.pnot x) (logic.pequal result ''t)))
                   (equal (logic.conclusion (second proofs)) (logic.por x (logic.pequal result ''nil)))
                   )))
   :rule-classes nil
   :hints(("Goal"
           :induct (logic.compile-formula x)
           :in-theory (enable logic.compile-formula
                              build.compile-formula
                              axiom-equal-when-same
                              axiom-equal-when-diff)))))

(%autoprove lemma-for-forcing-logic.appealp-of-first-of-build.compile-formula
            (%autoinduct logic.compile-formula)
            (%disable default
                      type-set-like-rules
                      expensive-term/formula-inference
                      formula-decomposition
                      expensive-arithmetic-rules
                      expensive-arithmetic-rules-two)
            (%auto)
            (%restrict default logic.compile-formula (equal x 'x))
            (%restrict default build.compile-formula (equal a 'x))
            (%enable default
                     axiom-equal-when-same
                     axiom-equal-when-diff)
            (%auto)
            (%enable default formula-decomposition))

(%autoprove forcing-logic.appealp-of-first-of-build.compile-formula
            (%use (%instance (%thm lemma-for-forcing-logic.appealp-of-first-of-build.compile-formula))))

(%autoprove forcing-logic.appealp-of-second-of-build.compile-formula
            (%use (%instance (%thm lemma-for-forcing-logic.appealp-of-first-of-build.compile-formula))))

(%autoprove forcing-logic.conclusion-of-first-of-build.compile-formula
            (%use (%instance (%thm lemma-for-forcing-logic.appealp-of-first-of-build.compile-formula))))

(%autoprove forcing-logic.conclusion-of-second-of-build.compile-formula
            (%use (%instance (%thm lemma-for-forcing-logic.appealp-of-first-of-build.compile-formula))))



;; BOZO unlocalize+rename in clauses/compile-formula
;; NOTE: need to add rule-classes nil, also
(encapsulate
 ()
 (local (in-theory (acl2::current-theory 'forcing-logic.proofp-of-first-of-build.compile-formula)))
 (defthm@ lemma-for-forcing-logic.proofp-of-first-of-build.compile-formula
   (implies (and (logic.formulap x)
                 (logic.formula-atblp x atbl)
                 (equal (cdr (lookup 'equal atbl)) 2)
                 (equal (cdr (lookup 'if atbl)) 3)
                 (@obligations build.compile-formula))
            (and (logic.proofp (first (build.compile-formula x)) axioms thms atbl)
                 (logic.proofp (second (build.compile-formula x)) axioms thms atbl)))
   :rule-classes nil
   :hints(("Goal" :in-theory (enable build.compile-formula
                                     logic.compile-formula
                                     axiom-equal-when-same
                                     axiom-equal-when-diff)))))

(%autoprove lemma-for-forcing-logic.proofp-of-first-of-build.compile-formula
            (%autoinduct logic.compile-formula)
            (%disable default
                      type-set-like-rules
                      expensive-term/formula-inference
                      formula-decomposition
                      expensive-arithmetic-rules
                      expensive-arithmetic-rules-two)
            (%auto :strategy (cleanup split urewrite crewrite))
            (%restrict default logic.compile-formula (equal x 'x))
            (%restrict default build.compile-formula (equal a 'x))
            (%enable default
                     axiom-equal-when-same
                     axiom-equal-when-diff)
            (%auto))

(%autoprove forcing-logic.proofp-of-first-of-build.compile-formula
            (%use (%instance (%thm lemma-for-forcing-logic.proofp-of-first-of-build.compile-formula))))

(%autoprove forcing-logic.proofp-of-second-of-build.compile-formula
            (%use (%instance (%thm lemma-for-forcing-logic.proofp-of-first-of-build.compile-formula))))


(%defprojection
  :list (logic.compile-formula-list x)
  :element (logic.compile-formula x)
  :nil-preservingp t)

(%autoprove forcing-logic.term-listp-of-logic.compile-formula-list
            (%cdr-induction x))

(%autoprove forcing-logic.term-list-atblp-of-logic.compile-formula-list
            (%cdr-induction x))



(%autoadmit build.compile-formula-list-comm-2)

(%autoprove len-of-build.compile-formula-list-comm-2
            (%cdr-induction x)
            (%restrict default build.compile-formula-list-comm-2 (equal x 'x)))

(%autoprove logic.appeal-listp-of-build.compile-formula-list-comm-2
            (%cdr-induction x)
            (%restrict default build.compile-formula-list-comm-2 (equal x 'x)))

(%autoprove logic.strip-conclusions-of-logic.compile-formula-list-bldr3
            ;; BOZO misnamed
            (%cdr-induction x)
            (%restrict default build.compile-formula-list-comm-2 (equal x 'x)))

(%autoprove logic.proof-listp-of-build.compile-formula-list-comm-2
            (%cdr-induction x)
            (%restrict default build.compile-formula-list-comm-2 (equal x 'x)))

(%ensure-exactly-these-rules-are-missing "../../build/formula-compiler")