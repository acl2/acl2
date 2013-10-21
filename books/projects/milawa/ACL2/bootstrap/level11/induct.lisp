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
(%interactive)



(encapsulate
 ()
 (%autoadmit build.stepwise-modus-ponens-2)
 (%autoprove true-listp-of-build.stepwise-modus-ponens-2
             (%autoinduct build.stepwise-modus-ponens-2)
             (%restrict default build.stepwise-modus-ponens-2 (equal x 'x)))
 (%autoprove forcing-logic.appeal-list-of-build.stepwise-modus-ponens-2
             (%autoinduct build.stepwise-modus-ponens-2)
             (%restrict default build.stepwise-modus-ponens-2 (equal x 'x)))
 (%autoprove forcing-logic.strip-conclusions-of-build.stepwise-modus-ponens-2
             (%autoinduct build.stepwise-modus-ponens-2)
             (%restrict default build.stepwise-modus-ponens-2 (equal x 'x)))
 (%autoprove forcing-logic.proof-list-of-build.stepwise-modus-ponens-2
             (%autoinduct build.stepwise-modus-ponens-2)
             (%restrict default build.stepwise-modus-ponens-2 (equal x 'x))))


(encapsulate
 ()
 (%autoadmit tactic.induct-basis-clause)
 (%autoprove forcing-logic.term-listp-of-tactic.induct-basis-clause
             (%enable default tactic.induct-basis-clause))
 (%autoprove consp-of-tactic.induct-basis-clause
             (%enable default tactic.induct-basis-clause)))


(encapsulate
 ()
 (%autoadmit tactic.compile-induct-basis-clause)
 (local (%enable default
                 logic.term-formula
                 tactic.induct-basis-clause
                 tactic.compile-induct-basis-clause))
 (%autoprove forcing-logic.appealp-of-tactic.compile-induct-basis-clause)
 (%autoprove forcing-logic.conclusion-of-tactic.compile-induct-basis-clause)
 (%autoprove forcing-logic.proofp-of-tactic.compile-induct-basis-clause))



(defthmd lemma-for-tactic.compile-induct-inductive-clauses
  ;; BOZO unlocalize/rename in tactics/induct
  (implies (equal (logic.strip-conclusions proofs)
                  (logic.negate-formulas x))
           (equal (len proofs)
                  (len x)))
  :hints(("Goal"
          :in-theory (disable len-of-logic.negate-formulas
                              len-of-logic.strip-conclusions)
          :use ((:instance len-of-logic.negate-formulas)
                (:instance len-of-logic.strip-conclusions (x proofs))))))

(encapsulate
 ()
 (%autoadmit tactic.induct-inductive-clauses)
 (%autoadmit tactic.compile-induct-inductive-clauses)
 (local (%enable default
                 tactic.induct-inductive-clauses
                 tactic.compile-induct-inductive-clauses))
 (%autoprove forcing-logic.term-list-listp-of-tactic.induct-inductive-clauses)
 (%autoprove cons-listp-of-tactic.induct-inductive-clauses)
 (%autoprove true-listp-of-tactic.induct-inductive-clauses)

 (%autoprove lemma-for-tactic.compile-induct-inductive-clauses
             (%disable default
                       len-of-logic.negate-formulas
                       [outside]len-of-logic.negate-formulas
                       len-of-logic.strip-conclusions
                       [outside]len-of-logic.strip-conclusions)
             (%use (%instance (%thm len-of-logic.negate-formulas)))
             (%use (%instance (%thm len-of-logic.strip-conclusions) (x proofs))))
 (local (%enable default lemma-for-tactic.compile-induct-inductive-clauses))

 (%autoprove forcing-logic.appeal-listp-of-tactic.compile-induct-inductive-clauses)
 (%autoprove forcing-logic.strip-conclusions-of-tactic.compile-induct-inductive-clauses)
 (%autoprove forcing-logic.proof-listp-of-tactic.compile-induct-inductive-clauses))

(encapsulate
 ()
 (%autoadmit tactic.induct-ordinal-clause)
 (%autoadmit tactic.compile-induct-ordinal-clause)
 (local (%enable default
                 logic.term-formula
                 tactic.induct-ordinal-clause
                 tactic.compile-induct-ordinal-clause))
 (%autoprove forcing-logic.term-listp-of-tactic.induct-ordinal-clause)
 (%autoprove consp-of-tactic.induct-ordinal-clause)
 (%autoprove forcing-logic.appealp-of-tactic.compile-induct-ordinal-clause)
 (%autoprove forcing-logic.conclusion-of-tactic.compile-induct-ordinal-clause)
 (%autoprove forcing-logic.proofp-of-tactic.compile-induct-ordinal-clause))

(encapsulate
 ()
 (%autoadmit tactic.induct-measure-clauses)
 (%autoadmit tactic.compile-induct-measure-clauses)
 (local (%enable default
                 tactic.induct-measure-clauses
                 tactic.compile-induct-measure-clauses))
 (%autoprove forcing-logic.term-list-listp-of-tactic.induct-measure-clauses)
 (%autoprove cons-listp-of-tactic.induct-measure-clauses)
 (%autoprove true-listp-of-tactic.induct-measure-clauses)
 (local (%enable default lemma-for-tactic.compile-induct-inductive-clauses))  ;; ugly, but it's the same lemma.
 (%autoprove true-listp-of-tactic.compile-induct-measure-clauses)
 (%autoprove forcing-logic.appeal-list-of-tactic.compile-induct-measure-clauses)
 (%autoprove forcing-logic.strip-conclusions-of-tactic.compile-induct-measure-clauses)
 (%autoprove forcing-logic.proof-listp-of-tactic.compile-induct-measure-clauses))



(%autoadmit tactic.induct-okp)
(%autoprove booleanp-of-tactic.induct-okp
            (%enable default tactic.induct-okp))

(%autoadmit tactic.induct-env-okp)
(%autoprove booleanp-of-tactic.induct-env-okp
            (%enable default tactic.induct-env-okp))


(%autoadmit tactic.induct-tac)
(%autoprove forcing-tactic.skeletonp-of-tactic.induct-tac
            (%enable default tactic.induct-tac))
(%autoprove forcing-tactic.induct-okp-of-tactic.induct-tac
            (%enable default tactic.induct-tac tactic.induct-okp))
;; BOZO shouldn't we have an env-okp lemma too??


(encapsulate
 ()
 (%autoadmit tactic.induct-compile-aux)
 (local (%enable default tactic.induct-compile-aux))
 (%autoprove forcing-logic.appealp-of-tactic.induct-compile-aux)
 (%autoprove forcing-logic.conclusion-of-tactic.induct-compile-aux)
 (%autoprove forcing-logic.proofp-of-tactic.induct-compile-aux))




;; BOZO all of this stuff has to get unlocalized/renamed.

(defthm crock1-for-tactic.induct-compile
  (implies (EQUAL (LOGIC.DISJOIN-EACH-FORMULA-LIST (LOGIC.TERM-LIST-LIST-FORMULAS goals))
                  (LOGIC.STRIP-CONCLUSIONS PROOFS))
           (equal (logic.strip-conclusions proofs)
                  (LOGIC.DISJOIN-EACH-FORMULA-LIST (LOGIC.TERM-LIST-LIST-FORMULAS goals)))))

(defthm crock2-for-tactic.induct-compile
  (implies (EQUAL (LOGIC.DISJOIN-EACH-FORMULA-LIST (LOGIC.TERM-LIST-LIST-FORMULAS goals))
                  (LOGIC.STRIP-CONCLUSIONS PROOFS))
           (equal (logic.strip-conclusions (firstn n proofs))
                  (LOGIC.DISJOIN-EACH-FORMULA-LIST (LOGIC.TERM-LIST-LIST-FORMULAS (firstn n goals)))))
  :hints(("Goal"
          :in-theory (disable FIRSTN-OF-LOGIC.DISJOIN-EACH-FORMULA-LIST)
          :use ((:instance FIRSTN-OF-LOGIC.DISJOIN-EACH-FORMULA-LIST
                           (Y n)
                           (X (LOGIC.TERM-LIST-LIST-FORMULAS goals)))))))

(defthm crock3-for-tactic.induct-compile
  (implies (EQUAL (LOGIC.DISJOIN-EACH-FORMULA-LIST (LOGIC.TERM-LIST-LIST-FORMULAS goals))
                  (LOGIC.STRIP-CONCLUSIONS PROOFS))
           (equal (logic.strip-conclusions (firstn n (cdr (cdr proofs))))
                  (LOGIC.DISJOIN-EACH-FORMULA-LIST (LOGIC.TERM-LIST-LIST-FORMULAS (firstn n (cdr (cdr goals)))))))
  :hints(("Goal"
          :in-theory (disable FIRSTN-OF-LOGIC.DISJOIN-EACH-FORMULA-LIST)
          :use ((:instance FIRSTN-OF-LOGIC.DISJOIN-EACH-FORMULA-LIST
                           (Y n)
                           (X (LOGIC.TERM-LIST-LIST-FORMULAS (cdr (cdr goals)))))))))

(defthm crock4-for-tactic.induct-compile
  (implies (equal (app a b) x)
           (equal (firstn (len a) x)
                  (list-fix a))))

(defthm crock5-for-tactic.induct-compile
  (implies (equal (app a b) x)
           (equal (restn (len a) x)
                  (list-fix b))))

(defthm crock6-for-tactic.induct-compile
  (implies (equal (app a (app b c)) x)
           (equal (firstn (len b) (restn (len a) x))
                  (list-fix b))))

(defthm crock7-for-tactic.induct-compile
  (implies (EQUAL (LOGIC.DISJOIN-EACH-FORMULA-LIST (LOGIC.TERM-LIST-LIST-FORMULAS goals))
                  (LOGIC.STRIP-CONCLUSIONS PROOFS))
           (equal (logic.conclusion (car proofs))
                  (logic.disjoin-formulas (logic.term-list-formulas (car goals))))))

(defthm crock8-for-tactic.induct-compile
  (implies (EQUAL (LOGIC.DISJOIN-EACH-FORMULA-LIST (LOGIC.TERM-LIST-LIST-FORMULAS goals))
                  (LOGIC.STRIP-CONCLUSIONS PROOFS))
           (equal (logic.conclusion (second proofs))
                  (logic.disjoin-formulas (logic.term-list-formulas (second goals))))))

(defthm crock9-for-tactic.induct-compile
  (implies (EQUAL (LOGIC.DISJOIN-EACH-FORMULA-LIST (LOGIC.TERM-LIST-LIST-FORMULAS goals))
                  (LOGIC.STRIP-CONCLUSIONS PROOFS))
           (equal (consp proofs)
                  (consp goals))))

(defthm crock10-for-tactic.induct-compile
  (implies (EQUAL (LOGIC.DISJOIN-EACH-FORMULA-LIST (LOGIC.TERM-LIST-LIST-FORMULAS goals))
                  (LOGIC.STRIP-CONCLUSIONS PROOFS))
           (equal (consp (cdr proofs))
                  (consp (cdr goals)))))

(defthm crock11-for-tactic.induct-compile
  (implies (EQUAL (LOGIC.DISJOIN-EACH-FORMULA-LIST (LOGIC.TERM-LIST-LIST-FORMULAS goals))
                  (LOGIC.STRIP-CONCLUSIONS PROOFS))
           (equal (logic.strip-conclusions (restn n (cdr (cdr proofs))))
                  (LOGIC.DISJOIN-EACH-FORMULA-LIST (LOGIC.TERM-LIST-LIST-FORMULAS (restn n (cdr (cdr goals)))))))
  :hints(("Goal"
          :in-theory (disable RESTN-OF-LOGIC.DISJOIN-EACH-FORMULA-LIST)
          :use ((:instance RESTN-OF-LOGIC.DISJOIN-EACH-FORMULA-LIST
                           (Y n)
                           (X (LOGIC.TERM-LIST-LIST-FORMULAS (cdr (cdr goals)))))))))

(defthm crock12-for-tactic.induct-compile
  (implies (EQUAL (LOGIC.DISJOIN-EACH-FORMULA-LIST (LOGIC.TERM-LIST-LIST-FORMULAS goals))
                  (LOGIC.STRIP-CONCLUSIONS PROOFS))
           (equal (logic.strip-conclusions (firstn n (restn m proofs)))
                  (LOGIC.DISJOIN-EACH-FORMULA-LIST (LOGIC.TERM-LIST-LIST-FORMULAS (firstn n (restn m goals))))))
  :hints(("Goal"
          :in-theory (disable FIRSTN-OF-LOGIC.DISJOIN-EACH-FORMULA-LIST
                              RESTN-OF-LOGIC.DISJOIN-EACH-FORMULA-LIST)
          :use ((:instance FIRSTN-OF-LOGIC.DISJOIN-EACH-FORMULA-LIST
                           (Y n)
                           (X (LOGIC.TERM-LIST-LIST-FORMULAS (restn m goals))))
                (:instance RESTN-OF-LOGIC.DISJOIN-EACH-FORMULA-LIST
                           (Y m)
                           (X (LOGIC.TERM-LIST-LIST-FORMULAS goals)))))))

(defthm crock13-for-tactic.induct-compile
  (implies (EQUAL (LOGIC.DISJOIN-EACH-FORMULA-LIST (LOGIC.TERM-LIST-LIST-FORMULAS goals))
                  (LOGIC.STRIP-CONCLUSIONS PROOFS))
           (equal (logic.strip-conclusions (firstn n (restn m (cdr (cdr proofs)))))
                  (LOGIC.DISJOIN-EACH-FORMULA-LIST
                   (LOGIC.TERM-LIST-LIST-FORMULAS (firstn n (restn m (cdr (cdr goals)))))))))

(defthm crock14-for-tactic.induct-compile
  (implies (EQUAL (LOGIC.DISJOIN-EACH-FORMULA-LIST (LOGIC.TERM-LIST-LIST-FORMULAS goals))
                  (LOGIC.STRIP-CONCLUSIONS PROOFS))
           (equal (logic.strip-conclusions (restn n (restn m proofs)))
                  (LOGIC.DISJOIN-EACH-FORMULA-LIST (LOGIC.TERM-LIST-LIST-FORMULAS (restn n (restn m goals))))))
  :hints(("Goal"
          :in-theory (disable RESTN-OF-LOGIC.DISJOIN-EACH-FORMULA-LIST)
          :use ((:instance RESTN-OF-LOGIC.DISJOIN-EACH-FORMULA-LIST
                           (Y n)
                           (X (LOGIC.TERM-LIST-LIST-FORMULAS (restn m goals))))
                (:instance RESTN-OF-LOGIC.DISJOIN-EACH-FORMULA-LIST
                           (Y m)
                           (X (LOGIC.TERM-LIST-LIST-FORMULAS goals)))))))

(defthm crock15-for-tactic.induct-compile
  (implies (EQUAL (LOGIC.DISJOIN-EACH-FORMULA-LIST (LOGIC.TERM-LIST-LIST-FORMULAS goals))
                  (LOGIC.STRIP-CONCLUSIONS PROOFS))
           (equal (logic.strip-conclusions (restn n (restn m (cdr (cdr proofs)))))
                  (LOGIC.DISJOIN-EACH-FORMULA-LIST
                   (LOGIC.TERM-LIST-LIST-FORMULAS (restn n (restn m (cdr (cdr goals)))))))))





(%autoprove crock1-for-tactic.induct-compile)
(%autoprove crock2-for-tactic.induct-compile
            (%disable default
                      FIRSTN-OF-LOGIC.DISJOIN-EACH-FORMULA-LIST
                      [outside]FIRSTN-OF-LOGIC.DISJOIN-EACH-FORMULA-LIST)
            (%use (%instance (%thm FIRSTN-OF-LOGIC.DISJOIN-EACH-FORMULA-LIST)
                             (Y n)
                             (X (LOGIC.TERM-LIST-LIST-FORMULAS goals)))))
(%autoprove crock3-for-tactic.induct-compile
            (%disable default
                      FIRSTN-OF-LOGIC.DISJOIN-EACH-FORMULA-LIST
                      [outside]FIRSTN-OF-LOGIC.DISJOIN-EACH-FORMULA-LIST)
            (%use (%instance (%thm FIRSTN-OF-LOGIC.DISJOIN-EACH-FORMULA-LIST)
                             (Y n)
                             (X (LOGIC.TERM-LIST-LIST-FORMULAS (cdr (cdr goals)))))))
(%autoprove crock4-for-tactic.induct-compile)
(%autoprove crock5-for-tactic.induct-compile)
(%autoprove crock6-for-tactic.induct-compile)
(%autoprove crock7-for-tactic.induct-compile)

(%autoprove crock8-for-tactic.induct-compile
            (%restrict default logic.strip-conclusions (or (equal x 'proofs)
                                                           (equal x '(cdr proofs)))))

(%autoprove crock9-for-tactic.induct-compile)
(%autoprove crock10-for-tactic.induct-compile)

(%autoprove crock11-for-tactic.induct-compile
            (%disable default
                      RESTN-OF-LOGIC.DISJOIN-EACH-FORMULA-LIST
                      [outside]RESTN-OF-LOGIC.DISJOIN-EACH-FORMULA-LIST)
            (%use (%instance (%thm RESTN-OF-LOGIC.DISJOIN-EACH-FORMULA-LIST)
                             (Y n)
                             (X (LOGIC.TERM-LIST-LIST-FORMULAS (cdr (cdr goals)))))))

(%autoprove crock12-for-tactic.induct-compile
            (%disable default
                      FIRSTN-OF-LOGIC.DISJOIN-EACH-FORMULA-LIST
                      [outside]FIRSTN-OF-LOGIC.DISJOIN-EACH-FORMULA-LIST
                      RESTN-OF-LOGIC.DISJOIN-EACH-FORMULA-LIST
                      [outside]RESTN-OF-LOGIC.DISJOIN-EACH-FORMULA-LIST
                      ;; causing rewrite loop??
                      crock1-for-tactic.induct-compile
                      )
            (%use (%instance (%thm FIRSTN-OF-LOGIC.DISJOIN-EACH-FORMULA-LIST)
                             (Y n)
                             (X (LOGIC.TERM-LIST-LIST-FORMULAS (restn m goals)))))
            (%use (%instance (%thm RESTN-OF-LOGIC.DISJOIN-EACH-FORMULA-LIST)
                             (Y m)
                             (X (LOGIC.TERM-LIST-LIST-FORMULAS goals)))))

(%autoprove crock13-for-tactic.induct-compile)

(%autoprove crock14-for-tactic.induct-compile
            (%disable default
                      RESTN-OF-LOGIC.DISJOIN-EACH-FORMULA-LIST
                      [outside]RESTN-OF-LOGIC.DISJOIN-EACH-FORMULA-LIST
                      ;; loop again??
                      crock1-for-tactic.induct-compile)
            (%use (%instance (%thm RESTN-OF-LOGIC.DISJOIN-EACH-FORMULA-LIST)
                             (Y n)
                             (X (LOGIC.TERM-LIST-LIST-FORMULAS (restn m goals)))))
            (%use (%instance (%thm RESTN-OF-LOGIC.DISJOIN-EACH-FORMULA-LIST)
                             (Y m)
                             (X (LOGIC.TERM-LIST-LIST-FORMULAS goals)))))

(%autoprove crock15-for-tactic.induct-compile
            (%disable default
                      expensive-arithmetic-rules
                      expensive-term/formula-inference))


(in-theory (disable
            CROCK1-FOR-TACTIC.INDUCT-COMPILE
            CROCK2-FOR-TACTIC.INDUCT-COMPILE
            CROCK3-FOR-TACTIC.INDUCT-COMPILE
            CROCK4-FOR-TACTIC.INDUCT-COMPILE
            CROCK5-FOR-TACTIC.INDUCT-COMPILE
            CROCK6-FOR-TACTIC.INDUCT-COMPILE
            CROCK7-FOR-TACTIC.INDUCT-COMPILE
            CROCK8-FOR-TACTIC.INDUCT-COMPILE
            CROCK9-FOR-TACTIC.INDUCT-COMPILE
            CROCK10-FOR-TACTIC.INDUCT-COMPILE
            CROCK11-FOR-TACTIC.INDUCT-COMPILE
            CROCK12-FOR-TACTIC.INDUCT-COMPILE
            CROCK13-FOR-TACTIC.INDUCT-COMPILE
            CROCK14-FOR-TACTIC.INDUCT-COMPILE
            CROCK15-FOR-TACTIC.INDUCT-COMPILE))


(encapsulate
 ()
 (%autoadmit tactic.induct-compile)
 (local (%enable default
                 tactic.induct-okp
                 tactic.induct-env-okp
                 tactic.induct-compile))
 (%autoprove forcing-logic.appeal-listp-of-tactic.induct-compile)
 (%autoprove forcing-logic.strip-conclusions-of-tactic.induct-compile)
 (%autoprove forcing-logic.proof-listp-of-tactic.induct-compile))

(%disable default
          CROCK1-FOR-TACTIC.INDUCT-COMPILE
          CROCK2-FOR-TACTIC.INDUCT-COMPILE
          CROCK3-FOR-TACTIC.INDUCT-COMPILE
          CROCK4-FOR-TACTIC.INDUCT-COMPILE
          CROCK5-FOR-TACTIC.INDUCT-COMPILE
          CROCK6-FOR-TACTIC.INDUCT-COMPILE
          CROCK7-FOR-TACTIC.INDUCT-COMPILE
          CROCK8-FOR-TACTIC.INDUCT-COMPILE
          CROCK9-FOR-TACTIC.INDUCT-COMPILE
          CROCK10-FOR-TACTIC.INDUCT-COMPILE
          CROCK11-FOR-TACTIC.INDUCT-COMPILE
          CROCK12-FOR-TACTIC.INDUCT-COMPILE
          CROCK13-FOR-TACTIC.INDUCT-COMPILE
          CROCK14-FOR-TACTIC.INDUCT-COMPILE
          CROCK15-FOR-TACTIC.INDUCT-COMPILE)

(%ensure-exactly-these-rules-are-missing "../../tactics/induct")

