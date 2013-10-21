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
(include-book "../prop")
(include-book "casesplit")
(include-book "factor-bldr")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


(defthm cdr-of-logic.smart-negate-formulas
  ;; BOZO move me
  (equal (cdr (logic.smart-negate-formulas x))
         (logic.smart-negate-formulas (cdr x))))

(defthm car-of-logic.smart-negate-formulas
  ;; BOZO move me
  (equal (car (logic.smart-negate-formulas x))
         (if (consp x)
             (if (equal (logic.fmtype (car x)) 'pnot*)
                 (logic.~arg (car x))
               (logic.pnot (car x)))
           nil))
  :hints(("Goal" :in-theory (disable FORCING-EQUAL-OF-LOGIC.PNOT-REWRITE-TWO
                                     FORCING-EQUAL-OF-LOGIC.PNOT-REWRITE))))




;; (clause.cases-bldr a cases assignment)
;;
;; We prove:
;;
;;   - a = a' if assignment is empty, or
;;   - hyps v a = a' otherwise,
;;
;; Where:
;;
;;   - a' = (clause.casesplit a cases assignment), and
;;   - hyps are the assumptions implied by assignment (as in clause.factor).

(deftheorem clause.cases-lemma
  :derive (v (! (v (= x nil) (= a y)))
             (v (! (v (!= x nil) (= a z)))
                (= a (if x y z))))
  :proof  (@derive
           ((v (= x nil) (= (if x y z) y))                                  (build.axiom (axiom-if-when-not-nil)))
           ((v (= x nil) (= y (if x y z)))                                  (build.disjoined-commute-pequal @-))
           ((v (v (! (v (= x nil) (= a y))) (= x nil)) (= y (if x y z)))    (build.multi-assoc-expansion @- (@formulas (! (v (= x nil) (= a y))) (= x nil)))   *1a)
           ((v (! (v (= x nil) (= a y))) (v (= x nil) (= a y)))             (build.propositional-schema (@formula (v (= x nil) (= a y)))))
           ((v (v (! (v (= x nil) (= a y))) (= x nil)) (= a y))             (build.associativity @-))
           ((v (v (! (v (= x nil) (= a y))) (= x nil)) (= a (if x y z)))    (build.disjoined-transitivity-of-pequal @- *1a))
           ((v (! (v (= x nil) (= a y))) (v (= x nil) (= a (if x y z))))    (build.right-associativity @-))
           ((v (v (= x nil) (= a (if x y z))) (! (v (= x nil) (= a y))))    (build.commute-or @-))
           ((v (= x nil) (v (= a (if x y z)) (! (v (= x nil) (= a y)))))    (build.right-associativity @-)  *1)
           ;; ---
           ((v (!= x nil) (= (if x y z) z))                                 (build.axiom (axiom-if-when-nil)))
           ((v (!= x nil) (= z (if x y z)))                                 (build.disjoined-commute-pequal @-))
           ((v (v (! (v (!= x nil) (= a z))) (!= x nil)) (= z (if x y z)))  (build.multi-assoc-expansion @- (@formulas (! (v (!= x nil) (= a z))) (!= x nil)))  *2a)
           ((v (! (v (!= x nil) (= a z))) (v (!= x nil) (= a z)))           (build.propositional-schema (@formula (v (!= x nil) (= a z)))))
           ((v (v (! (v (!= x nil) (= a z))) (!= x nil)) (= a z))           (build.associativity @-))
           ((v (v (! (v (!= x nil) (= a z))) (!= x nil)) (= a (if x y z)))  (build.disjoined-transitivity-of-pequal @- *2a))
           ((v (! (v (!= x nil) (= a z))) (v (!= x nil) (= a (if x y z))))  (build.right-associativity @-))
           ((v (v (!= x nil) (= a (if x y z))) (! (v (!= x nil) (= a z))))  (build.commute-or @-))
           ((v (!= x nil) (v (= a (if x y z)) (! (v (!= x nil) (= a z)))))  (build.right-associativity @-)  *2)
           ;; ---
           ((v (v (= a (if x y z)) (! (v (= x nil) (= a y))))
               (v (= a (if x y z)) (! (v (!= x nil) (= a z)))))             (build.cut *1 *2))
           ((v (v (= a (if x y z)) (= a (if x y z)))
               (v (! (v (!= x nil) (= a z))) (! (v (= x nil) (= a y)))))    (build.disjoined-assoc-lemma-3 @-))
           ((v (v (= a (if x y z)) (= a (if x y z)))
               (v (! (v (= x nil) (= a y))) (! (v (!= x nil) (= a z)))))    (build.disjoined-commute-or @-))
           ((v (v (! (v (= x nil) (= a y))) (! (v (!= x nil) (= a z))))
               (v (= a (if x y z)) (= a (if x y z))))                       (build.commute-or @-))
           ((v (v (! (v (= x nil) (= a y))) (! (v (!= x nil) (= a z))))
               (= a (if x y z)))                                            (build.disjoined-contraction @-))
           ((v (! (v (= x nil) (= a y)))
               (v (! (v (!= x nil) (= a z)))
                  (= a (if x y z))))                                        (build.right-associativity @-)))
  :minatbl ((if . 3)))

(defderiv clause.cases-lemma1-bldr
  :derive (= (? a) (if (? x) (? b) (? c)))
  :from   ((proof x (v (= (? x) nil) (= (? a) (? b))))
           (proof y (v (!= (? x) nil) (= (? a) (? c)))))
  :proof  (@derive
           ((v (! (v (= x nil) (= a y)))
               (v (! (v (!= x nil) (= a z)))
                  (= a (if x y z))))                        (build.theorem (clause.cases-lemma)))
           ((v (! (v (= (? x) nil) (= (? a) (? b))))
               (v (! (v (!= (? x) nil) (= (? a) (? c))))
                  (= (? a) (if (? x) (? b) (? c)))))        (build.instantiation @- (@sigma (x . (? x)) (a . (? a)) (y . (? b)) (z . (? c)))))
           ((v (= (? x) nil) (= (? a) (? b)))               (@given x))
           ((v (! (v (!= (? x) nil) (= (? a) (? c))))
                  (= (? a) (if (? x) (? b) (? c))))         (build.modus-ponens @- @--))
           ((v (!= (? x) nil) (= (? a) (? c)))              (@given y))
           ((= (? a) (if (? x) (? b) (? c)))                (build.modus-ponens @- @--)))
  :minatbl ((if . 3)))

(defderiv clause.disjoined-cases-lemma1-bldr
  :derive (v P (= (? a) (if (? x) (? b) (? c))))
  :from   ((proof x (v P (v (= (? x) nil) (= (? a) (? b)))))
           (proof y (v P (v (!= (? x) nil) (= (? a) (? c))))))
  :proof  (@derive
           ((v (! (v (= x nil) (= a y)))
               (v (! (v (!= x nil) (= a z)))
                  (= a (if x y z))))                            (build.theorem (clause.cases-lemma)))
           ((v (! (v (= (? x) nil) (= (? a) (? b))))
               (v (! (v (!= (? x) nil) (= (? a) (? c))))
                  (= (? a) (if (? x) (? b) (? c)))))            (build.instantiation @- (@sigma (x . (? x)) (a . (? a)) (y . (? b)) (z . (? c)))))
           ((v P (v (! (v (= (? x) nil) (= (? a) (? b))))
                    (v (! (v (!= (? x) nil) (= (? a) (? c))))
                       (= (? a) (if (? x) (? b) (? c))))))      (build.expansion (@formula P) @-))
           ((v P (v (= (? x) nil) (= (? a) (? b))))             (@given x))
           ((v P (v (! (v (!= (? x) nil) (= (? a) (? c))))
                    (= (? a) (if (? x) (? b) (? c)))))          (build.disjoined-modus-ponens @- @--))
           ((v P (v (!= (? x) nil) (= (? a) (? c))))            (@given y))
           ((v P (= (? a) (if (? x) (? b) (? c))))              (build.disjoined-modus-ponens @- @--)))
  :minatbl ((if . 3)))



(defund@ clause.cases-bldr (a cases assignment)
  (declare (xargs :guard (and (logic.termp a)
                              (logic.term-listp cases)
                              (mapp assignment)
                              (logic.term-listp (domain assignment)))
                  :verify-guards nil))
  (if (consp cases)
      ;; There are still cases to split on.
      (let* ((then-assignment (update (car cases) t assignment))
             (else-assignment (update (car cases) nil assignment))
             (then-proof      (clause.cases-bldr a (cdr cases) then-assignment))
             (else-proof      (clause.cases-bldr a (cdr cases) else-assignment))
             (at              (logic.=rhs (logic.vrhs (logic.conclusion then-proof))))
             (anil            (logic.=rhs (logic.vrhs (logic.conclusion else-proof)))))
        (if (not (consp assignment))
            ;; There are no hyps.
            (if (equal at anil)
                ;; Splitting on case1 does not change a.
                (@derive ((v (= case1 nil) (= a at))     (@given then-proof))
                         ((v (!= case1 nil) (= a anil))  (@given else-proof))
                         ((v (= a at) (= a anil))        (build.cut @-- @-))
                         ((= a at)                       (build.contraction @-)))
              ;; Splitting on case1 changes a.
              (@derive ((v (= case1 nil) (= a at))       (@given then-proof))
                       ((v (!= case1 nil) (= a anil))    (@given else-proof))
                       ((= a (if case1 at anil))         (clause.cases-lemma1-bldr @-- @-))))
          ;; Else there are some hyps.
          (if (equal at anil)
              ;; Splitting on case1 does not change a.
              (@derive ((v (v (= case1 nil) hyps) (= a at))        (@given then-proof))
                       ((v (v (!= case1 nil) hyps) (= a anil))     (@given else-proof))
                       ((v (= case1 nil) (v hyps (= a at)))        (build.right-associativity @--))
                       ((v (!= case1 nil) (v hyps (= a anil)))     (build.right-associativity @--))
                       ((v (v hyps (= a at)) (v hyps (= a anil)))  (build.cut @-- @-))
                       ((v hyps (= a at))                          (build.contraction @-)))
            ;; Splitting on case1 changes a.
            (@derive ((v (v (= case1 nil) hyps) (= a at))      (@given then-proof))
                     ((v (v (!= case1 nil) hyps) (= a anil))   (@given else-proof))
                     ((v hyps (v (= case1 nil) (= a at)))      (build.lhs-commute-or-then-rassoc @--))
                     ((v hyps (v (!= case1 nil) (= a anil)))   (build.lhs-commute-or-then-rassoc @--))
                     ((v hyps (= a (if case1 at anil)))        (clause.disjoined-cases-lemma1-bldr @-- @-))))))
    ;; Else there are no more cases to split on.
    (if (consp assignment)
        (clause.factor-bldr a assignment)
      (build.reflexivity a))))

(defobligations clause.cases-bldr
  (build.cut build.contraction clause.cases-lemma1-bldr build.right-associativity
   build.lhs-commute-or-then-rassoc clasue.disjoined-cases-lemma1-bldr clause.factor-bldr
   build.reflexivity))

(encapsulate
 ()
 (defthmd lemma-for-forcing-logic.appealp-of-clause.cases-bldr
   (implies (and (logic.termp a)
                 (logic.term-listp cases)
                 (logic.term-listp (domain assignment)))
            (and (logic.appealp (clause.cases-bldr a cases assignment))
                 (equal (logic.conclusion (clause.cases-bldr a cases assignment))
                        (if (consp assignment)
                            (logic.por (logic.disjoin-formulas (logic.smart-negate-formulas (assignment-formulas assignment)))
                                       (logic.pequal a (clause.casesplit a cases assignment)))
                          (logic.pequal a (clause.casesplit a cases assignment))))))
   :hints(("Goal"
           :do-not-induct t
           :in-theory (enable clause.cases-bldr)
           :induct (clause.cases-bldr a cases assignment))))

 (local (in-theory (enable lemma-for-forcing-logic.appealp-of-clause.cases-bldr)))

 (defthm forcing-logic.appealp-of-clause.cases-bldr
   (implies (force (and (logic.termp a)
                        (logic.term-listp cases)
                        (logic.term-listp (domain assignment))))
            (equal (logic.appealp (clause.cases-bldr a cases assignment))
                   t)))

 (defthm forcing-logic.conclusion-of-clause.cases-bldr
   (implies (force (and (logic.termp a)
                        (logic.term-listp cases)
                        (logic.term-listp (domain assignment))))
            (equal (logic.conclusion (clause.cases-bldr a cases assignment))
                   (if (consp assignment)
                       (logic.por (logic.disjoin-formulas (logic.smart-negate-formulas (assignment-formulas assignment)))
                                  (logic.pequal a (clause.casesplit a cases assignment)))
                     (logic.pequal a (clause.casesplit a cases assignment)))))
   :rule-classes ((:rewrite :backchain-limit-lst 0))))

(verify-guards clause.cases-bldr)


(defthm@ forcing-proofp-of-clause.cases-bldr
  (implies (force (and (logic.termp a)
                       (logic.term-listp cases)
                       (logic.term-listp (domain assignment))
                       ;; ---
                       (logic.term-atblp a atbl)
                       (logic.term-list-atblp cases atbl)
                       (logic.term-list-atblp (domain assignment) atbl)
                       (equal (cdr (lookup 'if atbl)) 3)
                       (@obligations clause.cases-bldr)))
           (equal (logic.proofp (clause.cases-bldr a cases assignment) axioms thms atbl)
                  t))
  :hints(("Goal"
          :in-theory (enable clause.cases-bldr)
          :induct (clause.cases-bldr a cases assignment))))



