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
(include-book "prop")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)

(dd.open "disjoined-rev-disjunction.tex")


(defderiv build.disjoined-revappend-disjunction-lemma1-bldr
  :derive (v P (v Q (v t1 R)))
  :from   ((proof x (v P (v (v t1 Q) R))))
  :proof  (@derive
           ((v P (v (v t1 Q) R))    (@given x))
           ((v P (v R (v t1 Q)))    (build.disjoined-commute-or @-))
           ((v P (v (v R t1) Q))    (build.disjoined-associativity @-))
           ((v P (v Q (v R t1)))    (build.disjoined-commute-or @-))
           ((v (v P Q) (v R t1))    (build.associativity @-))
           ((v (v P Q) (v t1 R))    (build.disjoined-commute-or @-))
           ((v P (v Q (v t1 R)))    (build.right-associativity @-))))

(defund@ build.disjoined-revappend-disjunction (p todo done proof)
  ;; Derive P v tn v ... v t1 v d1 v ... v dm from P v (t1 v ... v tn) v (d1 v ... v dm)
  (declare (xargs :guard (and (logic.formulap p)
                              (logic.formula-listp todo)
                              (logic.formula-listp done)
                              (or (consp todo) (consp done))
                              (logic.appealp proof)
                              (equal (logic.conclusion proof)
                                     (cond ((and (consp todo)
                                                 (consp done))
                                            (logic.por p (logic.por (logic.disjoin-formulas todo)
                                                                    (logic.disjoin-formulas done))))
                                           ((consp todo)
                                            (logic.por p (logic.disjoin-formulas todo)))
                                           (t
                                            (logic.por p (logic.disjoin-formulas done))))))
                  :verify-guards nil))
  (if (and (consp todo)
           (consp (cdr todo)))
      (if (consp done)
          (build.disjoined-revappend-disjunction p
                                                 (cdr todo)
                                                 (cons (car todo) done)
                                                 ;; P v (t1 v t2-tn) v d1-dm
                                                 ;; ------------------------
                                                 ;; P v t2-tn v t1 v d1-dm
                                                 (build.disjoined-revappend-disjunction-lemma1-bldr proof))
        (build.disjoined-revappend-disjunction p
                                               (cdr todo)
                                               (cons (car todo) done)
                                               ;; P v t1 v t2-tn
                                               ;; --------------
                                               ;; P v t2-tn v t1
                                               (build.disjoined-commute-or proof)))
    ;; Otherwise, the todo list is only one long, so we already have the proof
    ;; we were looking for.
    (logic.appeal-identity proof)))

(encapsulate
 ()
 (local (in-theory (enable build.disjoined-revappend-disjunction)))

 (defthm build.disjoined-revappend-disjunction-under-iff
   (iff (build.disjoined-revappend-disjunction p todo done proof)
        t))

 (local (defthm lemma
          (implies (and (logic.formulap p)
                        (logic.formula-listp todo)
                        (logic.formula-listp done)
                        (or (consp todo) (consp done))
                        (logic.appealp proof)
                        (equal (logic.conclusion proof)
                               (cond ((and (consp todo)
                                           (consp done))
                                      (logic.por p (logic.por (logic.disjoin-formulas todo)
                                                              (logic.disjoin-formulas done))))
                                     ((consp todo)
                                      (logic.por p (logic.disjoin-formulas todo)))
                                     (t
                                      (logic.por p (logic.disjoin-formulas done))))))
                   (and (logic.appealp (build.disjoined-revappend-disjunction p todo done proof))
                        (equal (logic.conclusion (build.disjoined-revappend-disjunction p todo done proof))
                               (logic.por p (logic.disjoin-formulas (app (rev todo) done))))))))

 (defthm forcing-logic.appealp-of-build.disjoined-revappend-disjunction
   (implies (force (and (logic.formulap p)
                        (logic.formula-listp todo)
                        (logic.formula-listp done)
                        (or (consp todo) (consp done))
                        (logic.appealp proof)
                        (equal (logic.conclusion proof)
                               (cond ((and (consp todo)
                                           (consp done))
                                      (logic.por p (logic.por (logic.disjoin-formulas todo)
                                                              (logic.disjoin-formulas done))))
                                     ((consp todo)
                                      (logic.por p (logic.disjoin-formulas todo)))
                                     (t
                                      (logic.por p (logic.disjoin-formulas done)))))))
            (equal (logic.appealp (build.disjoined-revappend-disjunction p todo done proof))
                   t)))

 (defthm forcing-logic.conclusion-of-build.disjoined-revappend-disjunction
   (implies (force (and (logic.formulap p)
                        (logic.formula-listp todo)
                        (logic.formula-listp done)
                        (or (consp todo) (consp done))
                        (logic.appealp proof)
                        (equal (logic.conclusion proof)
                               (cond ((and (consp todo)
                                           (consp done))
                                      (logic.por p (logic.por (logic.disjoin-formulas todo)
                                                              (logic.disjoin-formulas done))))
                                     ((consp todo)
                                      (logic.por p (logic.disjoin-formulas todo)))
                                     (t
                                      (logic.por p (logic.disjoin-formulas done)))))))
            (equal (logic.conclusion (build.disjoined-revappend-disjunction p todo done proof))
                   (logic.por p (logic.disjoin-formulas (app (rev todo) done)))))
   :rule-classes ((:rewrite :backchain-limit-lst 0)))

 (verify-guards build.disjoined-revappend-disjunction)

 (defthm forcing-logic.proofp-of-build.disjoined-revappend-disjunction
   (implies (force (and (logic.formulap p)
                        (logic.formula-listp todo)
                        (logic.formula-listp done)
                        (or (consp todo) (consp done))
                        (logic.appealp proof)
                        (equal (logic.conclusion proof)
                               (cond ((and (consp todo)
                                           (consp done))
                                      (logic.por p (logic.por (logic.disjoin-formulas todo)
                                                              (logic.disjoin-formulas done))))
                                     ((consp todo)
                                      (logic.por p (logic.disjoin-formulas todo)))
                                     (t
                                      (logic.por p (logic.disjoin-formulas done)))))
                        ;; ---
                        (logic.proofp proof axioms thms atbl)))
            (equal (logic.proofp (build.disjoined-revappend-disjunction p todo done proof) axioms thms atbl)
                   t))))


(defund build.disjoined-rev-disjunction (x proof)
  ;; Derive P v tn v ... v t1 from P v t1 v ... v tn
  ;; (x should be the list of formulas [t1, ..., tn])
  (declare (xargs :guard (and (consp x)
                              (logic.formula-listp x)
                              (logic.appealp proof)
                              (equal (logic.fmtype (logic.conclusion proof)) 'por*)
                              (equal (logic.vrhs (logic.conclusion proof))
                                     (logic.disjoin-formulas x)))
                  :export (build.generic-subset
                           (cons (logic.vlhs (logic.conclusion proof))
                                 x)
                           (cons (logic.vlhs (logic.conclusion proof))
                                 (fast-rev x))
                           proof)))
  (build.disjoined-revappend-disjunction (logic.vlhs (logic.conclusion proof)) x nil proof))

(encapsulate
 ()
 (local (in-theory (enable build.disjoined-rev-disjunction)))

 (defthm build.disjoined-rev-disjunction-under-iff
   (iff (build.disjoined-rev-disjunction x proof)
        t))

 (defthm forcing-logic.appealp-of-build.disjoined-rev-disjunction
   (implies (force (and (consp x)
                        (logic.formula-listp x)
                        (logic.appealp proof)
                        (equal (logic.fmtype (logic.conclusion proof)) 'por*)
                        (equal (logic.vrhs (logic.conclusion proof))
                               (logic.disjoin-formulas x))))
            (equal (logic.appealp (build.disjoined-rev-disjunction x proof))
                   t)))

 (defthm forcing-logic.conclusion-of-build.disjoined-rev-disjunction
   (implies (force (and (consp x)
                        (logic.formula-listp x)
                        (logic.appealp proof)
                        (equal (logic.fmtype (logic.conclusion proof)) 'por*)
                        (equal (logic.vrhs (logic.conclusion proof))
                               (logic.disjoin-formulas x))))
            (equal (logic.conclusion (build.disjoined-rev-disjunction x proof))
                   (logic.por (logic.vlhs (logic.conclusion proof))
                              (logic.disjoin-formulas (rev x)))))
   :rule-classes ((:rewrite :backchain-limit-lst 0)))

 (defthm forcing-logic.proofp-of-build.disjoined-rev-disjunction
   (implies (force (and (consp x)
                        (logic.formula-listp x)
                        (logic.appealp proof)
                        (equal (logic.fmtype (logic.conclusion proof)) 'por*)
                        (equal (logic.vrhs (logic.conclusion proof))
                               (logic.disjoin-formulas x))
                        ;; ---
                        (logic.proofp proof axioms thms atbl)))
            (equal (logic.proofp (build.disjoined-rev-disjunction x proof) axioms thms atbl)
                   t))))

(dd.close)