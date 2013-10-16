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
(include-book "../logic/top")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)



;; Clauses
;;
;; We use CLAUSES to represent our goals in goal-directed proof construction.
;; Each clause represents a disjunction of terms, i.e., L1 v ... v Ln, which
;; more accurately should be written as L1 != nil v ... v L1 != nil.  We just
;; use term lists to represent a clausees, but the empty clause does not have a
;; well defined meaning and we consider it to be degenerate.  The terms in a
;; clause are called LITERALS.

(defund clause.clause-formula (x)
  ;; NOTE: we (effectively) leave this function enabled via the redefinition rule below!
  (declare (xargs :guard (and (logic.term-listp x)
                              (consp x))))
  (if (consp x)
      (if (consp (cdr x))
          (logic.por (logic.term-formula (car x))
                     (clause.clause-formula (cdr x)))
        (logic.term-formula (car x)))
    nil))

(defthm redefinition-of-clause.clause-formula
  (equal (clause.clause-formula x)
         (logic.disjoin-formulas (logic.term-list-formulas x)))
  :rule-classes :definition
  :hints(("Goal" :in-theory (enable clause.clause-formula logic.disjoin-formulas))))

(ACL2::theory-invariant (not (ACL2::active-runep '(:definition clause.clause-formula))))



(defund clause.clause-list-formulas (x)
  ;; NOTE: we (effectively) leave this function enabled via the redefinition rule below!
  (declare (xargs :guard (and (logic.term-list-listp x)
                              (cons-listp x))))
  (if (consp x)
      (cons (clause.clause-formula (car x))
            (clause.clause-list-formulas (cdr x)))
    nil))

(defthm redefinition-of-clause.clause-list-formulas
  (equal (clause.clause-list-formulas x)
         (logic.disjoin-each-formula-list (logic.term-list-list-formulas x)))
  :hints(("Goal" :in-theory (enable clause.clause-list-formulas))))

(ACL2::theory-invariant (not (ACL2::active-runep '(:definition clause.clause-list-formulas))))





;; Polarity of literals.
;;
;; We sometimes talk about literals being POSITIVE or NEGATIVE.  A literal is
;; positive unless it matches one of the following patterns:
;;
;;    (not x)
;;    (if x nil t)
;;    (equal x nil)
;;    (equal nil x)
;;    (iff x nil)
;;    (iff nil x)
;;
;; The GUTS of a negative literals are the term being negated, e.g., the guts
;; of (not (consp 3)) are (consp 3).  The guts of a positive literal are the
;; entire literal, i.e., the guts of (+ 1 2) are (+ 1 2).

(definlined clause.negative-termp (x)
  (declare (xargs :guard (logic.termp x)))
  (and (logic.functionp x)
       (let ((name (logic.function-name x))
             (args (logic.function-args x)))
         (or (and (equal name 'not)
                  (equal (len args) 1))
             (and (equal name 'if)
                  (equal (len args) 3)
                  (equal (second args) ''nil)
                  (equal (third args) ''t))
             (and (equal name 'equal)
                  (equal (len args) 2)
                  (or (equal (first args) ''nil)
                      (equal (second args) ''nil)))
             (and (equal name 'iff)
                  (equal (len args) 2)
                  (or (equal (first args) ''nil)
                      (equal (second args) ''nil)))))))

(defthm booleanp-of-clause.negative-termp
  (equal (booleanp (clause.negative-termp x))
         t)
  :hints(("Goal" :in-theory (e/d (clause.negative-termp)
                                 ((:executable-counterpart acl2::force))))))

(defthm clause.negative-termp-of-logic.function-of-not
  (equal (clause.negative-termp (logic.function 'not args))
         (equal (len args) 1))
  :hints(("Goal" :in-theory (enable clause.negative-termp))))

(defthm logic.functionp-when-clause.negative-termp
  (implies (clause.negative-termp x)
           (equal (logic.functionp x)
                  t))
  :hints(("Goal" :in-theory (enable clause.negative-termp))))



(definlined clause.negative-term-guts (x)
  (declare (xargs :guard (and (logic.termp x)
                              (clause.negative-termp x))
                  :guard-hints (("Goal" :in-theory (enable clause.negative-termp)))))
  (let ((name (logic.function-name x))
        (args (logic.function-args x)))
    (cond ((equal name 'not)
           (first args))
          ((equal name 'if)
           (first args))
          ((equal name 'equal)
           (if (equal (first args) ''nil)
               (second args)
             (first args)))
          ((equal name 'iff)
           (if (equal (first args) ''nil)
               (second args)
             (first args)))
          (t nil))))

(defthm forcing-logic.termp-of-clause.negative-term-guts
  (implies (force (and (logic.termp x)
                       (clause.negative-termp x)))
           (equal (logic.termp (clause.negative-term-guts x))
                  t))
  :hints(("Goal" :in-theory (enable clause.negative-termp clause.negative-term-guts))))

(defthm forcing-logic.term-atblp-of-clause.negative-term-guts
  (implies (force (and (logic.termp x)
                       (logic.term-atblp x atbl)
                       (clause.negative-termp x)))
           (equal (logic.term-atblp (clause.negative-term-guts x) atbl)
                  t))
  :hints(("Goal" :in-theory (enable clause.negative-termp clause.negative-term-guts))))

(defthm clause.negative-term-guts-of-logic.function-of-not
  (equal (clause.negative-term-guts (logic.function 'not args))
         (first args))
  :hints(("Goal" :in-theory (enable clause.negative-term-guts))))

(defthm rank-of-clause.negative-term-guts-when-clause.negative-termp
  (implies (clause.negative-termp x)
           (equal (< (rank (clause.negative-term-guts x))
                     (rank x))
                  t))
  :hints(("Goal" :in-theory (enable clause.negative-term-guts
                                    clause.negative-termp
                                    logic.function-args ;; yuck but whatever
                                    ))))

(defthm rank-of-clause.negative-term-guts-of-clause.negative-term-guts
  (implies (and (clause.negative-termp x)
                (clause.negative-termp (clause.negative-term-guts x)))
           (equal (< (rank (clause.negative-term-guts (clause.negative-term-guts x)))
                     (rank x))
                  t))
  :hints(("Goal"
          :in-theory (disable rank-of-clause.negative-term-guts-when-clause.negative-termp)
          :use ((:instance rank-of-clause.negative-term-guts-when-clause.negative-termp
                           (x (clause.negative-term-guts x)))
                (:instance rank-of-clause.negative-term-guts-when-clause.negative-termp)))))



(definlined clause.term-guts (x)
  (declare (xargs :guard (logic.termp x)))
  (if (clause.negative-termp x)
      (clause.negative-term-guts x)
    x))

(defthm forcing-logic.termp-of-clause.term-guts
  (implies (force (logic.termp x))
           (equal (logic.termp (clause.term-guts x))
                  t))
  :hints(("Goal" :in-theory (enable clause.term-guts))))

(defthm forcing-logic.term-atblp-of-clause.term-guts
  (implies (force (and (logic.termp x)
                       (logic.term-atblp x atbl)))
           (equal (logic.term-atblp (clause.term-guts x) atbl)
                  t))
  :hints(("Goal" :in-theory (enable clause.term-guts))))




(defprojection :list (clause.term-list-guts x)
               :element (clause.term-guts x)
               :guard (logic.term-listp x)
               :nil-preservingp t)

(defthm forcing-logic.term-listp-of-clause.term-list-guts
  (implies (force (logic.term-listp x))
           (equal (logic.term-listp (clause.term-list-guts x))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-logic.term-list-atblp-of-clause.term-list-guts
  (implies (force (and (logic.term-listp x)
                       (logic.term-list-atblp x atbl)))
           (equal (logic.term-list-atblp (clause.term-list-guts x) atbl)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))


