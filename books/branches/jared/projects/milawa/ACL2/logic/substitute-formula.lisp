;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
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
(include-book "substitute-term")
(include-book "formulas")
(include-book "disjoin-formulas")
(include-book "negate-formulas")
(include-book "pequal-list")
(include-book "por-list")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


;; [logic.substitute-formula] extends our ability to substitute into terms, by
;; allowing us now to substitute into formulas.  Instead of taking a term as
;; its first input, it takes a formula instead.
(defund logic.substitute-formula (formula sigma)
  (declare (xargs :guard (and (logic.formulap formula)
                              (logic.sigmap sigma))
                  :verify-guards nil))
  (let ((type (logic.fmtype formula)))
    (cond ((equal type 'por*)
           (logic.por (logic.substitute-formula (logic.vlhs formula) sigma)
                      (logic.substitute-formula (logic.vrhs formula) sigma)))
          ((equal type 'pnot*)
           (logic.pnot (logic.substitute-formula (logic.~arg formula) sigma)))
          ((equal type 'pequal*)
           (logic.pequal (logic.substitute (logic.=lhs formula) sigma)
                         (logic.substitute (logic.=rhs formula) sigma)))
          (t nil))))

(defthm logic.substitute-formula-of-logic.por
  (equal (logic.substitute-formula (logic.por x y) sigma)
         (logic.por (logic.substitute-formula x sigma)
                    (logic.substitute-formula y sigma)))
  :hints(("Goal" :in-theory (enable logic.substitute-formula))))

(defthm logic.substitute-formula-of-logic.pnot
  (equal (logic.substitute-formula (logic.pnot x) sigma)
         (logic.pnot (logic.substitute-formula x sigma)))
  :hints(("Goal" :in-theory (enable logic.substitute-formula))))

(defthm logic.substitute-formula-of-logic.pequal
  (equal (logic.substitute-formula (logic.pequal x y) sigma)
         (logic.pequal (logic.substitute x sigma)
                       (logic.substitute y sigma)))
  :hints(("Goal" :in-theory (enable logic.substitute-formula))))

(defthm logic.substitute-formula-when-malformed-cheap
  (implies (and (not (equal (logic.fmtype formula) 'por*))
                (not (equal (logic.fmtype formula) 'pnot*))
                (not (equal (logic.fmtype formula) 'pequal*)))
           (equal (logic.substitute-formula formula sigma)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst 0))
  :hints(("Goal" :in-theory (e/d (logic.substitute-formula)
                                 (logic.fmtype-normalizer-cheap)))))

(defthm logic.substitute-formula-of-nil
  (equal (logic.substitute-formula nil sigma)
         nil)
  :hints(("Goal" :in-theory (enable logic.substitute-formula))))

(defthm forcing-logic.formulap-of-logic.substitute-formula
  (implies (and (force (logic.formulap formula))
                (force (logic.sigmap sigma)))
           (equal (logic.formulap (logic.substitute-formula formula sigma))
                  t))
  :hints(("Goal" :in-theory (enable logic.substitute-formula))))

(defthm forcing-logic.formula-atblp-of-logic.substitute-formula
  (implies (and (force (logic.formula-atblp formula atbl))
                (force (logic.sigma-atblp sigma atbl)))
           (equal (logic.formula-atblp (logic.substitute-formula formula sigma) atbl)
                  t))
  :hints(("Goal" :in-theory (e/d (logic.substitute-formula)
                                 (logic.fmtype-normalizer-cheap)))))

(verify-guards logic.substitute-formula)


(defthm forcing-logic.substitute-formula-under-iff
  (implies (force (logic.formulap formula))
           (iff (logic.substitute-formula formula sigma)
                t))
  :hints(("Goal" :in-theory (enable logic.substitute-formula))))

(defthm forcing-logic.fmtype-of-logic.substitute-formula
  (implies (force (logic.formulap x))
           (equal (logic.fmtype (logic.substitute-formula x sigma))
                  (logic.fmtype x)))
  :hints(("Goal" :in-theory (enable logic.substitute-formula))))

(defthm forcing-logic.=lhs-of-logic.substitute-formula
  (implies (and (force (logic.formulap x))
                (force (equal (logic.fmtype x) 'pequal*)))
           (equal (logic.=lhs (logic.substitute-formula x sigma))
                  (logic.substitute (logic.=lhs x) sigma)))
  :hints(("Goal" :in-theory (enable logic.substitute-formula))))

(defthm forcing-logic.=rhs-of-logic.substitute-formula
  (implies (and (force (logic.formulap x))
                (force (equal (logic.fmtype x) 'pequal*)))
           (equal (logic.=rhs (logic.substitute-formula x sigma))
                  (logic.substitute (logic.=rhs x) sigma)))
  :hints(("Goal" :in-theory (enable logic.substitute-formula))))




(defprojection :list (logic.substitute-formula-list x sigma)
               :element (logic.substitute-formula x sigma)
               :guard (and (logic.formula-listp x)
                           (logic.sigmap sigma))
               :nil-preservingp t)

(defthm forcing-logic.formula-listp-of-logic.substitute-formula-list
  (implies (force (and (logic.formula-listp x)
                       (logic.sigmap sigma)))
           (equal (logic.formula-listp (logic.substitute-formula-list x sigma))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-logic.formula-list-atblp-of-logic.substitute-formula-list
  (implies (force (and (logic.formula-list-atblp x atbl)
                       (logic.sigma-atblp sigma atbl)))
           (equal (logic.formula-list-atblp (logic.substitute-formula-list x sigma) atbl)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm logic.substitute-formula-of-logic.disjoin-formulas
  (equal (logic.substitute-formula (logic.disjoin-formulas x) sigma)
         (logic.disjoin-formulas (logic.substitute-formula-list x sigma)))
  :hints(("Goal"
          :induct (cdr-induction x)
          :in-theory (enable logic.substitute-formula logic.disjoin-formulas))))

(defthm logic.substitute-formula-list-of-logic.negate-formulas
  (equal (logic.substitute-formula-list (logic.negate-formulas x) sigma)
         (logic.negate-formulas (logic.substitute-formula-list x sigma)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm logic.substitute-formula-list-of-logic.pequal-list
  (equal (logic.substitute-formula-list (logic.pequal-list x y) sigma)
         (logic.pequal-list (logic.substitute-list x sigma)
                            (logic.substitute-list y sigma)))
  :hints(("Goal"
          :induct (cdr-cdr-induction x y)
          :in-theory (disable forcing-equal-of-logic.pequal-list-rewrite))))

(defthm logic.substitute-formula-list-of-logic.por-list
  (equal (logic.substitute-formula-list (logic.por-list x y) sigma)
         (logic.por-list (logic.substitute-formula-list x sigma)
                         (logic.substitute-formula-list y sigma)))
  :hints(("Goal"
          :induct (cdr-cdr-induction x y)
          :in-theory (disable forcing-equal-of-logic.por-list-rewrite))))




(defprojection :list (logic.substitute-formula-list-list x sigma)
               :element (logic.substitute-formula-list x sigma)
               :guard (and (logic.formula-list-listp x)
                           (logic.sigmap sigma)))

(defthm forcing-logic.formula-list-listp-of-logic.substitute-formula-list-list
  (implies (force (and (logic.formula-list-listp x)
                       (logic.sigmap sigma)))
           (equal (logic.formula-list-listp (logic.substitute-formula-list-list x sigma))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-logic.formula-list-list-atblp-of-logic.substitute-formula-list-list
  (implies (force (and (logic.formula-list-list-atblp x atbl)
                       (logic.sigma-atblp sigma atbl)))
           (equal (logic.formula-list-list-atblp (logic.substitute-formula-list-list x sigma) atbl)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm logic.substitute-formula-list-of-logic.disjoin-each-formula-list
  (equal (logic.substitute-formula-list (logic.disjoin-each-formula-list x) sigma)
         (logic.disjoin-each-formula-list (logic.substitute-formula-list-list x sigma)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm logic.substitute-formula-list-of-logic.disjoin-each-formula-list-free
  (implies (equal x (logic.disjoin-each-formula-list y))
           (equal (logic.substitute-formula-list x sigma)
                  (logic.disjoin-each-formula-list (logic.substitute-formula-list-list y sigma)))))





;; [logic.substitute-each-sigma-into-formula] takes two inputs: a formula F and
;; a list of sigmas, i.e., (sigma1 ... sigmaN).  It produces a list of formulas
;; as outputs, i.e., (F/sigma1 ... F/sigmaN)

(defprojection :list (logic.substitute-each-sigma-into-formula f x)
               :element (logic.substitute-formula f x)
               :guard (and (logic.formulap f)
                           (logic.sigma-listp x))
               :nil-preservingp nil)

(defthm logic.formula-listp-of-logic.substitute-each-sigma-into-formula
  (implies (and (force (logic.formulap f))
                (force (logic.sigma-listp sigmas)))
           (equal (logic.formula-listp (logic.substitute-each-sigma-into-formula f sigmas))
                  t))
  :hints(("Goal" :in-theory (enable logic.substitute-each-sigma-into-formula))))

(defthm logic.formula-list-atblp-of-logic.substitute-each-sigma-into-formula
  (implies (and (force (logic.formula-atblp f atbl))
                (force (logic.sigma-list-atblp sigmas atbl)))
           (equal (logic.formula-list-atblp (logic.substitute-each-sigma-into-formula f sigmas) atbl)
                  t))
  :hints(("Goal" :in-theory (enable logic.substitute-each-sigma-into-formula))))
