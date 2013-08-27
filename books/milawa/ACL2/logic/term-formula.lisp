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
(include-book "substitute-formula")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)

;; We sometimes think of a term, A, as if it were the formula A != nil.  We now
;; provide some functions to transform terms into these formulas.


(definlined logic.term-formula (x)
  (declare (xargs :guard (logic.termp x)))
  (logic.pnot (logic.pequal x ''nil)))

(defthm forcing-logic.formulap-of-logic.term-formula
  (implies (force (logic.termp x))
           (equal (logic.formulap (logic.term-formula x))
                  t))
  :hints(("Goal" :in-theory (enable logic.term-formula))))

(defthm forcing-logic.formula-atblp-of-logic.term-formula
  (implies (force (logic.term-atblp x atbl))
           (equal (logic.formula-atblp (logic.term-formula x) atbl)
                  t))
  :hints(("Goal" :in-theory (enable logic.term-formula))))

(defthm logic.substitute-formula-of-logic.term-formula
  (equal (logic.substitute-formula (logic.term-formula x) sigma)
         (logic.term-formula (logic.substitute x sigma)))
  :hints(("Goal" :in-theory (enable logic.term-formula))))




(defprojection :list (logic.term-list-formulas x)
               :element (logic.term-formula x)
               :guard (logic.term-listp x))

(defthmd redefinition-of-logic.term-list-formulas
  (equal (logic.term-list-formulas x)
         (logic.negate-formulas (logic.pequal-list x (repeat ''nil (len x)))))
  :hints(("Goal"
          :induct (cdr-induction x)
          :in-theory (enable logic.term-formula))))

(defthm forcing-logic.formula-listp-of-logic.term-list-formulas
  (implies (force (logic.term-listp x))
           (equal (logic.formula-listp (logic.term-list-formulas x))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-logic.formula-list-atblp-of-logic.term-list-formulas
  (implies (force (logic.term-list-atblp x atbl))
           (equal (logic.formula-list-atblp (logic.term-list-formulas x) atbl)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm memberp-of-logic.term-formula-and-logic.term-list-formulas
  (equal (memberp (logic.term-formula a) (logic.term-list-formulas x))
         (memberp a x))
  :hints(("Goal"
          :induct (cdr-induction x)
          :in-theory (enable logic.term-formula))))

(defthm memberp-of-logic.pnot-of-logic.pequal-nil-in-logic.term-list-formulas
  (equal (memberp (logic.pnot (logic.pequal a ''nil)) (logic.term-list-formulas x))
         (memberp a x))
  :hints(("Goal"
          :induct (cdr-induction x)
          :in-theory (enable logic.term-formula))))

(defthm subsetp-of-logic.term-list-formulas-and-logic.term-list-formulas
  (equal (subsetp (logic.term-list-formulas x) (logic.term-list-formulas y))
         (subsetp x y))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm logic.substitute-formula-list-of-logic.term-list-formulas
  (equal (logic.substitute-formula-list (logic.term-list-formulas x) sigma)
         (logic.term-list-formulas (logic.substitute-list x sigma)))
  :hints(("Goal" :induct (cdr-induction x))))




(defprojection :list (logic.term-list-list-formulas x)
               :element (logic.term-list-formulas x)
               :guard (logic.term-list-listp x))

(defthm forcing-logic.formula-list-listp-of-logic.term-list-list-formulas
  (implies (force (logic.term-list-listp x))
           (equal (logic.formula-list-listp (logic.term-list-list-formulas x))
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm forcing-logic.formula-list-list-atblp-of-logic.term-list-list-formulas
  (implies (force (logic.term-list-list-atblp x atbl))
           (equal (logic.formula-list-list-atblp (logic.term-list-list-formulas x) atbl)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm cons-listp-of-logic.term-list-list-formulas
  (equal (cons-listp (logic.term-list-list-formulas x))
         (cons-listp x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm supserset-of-somep-of-logic.term-list-formulas-and-logic.term-list-list-formulas
  (equal (superset-of-somep (logic.term-list-formulas a) (logic.term-list-list-formulas x))
         (superset-of-somep a x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm all-superset-of-somep-of-logic.term-list-list-formulas
  (equal (all-superset-of-somep (logic.term-list-list-formulas x) (logic.term-list-list-formulas y))
         (all-superset-of-somep x y))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm logic.term-list-list-formulas-of-list-list-fix
  (equal (logic.term-list-list-formulas (list-list-fix x))
         (logic.term-list-list-formulas x))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm logic.substitute-formula-list-list-of-logic.term-list-list-formulas
  (equal (logic.substitute-formula-list-list (logic.term-list-list-formulas x) sigma)
         (logic.term-list-list-formulas (logic.substitute-list-list x sigma)))
  :hints(("Goal" :induct (cdr-induction x))))

(defthm logic.term-list-list-formulas-of-listify-each
  (implies (force (logic.term-listp x))
           (equal (logic.term-list-list-formulas (listify-each x))
                  (listify-each (logic.negate-formulas (logic.pequal-list x (repeat ''nil (len x)))))))
  :hints(("Goal"
          :induct (cdr-induction x)
          :in-theory (enable logic.term-formula))))
