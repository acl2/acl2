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
(include-book "factor")
(include-book "simple-termp")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)



(defund clause.casesplit (x cases assignment)
  ;; Suppose x is a term, cases are a list of terms [c1, ..., cn], and
  ;; assignmetn is a mapping from terms to truth values.  Assignment acts
  ;; as an accumulator as we create a new term by splitting x based on
  ;; every term in cases.  I.e., we create a new term:
  ;;
  ;;  (if c1
  ;;      (if c2
  ;;          ...
  ;;          (if cn
  ;;              X|(revappend [c1=t,...,cn=t] assignment)
  ;;            X|(revappend [c1=t,...,cn=nil] assignment))
  ;;      ...)
  ;;      X|(revappend [c1=nil,...,cn=nil] assignment))
  (declare (xargs :guard (and (logic.termp x)
                              (logic.term-listp cases)
                              (mapp assignment))
                  :verify-guards nil))
  (if (consp cases)
      (let* ((true-assignment  (update (car cases) t assignment))
             (false-assignment (update (car cases) nil assignment))
             (true-term        (clause.casesplit x (cdr cases) true-assignment))
             (false-term       (clause.casesplit x (cdr cases) false-assignment)))
        (if (equal true-term false-term)
            true-term
          (logic.function 'if (list (car cases) true-term false-term))))
    (clause.factor x assignment)))

(defthm clause.casesplit-when-not-consp
  (implies (not (consp cases))
           (equal (clause.casesplit x cases assignment)
                  (clause.factor x assignment)))
  :hints(("Goal" :in-theory (enable clause.casesplit))))

(defthm clause.casesplit-of-cons
  (equal (clause.casesplit x (cons a cases) assignment)
         (let* ((true-assignment  (update a t assignment))
                (false-assignment (update a nil assignment))
                (true-term        (clause.casesplit x cases true-assignment))
                (false-term       (clause.casesplit x cases false-assignment)))
           (if (equal true-term false-term)
               true-term
             (logic.function 'if (list a true-term false-term)))))
  :hints(("Goal" :in-theory (enable clause.casesplit))))

(defthm forcing-logic.termp-of-clause.casesplit
  (implies (and (force (logic.termp x))
                (force (logic.term-listp cases)))
           (equal (logic.termp (clause.casesplit x cases assignment))
                  t))
  :hints(("Goal" :in-theory (enable clause.casesplit))))

(verify-guards clause.casesplit)

(defthm forcing-logic.term-atblp-of-clause.casesplit
  (implies (and (force (logic.termp x))
                (force (logic.term-atblp x atbl))
                (force (logic.term-list-atblp cases atbl))
                (force (equal (cdr (lookup 'if atbl)) 3)))
           (equal (logic.term-atblp (clause.casesplit x cases assignment) atbl)
                  t))
  :hints(("Goal" :in-theory (enable clause.casesplit))))




(defund clause.cases (cases assignment)
  ;; Suppose cases are a list of terms [c1, ..., cn] and assignment is a
  ;; mapping of terms to truth values as before.  We parallel the execution of
  ;; clause.casesplit, but instead of actually creating a new term, we just
  ;; create the list of all the assignments that x will get factored by.  I.e.,
  ;; we produce the list:
  ;;
  ;;  [ (revappend [c1=t,...,cn=t] assignment),
  ;;    ...,
  ;;    (revappend [c1=nil,...,cn=nil] assignment) ]
  (declare (xargs :guard (and (logic.term-listp cases)
                              (mapp assignment))))
  (if (consp cases)
      (let* ((true-assignment (update (car cases) t assignment))
             (false-assignment (update (car cases) nil assignment)))
        (app (clause.cases (cdr cases) true-assignment)
             (clause.cases (cdr cases) false-assignment)))
    (list assignment)))

(defthm clause.cases-when-not-consp
  (implies (not (consp cases))
           (equal (clause.cases cases assignment)
                  (list assignment)))
  :hints(("Goal" :in-theory (enable clause.cases))))

(defthm clause.cases-of-cons
  (equal (clause.cases (cons a cases) assignment)
         (app (clause.cases cases (update a t assignment))
              (clause.cases cases (update a nil assignment))))
  :hints(("Goal" :in-theory (enable clause.cases))))

(defthm consp-of-clause.cases
  (equal (consp (clause.cases cases assignment))
         t)
  :hints(("Goal" :in-theory (enable clause.cases))))

(defthm domain-of-clause.cases
  (implies (memberp assign (clause.cases cases baseassign))
           (equal (domain assign)
                  (app (rev cases) (domain baseassign))))
  :hints(("Goal" :in-theory (enable clause.cases))))

(defthm clause.simple-term-listp-of-domain-of-clause.cases
  (implies (and (clause.simple-term-listp (domain assignment))
                (clause.simple-term-listp cases)
                (memberp x (clause.cases cases assignment)))
           (equal (clause.simple-term-listp (domain x))
                  t)))

(defthm disjoint-from-nonep-of-domain-of-clause.cases
  (implies (and (disjoint-from-nonep cases set)
                (memberp x (clause.cases cases assignment)))
           (equal (disjoint-from-nonep (domain x) set)
                  t)))

