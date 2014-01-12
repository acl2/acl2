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
(include-book "proofp")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


(defund logic.functional-axiom (fn ti si)
  ;; Create the functional axiom instance for fn, ti, and si.
  (declare (xargs :guard (and (logic.function-namep fn)
                              (logic.term-listp ti)
                              (logic.term-listp si)
                              (equal (len ti) (len si)))))
  (logic.disjoin-formulas (fast-app (logic.negate-formulas (logic.pequal-list ti si))
                                    (list (logic.pequal (logic.function fn (list-fix ti))
                                                        (logic.function fn (list-fix si)))))))

(defthm forcing-logic.formulap-of-logic.functional-axiom
  (implies (force (and (logic.function-namep fn)
                       (equal (len ti) (len si))
                       (logic.term-listp ti)
                       (logic.term-listp si)))
           (equal (logic.formulap (logic.functional-axiom fn ti si))
                  t))
  :hints(("Goal" :in-theory (enable logic.functional-axiom))))

(defthm forcing-logic.formula-atblp-of-logic.functional-axiom
  (implies (force (and (logic.function-namep fn)
                       (logic.term-list-atblp ti atbl)
                       (logic.term-list-atblp si atbl)
                       (equal (cdr (lookup fn atbl)) (len ti))
                       (equal (len ti) (len si))))
           (equal (logic.formula-atblp (logic.functional-axiom fn ti si) atbl)
                  t))
  :hints(("Goal" :in-theory (enable logic.functional-axiom))))



;; We introduce two intermediate functions to bridge the gap between our axiom
;; generator and the checker in proofp.

(defund logic.functional-axiom-alt1 (fn ti si tacc sacc)
  (declare (xargs :verify-guards nil))
  (if (and (consp ti)
           (consp si))
      (logic.por (logic.pnot (logic.pequal (car ti) (car si)))
                 (logic.functional-axiom-alt1 fn (cdr ti) (cdr si) (cons (car ti) tacc) (cons (car si) sacc)))
    (logic.pequal (logic.function fn (rev tacc))
                  (logic.function fn (rev sacc)))))

(defthm logic.check-functional-axiom-of-logic.functional-axiom-alt1
  (implies (and (logic.function-namep fn)
                (equal (len ti) (len si)))
           (equal (logic.check-functional-axiom (logic.functional-axiom-alt1 fn ti si tacc sacc) tacc sacc)
                  t))
  :hints(("Goal"
          :in-theory (enable logic.check-functional-axiom
                             logic.functional-axiom-alt1)
          :induct (logic.functional-axiom-alt1 fn ti si tacc sacc))))

(defund logic.functional-axiom-alt2 (fn ti si tacc sacc)
  (declare (xargs :verify-guards nil))
  (logic.disjoin-formulas
   (app (logic.negate-formulas (logic.pequal-list ti si))
        (list (logic.pequal (logic.function fn (rev (revappend ti tacc)))
                            (logic.function fn (rev (revappend si sacc))))))))

(encapsulate
 ()
 (local (ACL2::allow-fertilize t))
 (defthm logic.functional-axiom-alt1/alt2-equivalence
   (implies (and (logic.function-namep fn)
                 (equal (len ti) (len si))
                 (true-listp tacc)
                 (true-listp sacc))
            (equal (logic.functional-axiom-alt1 fn ti si tacc sacc)
                   (logic.functional-axiom-alt2 fn ti si tacc sacc)))
   :hints(("Goal"
           :in-theory (e/d (logic.functional-axiom-alt2
                            logic.functional-axiom-alt1)
                           (forcing-logic.formulap-of-logic.pequal
                            forcing-logic.formulap-of-logic.pnot
                            forcing-equal-of-logic.por-rewrite-two
                            forcing-equal-of-logic.por-rewrite))
           :induct (logic.functional-axiom-alt1 fn ti si tacc sacc)))))

(defthm logic.functional-axiom-alt2/main-equivalence
  (implies (and (logic.function-namep fn)
                (equal (len ti) (len si)))
           (equal (logic.functional-axiom-alt2 fn ti si nil nil)
                  (logic.functional-axiom fn ti si)))
  :hints(("Goal" :in-theory (enable logic.functional-axiom-alt2
                                    logic.functional-axiom))))

(defthm forcing-logic.check-functional-axiom-of-logic.functional-axiom
   (implies (force (and (logic.function-namep fn)
                        (equal (len ti) (len si))))
            (equal (logic.check-functional-axiom (logic.functional-axiom fn ti si) nil nil)
                   t))
   :hints(("Goal"
           :use ((:instance logic.check-functional-axiom-of-logic.functional-axiom-alt1
                            (tacc nil)
                            (sacc nil))))))
