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
(include-book "evaluator-bldr")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


;; The magic-evaluator is very magical.
;;
;; It's like the generic-evaluator, except
;;   - You don't have to worry about how many steps it will take, and
;;   - It calls raw lisp eval under the hood so it runs much faster.
;;
;; Similarly, there is a magic-evaluator-bldr which doesn't need to take a
;; number of steps.
;;
;; There are some limitations to the magic.
;;   - You can only use the magic evaluator in conjunction with the
;;     tactic harness and only with
;;       (1) the currently defined functions, or
;;       (2) the currently defined syntactic functions (syndefs)
;;   - You can only use its builder with the currently defined functions.
;;
;; Attempting to break these rules will result in a hard error.

(encapsulate
 ()
 (set-verify-guards-eagerness 0)

 (defun-sk evaluable-termp (x defs)
   (exists n (generic-evaluator x defs n)))

 (set-verify-guards-eagerness 2))


(defund magic-evaluator (x defs)
  ;; This eventually gets replaced with a thin wrapper for common lisp "eval"
  (declare (xargs :guard (and (logic.termp x)
                              (logic.groundp x)
                              (definition-listp defs))))
  (ACL2::prog2$ (ACL2::cw "Warning: magic-evaluator has not yet been redefined!!~%")
                (generic-evaluator x defs (nfix (evaluable-termp-witness x defs)))))

(defthm forcing-logic.constantp-of-magic-evaluator
  (implies (force (and (magic-evaluator x defs)
                       (logic.termp x)
                       (definition-listp defs)))
           (logic.constantp (magic-evaluator x defs)))
  :hints(("Goal" :in-theory (enable magic-evaluator))))




(defund magic-evaluator-bldr (x defs)
  (declare (xargs :guard (and (logic.termp x)
                              (logic.groundp x)
                              (definition-listp defs)
                              (magic-evaluator x defs))
                  :guard-hints (("Goal" :in-theory (enable magic-evaluator)))))
  ;; This eventually gets replaced with a thing wrapper for an "unbounded"
  ;; version of the generic-evaluator-bldr.
  (ACL2::prog2$ (ACL2::cw "Warning: magic-evaluator-bldr has not yet been redefined!!~%")
                (generic-evaluator-bldr x defs (nfix (evaluable-termp-witness x defs)))))

(defobligations magic-evaluator-bldr
  (generic-evaluator-bldr))

(defthm forcing-logic.appealp-of-magic-evaluator-bldr
  (implies (force (and (magic-evaluator x defs)
                       (logic.termp x)
                       (definition-listp defs)))
           (equal (logic.appealp (magic-evaluator-bldr x defs))
                  t))
  :hints(("Goal" :in-theory (enable magic-evaluator magic-evaluator-bldr))))

(defthm forcing-logic.conclusion-of-magic-evaluator-bldr
  (implies (force (and (magic-evaluator x defs)
                       (logic.termp x)
                       (definition-listp defs)))
           (equal (logic.conclusion (magic-evaluator-bldr x defs))
                  (logic.pequal x (magic-evaluator x defs))))
  :hints(("Goal" :in-theory (enable magic-evaluator magic-evaluator-bldr))))

(defthm@ forcing-logic.proofp-of-magic-evaluator-bldr
  (implies (force (and (magic-evaluator x defs)
                       (logic.termp x)
                       (logic.term-atblp x atbl)
                       (definition-listp defs)
                       (logic.formula-list-atblp defs atbl)
                       (subsetp defs axioms)
                       (equal (cdr (lookup 'if atbl)) 3)
                       (equal (cdr (lookup 'equal atbl)) 2)
                       (@obligations generic-evaluator-bldr)))
           (equal (logic.proofp (magic-evaluator-bldr x defs) axioms thms atbl)
                  t))
  :hints(("Goal" :in-theory (enable magic-evaluator magic-evaluator-bldr))))

