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
(include-book "basic-builders") ;; for fail-trace
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)



(local (in-theory (e/d (booleanp-of-rw.trace->iffp)
                       (forcing-booleanp-of-rw.trace->iffp))))



(defund rw.urewrite-if-specialcase-same-trace (x y a)
  (declare (xargs :guard (and (rw.tracep x)
                              (rw.tracep y)
                              (logic.termp a)
                              (not (rw.hypbox->left (rw.trace->hypbox x)))
                              (not (rw.hypbox->right (rw.trace->hypbox x)))
                              (not (rw.hypbox->left (rw.trace->hypbox y)))
                              (not (rw.hypbox->right (rw.trace->hypbox y)))
                              (equal (rw.trace->iffp x) (rw.trace->iffp y))
                              (equal (rw.trace->rhs x) (rw.trace->rhs y)))))
  (rw.trace 'urewrite-if-specialcase-same
            (rw.trace->hypbox x)
            (logic.function 'if (list a (rw.trace->lhs x) (rw.trace->lhs y)))
            (rw.trace->rhs x)
            (rw.trace->iffp x)
            (list x y)
            nil))

(encapsulate
 ()
 (local (in-theory (enable rw.urewrite-if-specialcase-same-trace)))

 (defthm rw.trace->method-of-rw.urewrite-if-specialcase-same-trace
   (equal (rw.trace->method (rw.urewrite-if-specialcase-same-trace x y a))
          'urewrite-if-specialcase-same))

 (defthm rw.trace->hypbox-of-rw.urewrite-if-specialcase-same-trace
   (equal (rw.trace->hypbox (rw.urewrite-if-specialcase-same-trace x y a))
          (rw.trace->hypbox x)))

 (defthm rw.trace->lhs-of-rw.urewrite-if-specialcase-same-trace
   (equal (rw.trace->lhs (rw.urewrite-if-specialcase-same-trace x y a))
          (logic.function 'if (list a (rw.trace->lhs x) (rw.trace->lhs y)))))

 (defthm rw.trace->rhs-of-rw.urewrite-if-specialcase-same-trace
   (equal (rw.trace->rhs (rw.urewrite-if-specialcase-same-trace x y a))
          (rw.trace->rhs x)))

 (defthm rw.trace->iffp-of-rw.urewrite-if-specialcase-same-trace
   (equal (rw.trace->iffp (rw.urewrite-if-specialcase-same-trace x y a))
          (rw.trace->iffp x)))

 (defthm rw.trace->subtraces-of-rw.urewrite-if-specialcase-same-trace
   (equal (rw.trace->subtraces (rw.urewrite-if-specialcase-same-trace x y a))
          (list x y)))

 (defthm rw.trace->extras-of-rw.urewrite-if-specialcase-same-trace
   (equal (rw.trace->extras (rw.urewrite-if-specialcase-same-trace x y a))
          nil))

 (defthm forcing-rw.tracep-of-rw.urewrite-if-specialcase-same-trace
   (implies (force (and (rw.tracep x)
                        (rw.tracep y)
                        (logic.termp a)))
            (equal (rw.tracep (rw.urewrite-if-specialcase-same-trace x y a))
                   t)))

 (defthm forcing-rw.trace-atblp-of-rw.urewrite-if-specialcase-same-trace
   (implies (force (and (rw.trace-atblp x atbl)
                        (rw.trace-atblp y atbl)
                        (logic.term-atblp a atbl)
                        (equal (cdr (lookup 'if atbl)) 3)))
            (equal (rw.trace-atblp (rw.urewrite-if-specialcase-same-trace x y a) atbl)
                   t)))

 (local (in-theory (disable rw.urewrite-if-specialcase-same-trace)))

 (defthmd lemma-forcing-rw.urewrite-if-specialcase-same-tracep-of-rw.urewrite-if-specialcase-same-trace
   (implies (force (and (not (rw.hypbox->left (rw.trace->hypbox x)))
                        (not (rw.hypbox->right (rw.trace->hypbox x)))
                        (not (rw.hypbox->left (rw.trace->hypbox y)))
                        (not (rw.hypbox->right (rw.trace->hypbox y)))
                        (equal (rw.trace->iffp x) (rw.trace->iffp y))
                        (equal (rw.trace->rhs x) (rw.trace->rhs y))))
            (equal (rw.urewrite-if-specialcase-same-tracep (rw.urewrite-if-specialcase-same-trace x y a))
                   t))
   :hints(("Goal" :in-theory (enable rw.urewrite-if-specialcase-same-tracep))))

 (defthmd lemma-forcing-rw.trace-step-okp-of-rw.urewrite-if-specialcase-same-trace
   (implies (force (and (not (rw.hypbox->left (rw.trace->hypbox x)))
                        (not (rw.hypbox->right (rw.trace->hypbox x)))
                        (not (rw.hypbox->left (rw.trace->hypbox y)))
                        (not (rw.hypbox->right (rw.trace->hypbox y)))
                        (equal (rw.trace->iffp x) (rw.trace->iffp y))
                        (equal (rw.trace->rhs x) (rw.trace->rhs y))))
            (equal (rw.trace-step-okp (rw.urewrite-if-specialcase-same-trace x y a) defs)
                   t))
   :hints(("Goal" :in-theory (enable rw.trace-step-okp
                                     lemma-forcing-rw.urewrite-if-specialcase-same-tracep-of-rw.urewrite-if-specialcase-same-trace))))

 (defthm forcing-rw.trace-okp-of-rw.urewrite-if-specialcase-same-trace
   (implies (force (and (not (rw.hypbox->left (rw.trace->hypbox x)))
                        (not (rw.hypbox->right (rw.trace->hypbox x)))
                        (not (rw.hypbox->left (rw.trace->hypbox y)))
                        (not (rw.hypbox->right (rw.trace->hypbox y)))
                        (equal (rw.trace->iffp x) (rw.trace->iffp y))
                        (equal (rw.trace->rhs x) (rw.trace->rhs y))
                        (rw.trace-okp x defs)
                        (rw.trace-okp y defs)))
            (equal (rw.trace-okp (rw.urewrite-if-specialcase-same-trace x y a) defs)
                   t))
   :hints(("Goal"
           :expand ((rw.trace-okp (rw.urewrite-if-specialcase-same-trace x y a) defs))
           :in-theory (enable lemma-forcing-rw.trace-step-okp-of-rw.urewrite-if-specialcase-same-trace))))

 (defthmd lemma-forcing-rw.trace-step-env-okp-of-rw.urewrite-if-specialcase-same-trace
   (equal (rw.trace-step-env-okp (rw.urewrite-if-specialcase-same-trace x y a) defs thms atbl)
          t)
   :hints(("Goal" :in-theory (enable rw.trace-step-env-okp))))

 (defthm forcing-rw.trace-env-okp-of-rw.urewrite-if-specialcase-same-trace
   (implies (force (and (rw.trace-env-okp x defs thms atbl)
                        (rw.trace-env-okp y defs thms atbl)))
            (equal (rw.trace-env-okp (rw.urewrite-if-specialcase-same-trace x y a) defs thms atbl)
                   t))
   :hints(("Goal"
           :expand ((rw.trace-env-okp (rw.urewrite-if-specialcase-same-trace x y a) defs thms atbl))
           :in-theory (enable lemma-forcing-rw.trace-step-env-okp-of-rw.urewrite-if-specialcase-same-trace))))

 (defthm rw.collect-forced-goals-of-rw.urewrite-if-specialcase-same-trace
   (equal (rw.collect-forced-goals (rw.urewrite-if-specialcase-same-trace x y a))
          (fast-merge (rw.collect-forced-goals x)
                      (rw.collect-forced-goals y)))
   :hints(("Goal" :expand (rw.collect-forced-goals (rw.urewrite-if-specialcase-same-trace x y a))))))




(defund rw.urewrite-if-generalcase-trace (x y z)
  (declare (xargs :guard (and (rw.tracep x)
                              (rw.tracep y)
                              (rw.tracep z)
                              (not (rw.hypbox->left (rw.trace->hypbox x)))
                              (not (rw.hypbox->right (rw.trace->hypbox x)))
                              (not (rw.hypbox->left (rw.trace->hypbox y)))
                              (not (rw.hypbox->right (rw.trace->hypbox y)))
                              (not (rw.hypbox->left (rw.trace->hypbox z)))
                              (not (rw.hypbox->right (rw.trace->hypbox z)))
                              (equal (rw.trace->iffp x) t)
                              (equal (rw.trace->iffp y) (rw.trace->iffp z)))))
  (let ((a1 (rw.trace->lhs x))
        (a2 (rw.trace->rhs x))
        (b1 (rw.trace->lhs y))
        (b2 (rw.trace->rhs y))
        (c1 (rw.trace->lhs z))
        (c2 (rw.trace->rhs z))
        (iffp (rw.trace->iffp y)))
    ;(if (and (equal a1 a2)
    ;         (equal b1 b2)
    ;         (equal c1 c2))
    ;    (rw.fail-trace (rw.trace->hypbox x) (logic.function 'if (list a1 b1 c1)) iffp)
    (rw.trace 'urewrite-if-generalcase
              (rw.trace->hypbox x)
              (logic.function 'if (list a1 b1 c1))
              (logic.function 'if (list a2 b2 c2))
              iffp
              (list x y z)
              nil)))

(encapsulate
 ()
 (local (in-theory (enable rw.urewrite-if-generalcase-trace)))

 (defthm rw.trace->method-of-rw.urewrite-if-generalcase-trace
   (equal (rw.trace->method (rw.urewrite-if-generalcase-trace x y z))
          'urewrite-if-generalcase))

 (defthm rw.trace->hypbox-of-rw.urewrite-if-generalcase-trace
   (equal (rw.trace->hypbox (rw.urewrite-if-generalcase-trace x y z))
          (rw.trace->hypbox x)))

 (defthm rw.trace->lhs-of-rw.urewrite-if-generalcase-trace
   (equal (rw.trace->lhs (rw.urewrite-if-generalcase-trace x y z))
          (logic.function 'if (list (rw.trace->lhs x) (rw.trace->lhs y) (rw.trace->lhs z))))
   :hints(("Goal" :in-theory (disable forcing-true-listp-of-logic.function-args))))

 (defthm rw.trace->rhs-of-rw.urewrite-if-generalcase-trace
   (equal (rw.trace->rhs (rw.urewrite-if-generalcase-trace x y z))
          (logic.function 'if (list (rw.trace->rhs x) (rw.trace->rhs y) (rw.trace->rhs z))))
   :hints(("Goal" :in-theory (disable forcing-true-listp-of-logic.function-args))))

 (defthm rw.trace->iffp-of-rw.urewrite-if-generalcase-trace
   (equal (rw.trace->iffp (rw.urewrite-if-generalcase-trace x y z))
          (rw.trace->iffp y)))

 (defthm rw.trace->subtraces-of-rw.urewrite-if-generalcase-trace
   (equal (rw.trace->subtraces (rw.urewrite-if-generalcase-trace x y z))
          (list x y z)))

 (defthm rw.trace->extras-of-rw.urewrite-if-generalcase-trace
   (equal (rw.trace->extras (rw.urewrite-if-generalcase-trace x y z))
          nil))

 (defthm forcing-rw.tracep-of-rw.urewrite-if-generalcase-trace
   (implies (force (and (rw.tracep x)
                        (rw.tracep y)
                        (rw.tracep z)))
            (equal (rw.tracep (rw.urewrite-if-generalcase-trace x y z))
                   t)))

 (defthm forcing-rw.trace-atblp-of-rw.urewrite-if-generalcase-trace
   (implies (force (and (rw.trace-atblp x atbl)
                        (rw.trace-atblp y atbl)
                        (rw.trace-atblp z atbl)
                        (equal (cdr (lookup 'if atbl)) 3)))
            (equal (rw.trace-atblp (rw.urewrite-if-generalcase-trace x y z) atbl)
                   t)))

 (local (in-theory (disable rw.urewrite-if-generalcase-trace)))

 (defthmd lemma-forcing-rw.trace-step-okp-of-rw.urewrite-if-generalcase-trace
   (implies (force (and (not (rw.hypbox->left (rw.trace->hypbox x)))
                        (not (rw.hypbox->right (rw.trace->hypbox x)))
                        (not (rw.hypbox->left (rw.trace->hypbox y)))
                        (not (rw.hypbox->right (rw.trace->hypbox y)))
                        (not (rw.hypbox->left (rw.trace->hypbox z)))
                        (not (rw.hypbox->right (rw.trace->hypbox z)))
                        (equal (rw.trace->iffp x) t)
                        (equal (rw.trace->iffp y) (rw.trace->iffp z))))
            (equal (rw.trace-step-okp (rw.urewrite-if-generalcase-trace x y z) defs)
                   t))
   :hints(("Goal" :in-theory (enable rw.trace-step-okp rw.urewrite-if-generalcase-tracep))))

 (defthm forcing-rw.trace-okp-of-rw.urewrite-if-generalcase-trace
   (implies (force (and (not (rw.hypbox->left (rw.trace->hypbox x)))
                        (not (rw.hypbox->right (rw.trace->hypbox x)))
                        (not (rw.hypbox->left (rw.trace->hypbox y)))
                        (not (rw.hypbox->right (rw.trace->hypbox y)))
                        (not (rw.hypbox->left (rw.trace->hypbox z)))
                        (not (rw.hypbox->right (rw.trace->hypbox z)))
                        (equal (rw.trace->iffp x) t)
                        (equal (rw.trace->iffp y) (rw.trace->iffp z))
                        (rw.trace-okp x defs)
                        (rw.trace-okp y defs)
                        (rw.trace-okp z defs)))
            (equal (rw.trace-okp (rw.urewrite-if-generalcase-trace x y z) defs)
                   t))
   :hints(("Goal"
           :expand ((rw.trace-okp (rw.urewrite-if-generalcase-trace x y z) defs))
           :in-theory (enable lemma-forcing-rw.trace-step-okp-of-rw.urewrite-if-generalcase-trace))))

 (defthmd lemma-forcing-rw.trace-step-env-okp-of-rw.urewrite-if-generalcase-trace
   (equal (rw.trace-step-env-okp (rw.urewrite-if-generalcase-trace x y z) axioms thms atbl)
          t)
   :hints(("Goal" :in-theory (enable rw.trace-step-env-okp rw.urewrite-if-generalcase-tracep))))

 (defthm forcing-rw.trace-env-okp-of-rw.urewrite-if-generalcase-trace
   (implies (force (and (rw.trace-env-okp x defs thms atbl)
                        (rw.trace-env-okp y defs thms atbl)
                        (rw.trace-env-okp z defs thms atbl)))
            (equal (rw.trace-env-okp (rw.urewrite-if-generalcase-trace x y z) defs thms atbl)
                   t))
   :hints(("Goal"
           :expand ((rw.trace-env-okp (rw.urewrite-if-generalcase-trace x y z) defs thms atbl))
           :in-theory (enable lemma-forcing-rw.trace-step-env-okp-of-rw.urewrite-if-generalcase-trace))))

 (defthm rw.collect-forced-goals-of-rw.urewrite-if-generalcase-trace
   (equal (rw.collect-forced-goals (rw.urewrite-if-generalcase-trace x y z))
          (fast-merge (rw.collect-forced-goals x)
                      (fast-merge (rw.collect-forced-goals y)
                                  (rw.collect-forced-goals z))))
   :hints(("Goal" :in-theory (enable definition-of-rw.collect-forced-goals)))))




(defund rw.try-urewrite-rule (hypbox term rule iffp control)
  (declare (xargs :guard (and (rw.hypboxp hypbox)
                              (logic.termp term)
                              (rw.rulep rule)
                              (booleanp iffp)
                              (rw.controlp control))))
  (and
   ;; The rule must be unconditional
   (not (rw.rule->hyps rule))
   ;; The equivalence relation must be acceptable
   (let ((equiv (rw.rule->equiv rule)))
     (or (equal equiv 'equal)
         (and (equal equiv 'iff) iffp)))
   ;; Note: we ignore esigmas completely for urewrite rules
   (let ((match-result (logic.patmatch (rw.rule->lhs rule) term nil)))
     (and
      ;; We must have a match
      (not (equal 'fail match-result))
      ;; The syntactic restrictions must be satisfied.
      (rw.rule-syntax-okp rule match-result control)
      ;; Everything's ok; build the trace.
      (rw.trace 'urewrite-rule
                hypbox
                term
                (logic.substitute (rw.rule->rhs rule) match-result)
                iffp
                nil
                (list rule match-result))))))

(encapsulate
 ()
 (local (in-theory (enable rw.try-urewrite-rule)))

 (defthmd lemma-forcing-rw.trace->method-of-rw.try-urewrite-rule
   (implies (force (rw.try-urewrite-rule hypbox term rule iffp control))
            (equal (rw.trace->method (rw.try-urewrite-rule hypbox term rule iffp control))
                   'urewrite-rule)))

 (defthm forcing-rw.trace->hypbox-of-rw.try-urewrite-rule
   (implies (force (rw.try-urewrite-rule hypbox term rule iffp control))
            (equal (rw.trace->hypbox (rw.try-urewrite-rule hypbox term rule iffp control))
                   hypbox)))

 (defthm forcing-rw.trace->lhs-of-rw.try-urewrite-rule
   (implies (force (rw.try-urewrite-rule hypbox term rule iffp control))
            (equal (rw.trace->lhs (rw.try-urewrite-rule hypbox term rule iffp control))
                   term)))

 (defthm forcing-rw.trace->iffp-of-rw.try-urewrite-rule
   (implies (force (rw.try-urewrite-rule hypbox term rule iffp control))
            (equal (rw.trace->iffp (rw.try-urewrite-rule hypbox term rule iffp control))
                   iffp)))

 (defthmd lemma-forcing-rw.trace->subtraces-of-rw.try-urewrite-rule
   (implies (force (rw.try-urewrite-rule hypbox term rule iffp control))
            (equal (rw.trace->subtraces (rw.try-urewrite-rule hypbox term rule iffp control))
                   nil)))

 (defthmd lemma-forcing-rw.trace->extras-of-rw.try-urewrite-rule
   (implies (force (rw.try-urewrite-rule hypbox term rule iffp control))
            (equal (rw.trace->extras (rw.try-urewrite-rule hypbox term rule iffp control))
                   (list rule (logic.patmatch (rw.rule->lhs rule) term nil)))))

 (defthm forcing-rw.tracep-of-rw.try-urewrite-rule
   (implies (force (and (rw.try-urewrite-rule hypbox term rule iffp control)
                        (rw.hypboxp hypbox)
                        (logic.termp term)
                        (rw.rulep rule)
                        (booleanp iffp)))
            (equal (rw.tracep (rw.try-urewrite-rule hypbox term rule iffp control))
                   t)))

 (defthm forcing-rw.trace-atblp-of-rw.try-urewrite-rule
   (implies (force (and (rw.try-urewrite-rule hypbox term rule iffp control)
                        (rw.hypbox-atblp hypbox atbl)
                        (logic.term-atblp term atbl)
                        (rw.rule-atblp rule atbl)))
            (equal (rw.trace-atblp (rw.try-urewrite-rule hypbox term rule iffp control) atbl)
                   t)))

 (defthmd lemma-forcing-rw.urewrite-rule-tracep-of-rw.try-urewrite-rule
   (implies (force (and (rw.try-urewrite-rule hypbox term rule iffp control)
                        (logic.termp term)
                        (rw.rulep rule)
                        (rw.controlp control)))
            (equal (rw.urewrite-rule-tracep (rw.try-urewrite-rule hypbox term rule iffp control))
                   t))
   :hints(("Goal" :in-theory (enable rw.urewrite-rule-tracep))))

 (local (in-theory (disable rw.try-urewrite-rule)))
 (local (in-theory (enable lemma-forcing-rw.trace->method-of-rw.try-urewrite-rule
                           lemma-forcing-rw.trace->subtraces-of-rw.try-urewrite-rule
                           lemma-forcing-rw.trace->extras-of-rw.try-urewrite-rule
                           lemma-forcing-rw.urewrite-rule-tracep-of-rw.try-urewrite-rule)))

 (defthmd lemma-forcing-rw.trace-step-okp-of-rw.try-urewrite-rule
   (implies (force (and (rw.try-urewrite-rule hypbox term rule iffp control)
                        (logic.termp term)
                        (rw.rulep rule)
                        (rw.controlp control)))
            (equal (rw.trace-step-okp (rw.try-urewrite-rule hypbox term rule iffp control) defs)
                   t))
   :hints(("Goal" :in-theory (enable rw.trace-step-okp))))

 (defthm forcing-rw.trace-okp-of-rw.try-urewrite-rule
   (implies (force (and (rw.try-urewrite-rule hypbox term rule iffp control)
                        (logic.termp term)
                        (rw.rulep rule)
                        (rw.controlp control)))
            (equal (rw.trace-okp (rw.try-urewrite-rule hypbox term rule iffp control) defs)
                   t))
   :hints(("Goal"
           :expand ((rw.trace-okp (rw.try-urewrite-rule hypbox term rule iffp control) defs))
           :in-theory (enable lemma-forcing-rw.trace-step-okp-of-rw.try-urewrite-rule))))

 (defthmd lemma-forcing-rw.trace-step-env-okp-of-rw.try-urewrite-rule
   (implies (force (and (rw.try-urewrite-rule hypbox term rule iffp control)
                        (logic.termp term)
                        (logic.term-atblp term atbl)
                        (rw.rulep rule)
                        (rw.rule-atblp rule atbl)
                        (rw.rule-env-okp rule thms)
                        (rw.controlp control)))
            (equal (rw.trace-step-env-okp (rw.try-urewrite-rule hypbox term rule iffp control) defs thms atbl)
                   t))
   :hints(("Goal" :in-theory (enable rw.trace-step-env-okp rw.urewrite-rule-trace-env-okp))))

 (defthm forcing-rw.trace-env-okp-of-rw.try-urewrite-rule
   (implies (force (and (rw.try-urewrite-rule hypbox term rule iffp control)
                        (logic.termp term)
                        (logic.term-atblp term atbl)
                        (rw.rulep rule)
                        (rw.rule-atblp rule atbl)
                        (rw.rule-env-okp rule thms)
                        (rw.controlp control)))
            (equal (rw.trace-env-okp (rw.try-urewrite-rule hypbox term rule iffp control) defs thms atbl)
                   t))
   :hints(("Goal"
           :expand ((rw.trace-env-okp (rw.try-urewrite-rule hypbox term rule iffp control) defs thms atbl))
           :in-theory (enable lemma-forcing-rw.trace-step-env-okp-of-rw.try-urewrite-rule))))

 (defthm forcing-rw.collect-forced-goals-of-rw.try-urewrite-rule
   (implies (force (rw.try-urewrite-rule hypbox term rule iffp control))
            (equal (rw.collect-forced-goals (rw.try-urewrite-rule hypbox term rule iffp control))
                   nil))
   :hints(("Goal" :in-theory (enable definition-of-rw.collect-forced-goals)))))




(defund rw.try-urewrite-rule-list (hypbox term rules iffp control)
  (declare (xargs :guard (and (rw.hypboxp hypbox)
                              (logic.termp term)
                              (rw.rule-listp rules)
                              (booleanp iffp)
                              (rw.controlp control))))
  (if (consp rules)
      (or (rw.try-urewrite-rule hypbox term (car rules) iffp control)
          (rw.try-urewrite-rule-list hypbox term (cdr rules) iffp control))
    nil))

(encapsulate
 ()
 (local (in-theory (enable rw.try-urewrite-rule-list)))

 (defthm forcing-rw.trace->lhs-of-rw.try-urewrite-rule-list
   (implies (force (rw.try-urewrite-rule-list hypbox term rules iffp control))
            (equal (rw.trace->lhs (rw.try-urewrite-rule-list hypbox term rules iffp control))
                   term)))

 (defthm forcing-rw.trace->iffp-of-rw.try-urewrite-rule-list
   (implies (force (rw.try-urewrite-rule-list hypbox term rules iffp control))
            (equal (rw.trace->iffp (rw.try-urewrite-rule-list hypbox term rules iffp control))
                   iffp)))

 (defthm forcing-rw.trace->hypbox-of-rw.try-urewrite-rule-list
   (implies (force (rw.try-urewrite-rule-list hypbox term rules iffp control))
            (equal (rw.trace->hypbox (rw.try-urewrite-rule-list hypbox term rules iffp control))
                   hypbox)))

 (defthm forcing-rw.tracep-of-rw.try-urewrite-rule-list
   (implies (force (and (rw.hypboxp hypbox)
                        (logic.termp term)
                        (rw.rule-listp rules)
                        (booleanp iffp)))
            (equal (rw.tracep (rw.try-urewrite-rule-list hypbox term rules iffp control))
                   (if (rw.try-urewrite-rule-list hypbox term rules iffp control)
                       t
                     nil))))

 (defthm forcing-rw.trace-atblp-of-rw.try-urewrite-rule-list
   (implies (force (and (rw.hypbox-atblp hypbox atbl)
                        (logic.term-atblp term atbl)
                        (rw.rule-list-atblp rules atbl)))
            (equal (rw.trace-atblp (rw.try-urewrite-rule-list hypbox term rules iffp control) atbl)
                   (if (rw.try-urewrite-rule-list hypbox term rules iffp control)
                       t
                     nil))))

 (defthm forcing-rw.trace-okp-of-rw.try-urewrite-rule-list
   (implies (force (and (logic.termp term)
                        (rw.rule-listp rules)
                        (rw.controlp control)))
            (equal (rw.trace-okp (rw.try-urewrite-rule-list hypbox term rules iffp control) defs)
                   (if (rw.try-urewrite-rule-list hypbox term rules iffp control)
                       t
                     nil))))

 (defthm forcing-rw.trace-env-okp-of-rw.try-urewrite-rule-list
   (implies (force (and (logic.termp term)
                        (logic.term-atblp term atbl)
                        (rw.rule-listp rules)
                        (rw.rule-list-atblp rules atbl)
                        (rw.rule-list-env-okp rules thms)
                        (rw.controlp control)))
            (equal (rw.trace-env-okp (rw.try-urewrite-rule-list hypbox term rules iffp control) defs thms atbl)
                   t)))

 (defthm forcing-rw.collect-forced-goals-of-rw.try-urewrite-rule-list
   (implies (force (rw.try-urewrite-rule-list hypbox term rules iffp control))
            (equal (rw.collect-forced-goals (rw.try-urewrite-rule-list hypbox term rules iffp control))
                   nil))))



(defund rw.try-urewrite-rules (hypbox term type iffp control)
  (declare (xargs :guard (and (rw.hypboxp hypbox)
                              (logic.termp term)
                              (or (equal type 'inside)
                                  (equal type 'outside))
                              (booleanp iffp)
                              (rw.controlp control))))
  (let* ((rulemap (rw.theory-lookup term (rw.control->theory control)))
         (rules   (cdr (lookup type rulemap))))
    (rw.try-urewrite-rule-list hypbox term rules iffp control)))

(encapsulate
 ()
 (local (in-theory (enable rw.try-urewrite-rules)))

 (defthm forcing-rw.trace->lhs-of-rw.try-urewrite-rules
   (implies (force (rw.try-urewrite-rules hypbox term type iffp control))
            (equal (rw.trace->lhs (rw.try-urewrite-rules hypbox term type iffp control))
                   term)))

 (defthm forcing-rw.trace->iffp-of-rw.try-urewrite-rules
   (implies (force (rw.try-urewrite-rules hypbox term type iffp control))
            (equal (rw.trace->iffp (rw.try-urewrite-rules hypbox term type iffp control))
                   iffp)))

 (defthm forcing-rw.trace->hypbox-of-rw.try-urewrite-rules
   (implies (force (rw.try-urewrite-rules hypbox term type iffp control))
            (equal (rw.trace->hypbox (rw.try-urewrite-rules hypbox term type iffp control))
                   hypbox)))

 (defthm forcing-rw.tracep-of-rw.try-urewrite-rules
   (implies (force (and (rw.hypboxp hypbox)
                        (logic.termp term)
                        (booleanp iffp)
                        (rw.controlp control)))
            (equal (rw.tracep (rw.try-urewrite-rules hypbox term type iffp control))
                   (if (rw.try-urewrite-rules hypbox term type iffp control)
                       t
                     nil))))

 (defthm forcing-rw.trace-atblp-of-rw.try-urewrite-rules
   (implies (force (and (rw.hypbox-atblp hypbox atbl)
                        (logic.term-atblp term atbl)
                        (rw.controlp control)
                        (rw.control-atblp control atbl)))
            (equal (rw.trace-atblp (rw.try-urewrite-rules hypbox term type iffp control) atbl)
                   (if (rw.try-urewrite-rules hypbox term type iffp control)
                       t
                     nil))))

 (defthm forcing-rw.trace-okp-of-rw.try-urewrite-rules
   (implies (force (and (logic.termp term)
                        (rw.controlp control)))
            (equal (rw.trace-okp (rw.try-urewrite-rules hypbox term type iffp control) defs)
                   (if (rw.try-urewrite-rules hypbox term type iffp control)
                       t
                     nil))))

 (defthm forcing-rw.trace-env-okp-of-rw.try-urewrite-rules
   (implies (force (and (logic.termp term)
                        (logic.term-atblp term atbl)
                        (rw.controlp control)
                        (rw.control-atblp control atbl)
                        (rw.control-env-okp control axioms thms)))
            (equal (rw.trace-env-okp (rw.try-urewrite-rules hypbox term type iffp control) defs thms atbl)
                   t)))

 (defthm forcing-rw.collect-forced-goals-of-rw.try-urewrite-rules
   (implies (force (rw.try-urewrite-rules hypbox term type iffp control))
            (equal (rw.collect-forced-goals (rw.try-urewrite-rules hypbox term type iffp control))
                   nil))))

