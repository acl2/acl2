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
(include-book "trace-okp")
(include-book "collect-forced-goals")
(include-book "../controlp")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)



(defthmd booleanp-of-rw.trace->iffp
  (implies (rw.tracep x)
           (equal (booleanp (rw.trace->iffp x))
                  t)))

(ACL2::theory-invariant (ACL2::incompatible (:rewrite booleanp-of-rw.trace->iffp)
                                            (:rewrite forcing-booleanp-of-rw.trace->iffp)))

(local (in-theory (e/d (booleanp-of-rw.trace->iffp)
                       (forcing-booleanp-of-rw.trace->iffp))))




(defund rw.fail-trace (hypbox term iffp)
  (declare (xargs :guard (and (rw.hypboxp hypbox)
                              (logic.termp term)
                              (booleanp iffp))))
  (rw.trace 'fail hypbox term term iffp nil nil))

(encapsulate
 ()
 (local (in-theory (enable rw.fail-trace)))

 (defthm rw.trace->method-of-rw.fail-trace
   (equal (rw.trace->method (rw.fail-trace hypbox term iffp))
          'fail))

 (defthm rw.trace->hypbox-of-rw.fail-trace
   (equal (rw.trace->hypbox (rw.fail-trace hypbox term iffp))
          hypbox))

 (defthm rw.trace->lhs-of-rw.fail-trace
   (equal (rw.trace->lhs (rw.fail-trace hypbox term iffp))
          term))

 (defthm rw.trace->rhs-of-rw.fail-trace
   (equal (rw.trace->rhs (rw.fail-trace hypbox term iffp))
          term))

 (defthm rw.trace->iffp-of-rw.fail-trace
   (equal (rw.trace->iffp (rw.fail-trace hypbox term iffp))
          iffp))

 (defthm rw.trace->subtraces-of-rw.fail-trace
   (equal (rw.trace->subtraces (rw.fail-trace hypbox term iffp))
          nil))

 (defthm rw.trace->extras-of-rw.fail-trace
   (equal (rw.trace->extras (rw.fail-trace hypbox term iffp))
          nil))

 (defthm forcing-rw.tracep-of-rw.fail-trace
   (implies (force (and (rw.hypboxp hypbox)
                        (logic.termp term)
                        (booleanp iffp)))
            (equal (rw.tracep (rw.fail-trace hypbox term iffp))
                   t)))

 (defthm forcing-rw.trace-atblp-of-rw.fail-trace
   (implies (force (and (rw.hypbox-atblp hypbox atbl)
                        (logic.term-atblp term atbl)))
            (equal (rw.trace-atblp (rw.fail-trace hypbox term iffp) atbl)
                   t)))

 (local (in-theory (disable rw.fail-trace)))

 (defthm rw.fail-tracep-of-rw.fail-trace
   (equal (rw.fail-tracep (rw.fail-trace hypbox term iffp))
          t)
   :hints(("Goal" :in-theory (enable rw.fail-tracep))))

 (defthm rw.trace-step-okp-of-rw.fail-trace
   (equal (rw.trace-step-okp (rw.fail-trace hypbox term iffp) defs)
          t)
   :hints(("Goal" :in-theory (enable rw.trace-step-okp))))

 (defthm rw.trace-step-env-okp-of-rw.fail-trace
   (equal (rw.trace-step-env-okp (rw.fail-trace hypbox term iffp) defs thms atbl)
          t)
   :hints(("Goal" :in-theory (enable rw.trace-step-env-okp))))

 (defthm forcing-rw.trace-okp-of-rw.fail-trace
   (equal (rw.trace-okp (rw.fail-trace hypbox term iffp) defs)
          t)
   :hints(("Goal" :in-theory (enable definition-of-rw.trace-okp))))

 (defthm forcing-rw.trace-env-okp-of-rw.fail-trace
   (equal (rw.trace-env-okp (rw.fail-trace hypbox term iffp) defs thms atbl)
          t)
   :hints(("Goal" :in-theory (enable definition-of-rw.trace-env-okp))))

 (defthm rw.collect-forced-goals-of-rw.fail-trace
   (equal (rw.collect-forced-goals (rw.fail-trace hypbox term iffp))
          nil)
   :hints(("Goal" :in-theory (enable definition-of-rw.collect-forced-goals)))))





(defund rw.transitivity-trace (x y)
  (declare (xargs :guard (and (rw.tracep x)
                              (rw.tracep y)
                              (equal (rw.trace->iffp x) (rw.trace->iffp y))
                              (equal (rw.trace->hypbox x) (rw.trace->hypbox y))
                              (equal (rw.trace->rhs x) (rw.trace->lhs y)))))
  ;; Historical note.  Originally I checked to see if x.lhs == y.rhs, and if so
  ;; just used a fail trace.  Now I drop this optimization in favor of having
  ;; consistent fgoals, which helps in the proof of the fast rewriter.
  (let ((a     (rw.trace->lhs x))
        (c     (rw.trace->rhs y))
        (hypbox (rw.trace->hypbox x))
        (iffp  (rw.trace->iffp x)))
    (rw.trace 'transitivity hypbox a c iffp (list x y) nil)))

(encapsulate
 ()
 (local (in-theory (enable rw.transitivity-trace)))

 (defthm rw.transitivity-trace-under-iff
   (iff (rw.transitivity-trace x y)
        t))

 (defthm rw.trace->method-of-rw.transitivity-trace
   (equal (rw.trace->method (rw.transitivity-trace x y))
          'transitivity))

 (defthm rw.trace->hypbox-of-rw.transitivity-trace
   (equal (rw.trace->hypbox (rw.transitivity-trace x y))
          (rw.trace->hypbox x)))

 (defthm rw.trace->lhs-of-rw.transitivity-trace
   (equal (rw.trace->lhs (rw.transitivity-trace x y))
          (rw.trace->lhs x)))

 (defthm rw.trace->rhs-of-rw.transitivity-trace
   (equal (rw.trace->rhs (rw.transitivity-trace x y))
          (rw.trace->rhs y)))

 (defthm rw.trace->iffp-of-rw.transitivity-trace
   (equal (rw.trace->iffp (rw.transitivity-trace x y))
          (rw.trace->iffp x)))

 (defthm rw.trace->subtraces-of-rw.transitivity-trace
   (equal (rw.trace->subtraces (rw.transitivity-trace x y))
          (list x y)))

 (defthm rw.trace->extras-of-rw.transitivity-trace
   (equal (rw.trace->extras (rw.transitivity-trace x y))
          nil))

 (defthm forcing-rw.tracep-of-rw.transitivity-trace
   (implies (force (and (rw.tracep x)
                        (rw.tracep y)))
            (equal (rw.tracep (rw.transitivity-trace x y))
                   t)))

 (defthm forcing-rw.trace-atblp-of-rw.transitivity-trace
   (implies (force (and (rw.trace-atblp x atbl)
                        (rw.trace-atblp y atbl)))
            (equal (rw.trace-atblp (rw.transitivity-trace x y) atbl)
                   t)))

 (local (in-theory (disable rw.transitivity-trace)))

 (defthmd lemma-forcing-rw.trace-step-okp-of-rw.transitivity-trace
   (implies (force (and (equal (rw.trace->iffp x) (rw.trace->iffp y))
                        (equal (rw.trace->hypbox x) (rw.trace->hypbox y))
                        (equal (rw.trace->rhs x) (rw.trace->lhs y))))
            (equal (rw.trace-step-okp (rw.transitivity-trace x y) defs)
                   t))
   :hints(("Goal"
           :in-theory (enable rw.transitivity-tracep)
           :expand (rw.trace-step-okp (rw.transitivity-trace x y) defs))))

 (defthm forcing-rw.trace-okp-of-rw.transitivity-trace
   (implies (force (and (equal (rw.trace->iffp x) (rw.trace->iffp y))
                        (equal (rw.trace->hypbox x) (rw.trace->hypbox y))
                        (equal (rw.trace->rhs x) (rw.trace->lhs y))
                        (rw.trace-okp x defs)
                        (rw.trace-okp y defs)))
            (equal (rw.trace-okp (rw.transitivity-trace x y) defs)
                   t))
   :hints(("Goal"
           :expand ((rw.trace-okp (rw.transitivity-trace x y) defs))
           :in-theory (enable lemma-forcing-rw.trace-step-okp-of-rw.transitivity-trace))))

 (defthmd lemma-forcing-rw.trace-step-env-okp-of-rw.transitivity-trace
   (equal (rw.trace-step-env-okp (rw.transitivity-trace x y) defs thms atbl)
          t)
   :hints(("Goal"
           :in-theory (enable rw.transitivity-tracep)
           :expand (rw.trace-step-env-okp (rw.transitivity-trace x y) defs thms atbl))))

 (defthm forcing-rw.trace-env-okp-of-rw.transitivity-trace
   (implies (force (and (rw.trace-env-okp x defs thms atbl)
                        (rw.trace-env-okp y defs thms atbl)))
            (equal (rw.trace-env-okp (rw.transitivity-trace x y) defs thms atbl)
                   t))
   :hints(("Goal"
           :expand (rw.trace-env-okp (rw.transitivity-trace x y) defs thms atbl)
           :in-theory (enable lemma-forcing-rw.trace-step-env-okp-of-rw.transitivity-trace))))

 (defthm rw.collect-forced-goals-of-rw.transitivity-trace
   (equal (rw.collect-forced-goals (rw.transitivity-trace x y))
          (fast-merge (rw.collect-forced-goals x)
                      (rw.collect-forced-goals y)))
   :hints(("Goal" :in-theory (enable definition-of-rw.collect-forced-goals)))))




(defund rw.equiv-by-args-trace (hypbox f iffp traces)
  (declare (xargs :guard (and (rw.hypboxp hypbox)
                              (logic.function-namep f)
                              (booleanp iffp)
                              (rw.trace-listp traces)
                              (all-equalp nil (rw.trace-list-iffps traces))
                              (all-equalp hypbox (rw.trace-list-hypboxes traces)))))
  (let ((lhses (rw.trace-list-lhses traces))
        (rhses (rw.trace-list-rhses traces)))
    (rw.trace 'equiv-by-args
              hypbox
              (logic.function f lhses)
              (logic.function f rhses)
              iffp
              traces
              nil)))

(encapsulate
 ()
 (local (in-theory (enable rw.equiv-by-args-trace)))

 (defthm lemma-rw.trace->method-of-rw.equiv-by-args-trace
   (equal (rw.trace->method (rw.equiv-by-args-trace hypbox f iffp traces))
          'equiv-by-args))

 (defthm forcing-rw.trace->hypbox-of-rw.equiv-by-args-trace
   (equal (rw.trace->hypbox (rw.equiv-by-args-trace hypbox f iffp traces))
          hypbox))

 (defthm forcing-rw.trace->lhs-of-rw.equiv-by-args-trace
   (equal (rw.trace->lhs (rw.equiv-by-args-trace hypbox f iffp traces))
          (logic.function f (rw.trace-list-lhses traces)))
   :hints(("Goal" :in-theory (disable equal-of-logic.function-rewrite))))

 (defthm forcing-rw.trace->rhs-of-rw.equiv-by-args-trace
   (equal (rw.trace->rhs (rw.equiv-by-args-trace hypbox f iffp traces))
          (logic.function f (rw.trace-list-rhses traces)))
   :hints(("Goal" :in-theory (disable equal-of-logic.function-rewrite))))

 (defthm rw.trace->iffp-of-rw.equiv-by-args-trace
   (equal (rw.trace->iffp (rw.equiv-by-args-trace hypbox f iffp traces))
          iffp))

 (defthm rw.trace->subtraces-of-rw.equiv-by-args-trace
   (equal (rw.trace->subtraces (rw.equiv-by-args-trace hypbox f iffp traces))
          traces))

 (defthm rw.trace->extras-of-rw.equiv-by-args-trace
   (equal (rw.trace->extras (rw.equiv-by-args-trace hypbox f iffp traces))
          nil))

 (defthm forcing-rw.tracep-of-rw.equiv-by-args-trace
   (implies (force (and (rw.hypboxp hypbox)
                        (logic.function-namep f)
                        (booleanp iffp)
                        (rw.trace-listp traces)))
            (equal (rw.tracep (rw.equiv-by-args-trace hypbox f iffp traces))
                   t)))

 (defthm forcing-rw.trace-atblp-of-rw.equiv-by-args-trace
   (implies (force (and (rw.hypbox-atblp hypbox atbl)
                        (logic.function-namep f)
                        (equal (len traces) (cdr (lookup f atbl)))
                        (rw.trace-list-atblp traces atbl)))
            (equal (rw.trace-atblp (rw.equiv-by-args-trace hypbox f iffp traces) atbl)
                   t)))

 (local (in-theory (disable rw.equiv-by-args-trace)))

 (defthmd lemma-forcing-rw.trace-step-okp-of-rw.equiv-by-args-trace
   (implies (force (and (logic.function-namep f)
                        (all-equalp hypbox (rw.trace-list-hypboxes traces))
                        (all-equalp nil (rw.trace-list-iffps traces))))
            (equal (rw.trace-step-okp (rw.equiv-by-args-trace hypbox f iffp traces) defs)
                   t))
   :hints(("Goal" :in-theory (enable rw.equiv-by-args-tracep rw.trace-step-okp))))

 (defthm forcing-rw.trace-okp-of-rw.equiv-by-args-trace
   (implies (force (and (logic.function-namep f)
                        (all-equalp hypbox (rw.trace-list-hypboxes traces))
                        (all-equalp nil (rw.trace-list-iffps traces))
                        (rw.trace-list-okp traces defs)))
            (equal (rw.trace-okp (rw.equiv-by-args-trace hypbox f iffp traces) defs)
                   t))
   :hints(("Goal"
           :in-theory (enable definition-of-rw.trace-okp
                              lemma-forcing-rw.trace-step-okp-of-rw.equiv-by-args-trace))))

 (defthmd lemma-forcing-rw.trace-step-env-okp-of-rw.equiv-by-args-trace
   (equal (rw.trace-step-env-okp (rw.equiv-by-args-trace hypbox f iffp traces) defs thms abtl)
          t)
   :hints(("Goal" :in-theory (enable rw.equiv-by-args-tracep rw.trace-step-env-okp))))

 (defthm forcing-rw.trace-env-okp-of-rw.equiv-by-args-trace
   (implies (force (rw.trace-list-env-okp traces defs thms atbl))
            (equal (rw.trace-env-okp (rw.equiv-by-args-trace hypbox f iffp traces) defs thms atbl)
                   t))
   :hints(("Goal" :in-theory (enable definition-of-rw.trace-env-okp
                                     lemma-forcing-rw.trace-step-env-okp-of-rw.equiv-by-args-trace))))

 (defthm rw.collect-forced-goals-of-rw.equiv-by-args-trace
   (equal (rw.collect-forced-goals (rw.equiv-by-args-trace hypbox f iffp traces))
          (rw.collect-forced-goals-list traces))
   :hints(("Goal" :in-theory (enable definition-of-rw.collect-forced-goals)))))




(defund rw.lambda-equiv-by-args-trace (hypbox formals body iffp traces)
  (declare (xargs :guard (and (rw.hypboxp hypbox)
                              (true-listp formals)
                              (logic.variable-listp formals)
                              (uniquep formals)
                              (logic.termp body)
                              (subsetp (logic.term-vars body) formals)
                              (booleanp iffp)
                              (rw.trace-listp traces)
                              (all-equalp hypbox (rw.trace-list-hypboxes traces))
                              (all-equalp nil (rw.trace-list-iffps traces))
                              (equal (len traces) (len formals)))))
  (let ((lhses (rw.trace-list-lhses traces))
        (rhses (rw.trace-list-rhses traces)))
    ; same rationale as before.
    ;(if (equal lhses rhses)
    ;    (rw.fail-trace hypbox (logic.lambda formals body lhses) iffp)
    (rw.trace 'lambda-equiv-by-args
              hypbox
              (logic.lambda formals body lhses)
              (logic.lambda formals body rhses)
              iffp
              traces
              nil)))

(encapsulate
 ()
 (local (in-theory (enable rw.lambda-equiv-by-args-trace)))

 (defthm rw.trace->method-of-rw.lambda-equiv-by-args-trace
   (equal (rw.trace->method (rw.lambda-equiv-by-args-trace hypbox formals body iffp traces))
          'lambda-equiv-by-args))

 (defthm rw.trace->hypbox-of-rw.lambda-equiv-by-args-trace
   (equal (rw.trace->hypbox (rw.lambda-equiv-by-args-trace hypbox formals body iffp traces))
          hypbox))

 (defthm rw.trace->lhs-of-rw.lambda-equiv-by-args-trace
   (equal (rw.trace->lhs (rw.lambda-equiv-by-args-trace hypbox formals body iffp traces))
          (logic.lambda formals body (rw.trace-list-lhses traces))))

 (defthm rw.trace->rhs-of-rw.lambda-equiv-by-args-trace
   (equal (rw.trace->rhs (rw.lambda-equiv-by-args-trace hypbox formals body iffp traces))
          (logic.lambda formals body (rw.trace-list-rhses traces))))

 (defthm rw.trace->iffp-of-rw.lambda-equiv-by-args-trace
   (equal (rw.trace->iffp (rw.lambda-equiv-by-args-trace hypbox formals body iffp traces))
          iffp))

 (defthm rw.trace->subtraces-of-rw.lambda-equiv-by-args-trace
   (equal (rw.trace->subtraces (rw.lambda-equiv-by-args-trace hypbox formals body iffp traces))
          traces))

 (defthm rw.trace->extras-of-rw.lambda-equiv-by-args-trace
   (equal (rw.trace->extras (rw.lambda-equiv-by-args-trace hypbox formals body iffp traces))
          nil))

 (defthm forcing-rw.tracep-of-rw.lambda-equiv-by-args-trace
   (implies (force (and (rw.hypboxp hypbox)
                        (true-listp formals)
                        (logic.variable-listp formals)
                        (uniquep formals)
                        (logic.termp body)
                        (subsetp (logic.term-vars body) formals)
                        (booleanp iffp)
                        (rw.trace-listp traces)
                        (equal (len traces) (len formals))))
            (equal (rw.tracep (rw.lambda-equiv-by-args-trace hypbox formals body iffp traces))
                   t)))

 (defthm forcing-rw.trace-atblp-of-rw.lambda-equiv-by-args-trace
   (implies (force (and (rw.hypbox-atblp hypbox atbl)
                        (logic.term-atblp body atbl)
                        (rw.trace-list-atblp traces atbl)))
            (equal (rw.trace-atblp (rw.lambda-equiv-by-args-trace hypbox formals body iffp traces) atbl)
                   t)))

 (local (in-theory (disable rw.lambda-equiv-by-args-trace)))

 (defthmd lemma-forcing-rw.trace-step-okp-of-rw.lambda-equiv-by-args-trace
   (implies (force (and (all-equalp nil (rw.trace-list-iffps traces))
                        (all-equalp hypbox (rw.trace-list-hypboxes traces))))
            (equal (rw.trace-step-okp (rw.lambda-equiv-by-args-trace hypbox formals body iffp traces) defs)
                   t))
   :hints(("Goal" :in-theory (e/d (rw.trace-step-okp
                                   rw.lambda-equiv-by-args-tracep)
                                  (forcing-logic.termp-of-logic.lambda)))))

 (defthm forcing-rw.trace-okp-of-rw.lambda-equiv-by-args-trace
   (implies (force (and (all-equalp nil (rw.trace-list-iffps traces))
                        (all-equalp hypbox (rw.trace-list-hypboxes traces))
                        (rw.trace-list-okp traces defs)))
            (equal (rw.trace-okp (rw.lambda-equiv-by-args-trace hypbox formals body iffp traces) defs)
                   t))
   :hints(("Goal" :in-theory (enable definition-of-rw.trace-okp
                                     lemma-forcing-rw.trace-step-okp-of-rw.lambda-equiv-by-args-trace))))

 (defthmd lemma-forcing-rw.trace-step-env-okp-of-rw.lambda-equiv-by-args-trace
   (equal (rw.trace-step-env-okp (rw.lambda-equiv-by-args-trace hypbox formals body iffp traces) defs thms atbl)
          t)
   :hints(("Goal" :in-theory (enable rw.trace-step-env-okp rw.lambda-equiv-by-args-tracep))))

 (defthm forcing-rw.trace-env-okp-of-rw.lambda-equiv-by-args-trace
   (implies (force (rw.trace-list-env-okp traces defs thms atbl))
            (equal (rw.trace-env-okp (rw.lambda-equiv-by-args-trace hypbox formals body iffp traces) defs thms atbl)
                   t))
   :hints(("Goal" :in-theory (enable definition-of-rw.trace-env-okp
                                     lemma-forcing-rw.trace-step-env-okp-of-rw.lambda-equiv-by-args-trace))))

 (defthm rw.collect-forced-goals-of-rw.lambda-equiv-by-args-trace
   (equal (rw.collect-forced-goals (rw.lambda-equiv-by-args-trace hypbox formals body iffp traces))
          (rw.collect-forced-goals-list traces))
   :hints(("Goal" :in-theory (enable definition-of-rw.collect-forced-goals)))))




(defund rw.beta-reduction-trace (hypbox term iffp)
  (declare (xargs :guard (and (rw.hypboxp hypbox)
                              (logic.termp term)
                              (logic.lambdap term)
                              (booleanp iffp))))
  (rw.trace 'beta-reduction
            hypbox
            term
            (logic.substitute (logic.lambda-body term)
                              (pair-lists (logic.lambda-formals term)
                                          (logic.lambda-actuals term)))
            iffp
            nil
            nil))

(encapsulate
 ()
 (local (in-theory (enable rw.beta-reduction-trace)))

 (defthm rw.trace->method-of-rw.beta-reduction-trace
   (equal (rw.trace->method (rw.beta-reduction-trace hypbox term iffp))
          'beta-reduction))

 (defthm rw.trace->hypbox-of-rw.beta-reduction-trace
   (equal (rw.trace->hypbox (rw.beta-reduction-trace hypbox term iffp))
          hypbox))

 (defthm rw.trace->lhs-of-rw.beta-reduction-trace
   (equal (rw.trace->lhs (rw.beta-reduction-trace hypbox term iffp))
          term))

 (defthm rw.trace->rhs-of-rw.beta-reduction-trace
   (equal (rw.trace->rhs (rw.beta-reduction-trace hypbox term iffp))
          (logic.substitute (logic.lambda-body term)
                            (pair-lists (logic.lambda-formals term)
                                        (logic.lambda-actuals term)))))

 (defthm rw.trace->iffp-of-rw.beta-reduction-trace
   (equal (rw.trace->iffp (rw.beta-reduction-trace hypbox term iffp))
          iffp))

 (defthm rw.trace->subtraces-of-rw.beta-reduction-trace
   (equal (rw.trace->subtraces (rw.beta-reduction-trace hypbox term iffp))
          nil))

 (defthm rw.trace->extras-of-rw.beta-reduction-trace
   (equal (rw.trace->extras (rw.beta-reduction-trace hypbox term iffp))
          nil))

 (defthm forcing-rw.tracep-of-rw.beta-reduction-trace
   (implies (force (and (rw.hypboxp hypbox)
                        (logic.termp term)
                        (logic.lambdap term)
                        (booleanp iffp)))
            (equal (rw.tracep (rw.beta-reduction-trace hypbox term iffp))
                   t)))

 (defthm forcing-rw.trace-atblp-of-rw.beta-reduction-trace
   (implies (force (and (rw.hypbox-atblp hypbox atbl)
                        (logic.lambdap term)
                        (logic.termp term)
                        (logic.term-atblp term atbl)))
            (equal (rw.trace-atblp (rw.beta-reduction-trace hypbox term iffp) atbl)
                   t)))

 (local (in-theory (disable rw.beta-reduction-trace)))

 (defthmd lemma-forcing-rw.beta-reduction-tracep-of-rw.beta-reduction-trace
   (implies (force (logic.lambdap term))
            (equal (rw.beta-reduction-tracep (rw.beta-reduction-trace hypbox term iffp))
                   t))
   :hints(("Goal" :in-theory (enable rw.beta-reduction-tracep))))

 (defthmd lemma-forcing-rw.trace-step-okp-of-rw.beta-reduction-trace
   (implies (force (logic.lambdap term))
            (equal (rw.trace-step-okp (rw.beta-reduction-trace hypbox term iffp) defs)
                   t))
   :hints(("Goal" :in-theory (enable rw.trace-step-okp
                                     lemma-forcing-rw.beta-reduction-tracep-of-rw.beta-reduction-trace))))

 (defthm forcing-rw.trace-okp-of-rw.beta-reduction-trace
   (implies (force (logic.lambdap term))
            (equal (rw.trace-okp (rw.beta-reduction-trace hypbox term iffp) defs)
                   t))
   :hints(("Goal" :in-theory (enable definition-of-rw.trace-okp
                                     lemma-forcing-rw.trace-step-okp-of-rw.beta-reduction-trace))))

 (defthmd lemma-forcing-rw.trace-step-env-okp-of-rw.beta-reduction-trace
   (equal (rw.trace-step-env-okp (rw.beta-reduction-trace hypbox term iffp) defs thms atbl)
          t)
   :hints(("Goal" :in-theory (enable rw.trace-step-env-okp))))

 (defthm forcing-rw.trace-env-okp-of-rw.beta-reduction-trace
   (equal (rw.trace-env-okp (rw.beta-reduction-trace hypbox term iffp) defs thms atbl)
          t)
   :hints(("Goal" :in-theory (enable definition-of-rw.trace-env-okp
                                     lemma-forcing-rw.trace-step-env-okp-of-rw.beta-reduction-trace))))

 (defthm rw.collect-forced-goals-of-rw.beta-reduction-trace
   (equal (rw.collect-forced-goals (rw.beta-reduction-trace hypbox term iffp))
          nil)
   :hints(("Goal" :in-theory (enable definition-of-rw.collect-forced-goals)))))




(defund rw.try-ground-simplify (hypbox x iffp control)
  (declare (xargs :guard (and (rw.hypboxp hypbox)
                              (logic.termp x)
                              (logic.groundp x)
                              (booleanp iffp)
                              (rw.controlp control))))
  (if (and (logic.functionp x)
           (memberp (logic.function-name x) (rw.control->noexec control)))
      nil
    (let* ((defs   (rw.control->defs control))
           (depth  (rw.control->depth control))
           (result (generic-evaluator x defs depth)))
      (and result
           (let ((real-result (if (and iffp (not (equal (logic.unquote result) nil)))
                                  ''t
                                result)))
             (and (not (equal real-result x))
                  (rw.trace 'ground hypbox x real-result iffp nil depth)))))))

(encapsulate
 ()
 (local (in-theory (enable rw.try-ground-simplify)))

 (defthm rw.trace->method-of-rw.try-ground-simplify
   (implies (force (rw.try-ground-simplify hypbox x iffp control))
            (equal (rw.trace->method (rw.try-ground-simplify hypbox x iffp control))
                   'ground)))

 (defthm rw.trace->hypbox-of-rw.try-ground-simplify
   (implies (force (rw.try-ground-simplify hypbox x iffp control))
            (equal (rw.trace->hypbox (rw.try-ground-simplify hypbox x iffp control))
                   hypbox)))

 (defthm forcing-rw.trace->lhs-of-rw.try-ground-simplify
   (implies (force (rw.try-ground-simplify hypbox x iffp control))
            (equal (rw.trace->lhs (rw.try-ground-simplify hypbox x iffp control))
                   x)))

 (defthm forcing-rw.trace->iffp-of-rw.try-ground-simplify
   (implies (force (rw.try-ground-simplify hypbox x iffp control))
            (equal (rw.trace->iffp (rw.try-ground-simplify hypbox x iffp control))
                   iffp)))

 (defthm rw.trace->subtraces-of-rw.try-ground-simplify
   (implies (force (rw.try-ground-simplify hypbox x iffp control))
            (equal (rw.trace->subtraces (rw.try-ground-simplify hypbox x iffp control))
                   nil)))

 (defthm forcing-rw.trace->extras-of-rw.try-ground-simplify
   (implies (force (rw.try-ground-simplify hypbox x iffp control))
            (equal (rw.trace->extras (rw.try-ground-simplify hypbox x iffp control))
                   (rw.control->depth control))))

 (defthmd lemma-forcing-logic.constantp-of-rw.trace->rhs
   (implies (force (and (rw.try-ground-simplify hypbox x iffp control)
                        (logic.termp x)
                        (rw.controlp control)))
            (equal (logic.constantp (rw.trace->rhs (rw.try-ground-simplify hypbox x iffp control)))
                   t)))

 (defthm forcing-rw.tracep-of-rw.try-ground-simplify
   (implies (force (and (rw.try-ground-simplify hypbox x iffp control)
                        (rw.hypboxp hypbox)
                        (logic.termp x)
                        (logic.groundp x)
                        (booleanp iffp)
                        (rw.controlp control)))
            (equal (rw.tracep (rw.try-ground-simplify hypbox x iffp control))
                   t)))

 (defthm forcing-rw.trace-atblp-of-rw.try-ground-simplify
   (implies (force (and (rw.try-ground-simplify hypbox x iffp control)
                        (rw.hypbox-atblp hypbox atbl)
                        (logic.term-atblp x atbl)
                        (logic.termp x)
                        (rw.controlp control)))
            (equal (rw.trace-atblp (rw.try-ground-simplify hypbox x iffp control) atbl)
                   t)))

 (defthmd lemma-forcing-rw.ground-tracep-of-rw.try-ground-simplify
   (implies (force (and (rw.try-ground-simplify hypbox x iffp control)
                        (logic.groundp x)
                        (rw.controlp control)))
            (equal (rw.ground-tracep (rw.try-ground-simplify hypbox x iffp control)
                                     (rw.control->defs control))
                   t))
   :hints(("Goal" :in-theory (enable rw.ground-tracep))))

 (local (in-theory (disable rw.try-ground-simplify)))
 (local (in-theory (enable lemma-forcing-logic.constantp-of-rw.trace->rhs
                           lemma-forcing-rw.ground-tracep-of-rw.try-ground-simplify)))

 (defthmd lemma-forcing-rw.trace-step-okp-of-rw.try-ground-simplify
   (implies (force (and (rw.try-ground-simplify hypbox x iffp control)
                        (logic.groundp x)
                        (rw.controlp control)))
            (equal (rw.trace-step-okp (rw.try-ground-simplify hypbox x iffp control)
                                      (rw.control->defs control))
                   t))
   :hints(("Goal" :in-theory (enable rw.trace-step-okp))))

 (defthm forcing-rw.trace-okp-of-rw.try-ground-simplify
   (implies (force (and (rw.try-ground-simplify hypbox x iffp control)
                        (logic.groundp x)
                        (rw.controlp control)))
            (equal (rw.trace-okp (rw.try-ground-simplify hypbox x iffp control)
                                 (rw.control->defs control))
                   t))
   :hints(("Goal" :in-theory (enable definition-of-rw.trace-okp
                                     lemma-forcing-rw.trace-step-okp-of-rw.try-ground-simplify))))

 (defthmd lemma-forcing-rw.trace-step-env-okp-of-rw.try-ground-simplify
   (implies (force (and (rw.try-ground-simplify hypbox x iffp control)
                        (logic.groundp x)
                        (rw.controlp control)
                        (rw.control-atblp control atbl)))
            (equal (rw.trace-step-env-okp (rw.try-ground-simplify hypbox x iffp control)
                                          defs thms atbl)
                   t))
   :hints(("Goal" :in-theory (enable rw.trace-step-env-okp))))

 (defthm forcing-rw.trace-env-okp-of-rw.try-ground-simplify
   (implies (force (and (rw.try-ground-simplify hypbox x iffp control)
                        (logic.groundp x)
                        (rw.controlp control)
                        (rw.control-atblp control atbl)))
            (equal (rw.trace-env-okp (rw.try-ground-simplify hypbox x iffp control) defs thms atbl)
                   t))
   :hints(("Goal" :in-theory (enable definition-of-rw.trace-env-okp
                                     lemma-forcing-rw.trace-step-env-okp-of-rw.try-ground-simplify))))

 (defthm forcing-rw.collect-forced-goals-of-rw.try-ground-simplify
   (implies (force (rw.try-ground-simplify hypbox x iffp control))
            (equal (rw.collect-forced-goals (rw.try-ground-simplify hypbox x iffp control))
                   nil))
   :hints(("Goal" :in-theory (enable definition-of-rw.collect-forced-goals)))))




(defund rw.if-specialcase-nil-trace (x y b1)
  (declare (xargs :guard (and (rw.tracep x)
                              (rw.tracep y)
                              (equal (rw.trace->hypbox x) (rw.trace->hypbox y))
                              (logic.termp b1)
                              (rw.trace->iffp x)
                              (equal (rw.trace->rhs x) ''nil))))
  (rw.trace 'if-specialcase-nil
            (rw.trace->hypbox x)
            (logic.function 'if (list (rw.trace->lhs x) b1 (rw.trace->lhs y)))
            (rw.trace->rhs y)
            (rw.trace->iffp y)
            (list x y)
            nil))

(encapsulate
 ()
 (local (in-theory (enable rw.if-specialcase-nil-trace)))

 (defthm rw.trace->method-of-rw.if-specialcase-nil-trace
   (equal (rw.trace->method (rw.if-specialcase-nil-trace x y b1))
          'if-specialcase-nil))

 (defthm rw.trace->hypbox-of-rw.if-specialcase-nil-trace
   (equal (rw.trace->hypbox (rw.if-specialcase-nil-trace x y b1))
          (rw.trace->hypbox x)))

 (defthm rw.trace->lhs-of-rw.if-specialcase-nil-trace
   (equal (rw.trace->lhs (rw.if-specialcase-nil-trace x y b1))
          (logic.function 'if (list (rw.trace->lhs x) b1 (rw.trace->lhs y)))))

 (defthm rw.trace->rhs-of-rw.if-specialcase-nil-trace
   (equal (rw.trace->rhs (rw.if-specialcase-nil-trace x y b1))
          (rw.trace->rhs y)))

 (defthm rw.trace->iffp-of-rw.if-specialcase-nil-trace
   (equal (rw.trace->iffp (rw.if-specialcase-nil-trace x y b1))
          (rw.trace->iffp y)))

 (defthm rw.trace->subtraces-of-rw.if-specialcase-nil-trace
   (equal (rw.trace->subtraces (rw.if-specialcase-nil-trace x y b1))
          (list x y)))

 (defthm rw.trace->extras-of-rw.if-specialcase-nil-trace
   (equal (rw.trace->extras (rw.if-specialcase-nil-trace x y b1))
          nil))

 (defthm forcing-rw.tracep-of-rw.if-specialcase-nil-trace
   (implies (force (and (rw.tracep x)
                        (rw.tracep y)
                        (logic.termp b1)))
            (equal (rw.tracep (rw.if-specialcase-nil-trace x y b1))
                   t)))

 (defthm forcing-rw.trace-atblp-of-rw.if-specialcase-nil-trace
   (implies (force (and (rw.trace-atblp x atbl)
                        (rw.trace-atblp y atbl)
                        (logic.term-atblp b1 atbl)
                        (equal (cdr (lookup 'if atbl)) 3)))
            (equal (rw.trace-atblp (rw.if-specialcase-nil-trace x y b1) atbl)
                   t)))

 (local (in-theory (disable rw.if-specialcase-nil-trace)))

 (defthmd lemma-forcing-rw.if-specialcase-nil-tracep-of-rw.if-specialcase-nil-trace
   (implies (force (and (equal (rw.trace->hypbox x) (rw.trace->hypbox y))
                        (rw.trace->iffp x)
                        (equal (rw.trace->rhs x) ''nil)))
            (equal (rw.if-specialcase-nil-tracep (rw.if-specialcase-nil-trace x y b1))
                   t))
   :hints(("Goal" :in-theory (enable rw.if-specialcase-nil-tracep))))

 (defthmd lemma-forcing-rw.trace-step-okp-of-rw.if-specialcase-nil-trace
   (implies (force (and (equal (rw.trace->hypbox x) (rw.trace->hypbox y))
                        (rw.trace->iffp x)
                        (equal (rw.trace->rhs x) ''nil)))
            (equal (rw.trace-step-okp (rw.if-specialcase-nil-trace x y b1) defs)
                   t))
   :hints(("Goal" :in-theory (enable rw.trace-step-okp
                                     lemma-forcing-rw.if-specialcase-nil-tracep-of-rw.if-specialcase-nil-trace))))

 (defthm forcing-rw.trace-okp-of-rw.if-specialcase-nil-trace
   (implies (force (and (equal (rw.trace->hypbox x) (rw.trace->hypbox y))
                        (rw.trace->iffp x)
                        (equal (rw.trace->rhs x) ''nil)
                        (rw.trace-okp x defs)
                        (rw.trace-okp y defs)))
            (equal (rw.trace-okp (rw.if-specialcase-nil-trace x y b1) defs)
                   t))
   :hints(("Goal"
           :expand ((rw.trace-okp (rw.if-specialcase-nil-trace x y b1) defs))
           :in-theory (enable lemma-forcing-rw.trace-step-okp-of-rw.if-specialcase-nil-trace))))

 (defthmd lemma-forcing-rw.trace-step-env-okp-of-rw.if-specialcase-nil-trace
   (equal (rw.trace-step-env-okp (rw.if-specialcase-nil-trace x y b1) defs thms atbl)
          t)
   :hints(("Goal" :in-theory (enable rw.trace-step-env-okp))))

 (defthm forcing-rw.trace-env-okp-of-rw.if-specialcase-nil-trace
   (implies (force (and (rw.trace-env-okp x defs thms atbl)
                        (rw.trace-env-okp y defs thms atbl)))
            (equal (rw.trace-env-okp (rw.if-specialcase-nil-trace x y b1) defs thms atbl)
                   t))
   :hints(("Goal"
           :expand ((rw.trace-env-okp (rw.if-specialcase-nil-trace x y b1) defs thms atbl))
           :in-theory (enable lemma-forcing-rw.trace-step-env-okp-of-rw.if-specialcase-nil-trace))))

 (defthm rw.collect-forced-goals-of-rw.if-specialcase-nil-trace
   (equal (rw.collect-forced-goals (rw.if-specialcase-nil-trace x y b1))
          (fast-merge (rw.collect-forced-goals x)
                      (rw.collect-forced-goals y)))
   :hints(("Goal" :in-theory (enable definition-of-rw.collect-forced-goals)))))




(defund rw.if-specialcase-t-trace (x y c1)
  (declare (xargs :guard (and (rw.tracep x)
                              (rw.tracep y)
                              (logic.termp c1)
                              (equal (rw.trace->hypbox x) (rw.trace->hypbox y))
                              (rw.trace->iffp x)
                              (logic.constantp (rw.trace->rhs x))
                              (not (equal (logic.unquote (rw.trace->rhs x)) nil)))))
  (rw.trace 'if-specialcase-t
            (rw.trace->hypbox x)
            (logic.function 'if (list (rw.trace->lhs x) (rw.trace->lhs y) c1))
            (rw.trace->rhs y)
            (rw.trace->iffp y)
            (list x y)
            nil))

(encapsulate
 ()
 (local (in-theory (enable rw.if-specialcase-t-trace)))

 (defthm rw.trace->method-of-rw.if-specialcase-t-trace
   (equal (rw.trace->method (rw.if-specialcase-t-trace x y c1))
          'if-specialcase-t))

 (defthm rw.trace->hypbox-of-rw.if-specialcase-t-trace
   (equal (rw.trace->hypbox (rw.if-specialcase-t-trace x y c1))
          (rw.trace->hypbox x)))

 (defthm rw.trace->lhs-of-rw.if-specialcase-t-trace
   (equal (rw.trace->lhs (rw.if-specialcase-t-trace x y c1))
          (logic.function 'if (list (rw.trace->lhs x) (rw.trace->lhs y) c1))))

 (defthm rw.trace->rhs-of-rw.if-specialcase-t-trace
   (equal (rw.trace->rhs (rw.if-specialcase-t-trace x y c1))
          (rw.trace->rhs y)))

 (defthm rw.trace->iffp-of-rw.if-specialcase-t-trace
   (equal (rw.trace->iffp (rw.if-specialcase-t-trace x y c1))
          (rw.trace->iffp y)))

 (defthm rw.trace->subtraces-of-rw.if-specialcase-t-trace
   (equal (rw.trace->subtraces (rw.if-specialcase-t-trace x y c1))
          (list x y)))

 (defthm rw.trace->extras-of-rw.if-specialcase-t-trace
   (equal (rw.trace->extras (rw.if-specialcase-t-trace x y c1))
          nil))

 (defthm forcing-rw.tracep-of-rw.if-specialcase-t-trace
   (implies (force (and (rw.tracep x)
                        (rw.tracep y)
                        (logic.termp c1)))
            (equal (rw.tracep (rw.if-specialcase-t-trace x y c1))
                   t)))

 (defthm forcing-rw.trace-atblp-of-rw.if-specialcase-t-trace
   (implies (force (and (rw.trace-atblp x atbl)
                        (rw.trace-atblp y atbl)
                        (logic.term-atblp c1 atbl)
                        (equal (cdr (lookup 'if atbl)) 3)))
            (equal (rw.trace-atblp (rw.if-specialcase-t-trace x y c1) atbl)
                   t)))

 (local (in-theory (disable rw.if-specialcase-t-trace)))

 (defthmd lemma-forcing-rw.if-specialcase-t-tracep-of-rw.if-specialcase-t-trace
   (implies (force (and (equal (rw.trace->hypbox x) (rw.trace->hypbox y))
                        (rw.trace->iffp x)
                        (logic.constantp (rw.trace->rhs x))
                        (not (equal (logic.unquote (rw.trace->rhs x)) nil))))
            (equal (rw.if-specialcase-t-tracep (rw.if-specialcase-t-trace x y c1))
                   t))
   :hints(("Goal" :in-theory (enable rw.if-specialcase-t-tracep))))

 (defthmd lemma-forcing-rw.trace-step-okp-of-rw.if-specialcase-t-trace
   (implies (force (and (equal (rw.trace->hypbox x) (rw.trace->hypbox y))
                        (rw.trace->iffp x)
                        (logic.constantp (rw.trace->rhs x))
                        (not (equal (logic.unquote (rw.trace->rhs x)) nil))))
            (equal (rw.trace-step-okp (rw.if-specialcase-t-trace x y c1) defs)
                   t))
   :hints(("Goal" :in-theory (enable rw.trace-step-okp
                                     lemma-forcing-rw.if-specialcase-t-tracep-of-rw.if-specialcase-t-trace))))

 (defthm forcing-rw.trace-okp-of-rw.if-specialcase-t-trace
   (implies (force (and (equal (rw.trace->hypbox x) (rw.trace->hypbox y))
                        (rw.trace->iffp x)
                        (logic.constantp (rw.trace->rhs x))
                        (not (equal (logic.unquote (rw.trace->rhs x)) nil))
                        (rw.trace-okp x defs)
                        (rw.trace-okp y defs)))
            (equal (rw.trace-okp (rw.if-specialcase-t-trace x y c1) defs)
                   t))
   :hints(("Goal"
           :expand ((rw.trace-okp (rw.if-specialcase-t-trace x y c1) defs))
           :in-theory (enable lemma-forcing-rw.trace-step-okp-of-rw.if-specialcase-t-trace))))

 (defthmd lemma-forcing-rw.trace-step-env-okp-of-rw.if-specialcase-t-trace
   (equal (rw.trace-step-env-okp (rw.if-specialcase-t-trace x y c1) defs thms atbl)
          t)
   :hints(("Goal" :in-theory (enable rw.trace-step-env-okp))))

 (defthm forcing-rw.trace-env-okp-of-rw.if-specialcase-t-trace
   (implies (force (and (rw.trace-env-okp x defs thms atbl)
                        (rw.trace-env-okp y defs thms atbl)))
            (equal (rw.trace-env-okp (rw.if-specialcase-t-trace x y c1) defs thms atbl)
                   t))
   :hints(("Goal"
           :expand ((rw.trace-env-okp (rw.if-specialcase-t-trace x y c1) defs thms atbl))
           :in-theory (enable lemma-forcing-rw.trace-step-env-okp-of-rw.if-specialcase-t-trace))))

 (defthm rw.collect-forced-goals-of-rw.if-specialcase-t-trace
   (equal (rw.collect-forced-goals (rw.if-specialcase-t-trace x y c1))
          (fast-merge (rw.collect-forced-goals x)
                      (rw.collect-forced-goals y)))
   :hints(("Goal" :in-theory (enable definition-of-rw.collect-forced-goals)))))



(defund rw.not-trace (x iffp)
  (declare (xargs :guard (and (rw.tracep x)
                              (booleanp iffp)
                              (rw.trace->iffp x))))
  (rw.trace 'not
            (rw.trace->hypbox x)
            (logic.function 'not (list (rw.trace->lhs x)))
            (let ((rhs (rw.trace->rhs x)))
              (cond ((equal rhs ''nil) ''t)
                    ((equal rhs ''t)   ''nil)
                    (t                 (logic.function 'not (list rhs)))))
            iffp
            (list x)
            nil))

(encapsulate
 ()
 (local (in-theory (enable rw.not-trace)))

 (defthm rw.trace->method-of-rw.not-trace
   (equal (rw.trace->method (rw.not-trace x iffp))
          'not))

 (defthm rw.trace->hypbox-of-rw.not-trace
   (equal (rw.trace->hypbox (rw.not-trace x iffp))
          (rw.trace->hypbox x))
   :hints(("Goal" :in-theory (disable (:executable-counterpart ACL2::force)))))

 (defthm rw.trace->lhs-of-rw.not-trace
   (equal (rw.trace->lhs (rw.not-trace x iffp))
          (logic.function 'not (list (rw.trace->lhs x))))
   :hints(("Goal" :in-theory (disable (:executable-counterpart ACL2::force)))))

 (defthmd lemma-rw.trace->rhs-of-rw.not-trace
   (equal (rw.trace->rhs (rw.not-trace x iffp))
          (cond ((and (equal (rw.trace->lhs x) (rw.trace->rhs x))
                      (not (equal (rw.trace->rhs x) ''t))
                      (not (equal (rw.trace->rhs x) ''nil)))
                 (logic.function 'not (list (rw.trace->rhs x))))
                ((equal (rw.trace->rhs x) ''nil)
                 ''t)
                ((equal (rw.trace->rhs x) ''t)
                 ''nil)
                (t
                 (logic.function 'not (list (rw.trace->rhs x))))))
   :hints(("Goal" :in-theory (disable (:executable-counterpart ACL2::force)))))

 (defthm forcing-rw.trace->iffp-of-rw.not-trace
   (equal (rw.trace->iffp (rw.not-trace x iffp))
          iffp)
   :hints(("Goal" :in-theory (disable (:executable-counterpart ACL2::force)))))

 (defthm rw.trace->subtraces-of-rw.not-trace
   (equal (rw.trace->subtraces (rw.not-trace x iffp))
          (list x))
   :hints(("Goal" :in-theory (disable (:executable-counterpart ACL2::force)))))

 (defthm rw.trace->extras-of-rw.not-trace
   (equal (rw.trace->extras (rw.not-trace x iffp))
          nil)
   :hints(("Goal" :in-theory (disable (:executable-counterpart ACL2::force)))))

 (defthm forcing-rw.tracep-of-rw.not-trace
   (implies (force (and (rw.tracep x)
                        (booleanp iffp)))
            (equal (rw.tracep (rw.not-trace x iffp))
                   t)))

 (defthm forcing-rw.trace-atblp-of-rw.not-trace
   (implies (force (and (rw.trace-atblp x atbl)
                        (equal (cdr (lookup 'not atbl)) 1)))
            (equal (rw.trace-atblp (rw.not-trace x iffp) atbl)
                   t))
   :hints(("Goal" :in-theory (disable (:executable-counterpart ACL2::force)))))

 (local (in-theory (disable rw.not-trace)))
 (local (in-theory (enable lemma-rw.trace->rhs-of-rw.not-trace)))

 (defthmd lemma-forcing-rw.not-tracep-of-rw.not-trace
   (implies (force (and (rw.tracep x)
                        (rw.trace->iffp x)))
            (equal (rw.not-tracep (rw.not-trace x iffp))
                   t))
   :hints(("Goal" :in-theory (enable rw.not-tracep))))

 (defthmd lemma-forcing-rw.trace-step-okp-of-rw.not-trace
   (implies (force (and (rw.tracep x)
                        (rw.trace->iffp x)))
            (equal (rw.trace-step-okp (rw.not-trace x iffp) defs)
                   t))
   :hints(("Goal" :in-theory (enable rw.trace-step-okp
                                     lemma-forcing-rw.not-tracep-of-rw.not-trace))))

 (defthm forcing-rw.trace-okp-of-rw.not-trace
   (implies (force (and (rw.tracep x)
                        (rw.trace-okp x defs)
                        (rw.trace->iffp x)))
            (equal (rw.trace-okp (rw.not-trace x iffp) defs)
                   t))
   :hints(("Goal"
           :expand ((rw.trace-okp (rw.not-trace x iffp) defs))
           :in-theory (enable lemma-forcing-rw.trace-step-okp-of-rw.not-trace))))

 (defthmd lemma-forcing-rw.trace-step-env-okp-of-rw.not-trace
   (equal (rw.trace-step-env-okp (rw.not-trace x iffp) defs thms atbl)
          t)
   :hints(("Goal" :in-theory (enable rw.trace-step-env-okp))))

 (defthm forcing-rw.trace-env-okp-of-rw.not-trace
   (implies (force (and (rw.trace-env-okp x defs thms atbl)
                        (rw.trace-env-okp y defs thms atbl)
                        (rw.trace-env-okp z defs thms atbl)))
            (equal (rw.trace-env-okp (rw.not-trace x iffp) defs thms atbl)
                   t))
   :hints(("Goal"
           :expand ((rw.trace-env-okp (rw.not-trace x iffp) defs thms atbl))
           :in-theory (enable lemma-forcing-rw.trace-step-env-okp-of-rw.not-trace))))

 (defthm rw.collect-forced-goals-of-rw.not-trace
   (equal (rw.collect-forced-goals (rw.not-trace x iffp))
          (rw.collect-forced-goals x))
   :hints(("Goal" :in-theory (enable definition-of-rw.collect-forced-goals)))))




(defund rw.negative-if-trace (x iffp hypbox)
  (declare (xargs :guard (and (logic.termp x)
                              (booleanp iffp)
                              (rw.hypboxp hypbox))))
  (rw.trace 'negative-if
            hypbox
            (logic.function 'if (list x ''nil ''t))
            (logic.function 'not (list x))
            iffp
            nil
            nil))

(encapsulate
 ()
 (local (in-theory (enable rw.negative-if-trace)))

 (defthm rw.trace->method-of-rw.negative-if-trace
   (equal (rw.trace->method (rw.negative-if-trace x iffp hypbox))
          'negative-if))

 (defthm rw.trace->hypbox-of-rw.negative-if-trace
   (equal (rw.trace->hypbox (rw.negative-if-trace x iffp hypbox))
          hypbox)
   :hints(("Goal" :in-theory (disable (:executable-counterpart ACL2::force)))))

 (defthm rw.trace->lhs-of-rw.negative-if-trace
   (equal (rw.trace->lhs (rw.negative-if-trace x iffp hypbox))
          (logic.function 'if (list x ''nil ''t)))
   :hints(("Goal" :in-theory (disable (:executable-counterpart ACL2::force)))))

 (defthm rw.trace->rhs-of-rw.negative-if-trace
   (equal (rw.trace->rhs (rw.negative-if-trace x iffp hypbox))
          (logic.function 'not (list x)))
   :hints(("Goal" :in-theory (disable (:executable-counterpart ACL2::force)))))

 (defthm rw.trace->iffp-of-rw.negative-if-trace
   (equal (rw.trace->iffp (rw.negative-if-trace x iffp hypbox))
          iffp)
   :hints(("Goal" :in-theory (disable (:executable-counterpart ACL2::force)))))

 (defthm rw.trace->subtraces-of-rw.negative-if-trace
   (equal (rw.trace->subtraces (rw.negative-if-trace x iffp hypbox))
          nil)
   :hints(("Goal" :in-theory (disable (:executable-counterpart ACL2::force)))))

 (defthm rw.trace->extras-of-rw.negative-if-trace
   (equal (rw.trace->extras (rw.negative-if-trace x iffp hypbox))
          nil)
   :hints(("Goal" :in-theory (disable (:executable-counterpart ACL2::force)))))

 (defthm forcing-rw.tracep-of-rw.negative-if-trace
   (implies (force (and (logic.termp x)
                        (booleanp iffp)
                        (rw.hypboxp hypbox)))
            (equal (rw.tracep (rw.negative-if-trace x iffp hypbox))
                   t)))

 (defthm forcing-rw.trace-atblp-of-rw.negative-if-trace
   (implies (force (and (logic.term-atblp x atbl)
                        (rw.hypbox-atblp hypbox atbl)
                        (equal (cdr (lookup 'not atbl)) 1)
                        (equal (cdr (lookup 'if atbl)) 3)))
            (equal (rw.trace-atblp (rw.negative-if-trace x iffp hypbox) atbl)
                   t))
   :hints(("Goal" :in-theory (disable (:executable-counterpart ACL2::force)))))

 (local (in-theory (disable rw.negative-if-trace)))

 (defthmd lemma-forcing-rw.negative-if-tracep-of-rw.negative-if-trace
   (equal (rw.negative-if-tracep (rw.negative-if-trace x iffp hypbox))
          t)
   :hints(("Goal" :in-theory (enable rw.negative-if-tracep))))

 (defthmd lemma-forcing-rw.trace-step-okp-of-rw.negative-if-trace
   (equal (rw.trace-step-okp (rw.negative-if-trace x iffp hypbox) defs)
          t)
   :hints(("Goal" :in-theory (enable rw.trace-step-okp
                                     lemma-forcing-rw.negative-if-tracep-of-rw.negative-if-trace))))

 (defthm forcing-rw.trace-okp-of-rw.negative-if-trace
   (equal (rw.trace-okp (rw.negative-if-trace x iffp hypbox) defs)
          t)
   :hints(("Goal"
           :expand ((rw.trace-okp (rw.negative-if-trace x iffp hypbox) defs))
           :in-theory (enable lemma-forcing-rw.trace-step-okp-of-rw.negative-if-trace))))

 (defthmd lemma-forcing-rw.trace-step-env-okp-of-rw.negative-if-trace
   (equal (rw.trace-step-env-okp (rw.negative-if-trace x iffp hypbox) defs thms atbl)
          t)
   :hints(("Goal" :in-theory (enable rw.trace-step-env-okp))))

 (defthm forcing-rw.trace-env-okp-of-rw.negative-if-trace
   (equal (rw.trace-env-okp (rw.negative-if-trace x iffp hypbox) defs thms atbl)
          t)
   :hints(("Goal"
           :expand ((rw.trace-env-okp (rw.negative-if-trace x iffp hypbox) defs thms atbl))
           :in-theory (enable lemma-forcing-rw.trace-step-env-okp-of-rw.negative-if-trace))))

 (defthm rw.collect-forced-goals-of-rw.negative-if-trace
   (equal (rw.collect-forced-goals (rw.negative-if-trace x iffp hypbox))
          nil)
   :hints(("Goal" :in-theory (enable definition-of-rw.collect-forced-goals)))))




(defsection rw.maybe-extend-trace

  ;; Wrapper to avoid introducing ifs when extending traces.

  (defund rw.maybe-extend-trace (original extension)
    (declare (xargs :guard (and (rw.tracep original)
                                (or (not extension)
                                    (and (rw.tracep extension)
                                         (equal (rw.trace->iffp original)
                                                (rw.trace->iffp extension))
                                         (equal (rw.trace->hypbox original)
                                                (rw.trace->hypbox extension))
                                         (equal (rw.trace->rhs original)
                                                (rw.trace->lhs extension)))))))
    (if extension
        (rw.transitivity-trace original extension)
      original))

  (defthm forcing-rw.tracep-of-rw.maybe-extend-trace
    (implies (force (and (rw.tracep original)
                         (or (not extension)
                             (rw.tracep extension))))
             (equal (rw.tracep (rw.maybe-extend-trace original extension))
                    t))
    :hints(("Goal" :in-theory (enable rw.maybe-extend-trace))))

  (defthm forcing-rw.trace-okp-of-rw.maybe-extend-trace
    (implies (force (and (rw.tracep original)
                         (rw.trace-okp original defs)
                         (or (not extension)
                             (and (rw.tracep extension)
                                  (rw.trace-okp extension defs)
                                  (equal (rw.trace->iffp original)
                                         (rw.trace->iffp extension))
                                  (equal (rw.trace->hypbox original)
                                         (rw.trace->hypbox extension))
                                  (equal (rw.trace->rhs original)
                                         (rw.trace->lhs extension))))))
             (equal (rw.trace-okp (rw.maybe-extend-trace original extension) defs)
                    t))
    :hints(("Goal" :in-theory (enable rw.maybe-extend-trace))))

  (defthm forcing-rw.trace-atblp-of-rw.maybe-extend-trace
    (implies (force (and (rw.tracep original)
                         (rw.trace-atblp original atbl)
                         (or (not extension)
                             (and (rw.tracep extension)
                                  (rw.trace-atblp extension atbl)))))
             (equal (rw.trace-atblp (rw.maybe-extend-trace original extension) atbl)
                    t))
    :hints(("Goal" :in-theory (enable rw.maybe-extend-trace))))

  (defthm forcing-rw.trace-env-okp-of-rw.maybe-extend-trace
    (implies (force (and (rw.tracep original)
                         (rw.trace-env-okp original defs thms atbl)
                         (or (not extension)
                             (and (rw.tracep extension)
                                  (rw.trace-env-okp extension defs thms atbl)))))
             (equal (rw.trace-env-okp (rw.maybe-extend-trace original extension) defs thms atbl)
                    t))
    :hints(("Goal" :in-theory (enable rw.maybe-extend-trace))))

  (defthm forcing-rw.trace->iffp-of-rw.maybe-extend-trace
    (implies (force (and (rw.tracep original)
                         (or (not extension)
                             (rw.tracep extension))))
             (equal (rw.trace->iffp (rw.maybe-extend-trace original extension))
                    (rw.trace->iffp original)))
    :hints(("Goal" :in-theory (enable rw.maybe-extend-trace))))

  (defthm forcing-rw.trace->assms-of-rw.maybe-extend-trace
    (implies (force (and (rw.tracep original)
                         (or (not extension)
                             (rw.tracep extension))))
             (equal (rw.trace->hypbox (rw.maybe-extend-trace original extension))
                    (rw.trace->hypbox original)))
    :hints(("Goal" :in-theory (enable rw.maybe-extend-trace))))

  (defthm forcing-rw.trace->lhs-of-rw.maybe-extend-trace
    (implies (force (and (rw.tracep original)
                         (or (not extension)
                             (rw.tracep extension))))
             (equal (rw.trace->lhs (rw.maybe-extend-trace original extension))
                    (rw.trace->lhs original)))
    :hints(("Goal" :in-theory (enable rw.maybe-extend-trace)))))