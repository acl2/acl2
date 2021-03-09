;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (December 30th 2019)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "SMT")
(include-book "std/util/bstar" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "centaur/fty/top" :dir :system)
(include-book "tools/defevaluator-fast" :dir :system)
(include-book "clause-processors/just-expand" :dir :system)
(include-book "clause-processors/meta-extract-user" :dir :system)
(include-book "ordinals/lexicographic-ordering-without-arithmetic" :dir :system)

(include-book "reorder-hypotheses")
(include-book "type-inference-bottomup")
(include-book "type-inference-topdown")

(set-state-ok t)

(define type-judge-fn ((cl pseudo-term-listp)
                       (smtlink-hint t)
                       state)
  :returns (subgoal-lst pseudo-term-list-listp)
  (b* (((unless (pseudo-term-listp cl)) nil)
       ((unless (smtlink-hint-p smtlink-hint))
        (list cl))
       ((smtlink-hint h) smtlink-hint)
       (goal (disjoin cl))
       (options (construct-type-options smtlink-hint))
       (names (acl2::simple-term-vars goal))
       (type-judgements (type-judgement goal ''t options names state))
       (typed-term (make-typed-term :term goal :path-cond ''t
                                    :judgements type-judgements))
       ;; This check is probably provable
       ((unless (good-typed-term-p typed-term options))
        (prog2$ (er hard? 'type-inference=>type-judge-fn
                    "Not a good-typed-term-p: ~q0" typed-term)
                (list cl)))
       (unified-typed-term (unify-type typed-term ''t options names state))
       (unified-judgements (typed-term->judgements unified-typed-term))
       (new-cl `((implies ,unified-judgements ,goal)))
       (next-cp (cdr (assoc-equal 'type-judge *SMT-architecture*)))
       ((if (null next-cp)) (list cl))
       (the-hint
        `(:clause-processor (,next-cp clause ',h state)))
       (hinted-goal `((hint-please ',the-hint) ,@new-cl)))
    (list hinted-goal)))

(define type-judge-cp ((cl pseudo-term-listp)
                       (hints t)
                       state)
  (b* ((new-clause (type-judge-fn cl hints state)))
    (value new-clause)))

(local (in-theory (enable type-judge-cp type-judge-fn)))

(defthm correctness-of-type-judge-cp
  (implies (and (ev-smtcp-meta-extract-global-facts)
                (pseudo-term-listp cl)
                (alistp a)
                (ev-smtcp
                 (conjoin-clauses
                  (acl2::clauses-result
                   (type-judge-cp cl hint state)))
                 a))
           (ev-smtcp (disjoin cl) a))
  :hints (("Goal"
           :in-theory (e/d (correct-typed-term)
                           (ev-smtcp-of-if-call
                            pseudo-termp
                            symbol-listp))
           :use ((:instance correctness-of-unify-type
                            (options (construct-type-options hint))
                            (names (acl2::simple-term-vars (disjoin cl)))
                            (expected ''t)
                            (tterm (typed-term
                                    (disjoin cl)
                                    ''t
                                    (type-judgement (disjoin cl)
                                                    ''t
                                                    (construct-type-options hint)
                                                    (acl2::simple-term-vars (disjoin cl))
                                                    state)))
                            (a a)))))
  :rule-classes :clause-processor)
