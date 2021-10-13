;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (Oct 7th 2021)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "SMT")
(include-book "std/util/bstar" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "centaur/fty/top" :dir :system)

(include-book "reorder-options")
(include-book "extractor")

(define type-extract-cp ((cl pseudo-term-listp)
                         (smtlink-hint t))
  :returns (subgoal-lst pseudo-term-list-listp)
  (b* ((cl (pseudo-term-list-fix cl))
       ((unless (smtlink-hint-p smtlink-hint)) (list cl))
       (goal (disjoin cl))
       (- (cw "goal: ~q0" goal))
       (options (construct-reorder-options smtlink-hint))
       ((mv hypo-lst new-term) (extractor goal options))
       (- (cw "hypo-lst: ~q0" hypo-lst))
       (- (cw "new-term: ~q0" new-term))
       ((mv okp & term-body)
        (case-match new-term
          (('if judges term-body ''t)
           (mv t judges term-body))
          (('implies judges term-body)
           (mv t judges term-body))
          (& (mv nil nil nil))))
       ((unless okp)
        (prog2$ (er hard? 'type-extract=>type-extract-fn
                    "The input term is of wrong shape.~%")
                (list cl)))
       (type-hyp-list `(type-hyp ,(conjoin hypo-lst) ':type))
       (new-goal `(if ,type-hyp-list ,term-body 't))
       (- (cw "new-goal: ~q0" new-goal))
       (next-cp (cdr (assoc-equal 'type-extract *SMT-architecture*)))
       ((if (null next-cp)) (list cl))
       (the-hint
        `(:clause-processor (,next-cp clause ',smtlink-hint state)))
       (hinted-goal `((hint-please ',the-hint) ,new-goal)))
    (list hinted-goal)))

(skip-proofs
(defthm correctness-of-type-extract-cp
  (implies (and (ev-smtcp-meta-extract-global-facts)
                (pseudo-term-listp cl)
                (alistp a)
                (ev-smtcp
                 (conjoin-clauses
                  (type-extract-cp cl hint))
                 a))
           (ev-smtcp (disjoin cl) a))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (type-extract-cp) (correctness-of-extractor))
           :use ((:instance correctness-of-extractor
                            (term (disjoin cl))
                            (type-info (construct-reorder-options hint))))))
  :rule-classes :clause-processor)
)
