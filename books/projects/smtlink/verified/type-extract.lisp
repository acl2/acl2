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
       (options (construct-reorder-options smtlink-hint))
       ((mv hypo-lst new-term) (extractor goal options))
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
       (next-cp (cdr (assoc-equal 'type-extract *SMT-architecture*)))
       ((if (null next-cp)) (list cl))
       (the-hint
        `(:clause-processor (,next-cp clause ',smtlink-hint state)))
       (hinted-goal `((hint-please ',the-hint) ,new-goal)))
    (list hinted-goal)))

(defthm correctness-of-type-extract-cp-lemma
  (implies (and (pseudo-termp term)
                (symbol-symbol-alistp type-info)
                (alistp a))
           (b* (((mv hypo-lst new-term) (extractor term type-info)))
             (iff (ev-smtcp `(if (type-hyp ,(conjoin hypo-lst) ':type) ,new-term 't) a)
                  (ev-smtcp term a))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (type-hyp) (correctness-of-extractor))
           :use ((:instance correctness-of-extractor)))))

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
           :in-theory (e/d (type-extract-cp) (correctness-of-type-extract-cp-lemma))
           :use ((:instance correctness-of-type-extract-cp-lemma
                            (term (disjoin cl))
                            (type-info (construct-reorder-options hint))))))
  :rule-classes :clause-processor)
