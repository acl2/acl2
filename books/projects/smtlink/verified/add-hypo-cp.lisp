;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (July 6th 2018)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "SMT")
(include-book "std/util/bstar" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "basics")
(include-book "hint-please")
(include-book "hint-interface")
(include-book "computed-hints")
(include-book "evaluator")

(defsection add-hypo-cp
  :parents (verified)
  :short "Verified clause-processor for adding user hypotheses"

  ;; -----------------------------------------------------------------
  ;; Defines the clause-processor for adding hypotheses
  ;; H1 and H2 ... and Hn => G
  ;; H1 or G
  ;; H2 or G
  ;; ...
  ;; Hn or G

  (define add-hypo-subgoals ((hinted-hypos hint-pair-list-p)
                             (G pseudo-termp))
    :returns (mv (list-of-H-thm pseudo-term-list-listp)
                 (list-of-not-Hs pseudo-term-listp))
    :measure (len hinted-hypos)
    (b* ((hinted-hypos (hint-pair-list-fix hinted-hypos))
         (G (pseudo-term-fix G))
         ((unless (consp hinted-hypos)) (mv nil nil))
         ((cons first-hinted-H rest-hinted-Hs) hinted-hypos)
         (H (hint-pair->thm first-hinted-H))
         (H-hint (hint-pair->hints first-hinted-H))
         (merged-in-theory (treat-in-theory-hint '(hint-please) H-hint))
         (first-H-thm `((hint-please ',merged-in-theory) ,H ,G))
         (first-not-H-clause `(not ,H))
         ((mv rest-H-thms rest-not-H-clauses)
          (add-hypo-subgoals rest-hinted-Hs G)))
      (mv (cons first-H-thm rest-H-thms)
          (cons first-not-H-clause rest-not-H-clauses)))
    ///
    (defthm add-hypo-subgoals-correctness
      (implies (and (pseudo-termp G)
                    (alistp b)
                    (hint-pair-list-p hinted-hypos)
                    (ev-smtcp
                     (disjoin
                      (mv-nth 1 (add-hypo-subgoals hinted-hypos G)))
                     b)
                    (ev-smtcp
                     (conjoin-clauses
                      (mv-nth 0 (add-hypo-subgoals hinted-hypos G)))
                     b))
               (ev-smtcp G b))
      :hints (("Goal"
               :induct (add-hypo-subgoals hinted-hypos G)))))

  (local
   (defthm crock0
     (implies (and (pseudo-term-listp x) (pseudo-term-listp cl))
              (pseudo-term-listp (append x (list (disjoin cl)))))))

  (local
   (defthm crock1
     (implies (pseudo-term-listp x)
              (pseudo-term-listp (append x '('nil))))))

  (define add-hypo-cp ((cl pseudo-term-listp)
                       (smtlink-hint t))
    :returns (subgoal-lst pseudo-term-list-listp)
    (b* (((unless (pseudo-term-listp cl)) nil)
         ((unless (smtlink-hint-p smtlink-hint))
          (list cl))
         ((smtlink-hint h) smtlink-hint)
         (hinted-hypos h.hypotheses)
         (next-cp (cdr (assoc-equal 'add-hypo *SMT-architecture*)))
         ((if (null next-cp)) (list cl))
         ;; this one clause-processor has state, it's a bit ugly
         (the-hint
          `(:clause-processor (,next-cp clause ',smtlink-hint state)))
         (G (disjoin cl))
         ((mv aux-hypo-clauses list-of-not-Hs)
          (add-hypo-subgoals hinted-hypos G))
         (cl0 `((hint-please ',the-hint) ,@list-of-not-Hs ,G)))
      `(,cl0 ,@aux-hypo-clauses)))

  ;; proving correctness of the clause processor
  (local (in-theory (enable add-hypo-cp)))

  (defthm correctness-of-add-hypos
    (implies (and (pseudo-term-listp cl)
                  (alistp b)
                  (ev-smtcp
                   (conjoin-clauses (add-hypo-cp cl smtlink-hint))
                   b))
             (ev-smtcp (disjoin cl) b))
    :hints (("Goal"
             :in-theory (disable add-hypo-subgoals-correctness
                                 ev-smtcp-of-disjoin)
             :use ((:instance add-hypo-subgoals-correctness
                              (g (disjoin cl))
                              (hinted-hypos (smtlink-hint->hypotheses smtlink-hint))
                              (b b)))))
    :rule-classes :clause-processor)
  )
