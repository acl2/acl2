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
(include-book "hint-please")
(include-book "hint-interface")
(include-book "extractor")
(include-book "type-hyp")
(include-book "evaluator")

(defsection type-extract-cp
  :parents (verified)
  :short "Verified clause-processor for extracting type declarations"

  ;; -----------------------------------------------------------------
  ;; Defines the clause-processor for extracting type declarations
  ;; (type-hyp (list T1 ... Tn)) => G/type == Q3
  ;; Q3 => G

  (define type-extract-cp ((cl pseudo-term-listp)
                           (smtlink-hint t))
    :returns (subgoal-lst pseudo-term-list-listp)
    (b* (((unless (pseudo-term-listp cl)) nil)
         ((unless (smtlink-hint-p smtlink-hint))
          (list cl))
         ((smtlink-hint h) smtlink-hint)
         (G (disjoin cl))
         ((mv type-decl-term G/type)
          (SMT-extract G h.types-info))
         (next-cp (cdr (assoc-equal 'type-extract *SMT-architecture*)))
         ((if (null next-cp)) (list cl))
         (the-hint
          `(:clause-processor (,next-cp clause ',h state)))
         (cl0 `((hint-please ',the-hint)
                (not (type-hyp (hide ',type-decl-term) ':type))
                ,G/type))
         (cl1 `((hint-please '(:in-theory (enable hint-please type-hyp)
                                          :expand ((:free (x) (hide x)))))
                (not (implies (type-hyp (hide ',type-decl-term) ':type)
                              ,G/type))
                ,G)))
      `(,cl0 ,cl1)))

  ;; proving correctness of the type-extract clause processor
  (local (in-theory (enable type-extract-cp type-hyp hint-please hide)))

  (defthm correctness-of-type-extract-cp
    (implies (and (pseudo-term-listp cl)
                  (alistp b)
                  (ev-smtcp
                   (conjoin-clauses (type-extract-cp cl smtlink-hint))
                   b))
             (ev-smtcp (disjoin cl) b))
    :rule-classes :clause-processor)
  )
