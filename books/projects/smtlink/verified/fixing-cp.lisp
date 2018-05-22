;; Copyright (C) 2015, University of British Columbia
;; Written (originally) by Yan Peng (3rd May, 2018)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2


(in-package "SMT")
(include-book "centaur/fty/top" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "clause-processors/join-thms" :dir :system)

(include-book "hint-interface")
(include-book "hint-please")
(include-book "fixing-clause")

(defevaluator ev-fixing-clause-processor ev-lst-fixing-clause-processor
  ((not x) (if x y z) (hint-please hint tag)))

(def-join-thms ev-fixing-clause-processor)

;; The fixing clause processor generates two subgoals:
;;
;; fixed(cl)
;; and
;; fixed(cl) => cl
;;
(define fixing-clause-processor ((cl pseudo-term-listp) (smtlink-hint t))
  :returns (subgoal-lst pseudo-term-list-listp)
  (b* (((unless (pseudo-term-listp cl)) nil)
       ((unless (smtlink-hint-p smtlink-hint))
        (list (remove-hint-please cl)))
       ((smtlink-hint h) smtlink-hint)
       (fixed-clause (hint-pair->thm h.fixed-clause))
       (fix-hint (hint-pair->hints h.fixed-clause))
       (smt-hint
        (if h.custom-p
            `(:clause-processor (SMT-trusted-cp-custom clause ',smtlink-hint state))
          `(:clause-processor (SMT-trusted-cp clause ',smtlink-hint state))))
       (smt-goal `((hint-please ',smt-hint 'smt-hint) ,fixed-clause))
       (acl2-goal `((hint-please ',fix-hint 'fixed-hint)
                    (not ,fixed-clause) ,(disjoin cl))))
    `(,smt-goal ,acl2-goal))
  ///
  (defthm fixing-clause-processor-corollary
      (implies (and (pseudo-term-listp cl)
                    (alistp b)
                    (smtlink-hint-p smtlink-hint)
                    (ev-fixing-clause-processor
                     (conjoin-clauses
                      (fixing-clause-processor cl smtlink-hint))
                     b))
               (ev-fixing-clause-processor (disjoin cl) b))
      :hints nil))

;; -----------------------------------------------------------------
;;       Define evaluators


(local (in-theory (enable fixing-clause-processor)))

(defthm correctness-of-remove-hint-please-for-ev-fixing-cp
  (implies (and (pseudo-term-listp cl)
                (alistp b))
           (iff (ev-fixing-clause-processor (disjoin (remove-hint-please cl)) b)
                (ev-fixing-clause-processor (disjoin cl) b)))
  :hints (("Goal"
           :in-theory (enable hint-please remove-hint-please) )))

(defthm correctness-of-fixing-clause-processor
  (implies (and (pseudo-term-listp cl)
                (alistp b)
                (ev-fixing-clause-processor
                 (conjoin-clauses (fixing-clause-processor cl smtlink-hint))
                 b))
           (ev-fixing-clause-processor (disjoin cl) b))
  :rule-classes :clause-processor
  :hints (("Goal"
           :in-theory (e/d () (fixing-clause-processor-corollary))
           :use ((:instance fixing-clause-processor-corollary
                            (cl cl)
                            (smtlink-hint smtlink-hint))))))

(defmacro smt-fixing-cp (clause hint)
  `(fixing-clause-processor clause
                            ;; fixed-clause
                            (fixing-clause (remove-hint-please ,clause) ,hint)))
