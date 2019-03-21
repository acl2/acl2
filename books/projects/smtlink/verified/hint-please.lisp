;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (August 2nd 2016)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;
(in-package "SMT")
(include-book "std/util/bstar" :dir :system)
(include-book "misc/eval" :dir :system)
(include-book "clause-processors/join-thms" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)

(include-book "hint-interface")

(defsection SMT-hint-please
  :parents (verified)
  :short "The function hint-please in SMT is for passing hints to subgoals
  using the clause-processor and computed-hint mechanism."

  ;; -----------------------------------------------------------------
  ;;       Define the identity function.
  ;;

  ;; hint-please for SMT solver
  (define hint-please ((hint listp))
    (declare (ignore hint)
             (xargs :guard t))
    nil)

  (defthm hint-please-forward
    (implies (hint-please hint)
             nil)
    :rule-classes :forward-chaining)

  (in-theory (disable (:d hint-please)
                      (:e hint-please)
                      (:t hint-please)))

  ;; Function for removing hint-please from the clause.
  (define remove-hint-please ((cl pseudo-term-listp))
    :returns (cl-removed pseudo-term-list-listp
                         :hints (("Goal"
                                  :in-theory (enable pseudo-term-listp
                                                     pseudo-term-list-fix))))
    (b* ((cl (pseudo-term-list-fix cl))
         ((unless (consp cl)) (list cl)))
      (case-match cl
        ((('hint-please &) . term) (list term))
        (& (list cl)))))

  (defevaluator ev-remove-hint-please ev-lst-remove-hint-please
    ((not x) (if x y z) (hint-please hint)))

  (def-join-thms ev-remove-hint-please)

  (local (in-theory (enable remove-hint-please)))

  (defthm correctness-of-remove-hint-please
    (implies (and (pseudo-term-listp cl)
                  (alistp b)
                  (ev-remove-hint-please
                   (conjoin-clauses (remove-hint-please cl))
                   b))
             (ev-remove-hint-please (disjoin cl) b))
    :hints (("Goal"
             :in-theory (enable hint-please remove-hint-please)))
    :rule-classes :clause-processor)
)
