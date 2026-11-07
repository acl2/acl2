;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (August 2nd 2016)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;
(in-package "SMT")
(include-book "std/util/bstar" :dir :system)
(include-book "std/testing/eval" :dir :system)
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
)
