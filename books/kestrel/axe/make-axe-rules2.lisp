(in-package "ACL2")

(include-book "make-axe-rules")

;deprecate?  Used in the lifter.
(defund make-axe-rule-safe (lhs rhs rule-symbol hyps extra-hyps print wrld)
  (declare (xargs :guard (plist-worldp wrld)))
  (if (and (pseudo-termp lhs)
           (consp lhs)
           (symbolp (ffn-symb lhs))
           (not (eq 'quote (ffn-symb lhs)))
           (lambda-free-termp lhs)
           (pseudo-termp rhs)
           (pseudo-term-listp hyps)
           (axe-rule-hyp-listp extra-hyps)
           (all-axe-syntaxp-hypsp extra-hyps)
           (symbolp rule-symbol))
      (mv-let (erp rule)
        (make-axe-rule lhs rhs rule-symbol hyps extra-hyps print wrld)
        (if erp
            (er hard? 'make-axe-rule-safe "Error making axe rule. LHS: ~x0. RHS: ~x1. HYPS: ~x2." lhs rhs hyps)
          rule))
    (er hard? 'make-axe-rule-safe "Bad input to make-axe-rule-safe (perhaps things are not pseudo-terms). LHS: ~x0. RHS: ~x1. HYPS: ~x2." lhs rhs hyps)))

;;Returns (mv lhs rhs) or throws an error if it's not a theorem with a single conclusion conjunct and no hyps ("simple" means no hyps here)
;; Used in axe.lisp.
(defund lhs-and-rhs-of-simple-rule (rule-name wrld)
  (declare (xargs :guard (and (symbolp rule-name)
                              (plist-worldp wrld))))
  (b* ((body (defthm-body rule-name wrld))
       ((when (and (consp body) (eq 'implies (ffn-symb body))))
        (mv (er hard? 'lhs-and-rhs-of-simple-rule "Rules with hyps are not yet supported.") nil))
       (known-booleans (known-booleans wrld))
       ((mv erp lhs rhs) (lhs-and-rhs-of-conc body rule-name known-booleans)) ;may throw an error
       ((when erp) (mv (er hard? 'lhs-and-rhs-of-simple-rule "Can't extract an LHS nd RHS from ~x0." rule-name) nil)))
    (mv lhs rhs)))
