; Standard Utilities Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/system/acceptable-rewrite-rule-p" :dir :system)
(include-book "std/system/conjoin" :dir :system)
(include-book "std/system/dumb-negate-lit" :dir :system)
(include-book "std/system/untranslate-dollar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/defmacro-plus" :dir :system)
(include-book "tools/er-soft-logic" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

(local (include-book "std/system/w" :dir :system))
(local (include-book "std/typed-lists/pseudo-term-listp" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ def-guard-theorem-rewrite-implementation
  :parents (def-guard-theorem-rewrite)
  :short "Implementation of @(tsee def-guard-theorem-rewrite)."
  :long
  (xdoc::topstring-p
   "The implementation functions are in logic mode and guard-verified.
    Calls of program-mode system utilities are made via
    @(tsee in-logic-mode) or @(tsee untranslate$).
    Results used as terms are checked before further processing.")
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define guard-theorem-rewrite-clause ((clause pseudo-term-listp))
  :returns (mv (hyps pseudo-term-listp :hyp :guard)
               (concl pseudo-termp :hyp :guard))
  :short "Extract the hypotheses and conclusion of a guard theorem clause."
  :long
  (xdoc::topstring-p
   "The last literal is the conclusion, which is left unchanged.
    The preceding literals are negated to form the hypotheses.
    An empty clause is treated as an unconditional @('nil').")
  (b* (((when (endp clause)) (mv nil *nil*))
       ((when (endp (cdr clause))) (mv nil (car clause)))
       ((mv hyps concl) (guard-theorem-rewrite-clause (cdr clause))))
    (mv (cons (dumb-negate-lit (car clause)) hyps) concl))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define guard-theorem-rewrite-filter ((clauses true-listp) state)
  :returns (mv erp (terms pseudo-term-listp) state)
  :short "Retain the implications that can be installed as rewrite rules."
  :long
  (xdoc::topstring-p
   "The input is a list of clauses from the guard theorem.
    We check each complete implication with @('acceptable-rewrite-rule-p'),
    which uses ACL2's own rewrite-rule admissibility check
    without printing rule warnings.
    We retain the original conclusion of each accepted implication.")
  (b* (((when (endp clauses)) (mv nil nil state))
       (clause (car clauses))
       ((unless (pseudo-term-listp clause))
        (er-soft-logic 'def-guard-theorem-rewrite
                       "Internal error: malformed clause ~x0." clause))
       ((mv hyps concl) (guard-theorem-rewrite-clause clause))
       (term `(implies ,(conjoin hyps) ,concl))
       (ens (ens state))
       (wrld (w state))
       ((mv erp acceptable state)
        (in-logic-mode (acceptable-rewrite-rule-p term ens wrld) state))
       ((when erp) (mv erp nil state))
       ((mv erp terms state)
        (guard-theorem-rewrite-filter (cdr clauses) state))
       ((when erp) (mv erp nil state)))
    (mv nil (if acceptable (cons term terms) terms) state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define guard-theorem-rewrite (fn simplify state)
  :returns (mv erp (formula t) state)
  :short "Inspect the rewrite-rule formula for a function's guard theorem."
  :long
  (xdoc::topstring
   (xdoc::p
    "This returns an error triple whose value, on success, is
     the untranslated formula used by @(tsee def-guard-theorem-rewrite).
     It does not submit an event.
     @('fn') must name a guard-verified function.
     @('simplify') must be @(':limited') or @('nil'),
     with the meaning described in @(tsee def-guard-theorem-rewrite).")
   (xdoc::p
    "We call @('remove-guard-holders') mainly to match
     the fact that the @(':by') hint does the same;
     this is the hint we use to prove the generated theorem."))
  (b* ((wrld (w state))
       ((unless (and (symbolp fn)
                     (function-symbolp fn wrld)
                     (eq (getpropc fn 'symbol-class nil wrld)
                         :common-lisp-compliant)))
        (er-soft-logic 'def-guard-theorem-rewrite
                       "Expected a guard-verified function symbol, ~
                        but received ~x0."
                       fn))
       ((unless (member-eq simplify '(:limited nil)))
        (er-soft-logic 'def-guard-theorem-rewrite
                       "The :SIMPLIFY option must be :LIMITED or NIL, ~
                        but received ~x0."
                       simplify))
       ((mv erp term state)
        (in-logic-mode
         (remove-guard-holders (guard-theorem fn simplify nil wrld state) wrld)
         state
         '(fn simplify wrld)))
       ((when erp) (mv erp nil state))
       ((unless (pseudo-termp term))
        (er-soft-logic 'def-guard-theorem-rewrite
                       "Internal error: malformed guard theorem ~x0." term))
       ((mv erp clauses state)
        (in-logic-mode
         (clausify (expand-some-non-rec-fns '(implies) term wrld)
                   nil
                   t
                   (car (case-split-limitations wrld)))
         state
         '(term wrld)))
       ((when erp) (mv erp nil state))
       ((unless (true-listp clauses))
        (er-soft-logic 'def-guard-theorem-rewrite
                       "Internal error: malformed list of clauses ~x0."
                       clauses))
       ((mv erp terms state) (guard-theorem-rewrite-filter clauses state))
       ((when erp) (mv erp nil state)))
    (value (untranslate$ (conjoin terms) t state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define def-guard-theorem-rewrite-fn (name fn simplify state)
  :returns (mv erp (event t) state)
  :short "Generate the theorem event."
  (b* (((unless (symbolp name))
        (er-soft-logic 'def-guard-theorem-rewrite
                       "The theorem name must be a symbol, ~
                        but received ~x0."
                       name))
       ((mv erp formula state) (guard-theorem-rewrite fn simplify state))
       ((when erp) (mv erp nil state)))
    (value
     `(,(if (eq formula t) 'defthm 'defthmd) ,name
        ,formula
        :rule-classes ,(if (eq formula t) nil :rewrite)
        :hints (("Goal" :by (:guard-theorem ,fn ,simplify)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection def-guard-theorem-rewrite-definition
  :short "Definition of the @(tsee def-guard-theorem-rewrite) macro."
  (defmacro def-guard-theorem-rewrite (name fn &key (simplify ':limited))
    `(make-event
      (def-guard-theorem-rewrite-fn ',name ',fn ',simplify state))))
