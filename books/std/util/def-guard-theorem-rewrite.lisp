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
(include-book "std/system/fresh-logical-name-with-dollars-suffix" :dir :system)
(include-book "std/system/untranslate-dollar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/defmacro-plus" :dir :system)
(include-book "tools/er-soft-logic" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

(local (include-book "kestrel/utilities/read-acl2-oracle" :dir :system))
(local (include-book "std/system/all-vars" :dir :system))
(local (include-book "std/system/w" :dir :system))
(local (include-book "std/typed-lists/pseudo-term-listp" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ def-guard-theorem-rewrite-implementation
  :parents (def-guard-theorem-rewrite)
  :short "Implementation of @(tsee def-guard-theorem-rewrite)."
  :long
  (xdoc::topstring
   (xdoc::p
    "The implementation functions are in logic mode and guard-verified.
     Calls of program-mode system utilities are made via
     @(tsee in-logic-mode) or @(tsee untranslate$).
     Results used as terms are checked before further processing.")
   (xdoc::p
    "The theorem is proved in an @(tsee encapsulate)
     with a fresh local tagging function and a local auxiliary theorem.
     The tagging function @('(tag-fn tag x)') returns @('x').
     The auxiliary theorem replaces each variable @('v')
     by @('(tag-fn \'v v)')
     and is proved by a @(':by') hint
     with the corresponding variable instance of the guard theorem.
     The distinct quoted tags prevent subsumption from
     trying to match different variables,
     which can otherwise make proofs with many similar guard hypotheses slow.")
   (xdoc::p
    "A second @(':by') hint proves the public theorem
     by a functional instance of the auxiliary theorem,
     replacing the tagging function by @('(lambda (tag x) x)').
     Its defining constraint becomes @('(equal x x)').
     Thus the original guard theorem is used once,
     and neither the tags nor the local helpers appear in the public rules.
     Clause conversion still performs subsumption/replacement,
     so tagging does not introduce extra branch hypotheses
     into the rewrite rules."))
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
  :returns (mv erp
               (terms pseudo-term-listp)
               (new-state state-p1
                          :hyp (state-p1 state)
                          :hints (("Goal" :in-theory (enable error1-logic)))))
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

(define guard-theorem-rewrite-term (fn simplify state)
  :returns (mv erp
               (term pseudo-termp)
               (new-state state-p1
                          :hyp (state-p1 state)
                          :hints (("Goal" :in-theory (enable error1-logic)))))
  :short "Obtain the guard theorem and remove its guard holders."
  :long
  (xdoc::topstring
   (xdoc::p
    "@('fn') must name a guard-verified function.
     @('simplify') must be @(':limited') or @('nil'),
     with the meaning described in @(tsee def-guard-theorem-rewrite).")
   (xdoc::p
    "We call @('remove-guard-holders') mainly to match
     the fact that the @(':by') hint does the same;
     this is the hint we use to prove the generated auxiliary theorem."))
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
                       "Internal error: malformed guard theorem ~x0." term)))
    (value term)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define guard-theorem-rewrite-formula ((term pseudo-termp) state)
  :returns (mv erp
               (formula pseudo-termp)
               (new-state state-p1
                          :hyp (state-p1 state)
                          :hints (("Goal" :in-theory (enable error1-logic)))))
  :short "Extract the rewrite-rule formula from a guard theorem."
  :long
  (xdoc::topstring
   (xdoc::p
    "We call @('expand-some-non-rec-fns')
     to turn @(tsee implies) calls into @(tsee if) calls,
     because @('clausify') operates on @(tsee if) structures.")
   (xdoc::p
    "We always perform the subsumption/replacement step of @('clausify'),
     independently of @(tsee case-split-limitations).
     In particular, this can remove unnecessary branch hypotheses
     from the resulting rewrite rules.
     The generated @(':by') hints use the same unlimited setting
     so that they see matching clauses,
     while preserving the world's case-splitting limit."))
  (b* ((wrld (w state))
       ((mv erp clauses state)
        (in-logic-mode
         (clausify (expand-some-non-rec-fns '(implies) term wrld)
                   nil
                   t ; expand inside LETs (i.e. LAMBDAs)
                   nil) ; always perform subsumption/replacement
         state
         '(term wrld)))
       ((when erp) (mv erp nil state))
       ((unless (true-listp clauses))
        (er-soft-logic 'def-guard-theorem-rewrite
                       "Internal error: malformed list of clauses ~x0."
                       clauses))
       ((mv erp terms state) (guard-theorem-rewrite-filter clauses state))
       ((when erp) (mv erp nil state)))
    (value (conjoin terms))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define guard-theorem-rewrite (fn simplify state)
  :returns (mv erp (formula t) state)
  :short "Inspect the rewrite-rule formula for a function's guard theorem."
  :long
  (xdoc::topstring-p
   "This returns an error triple whose value, on success, is
    the untranslated formula used by @(tsee def-guard-theorem-rewrite).
    It does not submit an event.
    @('fn') must name a guard-verified function.
    @('simplify') must be @(':limited') or @('nil'),
    with the meaning described in @(tsee def-guard-theorem-rewrite).")
  (b* (((mv erp term state) (guard-theorem-rewrite-term fn simplify state))
       ((when erp) (mv erp nil state))
       ((mv erp formula state) (guard-theorem-rewrite-formula term state))
       ((when erp) (mv erp nil state)))
    (value (untranslate$ formula t state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define guard-theorem-rewrite-substitution ((vars symbol-listp)
                                            (tag-fn symbolp))
  :returns (subst alistp)
  :short "Map each variable to a call of the tagging function."
  :long
  (xdoc::topstring-p
   "Each variable @('v') is replaced by @('(tag-fn \'v v)').
    The quoted variable names make the resulting terms
    syntactically distinct during subsumption matching.
    We tag all the free variables of the original guard theorem,
    including variables in clauses omitted from the rewrite formula
    and variables of other functions in a mutually recursive clique.")
  (if (endp vars)
      nil
    (cons (cons (car vars) `(,tag-fn ',(car vars) ,(car vars)))
          (guard-theorem-rewrite-substitution (cdr vars) tag-fn))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define def-guard-theorem-rewrite-fn (name fn simplify state)
  :returns (mv erp (event t) state)
  :short "Generate the theorem event."
  :long
  (xdoc::topstring
   (xdoc::p
    "A direct @(':by') proof can be slow
     when many guard hypotheses have the same predicate
     applied to different variables.
     Subsumption may try many variable substitutions
     before discovering that the conclusions of two clauses do not match.")
   (xdoc::p
    "We introduce a fresh local function @('(tag-fn tag x)')
     that returns @('x').
     We prove a local auxiliary theorem
     by a variable instance of the original guard theorem,
     replacing every @('v') by @('(tag-fn \'v v)').
     Subsumption does not unfold the tagging function:
     the distinct quoted tags prevent it from matching different variables.")
   (xdoc::p
    "The public theorem follows by
     a functional instance of the auxiliary theorem,
     replacing @('tag-fn') by @('(lambda (tag x) x)').
     The constraint from the tagging function's definition
     reduces to @('(equal x x)').
     Both proofs use @(':by'), and the original guard theorem is used once.
     The helper function and auxiliary theorem
     are local to an @(tsee encapsulate),
     and the public rewrite formula is unchanged.
     A trivial rewrite formula needs no tagging."))
  (b* (((unless (symbolp name))
        (er-soft-logic 'def-guard-theorem-rewrite
                       "The theorem name must be a symbol, ~
                        but received ~x0."
                       name))
       (wrld (w state))
       ((mv erp case-limit state)
        (in-logic-mode (case-limit wrld) state '(wrld)))
       ((when erp) (mv erp nil state))
       ((mv erp term state) (guard-theorem-rewrite-term fn simplify state))
       ((when erp) (mv erp nil state))
       ((mv erp formula state) (guard-theorem-rewrite-formula term state))
       ((when erp) (mv erp nil state))
       ((when (equal formula *t*))
        (value
         `(defthm ,name
            t
            :rule-classes nil
            :hints (("Goal"
                     :by (:guard-theorem ,fn ,simplify)
                     :case-split-limitations (nil ,case-limit))))))
       (wrld (w state))
       ((mv tag-fn names-to-avoid)
        (fresh-logical-name-with-$s-suffix
         (add-suffix-to-fn name "$TAG") 'function (list name) wrld))
       ((mv aux-name &)
        (fresh-logical-name-with-$s-suffix
         (add-suffix name "$AUX") nil names-to-avoid wrld))
       (subst (guard-theorem-rewrite-substitution (all-vars term) tag-fn))
       ((mv erp tagged-formula state)
        (in-logic-mode (sublis-var subst formula) state '(subst formula)))
       ((when erp) (mv erp nil state))
       ((unless (pseudo-termp tagged-formula))
        (er-soft-logic 'def-guard-theorem-rewrite
                       "Internal error: malformed tagged formula ~x0."
                       tagged-formula))
       (bindings (pairlis$ (strip-cars subst)
                           (pairlis$ (strip-cdrs subst) nil))))
    (value
     `(encapsulate
        ()
        (local
         (defun ,tag-fn (tag x)
           (declare (xargs :mode :logic :guard t :verify-guards t)
                    (ignore tag))
           x))
        (local
         (defthm ,aux-name
           ,(untranslate$ tagged-formula t state)
           :rule-classes nil
           :hints (("Goal"
                    :by (:instance (:guard-theorem ,fn ,simplify) ,@bindings)
                    :case-split-limitations (nil ,case-limit)))))
        (defthmd ,name
          ,(untranslate$ formula t state)
          :rule-classes :rewrite
          :hints (("Goal"
                   :by (:functional-instance
                        ,aux-name (,tag-fn (lambda (tag x) x)))
                   :case-split-limitations (nil ,case-limit))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection def-guard-theorem-rewrite-definition
  :short "Definition of the @(tsee def-guard-theorem-rewrite) macro."
  (defmacro def-guard-theorem-rewrite (name fn &key (simplify ':limited))
    `(make-event
      (def-guard-theorem-rewrite-fn ',name ',fn ',simplify state))))
