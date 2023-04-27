; C Library
;
; Copyright (C) 2023 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2023 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "generation-contexts")
(include-book "types-to-recognizers")
(include-book "variable-tables")

(include-book "kestrel/event-macros/event-generation" :dir :system)
(include-book "kestrel/std/system/formals-plus" :dir :system)
(include-book "kestrel/std/system/fresh-logical-name-with-dollars-suffix" :dir :system)
(include-book "kestrel/std/system/untranslate-dollar" :dir :system)

(local (include-book "kestrel/std/system/good-atom-listp" :dir :system))
(local (include-book "kestrel/std/system/w" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atc-theorem-generation
  :parents (atc-event-and-code-generation)
  :short "Facilities for generating theorems in ATC."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are for the new approach to proof generation
     in which we generate modular, compositional theorems."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-expr-pure-correct-thm ((fn symbolp)
                                       (fn-guard symbolp)
                                       (context atc-contextp)
                                       (expr exprp)
                                       (type typep)
                                       (term pseudo-termp)
                                       (objdes pseudo-termp)
                                       (compst-var symbolp)
                                       (hints true-listp)
                                       (instructions true-listp)
                                       (thm-index posp)
                                       (names-to-avoid symbol-listp)
                                       state)
  :returns (mv (thm-event pseudo-event-formp)
               (thm-name symbolp)
               (thm-index posp :hyp (posp thm-index))
               (names-to-avoid symbol-listp :hyp (symbol-listp names-to-avoid)))
  :short "Generate a correctness theorem for a pure expression execution."
  :long
  (xdoc::topstring
   (xdoc::p
    "The function @('fn') that the expression is part of is passed as input.")
   (xdoc::p
    "As theorem name, we just combine
     @('fn') with @('correct') and with the theorem index.
     The name just needs to be unique locally to the call to ATC,
     so we expect that generally no @('$') signs will need to be added
     by @(tsee fresh-logical-name-with-$s-suffix).")
   (xdoc::p
    "The theorem says that
     @(tsee exec-expr-pure) called on the quoted expression
     is the same as the term;
     it also says that the term has the expression's type.
     The term is untranslated, to make it more readable,
     in particular to eliminate quotes before numbers.
     Term, expression, and type are passed as inputs.
     The theorem is contextualized,
     and further conditioned by the satisfaction of the guard of @('fn').")
   (xdoc::p
    "The hints to prove the theorem are passed as input,
     because they depend on the specifics of the expression."))
  (b* ((wrld (w state))
       (name (pack fn '-correct- thm-index))
       ((mv name names-to-avoid) (fresh-logical-name-with-$s-suffix
                                  name nil names-to-avoid wrld))
       (type-pred (type-to-recognizer type wrld))
       (uterm (untranslate$ term nil state))
       (uobjdes (untranslate$ objdes nil state))
       (formula1 `(equal (exec-expr-pure ',expr ,compst-var)
                         (expr-value ,uterm ,uobjdes)))
       (formula1 (atc-contextualize formula1 context fn fn-guard
                                    compst-var nil nil wrld))
       (formula2 `(,type-pred ,uterm))
       (formula2 (atc-contextualize formula2 context fn fn-guard
                                    nil nil nil wrld))
       (formula `(and ,formula1 ,formula2))
       ((mv event &) (evmac-generate-defthm name
                                            :formula formula
                                            :hints hints
                                            :instructions instructions
                                            :enable nil)))
    (mv event name (1+ thm-index) names-to-avoid)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-expr-bool-correct-thm ((fn symbolp)
                                       (fn-guard symbolp)
                                       (context atc-contextp)
                                       (expr exprp)
                                       (type typep)
                                       (aterm pseudo-termp)
                                       (cterm pseudo-termp)
                                       (objdes pseudo-termp)
                                       (compst-var symbolp)
                                       (hints true-listp)
                                       (instructions true-listp)
                                       (thm-index posp)
                                       (names-to-avoid symbol-listp)
                                       state)
  :returns (mv (thm-event pseudo-event-formp)
               (thm-name symbolp)
               (thm-index posp :hyp (posp thm-index))
               (names-to-avoid symbol-listp :hyp (symbol-listp names-to-avoid)))
  :short "Generate a correctness theorem for a boolean expression execution."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is similar to @(tsee atc-gen-expr-pure-correct-thm),
     but with some important differences.")
   (xdoc::p
    "The ACL2 term from which the C expression is generated is boolean-valued,
     so the execution of the expression cannot be equal to the term.
     Instead, there must be another ACL2 term,
     whose value is (the ACL2 model of) a C value,
     that the expression execution is equated to in the theorem.
     The two terms are
     @('aterm') (for `ACL2 term') and @('cterm') (for `C term'),
     both passed as parameters to this ACL2 function
     (unlike a single @('term') in @(tsee atc-gen-expr-pure-correct-thm)).
     The two terms and their relation are slightly different
     for different kinds of boolean expression terms;
     see the callers of this ACL2 function for details.")
   (xdoc::p
    "While @(tsee atc-gen-expr-pure-correct-thm) generates a theorem
     whose conclusion consists of two conjuncts,
     namely the equation with the expression execution
     and the type predicate applied to the term,
     here we generate four conjuncts.
     The first two are similar to @(tsee atc-gen-expr-pure-correct-thm),
     but we use @('cterm') for that purpose, as explained above.
     The other two conjuncts refer to @('aterm') instead:
     they say that @(tsee test-value) applied to @('cterm') yields @('aterm'),
     and that @('aterm') is a boolean.")
   (xdoc::p
    "The reason for the form of this theorem is that
     the symbolic execution rules have separate binding hypotheses
     for executing the expression and for applying @(tsee test-value):
     for example, see the @('exec-expr-pure-when-cond') rule
     in @(see atc-exec-expr-pure-rules)."))
  (b* ((wrld (w state))
       (name (pack fn '-correct- thm-index))
       ((mv name names-to-avoid) (fresh-logical-name-with-$s-suffix
                                  name nil names-to-avoid wrld))
       (type-pred (type-to-recognizer type wrld))
       (uaterm (untranslate$ aterm nil state))
       (ucterm (untranslate$ cterm nil state))
       (uobjdes (untranslate$ objdes nil state))
       (formula1 `(equal (exec-expr-pure ',expr ,compst-var)
                         (expr-value ,ucterm ,uobjdes)))
       (formula1 (atc-contextualize formula1 context fn fn-guard
                                    compst-var nil nil wrld))
       (formula2 `(and (,type-pred ,ucterm)
                       (equal (test-value ,ucterm)
                              ,uaterm)
                       (booleanp ,uaterm)))
       (formula2 (atc-contextualize formula2 context fn fn-guard
                                    nil nil nil wrld))
       (formula `(and ,formula1 ,formula2))
       ((mv event &) (evmac-generate-defthm name
                                            :formula formula
                                            :hints hints
                                            :instructions instructions
                                            :enable nil)))
    (mv event name (1+ thm-index) names-to-avoid)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-new-inscope ((fn symbolp)
                             (fn-guard symbolp)
                             (inscope atc-symbol-varinfo-alist-listp)
                             (new-context atc-contextp)
                             (compst-var symbolp)
                             (rules true-listp)
                             (thm-index posp)
                             (names-to-avoid symbol-listp)
                             (wrld plist-worldp))
  :returns (mv (new-inscope atc-symbol-varinfo-alist-listp
                            :hyp (atc-symbol-varinfo-alist-listp inscope))
               (events pseudo-event-form-listp)
               (names-to-avoid symbol-listp :hyp (symbol-listp names-to-avoid)))
  :short "Generate an updated symbol table according to given criteria."
  :long
  (xdoc::topstring
   (xdoc::p
    "The initial symbol table is generated by @(tsee atc-gen-init-inscope);
     see the documentation of that function.
     As we process ACL2 terms that represent C constructs,
     sometimes we need to generate an updated symbol table,
     which is mostly the same as the one just before the update,
     but with new theorems about the variables in it.
     For instance, when entering a scope,
     the new symbol table is almost the same,
     with the addition of a new empty scope;
     but the theorems about the variables in scope must be rephrased
     to be about the computation state updated with the new scope.")
   (xdoc::p
    "This ACL2 function goes through the given symbol table @('inscope')
     and constructs an updated symbol table @('new-inscope') from it,
     with the same scopes and variables, but different theorems (see below).
     Callers of this ACL2 function can further update the returned symbol table;
     for instance, when entering a scope,
     the caller of this ACL2 function adds a new empty scope.")
   (xdoc::p
    "The input context @('new-context') is already the new context,
     created by the caller of this ACL2 function
     by updating the previous context,
     e.g. by adding a computation state binding for entering a scope.")
   (xdoc::p
    "The theorems of the updated symbol table are generated here.
     They say that reading each variable name yields the variable
     in the computation state updated according to the (new) context.
     Each new theorem is proved from the old theorem,
     and using rules passed to this ACL2 function,
     since the rules may differ depending on
     the specifics of the updated context and computation state.")
   (xdoc::p
    "Since the generated theorem names involve the names of the variables,
     which are always distinct in a symbol table generated by ATC,
     we use the same theorem index for all the theorems.
     The updated theorem index, returned by this ACL2 function,
     is just one more than the input theorem index."))
  (b* (((mv new-inscope events names-to-avoid)
        (atc-gen-new-inscope-aux fn fn-guard inscope new-context compst-var
                                 rules thm-index names-to-avoid wrld)))
    (mv new-inscope events names-to-avoid))

  :prepwork
  ((define atc-gen-new-inscope-aux ((fn symbolp)
                                    (fn-guard symbolp)
                                    (inscope atc-symbol-varinfo-alist-listp)
                                    (new-context atc-contextp)
                                    (compst-var symbolp)
                                    (rules true-listp)
                                    (thm-index posp)
                                    (names-to-avoid symbol-listp)
                                    (wrld plist-worldp))
     :returns (mv (new-inscope atc-symbol-varinfo-alist-listp
                               :hyp (atc-symbol-varinfo-alist-listp inscope))
                  (events pseudo-event-form-listp)
                  (names-to-avoid symbol-listp
                                  :hyp (symbol-listp names-to-avoid)))
     :parents nil
     (b* (((when (endp inscope)) (mv nil nil names-to-avoid))
          (scope (car inscope))
          ((mv new-scope events names-to-avoid)
           (atc-gen-new-inscope-aux-aux fn fn-guard scope new-context compst-var
                                        rules thm-index names-to-avoid wrld))
          (scopes (cdr inscope))
          ((mv new-scopes more-events names-to-avoid)
           (atc-gen-new-inscope-aux fn fn-guard scopes new-context compst-var
                                    rules thm-index names-to-avoid wrld)))
       (mv (cons new-scope new-scopes)
           (append events more-events)
           names-to-avoid))

     :prepwork
     ((define atc-gen-new-inscope-aux-aux ((fn symbolp)
                                           (fn-guard symbolp)
                                           (scope atc-symbol-varinfo-alistp)
                                           (new-context atc-contextp)
                                           (compst-var symbolp)
                                           (rules true-listp)
                                           (thm-index posp)
                                           (names-to-avoid symbol-listp)
                                           (wrld plist-worldp))
        :returns (mv (new-scope atc-symbol-varinfo-alistp
                                :hyp (atc-symbol-varinfo-alistp scope)
                                :hints (("Goal"
                                         :induct t
                                         :in-theory (enable acons))))
                     (events pseudo-event-form-listp)
                     (names-to-avoid symbol-listp
                                     :hyp (symbol-listp names-to-avoid)))
        :parents nil
        (b* (((when (endp scope)) (mv nil nil names-to-avoid))
             ((cons var info) (car scope))
             (type (atc-var-info->type info))
             (thm (atc-var-info->thm info))
             (type-pred (type-to-recognizer type wrld))
             (new-thm (pack fn '- var '-in-scope- thm-index))
             ((mv new-thm names-to-avoid)
              (fresh-logical-name-with-$s-suffix new-thm nil names-to-avoid wrld))
             (formula1 `(and (objdesign-of-var (ident ,(symbol-name var))
                                               compst)
                             (equal (read-object
                                     (objdesign-of-var (ident ,(symbol-name var))
                                                       compst)
                                     compst)
                                    ,var)
                             (equal (read-var (ident ,(symbol-name var))
                                              ,compst-var)
                                    ,var)))
             (formula1 (atc-contextualize formula1 new-context fn fn-guard
                                          compst-var nil nil wrld))
             (formula2 `(,type-pred ,var))
             (formula2 (atc-contextualize formula2 new-context fn fn-guard
                                          nil nil nil wrld))
             (formula `(and ,formula1 ,formula2))
             (hints `(("Goal" :in-theory '(,thm ,@rules))))
             ((mv event &) (evmac-generate-defthm new-thm
                                                  :formula formula
                                                  :hints hints
                                                  :enable nil))
             (new-info (change-atc-var-info info :thm new-thm))
             (rest (cdr scope))
             ((mv new-rest events names-to-avoid)
              (atc-gen-new-inscope-aux-aux fn fn-guard rest new-context
                                           compst-var rules thm-index
                                           names-to-avoid wrld)))
          (mv (acons var new-info new-rest)
              (cons event events)
              names-to-avoid))
        :prepwork
        ((local
          (in-theory (enable alistp-when-atc-symbol-varinfo-alistp-rewrite))))
        :verify-guards :after-returns)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-enter-inscope ((fn symbolp)
                               (fn-guard symbolp)
                               (inscope atc-symbol-varinfo-alist-listp)
                               (context atc-contextp)
                               (compst-var symbolp)
                               (thm-index posp)
                               (names-to-avoid symbol-listp)
                               (wrld plist-worldp))
  :returns (mv (new-inscope atc-symbol-varinfo-alist-listp
                            :hyp (atc-symbol-varinfo-alist-listp inscope))
               (new-context atc-contextp :hyp (atc-contextp context))
               (events pseudo-event-form-listp)
               (thm-index posp :hyp (posp thm-index))
               (names-to-avoid symbol-listp :hyp (symbol-listp names-to-avoid)))
  :short "Generate an updated symbol table according to entering a new scope."
  :long
  (xdoc::topstring
   (xdoc::p
    "The context is updated with a @(tsee let) binding for the computation state
     that updates it via @(tsee enter-scope).
     We use @(tsee atc-gen-new-inscope) to generate most of the new symbol table
     and then we add a new empty scope to it.")
   (xdoc::p
    "The theorems for the new symbol table are proved from the old ones
     using the rule that reduces @(tsee read-var) of @(tsee enter-scope)
     to just @(tsee read-var).
     The hypothesis of that rule saying that there are frames
     is discharged via the rules in
     @(see atc-compustate-frames-number-rules):
     the computation state that @(tsee enter-scope) is applied to
     always starts with @(tsee add-frame)
     or @(tsee enter-scope)
     or @(tsee add-var);
     there may be other forms possible, which we will handle later."))
  (b* ((premise (make-atc-premise-compustate :var compst-var
                                             :term `(enter-scope ,compst-var)))
       (new-context (append context (list premise)))
       (rules '(objdesign-of-var-of-enter-scope-iff
                objdesign-of-var-of-add-var-iff
                read-object-of-objdesign-of-var-to-read-var
                read-var-of-enter-scope
                compustate-frames-number-of-add-frame-not-zero
                compustate-frames-number-of-enter-scope-not-zero
                compustate-frames-number-of-add-var-not-zero))
       ((mv new-inscope events names-to-avoid)
        (atc-gen-new-inscope fn fn-guard inscope new-context compst-var
                             rules thm-index names-to-avoid wrld)))
    (mv (cons nil new-inscope)
        new-context
        events
        (1+ thm-index)
        names-to-avoid)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-vardecl-inscope ((fn symbolp)
                                 (fn-guard symbolp)
                                 (inscope atc-symbol-varinfo-alist-listp)
                                 (context atc-contextp)
                                 (var symbolp)
                                 (type typep)
                                 (term "An untranslated term.")
                                 (term-thm symbolp)
                                 (compst-var symbolp)
                                 (thm-index posp)
                                 (names-to-avoid symbol-listp)
                                 (wrld plist-worldp))
  :returns (mv (new-inscope atc-symbol-varinfo-alist-listp
                            :hyp (atc-symbol-varinfo-alist-listp inscope))
               (new-context atc-contextp :hyp (atc-contextp context))
               (events pseudo-event-form-listp)
               (thm-index posp :hyp (posp thm-index))
               (names-to-avoid symbol-listp :hyp (symbol-listp names-to-avoid)))
  :short "Generate an updated symbol table according to
          declaring a new local variable."
  :long
  (xdoc::topstring
   (xdoc::p
    "The context is updated with a @(tsee let) binding for the variable
     followed by a @(tsee let) binding for the computation state.
     We use @(tsee atc-gen-new-inscope) to generate most of the new symbol table
     and then we add the new variable (to the innermost scope),
     along with a theorem for the new variable."))
  (b* ((var-premise (make-atc-premise-cvalue :var var :term term))
       (cs-premise-term `(add-var (ident ,(symbol-name var)) ,var ,compst-var))
       (cs-premise (make-atc-premise-compustate :var compst-var
                                                :term cs-premise-term))
       (new-context (append context (list var-premise cs-premise)))
       (rules '(objdesign-of-var-of-enter-scope-iff
                objdesign-of-var-of-add-var-iff
                read-object-of-objdesign-of-var-to-read-var
                read-var-of-add-var
                ident-fix-when-identp
                identp-of-ident
                equal-of-ident-and-ident
                (:e str-fix)))
       ((mv new-inscope new-inscope-events names-to-avoid)
        (atc-gen-new-inscope fn fn-guard inscope new-context compst-var rules
                             thm-index names-to-avoid wrld))
       (var-in-scope-thm (pack fn '- var '-in-scope- thm-index))
       (thm-index (1+ thm-index))
       ((mv var-in-scope-thm names-to-avoid)
        (fresh-logical-name-with-$s-suffix var-in-scope-thm
                                           nil
                                           names-to-avoid
                                           wrld))
       (type-pred (type-to-recognizer type wrld))
       (var-in-scope-formula1
        `(equal (read-var (ident ,(symbol-name var)) ,compst-var)
                ,var))
       (var-in-scope-formula1
        (atc-contextualize var-in-scope-formula1 new-context fn fn-guard
                           compst-var nil nil wrld))
       (var-in-scope-formula2 `(,type-pred ,var))
       (var-in-scope-formula2
        (atc-contextualize var-in-scope-formula2 new-context fn fn-guard
                           nil nil nil wrld))
       (var-in-scope-formula `(and ,var-in-scope-formula1
                                   ,var-in-scope-formula2))
       (valuep-when-type-pred (pack 'valuep-when- type-pred))
       (not-flexible-array-member-p-when-type-pred
        (pack 'not-flexible-array-member-p-when- type-pred))
       (var-in-scope-hints
        `(("Goal" :in-theory '(read-var-of-add-var
                               ident-fix-when-identp
                               identp-of-ident
                               equal-of-ident-and-ident
                               (:e str-fix)
                               remove-flexible-array-member-when-absent
                               ,not-flexible-array-member-p-when-type-pred
                               value-fix-when-valuep
                               ,valuep-when-type-pred
                               ,term-thm))))
       ((mv var-in-scope-event &) (evmac-generate-defthm
                                   var-in-scope-thm
                                   :formula var-in-scope-formula
                                   :hints var-in-scope-hints
                                   :enable nil))
       (varinfo (make-atc-var-info :type type
                                   :thm var-in-scope-thm
                                   :externalp nil))
       (new-inscope (atc-add-var var varinfo new-inscope)))
    (mv new-inscope
        new-context
        (append new-inscope-events (list var-in-scope-event))
        thm-index
        names-to-avoid)))
