; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2025 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "generation-contexts")
(include-book "variable-tables")
(include-book "tag-tables")

(include-book "kestrel/event-macros/event-generation" :dir :system)
(include-book "std/system/formals-plus" :dir :system)
(include-book "std/system/fresh-logical-name-with-dollars-suffix" :dir :system)
(include-book "std/system/untranslate-dollar" :dir :system)

(local (include-book "std/system/w" :dir :system))
(local (include-book "std/typed-lists/atom-listp" :dir :system))

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
                                       (term1 pseudo-termp)
                                       (term2 pseudo-termp)
                                       (objdes pseudo-termp)
                                       (compst-var symbolp)
                                       (hints true-listp)
                                       (instructions true-listp)
                                       (prec-tags atc-string-taginfo-alistp)
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
    "As theorem name, we combine
     @('fn') with @('correct') and with the theorem index.
     The name just needs to be unique locally to the call to ATC,
     so we expect that generally no @('$') signs will need to be added
     by @(tsee fresh-logical-name-with-$s-suffix).")
   (xdoc::p
    "The theorem says that
     @(tsee exec-expr-pure) called on the quoted expression
     is the same as @('term1');
     it also says that @('term2') has the expression's type.
     Often @('term1') and @('term2') are the same,
     but sometimes they differ,
     e.g. when @('term1') is a @('-ptr') variable
     while @('term2') is the same variable without @('-ptr').
     The input @('objdes') is a term that denotes an object designator,
     or @('nil') if no object designator is applicable:
     this is the object designator that the expression denotes, if any.
     The terms are untranslated, to make them more readable,
     in particular to eliminate quotes before numbers.
     Terms, expression, and type are passed as inputs.
     The theorem is contextualized,
     and further conditioned by the satisfaction of the guard of @('fn').")
   (xdoc::p
    "The hints or instructions to prove the theorem are passed as input,
     because they depend on the specifics of the expression."))
  (b* ((wrld (w state))
       (name (pack fn '-correct- thm-index))
       ((mv name names-to-avoid) (fresh-logical-name-with-$s-suffix
                                  name nil names-to-avoid wrld))
       (thm-index (1+ thm-index))
       (type-pred (atc-type-to-recognizer type prec-tags))
       (uterm1 (untranslate$ term1 nil state))
       (uterm2 (untranslate$ term2 nil state))
       (uobjdes (untranslate$ objdes nil state))
       (exec-formula `(equal (exec-expr-pure ',expr ,compst-var)
                             (expr-value ,uterm1 ,uobjdes)))
       (exec-formula (atc-contextualize exec-formula context fn fn-guard
                                        compst-var nil nil t wrld))
       (type-formula `(,type-pred ,uterm2))
       (type-formula (atc-contextualize type-formula context fn fn-guard
                                        nil nil nil nil wrld))
       (formula `(and ,exec-formula ,type-formula))
       ((mv event &) (evmac-generate-defthm name
                                            :formula formula
                                            :hints hints
                                            :instructions instructions
                                            :enable nil)))
    (mv event name thm-index names-to-avoid)))

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
                                       (prec-tags atc-string-taginfo-alistp)
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
     (unlike the terms @('term1') and @('term2')
     in @(tsee atc-gen-expr-pure-correct-thm)).
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
       (thm-index (1+ thm-index))
       (type-pred (atc-type-to-recognizer type prec-tags))
       (uaterm (untranslate$ aterm nil state))
       (ucterm (untranslate$ cterm nil state))
       (uobjdes (untranslate$ objdes nil state))
       (exec-formula `(equal (exec-expr-pure ',expr ,compst-var)
                             (expr-value ,ucterm ,uobjdes)))
       (exec-formula (atc-contextualize exec-formula context fn fn-guard
                                        compst-var nil nil t wrld))
       (type-formula `(and (,type-pred ,ucterm)
                           (equal (test-value ,ucterm)
                                  ,uaterm)
                           (booleanp ,uaterm)))
       (type-formula (atc-contextualize type-formula context fn fn-guard
                                        nil nil nil nil wrld))
       (formula `(and ,exec-formula ,type-formula))
       ((mv event &) (evmac-generate-defthm name
                                            :formula formula
                                            :hints hints
                                            :instructions instructions
                                            :enable nil)))
    (mv event name thm-index names-to-avoid)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-new-inscope ((fn symbolp)
                             (fn-guard symbolp)
                             (inscope atc-symbol-varinfo-alist-listp)
                             (new-context atc-contextp)
                             (compst-var symbolp)
                             (rules true-listp)
                             (prec-tags atc-string-taginfo-alistp)
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
     for instance, when encountering a new variable declaration,
     the caller of this ACL2 function adds the new variable.")
   (xdoc::p
    "The input context @('new-context') is already the new context,
     created by the caller of this ACL2 function
     by updating the previous context,
     e.g. by adding a computation state binding for entering a scope.")
   (xdoc::p
    "The theorems of the updated symbol table are generated here.
     They say that reading each C variable
     yields the corresponding ACL2 variable
     or the @('-ptr') ACL2 variable,
     in the computation state updated according to the (new) context.
     Each new theorem is proved from the old theorem,
     using rules passed to this ACL2 function,
     since the rules may differ depending on
     the specifics of the updated context and computation state.")
   (xdoc::p
    "Since the generated theorem names involve the names of the variables,
     which are always distinct in a symbol table generated by ATC,
     we use the same theorem index for all the theorems."))
  (b* (((when (endp inscope)) (mv nil nil names-to-avoid))
       (scope (car inscope))
       ((mv new-scope events names-to-avoid)
        (atc-gen-new-inscope-aux fn fn-guard scope new-context compst-var
                                 rules prec-tags thm-index names-to-avoid wrld))
       (scopes (cdr inscope))
       ((mv new-scopes more-events names-to-avoid)
        (atc-gen-new-inscope fn fn-guard scopes new-context compst-var
                             rules prec-tags thm-index names-to-avoid wrld)))
    (mv (cons new-scope new-scopes)
        (append events more-events)
        names-to-avoid))

  :prepwork
  ((define atc-gen-new-inscope-aux ((fn symbolp)
                                    (fn-guard symbolp)
                                    (scope atc-symbol-varinfo-alistp)
                                    (new-context atc-contextp)
                                    (compst-var symbolp)
                                    (rules true-listp)
                                    (prec-tags atc-string-taginfo-alistp)
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
          (externalp (atc-var-info->externalp info))
          (type-pred (atc-type-to-recognizer type prec-tags))
          (new-thm (pack fn '- var '-in-scope- thm-index))
          ((mv new-thm names-to-avoid)
           (fresh-logical-name-with-$s-suffix
            new-thm nil names-to-avoid wrld))
          (var/varptr (if (and (or (type-case type :pointer)
                                   (type-case type :array))
                               (not externalp))
                          (add-suffix-to-fn var "-PTR")
                        var))
          (formula1 `(and (objdesign-of-var (ident ,(symbol-name var))
                                            ,compst-var)
                          (equal (read-object
                                  (objdesign-of-var (ident ,(symbol-name var))
                                                    ,compst-var)
                                  ,compst-var)
                                 ,var/varptr)
                          ,@(and (or (type-case type :pointer)
                                     (type-case type :array))
                                 (not externalp)
                                 `((equal (read-object
                                           ,(add-suffix-to-fn var "-OBJDES")
                                           ,compst-var)
                                          ,var)))))
          (formula1 (atc-contextualize formula1 new-context fn fn-guard
                                       compst-var nil nil t wrld))
          (formula2 `(,type-pred ,var))
          (formula2 (atc-contextualize formula2 new-context fn fn-guard
                                       nil nil nil nil wrld))
          (formula `(and ,formula1 ,formula2))
          (hints `(("Goal" :in-theory '(,thm ,@rules))))
          ((mv event &) (evmac-generate-defthm new-thm
                                               :formula formula
                                               :hints hints
                                               :enable nil))
          (new-info (change-atc-var-info info :thm new-thm))
          (rest (cdr scope))
          ((mv new-rest events names-to-avoid)
           (atc-gen-new-inscope-aux fn fn-guard rest new-context
                                    compst-var rules prec-tags thm-index
                                    names-to-avoid wrld)))
       (mv (acons var new-info new-rest)
           (cons event events)
           names-to-avoid))
     :prepwork
     ((local
       (in-theory (enable alistp-when-atc-symbol-varinfo-alistp-rewrite))))
     :verify-guards :after-returns)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-enter-inscope ((fn symbolp)
                               (fn-guard symbolp)
                               (inscope atc-symbol-varinfo-alist-listp)
                               (context atc-contextp)
                               (compst-var symbolp)
                               (prec-tags atc-string-taginfo-alistp)
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
     that updates it via @(tsee enter-scope);
     we return the updated context.
     We use @(tsee atc-gen-new-inscope) to generate most of the new symbol table
     and then we add a new empty scope to it.")
   (xdoc::p
    "The theorems for the new symbol table are proved from the old ones
     using the rule that reduces
     @(tsee objdesign-of-var) and @(tsee read-object) of @(tsee enter-scope)
     to just @(tsee objdesign-of-var) and @(tsee read-object).
     The hypothesis of that rule saying that there are frames
     is discharged via the rules in
     @(see atc-compustate-frames-number-rules):
     the computation state that @(tsee enter-scope) is applied to
     always starts with @(tsee add-frame)
     or @(tsee enter-scope)
     or @(tsee add-var);
     there may be other forms possible, which we will handle later.
     For pointers, we also need the rule that reduces
     @(tsee read-object) of the object designator of @(tsee enter-scope)
     to just @(tsee read-object) of @(tsee enter-scope)."))
  (b* ((premise (make-atc-premise-compustate :var compst-var
                                             :term `(enter-scope ,compst-var)))
       (new-context (atc-context-extend context (list premise)))
       (rules '(objdesign-of-var-of-enter-scope-iff
                read-object-of-objdesign-of-var-of-enter-scope
                compustate-frames-number-of-add-frame-not-zero
                compustate-frames-number-of-enter-scope-not-zero
                compustate-frames-number-of-add-var-not-zero
                read-object-alloc-of-enter-scope))
       ((mv new-inscope events names-to-avoid)
        (atc-gen-new-inscope fn fn-guard inscope new-context compst-var
                             rules prec-tags thm-index names-to-avoid wrld)))
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
                                 (prec-tags atc-string-taginfo-alistp)
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
     followed by a @(tsee let) binding for the computation state;
     we return the updated context.
     We use @(tsee atc-gen-new-inscope) to generate most of the new symbol table
     and then we add the new variable (to the innermost scope),
     along with a theorem for the new variable.
     The term to which the variable is bound is passed as argument here,
     along with its associated theorem, which we use in the generated hints."))
  (b* ((var-premise (make-atc-premise-cvalue :var var :term term))
       (cs-premise-term `(add-var (ident ,(symbol-name var)) ,var ,compst-var))
       (cs-premise (make-atc-premise-compustate :var compst-var
                                                :term cs-premise-term))
       (new-context (atc-context-extend context (list var-premise cs-premise)))
       (rules '(objdesign-of-var-of-enter-scope-iff
                objdesign-of-var-of-add-var-iff
                read-object-of-objdesign-of-var-of-add-var
                read-object-of-objdesign-of-var-of-enter-scope
                ident-fix-when-identp
                identp-of-ident
                equal-of-ident-and-ident
                (:e str-fix)
                read-object-of-add-var))
       ((mv new-inscope new-inscope-events names-to-avoid)
        (atc-gen-new-inscope fn fn-guard inscope new-context compst-var rules
                             prec-tags thm-index names-to-avoid wrld))
       (var-in-scope-thm (pack fn '- var '-in-scope- thm-index))
       (thm-index (1+ thm-index))
       ((mv var-in-scope-thm names-to-avoid)
        (fresh-logical-name-with-$s-suffix var-in-scope-thm
                                           nil
                                           names-to-avoid
                                           wrld))
       (type-pred (atc-type-to-recognizer type prec-tags))
       (var-in-scope-formula1
        `(and (objdesign-of-var (ident ,(symbol-name var)) ,compst-var)
              (equal (read-object (objdesign-of-var (ident ,(symbol-name var))
                                                    ,compst-var)
                                  ,compst-var)
                     ,var)))
       (var-in-scope-formula1
        (atc-contextualize var-in-scope-formula1 new-context fn fn-guard
                           compst-var nil nil t wrld))
       (var-in-scope-formula2 `(,type-pred ,var))
       (var-in-scope-formula2
        (atc-contextualize var-in-scope-formula2 new-context fn fn-guard
                           nil nil nil nil wrld))
       (var-in-scope-formula `(and ,var-in-scope-formula1
                                   ,var-in-scope-formula2))
       (valuep-when-type-pred (atc-type-to-valuep-thm type prec-tags))
       (not-flexiblep-thms (atc-type-to-notflexarrmem-thms type prec-tags))
       (var-in-scope-hints
        `(("Goal" :in-theory '(objdesign-of-var-of-add-var-iff
                               read-object-of-objdesign-of-var-of-add-var
                               ident-fix-when-identp
                               identp-of-ident
                               equal-of-ident-and-ident
                               (:e str-fix)
                               remove-flexible-array-member-when-absent
                               ,@not-flexiblep-thms
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-if/ifelse-inscope ((fn symbolp)
                                   (fn-guard symbolp)
                                   (inscope atc-symbol-varinfo-alist-listp)
                                   (then-inscope atc-symbol-varinfo-alist-listp)
                                   (else-inscope atc-symbol-varinfo-alist-listp)
                                   (context atc-contextp)
                                   (new-context atc-contextp)
                                   (test-term "An untranslated term.")
                                   (then-term "An untranslated term.")
                                   (else-term "An untranslated term.")
                                   (compst-var symbolp)
                                   (new-compst "An untranslated term.")
                                   (then-new-compst "An untranslated term.")
                                   (else-new-compst "An untranslated term.")
                                   (prec-tags atc-string-taginfo-alistp)
                                   (thm-index posp)
                                   (names-to-avoid symbol-listp)
                                   (wrld plist-worldp))
  :returns (mv (new-inscope atc-symbol-varinfo-alist-listp
                            :hyp (atc-symbol-varinfo-alist-listp inscope))
               (events pseudo-event-form-listp)
               (thm-index posp :hyp (posp thm-index))
               (names-to-avoid symbol-listp :hyp (symbol-listp names-to-avoid)))
  :short "Generate an updated symbol table according to
          executing a conditional statement."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('inscope') and @('context') inputs are
     the ones just before the conditional statement.
     The @('then-inscope'),
     @('else-inscope'),
     @('then-new-compst'), and
     @('else-new-compst') inputs are
     the ones just after each branch.
     The @('new-context') and @('new-compst') inputs are
     the ones at the end of the conditional.")
   (xdoc::p
    "We generate proof builder instructions,
     in order to deal with the case split of the @(tsee if)
     in a controlled way.")
   (xdoc::p
    "Here we cannot use @(tsee atc-gen-new-inscope),
     because we need to use more elaborate proof builder instructions
     than just a set of rules."))
  (b* (((when (endp inscope)) (mv nil nil (1+ thm-index) names-to-avoid))
       (scope (car inscope))
       ((mv new-scope events names-to-avoid)
        (atc-gen-if/ifelse-inscope-aux fn
                                       fn-guard
                                       scope
                                       then-inscope
                                       else-inscope
                                       context
                                       new-context
                                       test-term
                                       then-term
                                       else-term
                                       compst-var
                                       new-compst
                                       then-new-compst
                                       else-new-compst
                                       prec-tags
                                       thm-index
                                       names-to-avoid
                                       wrld))
       ((mv new-inscope more-events thm-index names-to-avoid)
        (atc-gen-if/ifelse-inscope fn
                                   fn-guard
                                   (cdr inscope)
                                   then-inscope
                                   else-inscope
                                   context
                                   new-context
                                   test-term
                                   then-term
                                   else-term
                                   compst-var
                                   new-compst
                                   then-new-compst
                                   else-new-compst
                                   prec-tags
                                   thm-index
                                   names-to-avoid
                                   wrld)))
    (mv (cons new-scope new-inscope)
        (append events more-events)
        thm-index
        names-to-avoid))

  :prepwork
  ((define atc-gen-if/ifelse-inscope-aux
     ((fn symbolp)
      (fn-guard symbolp)
      (scope atc-symbol-varinfo-alistp)
      (then-inscope atc-symbol-varinfo-alist-listp)
      (else-inscope atc-symbol-varinfo-alist-listp)
      (context atc-contextp)
      (new-context atc-contextp)
      (test-term "An untranslated term.")
      (then-term "An untranslated term.")
      (else-term "An untranslated term.")
      (compst-var symbolp)
      (new-compst "An untranslated term.")
      (then-new-compst "An untranslated term.")
      (else-new-compst "An untranslated term.")
      (prec-tags atc-string-taginfo-alistp)
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
          (externalp (atc-var-info->externalp info))
          (type-pred (atc-type-to-recognizer type prec-tags))
          (new-thm (pack fn '- var '-in-scope- thm-index))
          ((mv new-thm names-to-avoid)
           (fresh-logical-name-with-$s-suffix
            new-thm nil names-to-avoid wrld))
          (var/varptr (if (and (or (type-case type :pointer)
                                   (type-case type :array))
                               (not externalp))
                          (add-suffix-to-fn var "-PTR")
                        var))
          (formula1
           `(and (objdesign-of-var (ident ,(symbol-name var))
                                   ,compst-var)
                 (equal (read-object
                         (objdesign-of-var (ident ,(symbol-name var))
                                           ,compst-var)
                         ,compst-var)
                        ,var/varptr)
                 ,@(and (or (type-case type :pointer)
                            (type-case type :array))
                        (not externalp)
                        `((equal (read-object
                                  ,(add-suffix-to-fn var "-OBJDES")
                                  ,compst-var)
                                 ,var)))))
          (formula1 (atc-contextualize formula1 new-context fn fn-guard
                                       compst-var nil nil t wrld))
          (formula2 `(,type-pred ,var))
          (formula2 (atc-contextualize formula2 new-context fn fn-guard
                                       nil nil nil nil wrld))
          (formula `(and ,formula1 ,formula2))
          (valuep-when-type-pred (atc-type-to-valuep-thm type prec-tags))
          (not-flexiblep-thms
           (atc-type-to-notflexarrmem-thms type prec-tags))
          (then-var-info (atc-get-var var then-inscope))
          ((unless then-var-info)
           (raise "Internal error: ~x0 not in scope after 'then'." var)
           (mv nil nil nil))
          (then-var-thm (atc-var-info->thm then-var-info))
          (else-var-info (atc-get-var var else-inscope))
          ((unless else-var-info)
           (raise "Internal error: ~x0 not in scope after 'else'." var)
           (mv nil nil nil))
          (else-var-thm (atc-var-info->thm else-var-info))
          (value-kind-thms
           (atc-string-taginfo-alist-to-value-kind-thms prec-tags))
          (writer-return-thms
           (atc-string-taginfo-alist-to-writer-return-thms prec-tags))
          (then-hints
           `(("Goal"
              :in-theory '(,then-var-thm
                           read-object-alloc-of-enter-scope
                           read-object-of-update-object-same
                           objdesign-of-var-of-update-object-iff
                           objdesign-of-var-of-enter-scope-iff
                           update-object-of-update-object-same
                           read-object-of-update-object-disjoint
                           object-disjointp-commutative
                           update-object-of-enter-scope
                           compustate-frames-number-of-enter-scope-not-zero
                           compustatep-of-enter-scope
                           compustate-frames-number-of-update-object
                           read-object-of-objdesign-of-var-of-enter-scope
                           read-object-of-objdesign-of-var-to-read-var
                           read-var-of-update-object
                           read-var-of-add-var
                           update-var-of-enter-scope
                           update-var-of-add-var
                           equal-of-ident-and-ident
                           (:e str-fix)
                           exit-scope-of-enter-scope-when-compustatep
                           compustatep-of-add-var
                           compustate-frames-number-of-add-var-not-zero
                           objdesign-of-var-of-add-var-iff
                           ident-fix-when-identp
                           identp-of-ident
                           read-object-of-objdesign-of-var-of-add-var
                           remove-flexible-array-member-when-absent
                           ,@not-flexiblep-thms
                           value-fix-when-valuep
                           ,valuep-when-type-pred
                           exit-scope-of-if*
                           objdesign-of-var-of-if*-when-both-objdesign-of-var
                           read-var-of-if*
                           read-var-of-enter-scope
                           acl2::if*-when-same
                           read-object-of-value-pointer->designator-of-if*
                           uchar-arrayp-of-uchar-array-write
                           schar-arrayp-of-schar-array-write
                           ushort-arrayp-of-ushort-array-write
                           sshort-arrayp-of-sshort-array-write
                           uint-arrayp-of-uint-array-write
                           sint-arrayp-of-sint-array-write
                           ulong-arrayp-of-ulong-array-write
                           slong-arrayp-of-slong-array-write
                           ullong-arrayp-of-ullong-array-write
                           sllong-arrayp-of-sllong-array-write
                           compustatep-of-update-object
                           ,@value-kind-thms
                           ,@writer-return-thms
                           update-static-var-of-enter-scope
                           compustatep-of-update-static-var
                           compustate-frames-number-of-update-static-var
                           compustate-frames-number-of-add-frame-not-zero
                           objdesign-of-var-of-update-static-var-iff
                           update-static-var-of-add-frame
                           read-var-of-add-frame
                           read-static-var-of-update-static-var
                           compustate-frames-number-of-update-static-var
                           compustatep-of-add-frame
                           objdesign-of-var-of-add-frame-when-read-object-static
                           read-object-of-objdesign-static
                           (:t objdesign-static)
                           read-static-var-of-add-frame
                           mv-nth-of-cons
                           (:e zp)))))
          (else-hints
           `(("Goal"
              :in-theory '(,else-var-thm
                           read-object-alloc-of-enter-scope
                           read-object-of-update-object-same
                           objdesign-of-var-of-update-object-iff
                           objdesign-of-var-of-enter-scope-iff
                           update-object-of-update-object-same
                           read-object-of-update-object-disjoint
                           object-disjointp-commutative
                           update-object-of-enter-scope
                           compustate-frames-number-of-enter-scope-not-zero
                           compustatep-of-enter-scope
                           compustate-frames-number-of-update-object
                           read-object-of-objdesign-of-var-of-enter-scope
                           read-object-of-objdesign-of-var-to-read-var
                           read-var-of-update-object
                           read-var-of-add-var
                           update-var-of-enter-scope
                           update-var-of-add-var
                           equal-of-ident-and-ident
                           (:e str-fix)
                           exit-scope-of-enter-scope-when-compustatep
                           compustatep-of-add-var
                           compustate-frames-number-of-add-var-not-zero
                           objdesign-of-var-of-add-var-iff
                           ident-fix-when-identp
                           identp-of-ident
                           read-object-of-objdesign-of-var-of-add-var
                           remove-flexible-array-member-when-absent
                           ,@not-flexiblep-thms
                           value-fix-when-valuep
                           ,valuep-when-type-pred
                           exit-scope-of-if*
                           objdesign-of-var-of-if*-when-both-objdesign-of-var
                           read-var-of-if*
                           read-var-of-enter-scope
                           acl2::if*-when-same
                           read-object-of-value-pointer->designator-of-if*
                           uchar-arrayp-of-uchar-array-write
                           schar-arrayp-of-schar-array-write
                           ushort-arrayp-of-ushort-array-write
                           sshort-arrayp-of-sshort-array-write
                           uint-arrayp-of-uint-array-write
                           sint-arrayp-of-sint-array-write
                           ulong-arrayp-of-ulong-array-write
                           slong-arrayp-of-slong-array-write
                           ullong-arrayp-of-ullong-array-write
                           sllong-arrayp-of-sllong-array-write
                           compustatep-of-update-object
                           ,@value-kind-thms
                           ,@writer-return-thms
                           update-static-var-of-enter-scope
                           compustatep-of-update-static-var
                           compustate-frames-number-of-update-static-var
                           compustate-frames-number-of-add-frame-not-zero
                           objdesign-of-var-of-update-static-var-iff
                           update-static-var-of-add-frame
                           read-var-of-add-frame
                           read-static-var-of-update-static-var
                           compustate-frames-number-of-update-static-var
                           compustatep-of-add-frame
                           objdesign-of-var-of-add-frame-when-read-object-static
                           read-object-of-objdesign-static
                           (:t objdesign-static)
                           read-static-var-of-add-frame
                           mv-nth-of-cons
                           (:e zp)))))
          (instructions
           `((casesplit ,(atc-contextualize
                          test-term
                          context nil nil nil nil nil nil wrld))
             (claim ,(atc-contextualize `(test* ,test-term)
                                        context nil nil nil nil nil nil wrld)
                    :hints (("Goal" :in-theory '(test*))))
             (drop 1)
             (claim ,(atc-contextualize
                      `(equal (if* ,test-term ,then-term ,else-term)
                              ,then-term)
                      context nil nil nil nil nil nil wrld)
                    :hints (("Goal"
                             :in-theory '(acl2::if*-when-true test*))))
             (claim ,(atc-contextualize
                      `(equal ,new-compst ,then-new-compst)
                      context nil nil compst-var nil nil nil wrld)
                    :hints (("Goal" :in-theory '(acl2::if*-when-true test*))))
             (prove :hints ,then-hints)
             (claim ,(atc-contextualize `(test* (not ,test-term))
                                        context nil nil nil nil nil nil wrld)
                    :hints (("Goal" :in-theory '(test*))))
             (drop 1)
             (claim ,(atc-contextualize
                      `(equal (if* ,test-term ,then-term ,else-term)
                              ,else-term)
                      context nil nil nil nil nil nil wrld)
                    :hints (("Goal" :in-theory '(acl2::if*-when-false test*))))
             (claim ,(atc-contextualize
                      `(equal ,new-compst ,else-new-compst)
                      context nil nil compst-var nil nil nil wrld)
                    :hints (("Goal" :in-theory '(acl2::if*-when-false test*))))
             (prove :hints ,else-hints)))
          ((mv event &) (evmac-generate-defthm new-thm
                                               :formula formula
                                               :instructions instructions
                                               :enable nil))
          (new-info (change-atc-var-info info :thm new-thm))
          (rest (cdr scope))
          ((mv new-rest events names-to-avoid)
           (atc-gen-if/ifelse-inscope-aux fn
                                          fn-guard
                                          rest
                                          then-inscope
                                          else-inscope
                                          context
                                          new-context
                                          test-term
                                          then-term
                                          else-term
                                          compst-var
                                          new-compst
                                          then-new-compst
                                          else-new-compst
                                          prec-tags
                                          thm-index
                                          names-to-avoid
                                          wrld)))
       (mv (acons var new-info new-rest)
           (cons event events)
           names-to-avoid))
     :prepwork
     ((local
       (in-theory (enable alistp-when-atc-symbol-varinfo-alistp-rewrite))))
     :verify-guards :after-returns)))
