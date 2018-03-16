; APT Tail Recursion Transformation -- Implementation
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "APT")

(include-book "kestrel/utilities/error-checking" :dir :system)
(include-book "kestrel/utilities/install-not-norm-event" :dir :system)
(include-book "kestrel/utilities/keyword-value-lists" :dir :system)
(include-book "kestrel/utilities/named-formulas" :dir :system)
(include-book "kestrel/utilities/paired-names" :dir :system)
(include-book "kestrel/utilities/user-interface" :dir :system)
(include-book "utilities/print-specifiers")
(include-book "utilities/transformation-table")

(local (xdoc::set-default-parents tailrec-implementation))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tailrec-check-nonrec-conditions
  ((combine-nonrec pseudo-termp "The term @('combine<nonrec<x1,...,xn>,r>')
                                 described in the documentation.")
   (nonrec? pseudo-termp "Candidate @('nonrec<x1,...,xn>') to check.")
   (r symbolp "The fresh variable @('r') described in the documentation.")
   (q symbolp "The fresh variable @('q') described in the documentation."))
  :returns
  (mv (yes/no booleanp)
      (combine "The @(tsee pseudo-termp) @('combine<q,r>')
                described in the documentation,
                if @('yes/no') is @('t')."))
  :verify-guards nil
  :short "Check whether @('nonrec?') satisfies the conditions
          for @('nonrec<x1,...,xn>') described in the documentation."
  :long
  "<p>
   The conditions are that
   @('r') does not occur in @('nonrec?')
   and that replacing every occurrence of @('nonrec?')
   in @('combine<nonrec<x1,...,xn>,r>') with @('q')
   yields a term whose only free variables are @('q') and @('r').
   </p>"
  (if (member-eq r (all-vars nonrec?))
      (mv nil nil)
    (let ((combine (subst-expr1 q nonrec? combine-nonrec)))
      (if (set-equiv (all-vars combine) (list q r))
          (mv t combine)
        (mv nil nil)))))

(defines tailrec-find-nonrec-term-in-term/terms
  :short "Decompose @('combine<nonrec<x1,...,xn>,r>') into
          @('nonrec<x1,...,xn>') and @('combine<q,r>'),
          as described in the documentation."
  :verify-guards nil

  (define tailrec-find-nonrec-term
    ((combine-nonrec pseudo-termp "The term @('combine<nonrec<x1,...,xn>,r>')
                                   described in the documentation.")
     (term-to-try pseudo-termp "Subterm of @('combine<nonrec<x1,...,xn>,r>')
                                to examine next.")
     (r symbolp "The fresh variable @('r') described in the documentation.")
     (q symbolp "The fresh variable @('q') described in the documentation."))
    :returns (mv (success "A @(tsee booleanp).")
                 (nonrec "The @(tsee pseudo-termp) @('nonrec<x1,...,xn>')
                          described in the documentation,
                          if @('success') is @('t').")
                 (combine "The @(tsee pseudo-termp) @('combine<q,r>')
                           described in the documentation,
                           if @('success') is @('t')."))
    :parents (tailrec-find-nonrec-term-in-term/terms)
    :short "Find the maximal and leftmost subterm of @('term-to-try')
            that satisfies the conditions for @('nonrec<x1,...,xn>')
            described in the documentation."
    :long
    "<p>
     When initially invoked
     on @('combine<nonrec<x1,...,xn>,r>') as @('term-to-try'),
     attempt to recursively finds @('nonrec<x1,...,xn>')
     as described in the documentation.
     </p>"
    (b* (((mv found combine) (tailrec-check-nonrec-conditions
                              combine-nonrec term-to-try r q))
         ((when found) (mv t term-to-try combine))
         ((when (or (variablep term-to-try)
                    (fquotep term-to-try)))
          (mv nil nil nil)))
      (tailrec-find-nonrec-terms combine-nonrec (fargs term-to-try) r q)))

  (define tailrec-find-nonrec-terms
    ((combine-nonrec pseudo-termp "The term @('combine<nonrec<x1,...,xn>,r>')
                                   described in the documentation.")
     (terms-to-try pseudo-term-listp "Subterms of @('combine-nonrec')
                                      to examine next.")
     (r symbolp "The fresh variable @('r') described in the documentation.")
     (q symbolp "The fresh variable @('q') described in the documentation."))
    :returns (mv (success "A @(tsee booleanp).")
                 (nonrec "The @(tsee pseudo-termp) @('nonrec<x1,...,xn>')
                          described in the documentation,
                          if @('success') is @('t');
                          otherwise @('nil').")
                 (combine "The @(tsee pseudo-termp) @('combine<q,r>')
                           described in the documentation,
                           if @('success') is @('t');
                           otherwise @('nil')."))
    :parents (tailrec-find-nonrec-term-in-term/terms)
    :short "Find the maximal and leftmost subterm of @('terms-to-try')
            that satisfies the conditions for @('nonrec<x1,...,xn>')
            described in the documentation."
    :long
    "<p>
     This is the companion function to @(tsee tailrec-find-nonrec-term),
     used to recursively process arguments of function calls.
     </p>"
    (cond ((endp terms-to-try) (mv nil nil nil))
          (t (b* (((mv found nonrec combine)
                   (tailrec-find-nonrec-term
                    combine-nonrec (car terms-to-try) r q))
                  ((when found) (mv t nonrec combine)))
               (tailrec-find-nonrec-terms
                combine-nonrec (cdr terms-to-try) r q))))))

(define tailrec-decompose-recursive-branch
  ((old-fn-name symbolp "Target function of the transformation,
                         denoted by the input @('old').")
   (rec-branch pseudo-termp
               "Recursive branch of the target function,
                namely the term @('combine<nonrec<x1,...,xn>,
                                           (old update-x1<x1,...,xn>
                                                ...
                                                update-xn<x1,...,xn>)>')
                described in the documentation.")
   (ctx "Context for errors.")
   state)
  :returns (mv (erp "@(tsee booleanp) flag of the
                     <see topic='@(url acl2::error-triple)'>error
                     triple</see>.")
               (result "A tuple @('(nonrec<x1,...,xn>
                                    (... update-xi<x1...,xn> ...)
                                    combine<q,r>
                                    q
                                    r)'),
                        whose components are described in the documentation,
                        satisfying
                        @('(typed-tuplep pseudo-termp
                                         pseudo-term-listp
                                         pseudo-termp
                                         symbolp
                                         symbolp
                                         result)').")
               state)
  :mode :program
  :short "Decompose the recursive branch of the target function
          into its components,
          as described in the documentation."
  (b* ((rec-calls (all-calls (list old-fn-name) rec-branch nil nil))
       (rec-calls (remove-duplicates-equal rec-calls))
       ((when (/= (len rec-calls) 1))
        (er-soft+ ctx t nil
                  "After translation and LET expansion, ~
                   the recursive branch ~x0 of the target function ~x1 ~
                   must not contain different calls to ~x1."
                  rec-branch old-fn-name))
       (rec-call (car rec-calls))
       ((when (equal rec-call rec-branch))
        (er-soft+ ctx t nil
                  "The target function ~x0 is already tail-recursive."
                  old-fn-name))
       (updates (fargs rec-call))
       (formals (formals old-fn-name (w state)))
       (r (genvar old-fn-name "R" nil formals))
       (q (genvar old-fn-name "Q" nil formals))
       (combine-nonrec (subst-expr r rec-call rec-branch))
       ((er &) (ensure-term-does-not-call$
                combine-nonrec
                'if
                (msg "After translation and LET expansion, ~
                      and after replacing the calls to ~x0 ~
                      with a fresh variable ~x1, ~
                      the recursive branch ~x2 of the target function ~x0"
                     old-fn-name r combine-nonrec)
                t nil))
       ((mv found nonrec combine)
        (tailrec-find-nonrec-term combine-nonrec combine-nonrec r q))
       ((unless found)
        (er-soft+ ctx t nil
                  "Unable to decompose the recursive branch ~x0 ~
                   of the target function ~x1." rec-branch old-fn-name)))
    (value (list nonrec updates combine q r))))

(define tailrec-check-old
  ((old "Input to the transformation.")
   (variant "Input to the transformation.")
   (verify-guards "Input to the transformation.")
   (verbose booleanp "Print informative messages or not.")
   (ctx "Context for errors.")
   state)
  :returns (mv (erp "@(tsee booleanp) flag of the
                     <see topic='@(url acl2::error-triple)'>error
                     triple</see>.")
               (result "A tuple @('(old-fn-name
                                    test<x1,...,xn>
                                    base<x1,...,xn>
                                    nonrec<x1,...,xn>
                                    (... update-xi<x1...,xn> ...)
                                    combine<q,r>
                                    q
                                    r)'),
                        satisfying
                        @('(typed-tuplep symbolp
                                         pseudo-termp
                                         pseudo-termp
                                         pseudo-termp
                                         pseudo-term-listp
                                         pseudo-termp
                                         symbolp
                                         symbolp
                                         result)'),
                        where @('old-fn-name') is the name
                        of the target function of the transformation
                        (denoted by the @('old') input)
                        and the other components
                        are described in the documentation.")
               state)
  :mode :program
  :short "Ensure that the @('old') input to the transformation is valid."
  :long
  "<p>
   Show the components of the function denoted by @('old')
   if @('verbose') is @('t').
   </p>"
  (b* ((wrld (w state))
       ((er old-fn-name) (ensure-function-name-or-numbered-wildcard$
                          old "The first input" t nil))
       (description (msg "The target function ~x0" old-fn-name))
       ((er &) (ensure-function-logic-mode$ old-fn-name description t nil))
       ((er &) (ensure-function-defined$ old-fn-name description t nil))
       ((er &) (ensure-function-number-of-results$ old-fn-name 1
                                                   description t nil))
       ((er &) (ensure-function-no-stobjs$ old-fn-name description t nil))
       ((er &) (ensure-function-singly-recursive$ old-fn-name
                                                  description t nil))
       ((er &) (ensure-function-known-measure$ old-fn-name description t nil))
       (body (if (non-executablep old-fn-name wrld)
                 (unwrapped-nonexec-body old-fn-name wrld)
               (ubody old-fn-name wrld)))
       (body (remove-lambdas body))
       ((er (list test base combine-nonrec-reccall))
        (ensure-term-if-call$ body
                              (msg "After translation and LET expansion, ~
                                    the body ~x0 of the target function ~x1"
                                   body old-fn-name)
                              t nil))
       ((er &) (ensure-term-does-not-call$
                test old-fn-name
                (msg "After translation and LET expansion, ~
                      the exit test ~x0 ~
                      of the target function ~x1"
                     test old-fn-name)
                t nil))
       ((er &) (ensure-term-does-not-call$
                base old-fn-name
                (msg "After translation and LET expansion, ~
                      the first branch ~x0 ~
                      of the target function ~x1"
                     base old-fn-name)
                t nil))
       ((er &) (if (member-eq variant '(:monoid :monoid-alt))
                   (ensure-term-ground$
                    base
                    (msg "Since the :VARIANT input is ~s0~x1, ~
                          after translation and LET expansion, ~
                          the first branch ~x2 ~
                          of the target function ~x3"
                         (if (eq variant :monoid)
                             "(perhaps by default) "
                           "")
                         variant
                         base
                         old-fn-name)
                    t nil)
                 (value nil)))
       ((er (list nonrec updates combine q r))
        (tailrec-decompose-recursive-branch
         old-fn-name combine-nonrec-reccall ctx state))
       ((er &) (if (eq verify-guards t)
                   (ensure-function-guard-verified$
                    old-fn-name
                    (msg "Since the :VERIFY-GUARDS input is T, ~
                          the target function ~x0" old-fn-name)
                    t nil)
                 (value nil)))
       ((run-when verbose)
        (cw "~%")
        (cw "Components of the target function ~x0:~%" old-fn-name)
        (cw "- Exit test: ~x0.~%" (untranslate test nil wrld))
        (cw "- Base value: ~x0.~%" (untranslate base nil wrld))
        (cw "- Non-recursive computation: ~x0.~%" (untranslate nonrec nil wrld))
        (cw "- Argument updates: ~x0.~%" (untranslate-lst updates nil wrld))
        (cw "- Combination operator: ~x0.~%" (untranslate combine nil wrld))
        (cw "- Fresh variable for non-recursive computation: ~x0.~%" q)
        (cw "- Fresh variable for recursive call: ~x0.~%" r)))
    (value (list old-fn-name test base nonrec updates combine q r))))

(std::defenum tailrec-variantp (:assoc :monoid :monoid-alt)
  :short "Variants of the tail recursion transformation.")

(def-error-checker tailrec-check-variant
  ((variant "Input to the transformation."))
  "Ensure that the @('variant') input to the transformation is valid."
  (((tailrec-variantp variant)
    "~@0 must be :MONOID, :MONOID-ALT, or :ASSOC." description)))

(define tailrec-infer-domain
  ((combine pseudo-termp "Result of @(tsee tailrec-check-old).")
   (q symbolp "Result of @(tsee tailrec-check-inputs).")
   (r symbolp "Result of @(tsee tailrec-check-inputs).")
   (variant tailrec-variantp "Input to the trasformation, after validation.")
   (verbose booleanp "Print informative messages or not.")
   (wrld plist-worldp))
  :returns (domain "A @(tsee pseudo-termfnp).")
  :verify-guards nil
  :short "Infer the domain over which some applicability conditions must hold."
  :long
  "<p>
   This is used when the @(':domain') input is @(':auto').
   A domain is inferred as described in the documentation.
   </p>"
  (b* ((default '(lambda (x) 't))
       (domain
        (if (member-eq variant '(:monoid :monoid-alt))
            (case-match combine
              ((op . args)
               (b* (((unless (symbolp op)) default)
                    ((unless (or (equal args (list q r))
                                 (equal args (list r q))))
                     default)
                    ((list y1 y2) (formals op wrld))
                    (guard (uguard op wrld)))
                 (case-match guard
                   (('if (dom must-be-y1) (dom must-be-y2) *nil*)
                    (if (and (eq must-be-y1 y1)
                             (eq must-be-y2 y2))
                        dom
                      default))
                   (& default))))
              (& default))
          default))
       ((run-when verbose)
        (cw "~%")
        (cw "Inferred domain for the applicability conditions: ~x0.~%" domain)))
    domain))

(define tailrec-check-domain
  ((domain "Input to the transformation.")
   (old-fn-name symbolp "Result of @(tsee tailrec-check-old).")
   (combine pseudo-termp "Result of @(tsee tailrec-check-old).")
   (q symbolp "Result of @(tsee tailrec-check-inputs).")
   (r symbolp "Result of @(tsee tailrec-check-inputs).")
   (variant tailrec-variantp "Input to the trasformation, after validation.")
   (do-verify-guards booleanp
                     "Result of validating
                      the @(':verify-guards') input to the transformation
                      (in @(tsee tailrec-check-inputs)).")
   (verbose booleanp "Print informative messages or not.")
   (ctx "Context for errors.")
   state)
  :returns (mv (erp "@(tsee booleanp) flag of the
                     <see topic='@(url acl2::error-triple)'>error
                     triple</see>.")
               (domain$ "A @(tsee pseudo-termfnp) that is
                         the predicate denoted by @('domain').")
               state)
  :mode :program
  :short "Ensure that the @(':domain') input to the transformation is valid."
  :long
  "<p>
   If successful, return:
   the input itself, if it is a function name;
   the translated lambda expression denoted by the input,
   if the input is a macro name;
   the translation of the input,
   if the input is a lambda expression;
   the inferred function name
   or the default translated lambda expression that holds for every value,
   if the input is @(':auto').
   </p>"
  (b* ((wrld (w state))
       ((when (eq domain :auto))
        (value (tailrec-infer-domain combine q r variant verbose wrld)))
       (description "The :DOMAIN input")
       ((er (list fn/lambda stobjs-in stobjs-out description))
        (cond ((function-namep domain wrld)
               (value (list domain
                            (stobjs-in domain wrld)
                            (stobjs-out domain wrld)
                            (msg "~@0, which is the function ~x1,"
                                 description domain))))
              ((macro-namep domain wrld)
               (b* ((args (macro-required-args domain wrld))
                    (ulambda `(lambda ,args (,domain ,@args)))
                    ((mv tlambda stobjs-out) (check-user-lambda ulambda wrld))
                    (stobjs-in (compute-stobj-flags args t wrld)))
                 (value
                  (list tlambda
                        stobjs-in
                        stobjs-out
                        (msg "~@0, which is the lambda expression ~x1 ~
                              denoted by the macro ~x2,"
                             description ulambda domain)))))
              ((symbolp domain)
               (er-soft+ ctx t nil "~@0 must be :AUTO, ~
                                    a function name, ~
                                    a macro name, ~
                                    or a lambda expression.  ~
                                    The symbol ~x1 is not :AUTO or ~
                                    the name of a function or macro."
                         description domain))
              (t (b* (((mv tlambda/msg stobjs-out)
                       (check-user-lambda domain wrld))
                      ((when (msgp tlambda/msg))
                       (er-soft+ ctx t nil
                                 "~@0 must be :AUTO, ~
                                  a function name, ~
                                  a macro name, ~
                                  or a lambda expression.  ~
                                  Since ~x1 is not a symbol, ~
                                  it must be a lambda expression.  ~
                                  ~@2"
                                 description domain tlambda/msg))
                      (tlambda tlambda/msg)
                      (stobjs-in
                       (compute-stobj-flags (lambda-formals tlambda) t wrld)))
                   (value (list tlambda
                                stobjs-in
                                stobjs-out
                                (msg "~@0, which is the lambda expression ~x1,"
                                     description domain)))))))
       ((er &) (ensure-function/lambda-logic-mode$ fn/lambda description t nil))
       ((er &) (ensure-function/lambda-arity$ stobjs-in 1 description t nil))
       ((er &) (ensure-function/lambda/term-number-of-results$ stobjs-out 1
                                                               description
                                                               t nil))
       ((er &) (ensure-function/lambda-no-stobjs$ stobjs-in
                                                  stobjs-out
                                                  description t nil))
       ((er &) (ensure-function/lambda-closed$ fn/lambda description t nil))
       ((er &) (if do-verify-guards
                   (ensure-function/lambda-guard-verified-exec-fns$
                    fn/lambda
                    (msg "Since either the :VERIFY-GUARDS input is T, ~
                          or it is (perhaps by default) :AUTO ~
                          and the target function ~x0 is guard-verified, ~@1"
                         old-fn-name (msg-downcase-first description))
                    t nil)
                 (value nil)))
       ((er &) (if (symbolp fn/lambda)
                   (ensure-symbol-different$ fn/lambda
                                             old-fn-name
                                             (msg "the target function ~x0"
                                                  old-fn-name)
                                             description t nil)
                 (ensure-term-does-not-call$ (lambda-body fn/lambda)
                                             old-fn-name
                                             description t nil))))
    (value fn/lambda)))

(define tailrec-check-new-name
  ((new-name "Input to the transformation.")
   (old-fn-name symbolp "Result of @(tsee tailrec-check-old).")
   (ctx "Context for errors.")
   state)
  :returns (mv (erp "@(tsee booleanp) flag of the
                     <see topic='@(url acl2::error-triple)'>error
                     triple</see>.")
               (new-fn-name "A @(tsee symbolp)
                             to use as the name for the new function.")
               state)
  :mode :program
  :short "Ensure that the @(':new-name') input to the transformation is valid."
  (b* (((er &) (ensure-symbol$ new-name "The :NEW-NAME input" t nil))
       (name (if (eq new-name :auto)
                 (next-numbered-name old-fn-name (w state))
               new-name))
       (description (msg "The name ~x0 of the new function, ~@1,"
                         name
                         (if (eq new-name :auto)
                             "automatically generated ~
                              since the :NEW-NAME input ~
                              is (perhaps by default) :AUTO"
                           "supplied as the :NEW-NAME input")))
       ((er &) (ensure-symbol-new-event-name$ name description t nil)))
    (value name)))

(define tailrec-check-wrapper-name
  ((wrapper-name "Input to the transformation.")
   (new-fn-name symbolp "Result of @(tsee tailrec-check-new-name).")
   (ctx "Context for errors.")
   state)
  :returns (mv (erp "@(tsee booleanp) flag of the
                     <see topic='@(url acl2::error-triple)'>error
                     triple</see>.")
               (wrapper-fn-name "A @(tsee symbolp)
                                 to use as the name for the wrapper function.")
               state)
  :mode :program
  :short "Ensure that the @(':wrapper-name') input to the transformation
          is valid."
  (b* (((er &) (ensure-symbol$ wrapper-name "The :WRAPPER-NAME input" t nil))
       (name (if (eq wrapper-name :auto)
                 (add-suffix-to-fn new-fn-name "-WRAPPER")
               wrapper-name))
       (description (msg "The name ~x0 of the wrapper function, ~@1,"
                         name
                         (if (eq wrapper-name :auto)
                             "automatically generated ~
                              since the :WRAPPER-NAME input ~
                              is (perhaps by default) :AUTO"
                           "supplied as the :WRAPPER-NAME input")))
       ((er &) (ensure-symbol-new-event-name$ name description t nil))
       ((er &) (ensure-symbol-different$
                name new-fn-name
                (msg "the name ~x0 of the new function ~
                      (determined by the :NEW-NAME input)." new-fn-name)
                description
                t nil)))
    (value name)))

(define tailrec-check-thm-name
  ((thm-name "Input to the transformation.")
   (old-fn-name symbolp "Result of @(tsee tailrec-check-old).")
   (new-fn-name symbolp "Result of @(tsee tailrec-check-new-name).")
   (wrapper-fn-name symbolp "Result of @(tsee tailrec-check-wrapper-name).")
   (ctx "Context for errors.")
   state)
  :returns (mv (erp "@(tsee booleanp) flag of the
                     <see topic='@(url acl2::error-triple)'>error
                     triple</see>.")
               (old-to-wrapper-thm-name "A @(tsee symbolp)
                                         to use for the theorem that
                                         relates the old and new functions.")
               state)
  :mode :program
  :short "Ensure that the @(':thm-name') input to the transformation
          is valid."
  (b* (((er &) (ensure-symbol$ thm-name "The :THM-NAME input" t nil))
       (name (if (eq thm-name :auto)
                 (make-paired-name old-fn-name wrapper-fn-name 2 (w state))
               thm-name))
       (description (msg "The name ~x0 of the theorem ~
                          that relates the target function ~x1 ~
                          to the wrapper function ~x2 ~
                          ~@3,"
                         name old-fn-name wrapper-fn-name
                         (if (eq thm-name :auto)
                             "automatically generated ~
                              since the :THM-NAME input ~
                              is (perhaps by default) :AUTO"
                           "supplied as the :THM-NAME input")))
       ((er &) (ensure-symbol-new-event-name$ name description t nil))
       ((er &) (ensure-symbol-different$
                name new-fn-name
                (msg "the name ~x0 of the new function ~
                      (determined by the :NEW-NAME input)." new-fn-name)
                description
                t nil))
       ((er &) (ensure-symbol-different$
                name wrapper-fn-name
                (msg "the name ~x0 of the wrapper function ~
                      (determined by the :WRAPPER-NAME input)." wrapper-fn-name)
                description
                t nil)))
    (value name)))

(defval *tailrec-app-cond-names*
  :short "Names of all the applicability conditions."
  '(:domain-of-base
    :domain-of-nonrec
    :domain-of-combine
    :domain-of-combine-uncond
    :combine-associativity
    :combine-associativity-uncond
    :combine-left-identity
    :combine-right-identity
    :domain-guard
    :combine-guard
    :domain-of-nonrec-when-guard)
  ///

  (defruled symbol-listp-of-*tailrec-app-cond-names*
    (symbol-listp *tailrec-app-cond-names*))

  (defruled no-duplicatesp-eq-of-*tailrec-app-cond-names*
    (no-duplicatesp-eq *tailrec-app-cond-names*)))

(define tailrec-check-hints
  ((hints "Input to the transformation.")
   (ctx "Context for errors.")
   state)
  :returns (mv (erp "@(tsee booleanp) flag of the
                     <see topic='@(url acl2::error-triple)'>error
                     triple</see>.")
               (hints-alist "A @('symbol-alistp') that is the alist form of
                             the keyword-value list @('hints').")
               state)
  :mode :program
  :short "Ensure that the @(':hints') input to the transformation is valid."
  :long
  "<p>
   Here we only check that the input is a keyword-value list
   whose keywords are unique and include only names of applicability conditions.
   The values of the keyword-value list
   are checked to be well-formed hints not here,
   but implicitly when attempting to prove the applicability conditions.
   </p>"
  (b* (((er &) (ensure-keyword-value-list$ hints "The :HINTS input" t nil))
       (alist (keyword-value-list-to-alist hints))
       (keys (strip-cars alist))
       (description
        (msg "The list ~x0 of keywords of the :HINTS input" keys))
       ((er &) (ensure-list-no-duplicates$ keys description t nil))
       ((er &) (ensure-list-subset$ keys *tailrec-app-cond-names*
                                    description t nil)))
    (value alist)))

(define tailrec-check-inputs ((old "Input to the transformation.")
                              (variant "Input to the transformation.")
                              (domain "Input to the transformation.")
                              (new-name "Input to the transformation.")
                              (new-enable "Input to the transformation.")
                              (wrapper-name "Input to the transformation.")
                              (wrapper-enable "Input to the transformation.")
                              (thm-name "Input to the transformation.")
                              (thm-enable "Input to the transformation.")
                              (non-executable "Input to the transformation.")
                              (verify-guards "Input to the transformation.")
                              (hints "Input to the transformation.")
                              (print "Input to the transformation.")
                              (show-only "Input to the transformation.")
                              (ctx "Context for errors.")
                              state)
  :returns (mv (erp "@(tsee booleanp) flag of the
                     <see topic='@(url acl2::error-triple)'>error
                     triple</see>.")
               (result "A tuple @('(old-fn-name
                                    test<x1,...,xn>
                                    base<x1,...,xn>
                                    nonrec<x1,...,xn>
                                    (... update-xi<x1...,xn> ...)
                                    combine<q,r>
                                    q
                                    r
                                    domain$
                                    new-fn-name
                                    new-fn-enable
                                    wrapper-fn-name
                                    old-to-wrapper-thm-name
                                    make-non-executable
                                    do-verify-guards
                                    hints-alist
                                    print$)')
                        satisfying
                        @('(typed-tuplep symbolp
                                         pseudo-termp
                                         pseudo-termp
                                         pseudo-termp
                                         pseudo-term-listp
                                         pseudo-termp
                                         symbolp
                                         symbolp
                                         pseudo-termfnp
                                         symbolp
                                         booleanp
                                         symbolp
                                         symbolp
                                         booleanp
                                         booleanp
                                         symbol-alistp
                                         canonical-print-specifier-p
                                         result)'),
                        where the first 8 components are
                        the results of @(tsee tailrec-check-old),
                        @('domain$') is
                        the result of @(tsee tailrec-check-domain),
                        @('new-fn-name') is
                        the result of @(tsee tailrec-check-new-name),
                        @('new-fn-enable') indicates whether
                        the new function should be enabled or not,
                        @('wrapper-fn-name') is
                        the result of @(tsee tailrec-check-wrapper-name),
                        @('old-to-wrapper-thm-name') is
                        the result of @(tsee tailrec-check-thm-name),
                        @('non-executable') indicates whether
                        the new and wrapper functions should be
                        non-executable or not, and
                        @('do-verify-guards') indicates whether the guards of
                        the new and wrapper functions
                        should be verified or not,
                        @('hints-alist') is
                        the result of @(tsee tailrec-check-hints), and
                        @('print$') is a canonicalized version of
                        the @(':print') input.")
               state)
  :mode :program
  :short "Ensure that all the inputs to the transformation are valid."
  :long
  "<p>
   The inputs are validated
   in the order in which they appear in the documentation,
   except that @(':print') is validated just before @('old')
   so that the @('verbose') argument of @(tsee tailrec-check-old)
   can be computed from @(':print'),
   and except that @(':verify-guards') is validated just before @('domain')
   because the result of validating @(':verify-guards')
   is used to validate @('domain').
   @('old') is validated before @(':verify-guards')
   because the result of validating @('old')
   is used to validate @(':verify-guards').
   @(':verify-guards') is also used to validate @('old'),
   but it is only tested for equality with @('t')
   (see @(tsee tailrec-check-old)).
   </p>"
  (b* (((er print$) (ensure-is-print-specifier$ print "The :PRINT input" t nil))
       (verbose (if (member-eq :expand print$) t nil))
       ((er (list old-fn-name
                  test
                  base
                  nonrec
                  updates
                  combine
                  q
                  r)) (tailrec-check-old old variant verify-guards
                                         verbose ctx state))
       ((er &) (tailrec-check-variant$ variant "The :VARIANT input" t nil))
       ((er do-verify-guards) (ensure-boolean-or-auto-and-return-boolean$
                               verify-guards
                               (guard-verified-p old-fn-name (w state))
                               "The :VERIFY-GUARDS input" t nil))
       ((er domain$) (tailrec-check-domain
                      domain old-fn-name combine q r variant do-verify-guards
                      verbose ctx state))
       ((er new-fn-name) (tailrec-check-new-name
                          new-name old-fn-name ctx state))
       ((er new-fn-enable) (ensure-boolean-or-auto-and-return-boolean$
                            new-enable
                            (fundef-enabledp old state)
                            "The :NEW-ENABLE input" t nil))
       ((er wrapper-fn-name) (tailrec-check-wrapper-name
                              wrapper-name new-fn-name ctx state))
       ((er &) (ensure-boolean$ wrapper-enable
                                "The :WRAPPER-ENABLE input" t nil))
       ((er old-to-wrapper-thm-name) (tailrec-check-thm-name
                                      thm-name
                                      old-fn-name new-fn-name wrapper-fn-name
                                      ctx state))
       ((er &) (ensure-boolean$ thm-enable "The :THM-ENABLE input" t nil))
       ((er make-non-executable) (ensure-boolean-or-auto-and-return-boolean$
                                  non-executable
                                  (non-executablep old (w state))
                                  "The :NON-EXECUTABLE input" t nil))
       ((er hints-alist) (tailrec-check-hints hints ctx state))
       ((er &) (ensure-boolean$ show-only "The :SHOW-ONLY input" t nil)))
    (value (list old-fn-name
                 test
                 base
                 nonrec
                 updates
                 combine
                 q
                 r
                 domain$
                 new-fn-name
                 new-fn-enable
                 wrapper-fn-name
                 old-to-wrapper-thm-name
                 make-non-executable
                 do-verify-guards
                 hints-alist
                 print$))))

(define tailrec-var-u
  ((old-fn-name symbolp "Result of @(tsee tailrec-check-inputs)."))
  :returns (u "A @(tsee symbolp).")
  :mode :program
  :short "The variable @('u') to use in the
          @(':domain-of-combine'),
          @(':domain-of-combine-uncond'),
          @(':combine-associativity'), and
          @(':combine-associativity-uncond')
          applicability conditions."
  (genvar old-fn-name "U" nil nil))

(define tailrec-var-v
  ((old-fn-name symbolp "Result of @(tsee tailrec-check-inputs)."))
  :returns (v "A @(tsee symbolp).")
  :mode :program
  :short "The variable @('u') to use in the
          @(':domain-of-combine'),
          @(':domain-of-combine-uncond'),
          @(':combine-associativity'), and
          @(':combine-associativity-uncond')
          applicability conditions."
  (genvar old-fn-name "V" nil nil))

(define tailrec-var-w
  ((old-fn-name symbolp "Result of @(tsee tailrec-check-inputs)."))
  :returns (w "A @(tsee symbolp).")
  :mode :program
  :short "The variable @('u') to use in the
          @(':combine-associativity') and
          @(':combine-associativity-uncond')
          applicability conditions."
  (genvar old-fn-name "W" nil nil))

(define tailrec-id-var-u
  ((old-fn-name symbolp "Result of @(tsee tailrec-check-inputs).")
   (wrld plist-worldp))
  :returns (u "A @(tsee symbolp).")
  :mode :program
  :short "The variable @('u') to use in the
          @(':combine-left-identity') and
          @(':combine-right-identity')
          applicability conditions."
  :long
  "<p>
   This must be distinct from the formals of the old function.
   </p>"
  (genvar old-fn-name "U" nil (formals old-fn-name wrld)))

(define tailrec-combine-op
  ((combine pseudo-termp "Result of @(tsee tailrec-check-inputs).")
   (q symbolp "Result of @(tsee tailrec-check-inputs).")
   (r symbolp "Result of @(tsee tailrec-check-inputs)."))
  :returns (combine-op pseudo-lambdap
                       :hyp :guard
                       :hints (("Goal" :in-theory (enable pseudo-lambdap))))
  :short "Combination operator."
  :long
  "<p>
   This is obtained by abstracting @('combine<q,r>') over @('q') and @('r').
   </p>"
  (make-lambda (list q r) combine))

(define tailrec-app-cond-formula
  ((name (member-eq name *tailrec-app-cond-names*)
         "Name of the applicability condition.")
   (old-fn-name symbolp "Result of @(tsee tailrec-check-inputs).")
   (test pseudo-termp "Result of @(tsee tailrec-check-inputs).")
   (base pseudo-termp "Result of @(tsee tailrec-check-inputs).")
   (nonrec pseudo-termp "Result of @(tsee tailrec-check-inputs).")
   (combine pseudo-termp "Result of @(tsee tailrec-check-inputs).")
   (q symbolp "Result of @(tsee tailrec-check-inputs).")
   (r symbolp "Result of @(tsee tailrec-check-inputs).")
   (domain$ pseudo-termfnp "Result of @(tsee tailrec-check-inputs).")
   state)
  :returns (formula "An untranslated term.")
  :mode :program
  :short "Formula of the named applicability condition."
  (b* ((wrld (w state))
       (u (tailrec-var-u old-fn-name))
       (v (tailrec-var-v old-fn-name))
       (w (tailrec-var-w old-fn-name))
       (u1 (tailrec-id-var-u old-fn-name wrld))
       (combine-op (tailrec-combine-op combine q r)))
    (case name
      (:domain-of-base
       (untranslate (implicate test
                               (apply-term* domain$ base))
                    t wrld))
      (:domain-of-nonrec
       (untranslate (implicate (dumb-negate-lit test)
                               (apply-term* domain$ nonrec))
                    t wrld))
      (:domain-of-combine
       (untranslate (implicate (conjoin2 (apply-term* domain$ u)
                                         (apply-term* domain$ v))
                               (apply-term* domain$
                                            (apply-term* combine-op u v)))
                    t wrld))
      (:domain-of-combine-uncond
       (untranslate (apply-term* domain$
                                 (apply-term* combine-op u v))
                    t wrld))
      (:combine-associativity
       (untranslate (implicate
                     (conjoin (list (apply-term* domain$ u)
                                    (apply-term* domain$ v)
                                    (apply-term* domain$ w)))
                     `(equal ,(apply-term* combine-op
                                           u
                                           (apply-term* combine-op v w))
                             ,(apply-term* combine-op
                                           (apply-term* combine-op u v)
                                           w)))
                    t wrld))
      (:combine-associativity-uncond
       (untranslate `(equal ,(apply-term* combine-op
                                          u
                                          (apply-term* combine-op v w))
                            ,(apply-term* combine-op
                                          (apply-term* combine-op u v)
                                          w))
                    t wrld))
      (:combine-left-identity
       (untranslate (implicate (conjoin2 test
                                         (apply-term* domain$ u1))
                               `(equal ,(apply-term* combine-op base u1)
                                       ,u1))
                    t wrld))
      (:combine-right-identity
       (untranslate (implicate (conjoin2 test
                                         (apply-term* domain$ u1))
                               `(equal ,(apply-term* combine-op u1 base)
                                       ,u1))
                    t wrld))
      (:domain-guard
       (if (symbolp domain$)
           (untranslate (guard domain$ nil wrld)
                        t wrld)
         (untranslate (term-guard-obligation (lambda-body domain$) state)
                      t wrld)))
      (:combine-guard
       (untranslate (implicate (conjoin2 (apply-term* domain$ q)
                                         (apply-term* domain$ r))
                               (term-guard-obligation combine state))
                    t wrld))
      (:domain-of-nonrec-when-guard
       (untranslate (implicate (conjoin2 (guard old-fn-name nil wrld)
                                         (dumb-negate-lit test))
                               (apply-term* domain$ nonrec))
                    t wrld))
      (t (impossible)))))

(define tailrec-app-cond-present-p
  ((name (member-eq name *tailrec-app-cond-names*)
         "Name of the applicability condition.")
   (variant tailrec-variantp "Input to the trasformation, after validation.")
   (do-verify-guards booleanp "Result of @(tsee tailrec-check-inputs)."))
  :returns (yes/no booleanp :hyp (booleanp do-verify-guards))
  :short "Check if the named applicability condition is present."
  (case name
    (:domain-of-base t)
    ((:domain-of-nonrec
      :domain-of-combine
      :combine-associativity) (if (member-eq variant '(:monoid :assoc)) t nil))
    ((:domain-of-combine-uncond
      :combine-associativity-uncond) (eq variant :monoid-alt))
    ((:combine-left-identity
      :combine-right-identity) (if (member-eq variant '(:monoid :monoid-alt))
                                   t nil))
    ((:domain-guard
      :combine-guard) do-verify-guards)
    (:domain-of-nonrec-when-guard (and (eq variant :monoid-alt)
                                       do-verify-guards))
    (t (impossible))))

(define tailrec-app-conds
  ((old-fn-name symbolp "Result of @(tsee tailrec-check-inputs).")
   (test pseudo-termp "Result of @(tsee tailrec-check-inputs).")
   (base pseudo-termp "Result of @(tsee tailrec-check-inputs).")
   (nonrec pseudo-termp "Result of @(tsee tailrec-check-inputs).")
   (combine pseudo-termp "Result of @(tsee tailrec-check-inputs).")
   (q symbolp "Result of @(tsee tailrec-check-inputs).")
   (r symbolp "Result of @(tsee tailrec-check-inputs).")
   (variant tailrec-variantp "Input to the trasformation, after validation.")
   (domain$ pseudo-termfnp "Result of @(tsee tailrec-check-inputs).")
   (do-verify-guards booleanp "Result of @(tsee tailrec-check-inputs).")
   state)
  :returns (app-conds "A @(tsee symbol-alistp).")
  :mode :program
  :short "Generate the applicability conditions that must hold."
  (tailrec-app-conds-aux *tailrec-app-cond-names*
                         old-fn-name test base nonrec combine q r
                         variant domain$ do-verify-guards
                         nil state)

  :prepwork
  ((define tailrec-app-conds-aux
     ((names (subsetp-eq names *tailrec-app-cond-names*))
      (old-fn-name symbolp)
      (test pseudo-termp)
      (base pseudo-termp)
      (nonrec pseudo-termp)
      (combine pseudo-termp)
      (q symbolp)
      (r symbolp)
      (variant tailrec-variantp)
      (domain$ pseudo-termfnp)
      (do-verify-guards booleanp)
      (rev-app-conds symbol-alistp)
      state)
     :returns (app-conds) ; SYMBOL-LISTP
     :mode :program
     :parents nil
     (if (endp names)
         (reverse rev-app-conds)
       (b* ((name (car names))
            ((unless (tailrec-app-cond-present-p
                      name variant do-verify-guards))
             (tailrec-app-conds-aux (cdr names)
                                    old-fn-name
                                    test base nonrec combine q r
                                    variant domain$ do-verify-guards
                                    rev-app-conds state))
            (formula (tailrec-app-cond-formula
                      name
                      old-fn-name test base nonrec combine q r domain$
                      state)))
         (tailrec-app-conds-aux (cdr names)
                                old-fn-name test base nonrec combine q r
                                variant domain$ do-verify-guards
                                (acons name formula rev-app-conds)
                                state))))))

(define tailrec-domain-of-old-intro-event
  ((old-fn-name symbolp "Result of @(tsee tailrec-check-inputs).")
   (test pseudo-termp "Result of @(tsee tailrec-check-inputs).")
   (nonrec pseudo-termp "Result of @(tsee tailrec-check-inputs).")
   (updates pseudo-term-listp "Result of @(tsee tailrec-check-inputs).")
   (variant tailrec-variantp "Input to the trasformation, after validation.")
   (domain$ pseudo-termfnp "Result of @(tsee tailrec-check-inputs).")
   (names-to-avoid symbol-listp "Names of other events
                                 (calculated in @(tsee tailrec-event)).")
   (app-cond-thm-names symbol-symbol-alistp
                       "Map from the names of the applicability conditions
                        to the corresponding theorems
                        (calculated in @(tsee tailrec-event)).")
   (old-fn-unnorm-name symbolp "Name of the theorem that installs
                                the non-normalized definition
                                of the old function.")
   (wrld plist-worldp))
  :returns (mv (domain-of-old-thm-event "A @(tsee pseudo-event-formp).")
               (domain-of-old-thm-name "A @(tsee symbolp)
                                        that names the theorem."))
  :mode :program
  :short "Event form for the theorem asserting that
          the old function always yields values in the domain
          (@($D{}f$) in the design notes)."
  :long
  "<p>
   The theorem's formula is @('(domain (old x1 ... xn))').
   This is just @('t') if @('domain') is @('(lambda (x) t)') (e.g. as default).
   </p>
   <p>
   The hints follow the proofs in the design notes.
   </p>
   <p>
   This theorem event
   is local to the @(tsee encapsulate) generated by the transformation,
   because it is a lemma used to prove the exported main theorem.
   </p>"
  (b* ((name (fresh-name-in-world-with-$s 'domain-of-old names-to-avoid wrld))
       (formula (untranslate (apply-term* domain$
                                          (apply-term old-fn-name
                                                      (formals old-fn-name
                                                               wrld)))
                             t wrld))
       (hints
        (case variant
          ((:monoid :assoc)
           (b* ((domain-of-base-thm
                 (cdr (assoc-eq :domain-of-base app-cond-thm-names)))
                (domain-of-nonrec-thm
                 (cdr (assoc-eq :domain-of-nonrec app-cond-thm-names)))
                (domain-of-combine-thm
                 (cdr (assoc-eq :domain-of-combine app-cond-thm-names)))
                (domain-of-combine-instance
                 `(:instance ,domain-of-combine-thm
                             :extra-bindings-ok
                             (,(tailrec-var-u old-fn-name)
                              ,nonrec)
                             (,(tailrec-var-v old-fn-name)
                              (,old-fn-name ,@updates)))))
             `(("Goal"
                :in-theory '(,old-fn-unnorm-name
                             (:induction ,old-fn-name))
                :induct (,old-fn-name ,@(formals old-fn-name wrld)))
               '(:use (,domain-of-base-thm
                       ,domain-of-nonrec-thm
                       ,domain-of-combine-instance)))))
          (:monoid-alt
           (b* ((domain-of-base-thm
                 (cdr (assoc-eq :domain-of-base app-cond-thm-names)))
                (domain-of-combine-uncond-thm
                 (cdr (assoc-eq :domain-of-combine-uncond app-cond-thm-names)))
                (domain-of-combine-uncond-instance
                 `(:instance ,domain-of-combine-uncond-thm
                             :extra-bindings-ok
                             (,(tailrec-var-u old-fn-name)
                              ,nonrec)
                             (,(tailrec-var-v old-fn-name)
                              (,old-fn-name ,@updates)))))
             `(("Goal"
                :in-theory '(,old-fn-unnorm-name)
                :cases (,test))
               '(:use (,domain-of-base-thm
                       ,domain-of-combine-uncond-instance)))))
          (t (impossible))))
       (event `(local (defthm ,name
                        ,formula
                        :rule-classes nil
                        :hints ,hints))))
    (mv event name)))

(define tailrec-new-fn-intro-events
  ((old-fn-name symbolp "Result of @(tsee tailrec-check-inputs).")
   (test pseudo-termp "Result of @(tsee tailrec-check-inputs).")
   (base pseudo-termp "Result of @(tsee tailrec-check-inputs).")
   (nonrec pseudo-termp "Result of @(tsee tailrec-check-inputs).")
   (updates pseudo-term-listp "Result of @(tsee tailrec-check-inputs).")
   (combine pseudo-termp "Result of @(tsee tailrec-check-inputs).")
   (q symbolp "Result of @(tsee tailrec-check-inputs).")
   (r symbolp "Result of @(tsee tailrec-check-inputs).")
   (variant tailrec-variantp "Input to the trasformation, after validation.")
   (domain$ pseudo-termfnp "Result of @(tsee tailrec-check-inputs).")
   (new-fn-name symbolp "Result of @(tsee tailrec-check-inputs).")
   (new-fn-enable booleanp "Result of @(tsee tailrec-check-inputs).")
   (make-non-executable booleanp "Result of @(tsee tailrec-check-inputs).")
   (do-verify-guards booleanp "Result of @(tsee tailrec-check-inputs).")
   (app-cond-thm-names symbol-symbol-alistp
                       "Map from the names of the applicability conditions
                        to the corresponding theorems
                        (calculated in @(tsee tailrec-event)).")
   (wrld plist-worldp))
  :returns (mv (new-fn-local-event "A @(tsee pseudo-event-formp).")
               (new-fn-exported-event "A @(tsee pseudo-event-formp).")
               (new-fn-formals "A @(tsee symbol-listp)."))
  :mode :program
  :short "Local and exported events to introduce the new function,
          and formals of the new function."
  :long
  "<p>
   In the @(tsee encapsulate) generated by @(tsee tailrec-event),
   the new function is introduced via a local event first,
   then via a redundant non-local (i.e. exported) event.
   The local event includes the hints for the termination and guard proofs.
   The exported event has no termination or guard proof hints.
   This keeps the event history after the transformation &ldquo;clean&rdquo;,
   without implementation-specific termination and guard hints.
   </p>
   <p>
   The macro used to introduce the new function is determined by
   whether the new function must be
   enabled or not, and non-executable or not.
   </p>
   <p>
   The formals of the new function consist of
   the formals of the old function
   followed by the variable @('r') generated
   during the decomposition of the recursive branch of the old function.
   This variable is distinct from the formals of the old function
   by construction.
   </p>
   <p>
   The body of the new function is
   as described in the documentation and design notes.
   The non-recursive branch varies slightly,
   depending on the transformation's variant.
   </p>
   <p>
   The new function's well-founded relation and measure
   are the same as the old function's.
   Following the design notes,
   the termination of the new function is proved
   in the empty theory, using the termination theorem of the old function.
   </p>
   <p>
   The guard of the new function is obtained
   by conjoining the guard of the old function
   with the fact that the additional formal @('r') is in the domain,
   as described in the documentation.
   </p>
   <p>
   The guards of the new function are verified
   following the proof in the design notes.
   The facts used in the proof for the case in which right identity holds
   are a subset of those for the case in which right identity does not hold.
   We use the hints for the latter case also for the former case
   (which will ignore some of the supplied facts).
   </p>"
  (b* ((macro (function-intro-macro new-fn-enable make-non-executable))
       (formals (rcons r (formals old-fn-name wrld)))
       (body
        (b* ((combine-op (tailrec-combine-op combine q r))
             (nonrec-branch (case variant
                              ((:monoid :monoid-alt) r)
                              (:assoc (apply-term* combine-op r base))
                              (t (impossible))))
             (rec-branch (subcor-var (cons r (formals old-fn-name wrld))
                                     (cons (apply-term* combine-op r nonrec)
                                           updates)
                                     (apply-term new-fn-name formals)))
             (body `(if ,test
                        ,nonrec-branch
                      ,rec-branch)))
          (untranslate body nil wrld)))
       (wfrel (well-founded-relation old-fn-name wrld))
       (measure (untranslate (measure old-fn-name wrld) nil wrld))
       (termination-hints
        `(("Goal" :use (:termination-theorem ,old-fn-name) :in-theory nil)))
       (guard (untranslate (conjoin2 (guard old-fn-name nil wrld)
                                     (apply-term* domain$ r))
                           t wrld))
       (guard-hints
        (case variant
          ((:monoid :assoc)
           (b* ((z (car (if (symbolp domain$)
                            (formals domain$ wrld)
                          (lambda-formals domain$))))
                (domain-of-base-thm
                 (cdr (assoc-eq :domain-of-base app-cond-thm-names)))
                (domain-of-nonrec-thm
                 (cdr (assoc-eq :domain-of-nonrec app-cond-thm-names)))
                (domain-of-combine-thm
                 (cdr (assoc-eq :domain-of-combine app-cond-thm-names)))
                (domain-guard-thm
                 (cdr (assoc-eq :domain-guard app-cond-thm-names)))
                (combine-guard-thm
                 (cdr (assoc-eq :combine-guard app-cond-thm-names)))
                (domain-of-combine-instance
                 `(:instance ,domain-of-combine-thm
                             :extra-bindings-ok
                             (,(tailrec-var-u old-fn-name) ,r)
                             (,(tailrec-var-v old-fn-name) ,nonrec)))
                (domain-guard-instance
                 `(:instance ,domain-guard-thm
                             :extra-bindings-ok
                             (,z ,r)))
                (combine-guard-instance-base
                 `(:instance ,combine-guard-thm
                             :extra-bindings-ok
                             (,q ,r)
                             (,r ,base)))
                (combine-guard-instance-nonrec
                 `(:instance ,combine-guard-thm
                             :extra-bindings-ok
                             (,q ,r)
                             (,r ,nonrec))))
             `(("Goal"
                :in-theory nil
                :use ((:guard-theorem ,old-fn-name)
                      ,domain-guard-instance
                      ,domain-of-base-thm
                      ,domain-of-nonrec-thm
                      ,combine-guard-instance-base
                      ,combine-guard-instance-nonrec
                      ,domain-of-combine-instance)))))
          (:monoid-alt
           (b* ((z (car (if (symbolp domain$)
                            (formals domain$ wrld)
                          (lambda-formals domain$))))
                (domain-of-base-thm
                 (cdr (assoc-eq :domain-of-base app-cond-thm-names)))
                (domain-of-combine-uncond-thm
                 (cdr (assoc-eq :domain-of-combine-uncond app-cond-thm-names)))
                (domain-guard-thm
                 (cdr (assoc-eq :domain-guard app-cond-thm-names)))
                (combine-guard-thm
                 (cdr (assoc-eq :combine-guard app-cond-thm-names)))
                (domain-of-nonrec-when-guard-thm
                 (cdr (assoc-eq :domain-of-nonrec-when-guard
                                app-cond-thm-names)))
                (domain-of-combine-uncond-instance
                 `(:instance ,domain-of-combine-uncond-thm
                             :extra-bindings-ok
                             (,(tailrec-var-u old-fn-name) ,r)
                             (,(tailrec-var-v old-fn-name) ,nonrec)))
                (domain-guard-instance
                 `(:instance ,domain-guard-thm
                             :extra-bindings-ok
                             (,z ,r)))
                (combine-guard-instance-base
                 `(:instance ,combine-guard-thm
                             :extra-bindings-ok
                             (,q ,r)
                             (,r ,base)))
                (combine-guard-instance-nonrec
                 `(:instance ,combine-guard-thm
                             :extra-bindings-ok
                             (,q ,r)
                             (,r ,nonrec))))
             `(("Goal"
                :in-theory nil
                :use ((:guard-theorem ,old-fn-name)
                      ,domain-guard-instance
                      ,domain-of-base-thm
                      ,domain-of-nonrec-when-guard-thm
                      ,combine-guard-instance-base
                      ,combine-guard-instance-nonrec
                      ,domain-of-combine-uncond-instance)))))
          (t (impossible))))
       (local-event
        `(local
          (,macro ,new-fn-name (,@formals)
                  (declare (xargs :well-founded-relation ,wfrel
                                  :measure ,measure
                                  :hints ,termination-hints
                                  :guard ,guard
                                  :verify-guards ,do-verify-guards
                                  ,@(and do-verify-guards
                                         (list :guard-hints guard-hints))))
                  ,body)))
       (exported-event
        `(,macro ,new-fn-name (,@formals)
                 (declare (xargs :well-founded-relation ,wfrel
                                 :measure ,measure
                                 :guard ,guard
                                 :verify-guards ,do-verify-guards))
                 ,body)))
    (mv local-event exported-event formals)))

(define tailrec-new-to-old-intro-event
  ((old-fn-name symbolp "Result of @(tsee tailrec-check-inputs).")
   (nonrec pseudo-termp "Result of @(tsee tailrec-check-inputs).")
   (updates pseudo-term-listp "Result of @(tsee tailrec-check-inputs).")
   (combine pseudo-termp "Result of @(tsee tailrec-check-inputs).")
   (q symbolp "Result of @(tsee tailrec-check-inputs).")
   (r symbolp "Result of @(tsee tailrec-check-inputs).")
   (variant tailrec-variantp "Input to the trasformation, after validation.")
   (domain$ pseudo-termfnp "Result of @(tsee tailrec-check-inputs).")
   (new-fn-name symbolp "Result of @(tsee tailrec-check-inputs).")
   (names-to-avoid symbol-listp "Names of other events
                                 (calculated in @(tsee tailrec-event)).")
   (app-cond-thm-names symbol-symbol-alistp
                       "Map from the names of the applicability conditions
                        to the corresponding theorems
                        (calculated in @(tsee tailrec-event)).")
   (old-fn-unnorm-name symbolp "Name of the theorem that installs
                                the non-normalized definition
                                of the old function.")
   (domain-of-old-thm-name
    symbolp "Result of @(tsee tailrec-domain-of-old-intro-event).")
   (new-fn-formals symbol-listp
                   "Result of @(tsee tailrec-new-fn-intro-events).")
   (new-fn-unnorm-name symbolp "Name of the theorem that installs
                                the non-normalized definition
                                of the new function.")
   (wrld plist-worldp))
  :returns (mv (new-to-old-thm-event "A @(tsee pseudo-event-formp).")
               (new-to-old-thm-name "A @(tsee symbolp)
                                     that names the theorem."))
  :mode :program
  :short "Event for the theorem equating the new function
          to a combination of the old function with @('r')
          (@($f'{}f$) in the design notes)."
  :long
  "<p>
   The theorem's formula is
   </p>
   @({
     (implies (domain r)
              (equal (new x1 ... xn r)
                     combine<r,(old x1 ... xn)>))
   })
   <p>
   The equality is unconditional
   if @('domain') is @('(lambda (x) t)') (e.g. as default).
   </p>
   <p>
   The hints follow the proofs in the design notes.
   Note that @('combine-right-identity-thm?') is @('nil') iff
   the @(':combine-right-identity') applicability condition is absent,
   which happens exactly when
   the @(':variant') input to the transformation is @(':assoc').
   In this case, no instance of that applicability condition
   is used in the proof.
   </p>
   <p>
   This theorem event
   is local to the @(tsee encapsulate) generated by the transformation,
   because it is a lemma used to prove the exported main theorem.
   </p>"
  (b* ((name (fresh-name-in-world-with-$s 'new-to-old names-to-avoid wrld))
       (formula
        (untranslate (implicate
                      (apply-term* domain$ r)
                      `(equal ,(apply-term new-fn-name new-fn-formals)
                              ,(apply-term* (tailrec-combine-op combine q r)
                                            r
                                            (apply-term old-fn-name
                                                        (formals old-fn-name
                                                                 wrld)))))
                     t wrld))
       (hints
        (case variant
          ((:monoid :assoc)
           (b* ((domain-of-nonrec-thm
                 (cdr (assoc-eq :domain-of-nonrec app-cond-thm-names)))
                (domain-of-combine-thm
                 (cdr (assoc-eq :domain-of-combine app-cond-thm-names)))
                (combine-associativity-thm
                 (cdr (assoc-eq :combine-associativity app-cond-thm-names)))
                (combine-right-identity-thm?
                 (cdr (assoc-eq :combine-right-identity app-cond-thm-names)))
                (domain-of-combine-instance
                 `(:instance ,domain-of-combine-thm
                             :extra-bindings-ok
                             (,(tailrec-var-u old-fn-name) ,r)
                             (,(tailrec-var-v old-fn-name) ,nonrec)))
                (combine-associativity-instance
                 `(:instance ,combine-associativity-thm
                             :extra-bindings-ok
                             (,(tailrec-var-u old-fn-name) ,r)
                             (,(tailrec-var-v old-fn-name) ,nonrec)
                             (,(tailrec-var-w old-fn-name)
                              ,(apply-term old-fn-name updates))))
                (combine-right-identity-instance?
                 (and combine-right-identity-thm?
                      `(:instance ,combine-right-identity-thm?
                                  :extra-bindings-ok
                                  (,(tailrec-id-var-u old-fn-name wrld) ,r))))
                (domain-of-old-thm-instance
                 `(:instance ,domain-of-old-thm-name
                             :extra-bindings-ok
                             ,@(alist-to-doublets (pairlis$ (formals old-fn-name
                                                                     wrld)
                                                            updates)))))
             `(("Goal"
                :in-theory '(,old-fn-unnorm-name
                             ,new-fn-unnorm-name
                             (:induction ,new-fn-name))
                :induct (,new-fn-name ,@new-fn-formals))
               '(:use (,@(and combine-right-identity-thm?
                              (list combine-right-identity-instance?))
                       ,domain-of-nonrec-thm
                       ,domain-of-combine-instance
                       ,domain-of-old-thm-instance
                       ,combine-associativity-instance)))))
          (:monoid-alt
           (b* ((domain-of-combine-uncond-thm
                 (cdr (assoc-eq :domain-of-combine-uncond app-cond-thm-names)))
                (combine-associativity-uncond-thm
                 (cdr (assoc-eq :combine-associativity-uncond
                                app-cond-thm-names)))
                (combine-right-identity-thm
                 (cdr (assoc-eq :combine-right-identity app-cond-thm-names)))
                (domain-of-combine-uncond-instance
                 `(:instance ,domain-of-combine-uncond-thm
                             :extra-bindings-ok
                             (,(tailrec-var-u old-fn-name) ,r)
                             (,(tailrec-var-v old-fn-name) ,nonrec)))
                (combine-associativity-uncond-instance
                 `(:instance ,combine-associativity-uncond-thm
                             :extra-bindings-ok
                             (,(tailrec-var-u old-fn-name) ,r)
                             (,(tailrec-var-v old-fn-name) ,nonrec)
                             (,(tailrec-var-w old-fn-name)
                              ,(apply-term old-fn-name updates))))
                (combine-right-identity-instance
                 `(:instance ,combine-right-identity-thm
                             :extra-bindings-ok
                             (,(tailrec-id-var-u old-fn-name wrld) ,r))))
             `(("Goal"
                :in-theory '(,old-fn-unnorm-name
                             ,new-fn-unnorm-name
                             (:induction ,new-fn-name))
                :induct (,new-fn-name ,@new-fn-formals))
               '(:use (,combine-right-identity-instance
                       ,domain-of-combine-uncond-instance
                       ,combine-associativity-uncond-instance)))))
          (t (impossible))))
       (event `(local (defthm ,name
                        ,formula
                        :rule-classes nil
                        :hints ,hints))))
    (mv event name)))

(define tailrec-alpha-fn-intro-event
  ((old-fn-name symbolp "Result of @(tsee tailrec-check-inputs).")
   (test pseudo-termp "Result of @(tsee tailrec-check-inputs).")
   (updates pseudo-term-listp "Result of @(tsee tailrec-check-inputs).")
   (names-to-avoid symbol-listp "Names already used by preceding events.")
   (wrld plist-worldp))
  :returns (mv (alpha-fn-event "A @(tsee pseudo-event-formp).")
               (alpha-fn-name "A @(tsee symbolp)."))
  :mode :program
  :short "Event to introduce the @($\\alpha$) function of the design notes."
  :long
  "<p>
   This function is generated only locally,
   because its purpose is just to prove local theorems
   (@($a\\alpha$) and @($\\gamma_f\\alpha$) in the design notes).
   Since this function is only used in theorems,
   it has a @('t') guard and its guards are not verified.
   The termination proof follows the design notes:
   measure and well-founded relation are the same as @('old').
   We do not normalize the function, so we can better control the proofs.
   </p>
   <p>
   The name used for @($\\alpha$) is returned, along with the event.
   </p>"
  (b* ((name (fresh-name-in-world-with-$s 'alpha names-to-avoid wrld))
       (formals (formals old-fn-name wrld))
       (body `(if ,test (list ,@formals) (,name ,@updates)))
       (wfrel (well-founded-relation old-fn-name wrld))
       (measure (measure old-fn-name wrld))
       (termination-hints
        `(("Goal" :use (:termination-theorem ,old-fn-name) :in-theory nil)))
       (event `(local
                (defun ,name ,formals
                  (declare (xargs :well-founded-relation ,wfrel
                                  :measure ,measure
                                  :hints ,termination-hints
                                  :guard t
                                  :verify-guards nil
                                  :normalize nil))
                  ,body))))
    (mv event name)))

(define tailrec-alpha-component-terms
  ((alpha-fn-name symbolp "Result of @(tsee tailrec-alpha-fn-intro-event).")
   (old-fn-name symbolp "Result of @(tsee tailrec-check-inputs).")
   (wrld plist-worldp))
  :returns (terms "A @(tsee pseudo-term-listp).")
  :verify-guards nil
  :short "Generate the terms of the components of the result of @($\\alpha$)."
  :long
  "<p>
   These are the terms
   @('(nth 0 (alpha x1 ... xn))'), ... @('(nth n-1 (alpha x1 ... xn))').
   </p>
   <p>
   The recursion constructs the terms in reverse order,
   with @('i') going from @('n') down to 1, exiting when it reaches 0.
   </p>"
  (b* ((formals (formals old-fn-name wrld))
       (n (len formals)))
    (tailrec-alpha-component-terms-aux n alpha-fn-name formals nil))

  :prepwork
  ((define tailrec-alpha-component-terms-aux ((i natp)
                                              (alpha-fn-name symbolp)
                                              (formals symbol-listp)
                                              (terms pseudo-term-listp))
     :returns (final-terms) ; PSEUDO-TERM-LISTP
     :verify-guards nil
     (if (zp i)
         terms
       (b* ((i-1 (1- i))
            (term `(nth ',i-1 (,alpha-fn-name ,@formals))))
         (tailrec-alpha-component-terms-aux i-1
                                            alpha-fn-name
                                            formals
                                            (cons term terms)))))))

(define tailrec-test-of-alpha-intro-event
  ((old-fn-name symbolp "Result of @(tsee tailrec-check-inputs).")
   (test pseudo-termp "Result of @(tsee tailrec-check-inputs).")
   (alpha-fn-name symbolp "Result of @(tsee tailrec-alpha-fn-intro-event).")
   (names-to-avoid symbol-listp "Names already used by preceding events.")
   (wrld plist-worldp))
  :returns (mv (test-of-alpha-thm-event "A @(tsee pseudo-event-formp).")
               (test-of-alpha-thm-name "A @(tsee symbolp)
                                        that names the theorem."))
  :mode :program
  :short "Event form for the theorem asserting that
          the recursion exit test succeeds on the result of @($\\alpha$)
          (@($a\\alpha$) in the design notes)."
  :long
  "<p>
   The theorem's formula is @('test<alpha_x1,...,alpha_xn>'),
   where @('alpha_xi') is the @('i')-th result of @($\\alpha$),
   counting from 1.
   </p>
   <p>
   The hints follow the proof in the design notes.
   Since the theorem involves @(tsee nth) applied to @(tsee cons),
   we enable the built-in theorems @('nth-0-cons') and @('nth-add1');
   this is implicit in the design notes.
   </p>
   <p>
   This theorem event
   is local to the @(tsee encapsulate) generated by the transformation,
   because it is just a lemma used to prove other theorems.
   </p>"
  (b* ((name (fresh-name-in-world-with-$s 'test-of-alpha names-to-avoid wrld))
       (formals (formals old-fn-name wrld))
       (alpha-component-terms (tailrec-alpha-component-terms alpha-fn-name
                                                             old-fn-name
                                                             wrld))
       (formula (subcor-var formals alpha-component-terms test))
       (hints `(("Goal"
                 :in-theory '(,alpha-fn-name nth-0-cons nth-add1)
                 :induct (,alpha-fn-name ,@formals))))
       (event `(local (defthm ,name
                        ,formula
                        :rule-classes nil
                        :hints ,hints))))
    (mv event name)))

(define tailrec-old-guard-of-alpha-intro-event
  ((old-fn-name symbolp "Result of @(tsee tailrec-check-inputs).")
   (alpha-fn-name symbolp "Result of @(tsee tailrec-alpha-fn-intro-event).")
   (names-to-avoid symbol-listp "Names already used by preceding events.")
   (wrld plist-worldp))
  :returns (mv (old-guard-of-alpha-thm-event "A @(tsee pseudo-event-formp).")
               (old-guard-of-alpha-thm-name "A @(tsee symbolp)
                                             that names the theorem."))
  :mode :program
  :short "Event form for the theorem asserting that
          the guard of the old function is preserved by @($\\alpha$)
          (@($\\gamma_f\\alpha$) in the design notes)."
  :long
  "<p>
   The theorem's formula is
   @('(implies old-guard<x1,...,xn> old-guard<alpha_x1,...,alpha_xn>)'),
   where @('alpha_xi') is the @('i')-th result of @($\\alpha$),
   counting from 1.
   </p>
   <p>
   The hints follow the proof in the design notes.
   Since the theorem involves @(tsee nth) applied to @(tsee cons),
   we enable the built-in theorems @('nth-0-cons') and @('nth-add1');
   this is implicit in the design notes.
   </p>
   <p>
   This theorem event
   is local to the @(tsee encapsulate) generated by the transformation,
   because it is just a lemma used to prove other theorems.
   </p>"
  (b* ((name (fresh-name-in-world-with-$s 'old-guard-of-alpha
                                          names-to-avoid
                                          wrld))
       (formals (formals old-fn-name wrld))
       (alpha-component-terms (tailrec-alpha-component-terms alpha-fn-name
                                                             old-fn-name
                                                             wrld))
       (old-guard (guard old-fn-name nil wrld))
       (formula (implicate old-guard
                           (subcor-var
                            formals alpha-component-terms old-guard)))
       (hints `(("Goal"
                 :in-theory '(,alpha-fn-name nth-0-cons nth-add1)
                 :induct (,alpha-fn-name ,@formals))
                '(:use (:guard-theorem ,old-fn-name))))
       (event `(local (defthm ,name
                        ,formula
                        :rule-classes nil
                        :hints ,hints))))
    (mv event name)))

(define tailrec-domain-of-ground-base-intro-event
  ((old-fn-name symbolp "Result of @(tsee tailrec-check-inputs).")
   (base pseudo-termp "Result of @(tsee tailrec-check-inputs).")
   (domain$ pseudo-termfnp "Result of @(tsee tailrec-check-inputs).")
   (app-cond-thm-names symbol-symbol-alistp
                       "Map from the names of the applicability conditions
                        to the corresponding theorems
                        (calculated in @(tsee tailrec-event)).")
   (alpha-fn-name symbolp "Result of @(tsee tailrec-alpha-fn-intro-event).")
   (test-of-alpha-thm-name
    symbolp "Result of @(tsee tailrec-test-of-alpha-intro-event).")
   (names-to-avoid symbol-listp "Names already used by preceding events.")
   (wrld plist-worldp))
  :returns (mv (domain-of-ground-base-thm-event "A @(tsee pseudo-event-formp).")
               (domain-of-ground-base-thm-name "A @(tsee symbolp)
                                                that names the theorem."))
  :mode :program
  :short "Event form for the theorem asserting that
          the base value of the recursion is in the domain
          (@($D{}b_0$) in the design notes)."
  :long
  "<p>
   The hints follow the proof in the design notes.
   </p>
   <p>
   This theorem event
   is local to the @(tsee encapsulate) generated by the transformation,
   because it is just a lemma used to prove other theorems.
   </p>"
  (b* ((name (fresh-name-in-world-with-$s 'domain-of-ground-base
                                          names-to-avoid
                                          wrld))
       (formula (apply-term* domain$ base))
       (domain-of-base-thm
        (cdr (assoc-eq :domain-of-base app-cond-thm-names)))
       (formals (formals old-fn-name wrld))
       (alpha-comps (tailrec-alpha-component-terms alpha-fn-name
                                                   old-fn-name
                                                   wrld))
       (hints `(("Goal"
                 :in-theory nil
                 :use (,test-of-alpha-thm-name
                       (:instance ,domain-of-base-thm
                        :extra-bindings-ok
                        ,@(alist-to-doublets (pairlis$ formals
                                                       alpha-comps)))))))
       (event `(local (defthm ,name
                        ,formula
                        :rule-classes nil
                        :hints ,hints))))
    (mv event name)))

(define tailrec-combine-left-identity-ground-intro-event
  ((old-fn-name symbolp "Result of @(tsee tailrec-check-inputs).")
   (base pseudo-termp "Result of @(tsee tailrec-check-inputs).")
   (combine pseudo-termp "Result of @(tsee tailrec-check-inputs).")
   (q symbolp "Result of @(tsee tailrec-check-inputs).")
   (r symbolp "Result of @(tsee tailrec-check-inputs).")
   (domain$ pseudo-termfnp "Result of @(tsee tailrec-check-inputs).")
   (app-cond-thm-names symbol-symbol-alistp
                       "Map from the names of the applicability conditions
                        to the corresponding theorems
                        (calculated in @(tsee tailrec-event)).")
   (alpha-fn-name symbolp "Result of @(tsee tailrec-alpha-fn-intro-event).")
   (test-of-alpha-thm-name
    symbolp "Result of @(tsee tailrec-test-of-alpha-intro-event).")
   (names-to-avoid symbol-listp "Names already used by preceding events.")
   (wrld plist-worldp))
  :returns (mv (combine-left-identity-ground-thm-event
                "A @(tsee pseudo-event-formp).")
               (combine-left-identity-ground-thm-name
                "A @(tsee symbolp) that names the theorem."))
  :mode :program
  :short "Event form for the theorem asserting that
          the base value of the recursion
          is left identity of the combination operator
          (@($L{}I_0$) in the design notes)."
  :long
  "<p>
   The hints follow the proof in the design notes.
   </p>
   <p>
   This theorem event
   is local to the @(tsee encapsulate) generated by the transformation,
   because it is just a lemma used to prove other theorems.
   </p>"
  (b* ((name (fresh-name-in-world-with-$s 'combine-left-identity-ground
                                          names-to-avoid
                                          wrld))
       (u (tailrec-var-u old-fn-name))
       (combine-op (tailrec-combine-op combine q r))
       (formula (implicate (apply-term* domain$ u)
                           `(equal ,(apply-term* combine-op base u)
                                   ,u)))
       (combine-left-identity-thm
        (cdr (assoc-eq :combine-left-identity app-cond-thm-names)))
       (formals (formals old-fn-name wrld))
       (alpha-comps (tailrec-alpha-component-terms alpha-fn-name
                                                   old-fn-name
                                                   wrld))
       (hints `(("Goal"
                 :in-theory nil
                 :use (,test-of-alpha-thm-name
                       (:instance ,combine-left-identity-thm
                        :extra-bindings-ok
                        ,@(alist-to-doublets (pairlis$ formals
                                                       alpha-comps)))))))
       (event `(local (defthm ,name
                        ,formula
                        :rule-classes nil
                        :hints ,hints))))
    (mv event name)))

(define tailrec-base-guard-intro-event
  ((old-fn-name symbolp "Result of @(tsee tailrec-check-inputs).")
   (base pseudo-termp "Result of @(tsee tailrec-check-inputs).")
   (alpha-fn-name symbolp "Result of @(tsee tailrec-alpha-fn-intro-event).")
   (test-of-alpha-thm-name
    symbolp "Result of @(tsee tailrec-test-of-alpha-intro-event).")
   (old-guard-of-alpha-thm-name
    symbolp "Result of @(tsee tailrec-old-guard-of-alpha-intro-event).")
   (names-to-avoid symbol-listp "Names already used by preceding events.")
   state)
  :returns (mv (base-guard-thm-event "A @(tsee pseudo-event-formp).")
               (base-guard-thm-name "A @(tsee symbolp)
                                     that names the theorem."))
  :mode :program
  :short "Event form for the theorem asserting that
          the guard of the base term is satisfied
          if the guard of the target function is
          (@($G{}b$) in the design notes)."
  :long
  "<p>
   The hints follow the proof in the design notes.
   </p>
   <p>
   This theorem event
   is local to the @(tsee encapsulate) generated by the transformation,
   because it is just a lemma used to prove other theorems.
   </p>"
  (b* ((wrld (w state))
       (name (fresh-name-in-world-with-$s 'base-guard names-to-avoid wrld))
       (formula (implicate (guard old-fn-name nil wrld)
                           (term-guard-obligation base state)))
       (formals (formals old-fn-name wrld))
       (alpha-comps (tailrec-alpha-component-terms alpha-fn-name
                                                   old-fn-name
                                                   wrld))
       (hints `(("Goal"
                 :in-theory nil
                 :use (,old-guard-of-alpha-thm-name
                       ,test-of-alpha-thm-name
                       (:instance (:guard-theorem ,old-fn-name)
                        :extra-bindings-ok
                        ,@(alist-to-doublets (pairlis$ formals
                                                       alpha-comps)))))))
       (event `(local (defthm ,name
                        ,formula
                        :rule-classes nil
                        :hints ,hints))))
    (mv event name)))

(define tailrec-old-as-new
  ((old-fn-name symbolp "Result of @(tsee tailrec-check-inputs).")
   (test pseudo-termp "Result of @(tsee tailrec-check-inputs).")
   (base pseudo-termp "Result of @(tsee tailrec-check-inputs).")
   (nonrec pseudo-termp "Result of @(tsee tailrec-check-inputs).")
   (updates pseudo-term-listp "Result of @(tsee tailrec-check-inputs).")
   (r symbolp "Result of @(tsee tailrec-check-inputs).")
   (variant tailrec-variantp "Input to the trasformation, after validation.")
   (new-fn-name symbolp "Result of @(tsee tailrec-check-inputs).")
   (new-fn-formals symbol-listp
                   "Result of @(tsee tailrec-new-fn-intro-events).")
   (wrld plist-worldp))
  :returns (term "An untranslated term.")
  :mode :program
  :short "Rephrasing of (a generic call to) the old function
          in terms of the new function."
  :long
  "<p>
   This is the right-hand side of the theorem
   that relates the old function to the new function
   (@($f{}f'$) in the design notes),
   and it is also the body of the wrapper function.
   </p>
   <p>
   This is as described in the documentation and design notes.
   It varies slightly, depending on the transformation's variant.
   As explained in the documentation,
   for now it uses @('base<x1,...,xn>') instead of the @($\\beta$) function.
   </p>"
  (untranslate (case variant
                 (:assoc
                  `(if ,test
                       ,base
                     ,(subcor-var (cons r (formals old-fn-name wrld))
                                  (cons nonrec updates)
                                  (apply-term new-fn-name new-fn-formals))))
                 ((:monoid :monoid-alt)
                  (subst-var base r (apply-term new-fn-name new-fn-formals)))
                 (t (impossible)))
               nil wrld))

(define tailrec-old-to-new-intro-event
  ((old-fn-name symbolp "Result of @(tsee tailrec-check-inputs).")
   (test pseudo-termp "Result of @(tsee tailrec-check-inputs).")
   (base pseudo-termp "Result of @(tsee tailrec-check-inputs).")
   (nonrec pseudo-termp "Result of @(tsee tailrec-check-inputs).")
   (updates pseudo-term-listp "Result of @(tsee tailrec-check-inputs).")
   (r symbolp "Result of @(tsee tailrec-check-inputs).")
   (variant tailrec-variantp "Input to the trasformation, after validation.")
   (new-fn-name symbolp "Result of @(tsee tailrec-check-inputs).")
   (names-to-avoid symbol-listp "Names of other events
                                 (calculated in @(tsee tailrec-event)).")
   (app-cond-thm-names symbol-symbol-alistp
                       "Map from the names of the applicability conditions
                        to the corresponding theorems
                        (calculated in @(tsee tailrec-event)).")
   (domain-of-old-thm-name
    symbolp "Result of @(tsee tailrec-domain-of-old-intro-event).")
   (domain-of-ground-base-thm-name
    symbolp "Result of @(tsee tailrec-domain-of-ground-base-intro-event).")
   (combine-left-identity-ground-thm-name
    symbolp
    "Result of @(tsee tailrec-combine-left-identity-ground-intro-event).")
   (new-fn-formals symbol-listp
                   "Result of @(tsee tailrec-new-fn-intro-events).")
   (new-to-old-thm-name
    symbolp "Result of @(tsee tailrec-new-to-old-intro-event).")
   (wrld plist-worldp))
  :returns (mv (old-to-new-thm-event "A @(tsee pseudo-event-formp).")
               (old-to-new-thm-name "A @(tsee symbolp)
                                     that names the theorem."))
  :mode :program
  :short "Event form for the theorem that relates
          the old function to the new function
          (@($f{}f'$) and @($f{}f'_0$) in the design notes)."
  :long
  "<p>
   The theorem is @($f{}f'$) when the variant is @(':assoc')
   (in this case, left identity does not hold),
   and @($f{}f'_0$) when the variant is @(':monoid') or @(':monoid-alt')
   (in this case, left identity holds,
   and we are in the special case of a ground base term).
   </p>
   <p>
   The hints follow the proof in the design notes,
   for the case in which left identity holds
   when the variant is @(':monoid') or @(':monoid-alt'),
   and for the case in which left identity does not hold
   when the variant is @(':assoc').
   In the first case, the proof is for the special case of a ground base term.
   </p>
   <p>
   For the @(':assoc') variant,
   since the old function is recursive,
   we use an explicit @(':expand') hint
   instead of just enabling the definition of old function.
   </p>"
  (b* ((name (fresh-name-in-world-with-$s 'old-to-new names-to-avoid wrld))
       (formula `(equal ,(apply-term old-fn-name (formals old-fn-name wrld))
                        ,(tailrec-old-as-new
                          old-fn-name test base nonrec updates r variant
                          new-fn-name new-fn-formals wrld)))
       (hints
        (case variant
          ((:monoid :monoid-alt)
           (b* ((combine-left-identity-ground-instance
                 `(:instance ,combine-left-identity-ground-thm-name
                             :extra-bindings-ok
                             (,(tailrec-id-var-u old-fn-name wrld)
                              ,(apply-term old-fn-name (formals old-fn-name
                                                                wrld)))))
                (new-to-old-thm-instance
                 `(:instance ,new-to-old-thm-name
                             :extra-bindings-ok
                             (,r ,base))))
             `(("Goal"
                :in-theory nil
                :use (,domain-of-ground-base-thm-name
                      ,domain-of-old-thm-name
                      ,new-to-old-thm-instance
                      ,combine-left-identity-ground-instance)))))
          (:assoc
           (b* ((formals (formals old-fn-name wrld))
                (domain-of-nonrec-thm
                 (cdr (assoc-eq :domain-of-nonrec app-cond-thm-names)))
                (new-to-old-thm-instance
                 `(:instance ,new-to-old-thm-name
                             :extra-bindings-ok
                             (,r ,nonrec)
                             ,@(alist-to-doublets (pairlis$ formals updates)))))
             `(("Goal"
                :in-theory nil
                :expand ((,old-fn-name ,@formals))
                :use (,domain-of-nonrec-thm
                      ,new-to-old-thm-instance)))))
          (t (impossible))))
       (event `(local (defthm ,name
                        ,formula
                        :rule-classes nil
                        :hints ,hints))))
    (mv event name)))

(define tailrec-wrapper-fn-intro-events
  ((old-fn-name symbolp "Result of @(tsee tailrec-check-inputs).")
   (test pseudo-termp "Result of @(tsee tailrec-check-inputs).")
   (base pseudo-termp "Result of @(tsee tailrec-check-inputs).")
   (nonrec pseudo-termp "Result of @(tsee tailrec-check-inputs).")
   (updates pseudo-term-listp "Result of @(tsee tailrec-check-inputs).")
   (r symbolp "Result of @(tsee tailrec-check-inputs).")
   (variant tailrec-variantp "Input to the trasformation, after validation.")
   (new-fn-name symbolp "Result of @(tsee tailrec-check-inputs).")
   (wrapper-fn-name symbolp "Result of @(tsee tailrec-check-inputs).")
   (wrapper-enable booleanp "Input to the trasformation, after validation.")
   (make-non-executable booleanp "Result of @(tsee tailrec-check-inputs).")
   (do-verify-guards booleanp "Result of @(tsee tailrec-check-inputs).")
   (app-cond-thm-names symbol-symbol-alistp
                       "Map from the names of the applicability conditions
                        to the corresponding theorems
                        (calculated in @(tsee tailrec-event)).")
   (domain-of-ground-base-thm-name
    symbolp "Result of @(tsee tailrec-domain-of-ground-base-intro-event).")
   (base-guard-thm-name
    symbolp "Result of @(tsee tailrec-base-guard-intro-event).")
   (new-fn-formals symbol-listp
                   "Result of @(tsee tailrec-new-fn-intro-events).")
   (wrld plist-worldp))
  :returns (mv (local-event "A @(tsee pseudo-event-formp).")
               (exported-event "A @(tsee pseudo-event-formp)."))
  :mode :program
  :short "Local and exported events to introduce the wrapper function."
  :long
  "<p>
   In the @(tsee encapsulate) generated by @(tsee tailrec-event),
   the wrapper function is introduced via a local event first,
   then via a redundant non-local (i.e. exported) event.
   The local event includes the hints for the guard proof.
   The exported event has no guard proof hints.
   This keeps the event history after the transformation &ldquo;clean&rdquo;,
   without implementation-specific guard hints.
   </p>
   <p>
   The macro used to introduce the new function is determined by
   whether the new function must be
   enabled or not, and non-executable or not.
   </p>
   <p>
   The wrapper function has the same formal arguments as the old function.
   </p>
   <p>
   The body of the wrapper function is
   the rephrasing of the old function in terms of the new function.
   </p>
   <p>
   The guard of the wrapper function is the same as the old function.
   </p>
   <p>
   The guard hints are based on the proofs in the design notes.
   Since the base term is always ground,
   the proof for the case in which left identity holds
   (i.e. when the variant is @(':monoid') or @(':monoid-alt'))
   follows the proof for the special case of a ground base term.
   </p>"
  (b* ((macro (function-intro-macro wrapper-enable make-non-executable))
       (formals (formals old-fn-name wrld))
       (body (tailrec-old-as-new old-fn-name test base nonrec updates r variant
                                 new-fn-name new-fn-formals wrld))
       (guard (untranslate (guard old-fn-name nil wrld) t wrld))
       (guard-hints
        (case variant
          ((:monoid :monoid-alt)
           `(("Goal"
              :in-theory nil
              :use ((:guard-theorem ,old-fn-name)
                    ,domain-of-ground-base-thm-name
                    ,base-guard-thm-name))))
          (:assoc
           (b* ((domain-of-nonrec-thm
                 (cdr (assoc-eq :domain-of-nonrec app-cond-thm-names))))
             `(("Goal"
                :in-theory nil
                :use ((:guard-theorem ,old-fn-name)
                      ,domain-of-nonrec-thm)))))
          (t (impossible))))
       (local-event
        `(local
          (,macro ,wrapper-fn-name (,@formals)
                  (declare (xargs :guard ,guard
                                  :verify-guards ,do-verify-guards
                                  ,@(and do-verify-guards
                                         (list :guard-hints guard-hints))))
                  ,body)))
       (exported-event
        `(,macro ,wrapper-fn-name (,@formals)
                 (declare (xargs :guard ,guard
                                 :verify-guards ,do-verify-guards))
                 ,body)))
    (mv local-event exported-event)))

(define tailrec-old-to-wrapper-intro-events
  ((old-fn-name symbolp "Result of @(tsee tailrec-check-inputs).")
   (wrapper-fn-name symbolp "Result of @(tsee tailrec-check-inputs).")
   (old-to-wrapper-thm-name symbolp "Result of @(tsee tailrec-check-inputs).")
   (thm-enable booleanp "Input to the trasformation, after validation.")
   (old-to-new-thm-name symbolp
                        "Result of @(tsee tailrec-old-to-new-intro-event).")
   (wrapper-fn-unnorm-name symbolp "Name of the theorem that installs
                                    the non-normalized definition
                                    of the wrapper function.")
   (wrld plist-worldp))
  :returns (mv (local-event "A @(tsee pseudo-event-formp).")
               (exported-event "A @(tsee pseudo-event-formp)."))
  :mode :program
  :short "Local and exported events for the theorem
          that relates the old function to the wrapper function
          (@($f{}\\tilde{f}$) in the design notes)."
  :long
  "<p>
   In the @(tsee encapsulate) generated by @(tsee tailrec-event),
   the theorem that relates the old and wrapper functions
   is introduced via a local event first,
   then via a redundant non-local (i.e. exported) event.
   The local event includes the hints for the proof.
   The exported event has no proof hints.
   This keeps the event history after the transformation &ldquo;clean&rdquo;,
   without implementation-specific proof hints
   that may refer to local events of the @(tsee encapsulate)
   that do not exist in the history after the transformation.
   </p>
   <p>
   The macro used to introduce the theorem is determined by
   whether the theorem must be enabled or not.
   </p>
   <p>
   The theorem's formula
   has the form @('(equal (old x1 ... xn) (wrapper x1 ... xn))').
   </p>
   <p>
   The theorem is proved by
   expanding the (non-normalized) definition of the wrapper function
   and using the theorem that relates the old function to the new function.
   </p>"
  (b* ((macro (theorem-intro-macro thm-enable))
       (formals (formals old-fn-name wrld))
       (formula (untranslate `(equal ,(apply-term old-fn-name formals)
                                     ,(apply-term wrapper-fn-name formals))
                             t wrld))
       (hints `(("Goal"
                 :in-theory '(,wrapper-fn-unnorm-name)
                 :use ,old-to-new-thm-name)))
       (local-event `(local (,macro ,old-to-wrapper-thm-name
                                    ,formula
                                    :hints ,hints)))
       (exported-event `(,macro ,old-to-wrapper-thm-name
                                ,formula)))
    (mv local-event exported-event)))

(define tailrec-event
  ((old-fn-name symbolp "Result of @(tsee tailrec-check-inputs).")
   (test pseudo-termp "Result of @(tsee tailrec-check-inputs).")
   (base pseudo-termp "Result of @(tsee tailrec-check-inputs).")
   (nonrec pseudo-termp "Result of @(tsee tailrec-check-inputs).")
   (updates pseudo-term-listp "Result of @(tsee tailrec-check-inputs).")
   (combine pseudo-termp "Result of @(tsee tailrec-check-inputs).")
   (q symbolp "Result of @(tsee tailrec-check-inputs).")
   (r symbolp "Result of @(tsee tailrec-check-inputs).")
   (variant tailrec-variantp "Input to the trasformation, after validation.")
   (domain$ pseudo-termfnp "Result of @(tsee tailrec-check-inputs).")
   (new-fn-name symbolp "Result of @(tsee tailrec-check-inputs).")
   (new-fn-enable booleanp "Result of @(tsee tailrec-check-inputs).")
   (wrapper-fn-name symbolp "Result of @(tsee tailrec-check-inputs).")
   (wrapper-enable booleanp "Input to the trasformation, after validation.")
   (old-to-wrapper-thm-name symbolp "Result of @(tsee tailrec-check-inputs).")
   (thm-enable booleanp "Input to the trasformation, after validation.")
   (make-non-executable booleanp "Result of @(tsee tailrec-check-inputs).")
   (do-verify-guards booleanp "Result of @(tsee tailrec-check-inputs).")
   (hints-alist symbol-alistp "Result of @(tsee tailrec-check-inputs).")
   (print$ booleanp "Result of @(tsee tailrec-check-inputs).")
   (show-only booleanp "Input to the transformation, after validation.")
   (app-conds symbol-alistp "Result of @(tsee tailrec-app-conds).")
   (call pseudo-event-formp "Call to the transformation.")
   state)
  :returns (event "A @(tsee pseudo-event-formp).")
  :mode :program
  :short "Event form generated by the transformation."
  :long
  "<p>
   This is a @(tsee progn) that starts with
   a (trivial) @(tsee encapsulate) that includes the events for
   the applicability conditions,
   the new and wrapper functions,
   the main theorem and its supporting lemmas,
   and the recording of the generated numbered names.
   The @(tsee encapsulate) is followed by events
   for the recording in the transformation table,
   and possibly for printing the transformation results on the screen.
   </p>
   <p>
   The @(tsee encapsulate) starts with some implicitly local event forms to
   ensure logic mode and
   avoid errors due to ignored or irrelevant formals in the generated functions.
   Other implicitly local event forms remove any default and override hints,
   to improve the robustness of the generated proofs;
   this is done after proving the applicability conditions,
   in case their proofs rely on the default or override hints.
   </p>
   <p>
   The applicability condition theorems
   are all local to the @(tsee encapsulate),
   have no rule classes,
   and are enabled (they must be, because they have no rule classes).
   </p>
   <p>
   The @(tsee encapsulate) also includes events
   to locally install the non-normalized definitions
   of the old, new, and wrapper functions,
   because the generated proofs are based on the unnormalized bodies.
   </p>
   <p>
   As explained in @(tsee tailrec-new-fn-intro-events),
   @(tsee tailrec-wrapper-fn-intro-events),
   and @(tsee tailrec-old-to-wrapper-intro-events),
   the events for the new and wrapper functions
   and for the theorem that relates the old and wrapper functions
   are introduced locally first, then redundantly non-locally
   (with slight variations).
   </p>
   <p>
   The @(tsee encapsulate) is stored into the transformation table,
   associated to the call to the transformation.
   Thus, the table event and (if present) the screen output events
   (which are in the @(tsee progn) but not in the @(tsee encapsulate))
   are not stored into the transformation table,
   because they carry no additional information,
   and because otherwise the table event would have to contain itself.
   </p>
   <p>
   If @(':print') includes @(':submit'),
   the @(tsee encapsulate) is wrapped to show the normal screen output
   for the submitted events.
   This screen output always starts with a blank line,
   so we do need to print a blank line to separate the submission output
   from the expansion output (if any).
   </p>
   <p>
   If @(':print') includes @(':result'),
   the @(tsee progn) includes events to print
   the exported events on the screen without hints.
   They are the same event forms
   that are introduced non-locally and redundantly in the @(tsee encapsulate).
   If @(':print') also includes @(':expand') or @(':submit'),
   an event to print a blank line is also generated
   to separate the result output from the expansion or submission output.
   </p>
   <p>
   The @(tsee progn) ends with an event form
   to avoiding printing any return value on the screen.
   </p>
   <p>
   If @(':show-only') is @('t'),
   the @(tsee encapsulate) is just printed on screen, not submitted.
   In this case,
   the presence or absence of @(':submit') and @(':result') in @(':print')
   is ignored.
   If @(':print') includes @(':expand'),
   a blank line is printed just before the @(tsee encapsulate)
   to separate it from the expansion output.
   </p>
   <p>
   To ensure the absence of name conflicts inside the @(tsee encapsulate),
   the event names to avoid are accumulated
   and threaded through the event-generating code.
   </p>"
  (b* ((wrld (w state))
       (names-to-avoid (list new-fn-name
                             wrapper-fn-name
                             old-to-wrapper-thm-name))
       ((mv app-cond-thm-events
            app-cond-thm-names) (named-formulas-to-thm-events app-conds
                                                              hints-alist
                                                              nil
                                                              t
                                                              t
                                                              names-to-avoid
                                                              wrld))
       (names-to-avoid (append names-to-avoid
                               (strip-cdrs app-cond-thm-names)))
       ((mv old-fn-unnorm-event
            old-fn-unnorm-name) (install-not-norm-event old-fn-name
                                                        t
                                                        names-to-avoid
                                                        wrld))
       (names-to-avoid (rcons old-fn-unnorm-name names-to-avoid))
       ((mv domain-of-old-thm-event
            domain-of-old-thm-name) (tailrec-domain-of-old-intro-event
                                     old-fn-name test nonrec updates
                                     variant domain$
                                     names-to-avoid
                                     app-cond-thm-names
                                     old-fn-unnorm-name
                                     wrld))
       (names-to-avoid (rcons domain-of-old-thm-name names-to-avoid))
       ((mv new-fn-local-event
            new-fn-exported-event
            new-fn-formals) (tailrec-new-fn-intro-events
                             old-fn-name
                             test base nonrec updates combine q r
                             variant domain$
                             new-fn-name new-fn-enable
                             make-non-executable do-verify-guards
                             app-cond-thm-names
                             wrld))
       ((mv new-fn-unnorm-event
            new-fn-unnorm-name) (install-not-norm-event new-fn-name
                                                        t
                                                        names-to-avoid
                                                        wrld))
       (names-to-avoid (rcons new-fn-unnorm-name names-to-avoid))
       ((mv new-to-old-thm-event
            new-to-old-thm-name) (tailrec-new-to-old-intro-event
                                  old-fn-name nonrec updates combine q r
                                  variant domain$
                                  new-fn-name
                                  names-to-avoid
                                  app-cond-thm-names
                                  old-fn-unnorm-name
                                  domain-of-old-thm-name
                                  new-fn-formals
                                  new-fn-unnorm-name
                                  wrld))
       (names-to-avoid (rcons new-to-old-thm-name names-to-avoid))
       (gen-alpha (member-eq variant '(:monoid :monoid-alt)))
       ((mv alpha-fn-event?
            alpha-fn-name?) (if gen-alpha
                                (tailrec-alpha-fn-intro-event
                                 old-fn-name test updates
                                 names-to-avoid wrld)
                              (mv nil nil)))
       (names-to-avoid (if gen-alpha
                           (rcons alpha-fn-name? names-to-avoid)
                         names-to-avoid))
       ((mv test-of-alpha-thm-event?
            test-of-alpha-thm-name?) (if gen-alpha
                                         (tailrec-test-of-alpha-intro-event
                                          old-fn-name test
                                          alpha-fn-name?
                                          names-to-avoid wrld)
                                       (mv nil nil)))
       (names-to-avoid (if gen-alpha
                           (rcons test-of-alpha-thm-name? names-to-avoid)
                         names-to-avoid))
       ((mv old-guard-of-alpha-thm-event?
            old-guard-of-alpha-thm-name?)
        (if (and gen-alpha
                 do-verify-guards)
            (tailrec-old-guard-of-alpha-intro-event
             old-fn-name alpha-fn-name? names-to-avoid wrld)
          (mv nil nil)))
       (names-to-avoid (if (and gen-alpha
                                do-verify-guards)
                           (rcons old-guard-of-alpha-thm-name? names-to-avoid)
                         names-to-avoid))
       ((mv domain-of-ground-base-thm-event?
            domain-of-ground-base-thm-name?)
        (if gen-alpha
            (tailrec-domain-of-ground-base-intro-event
             old-fn-name base domain$ app-cond-thm-names
             alpha-fn-name? test-of-alpha-thm-name?
             names-to-avoid wrld)
          (mv nil nil)))
       (names-to-avoid (if gen-alpha
                           (rcons domain-of-ground-base-thm-name?
                                  names-to-avoid)
                         names-to-avoid))
       ((mv combine-left-identity-ground-thm-event?
            combine-left-identity-ground-thm-name?)
        (if gen-alpha
            (tailrec-combine-left-identity-ground-intro-event
             old-fn-name base combine q r domain$ app-cond-thm-names
             alpha-fn-name? test-of-alpha-thm-name?
             names-to-avoid wrld)
          (mv nil nil)))
       (names-to-avoid (if gen-alpha
                           (rcons combine-left-identity-ground-thm-name?
                                  names-to-avoid)
                         names-to-avoid))
       ((mv base-guard-thm-event?
            base-guard-thm-name?) (if (and gen-alpha
                                           do-verify-guards)
                                      (tailrec-base-guard-intro-event
                                       old-fn-name base
                                       alpha-fn-name? test-of-alpha-thm-name?
                                       old-guard-of-alpha-thm-name?
                                       names-to-avoid state)
                                    (mv nil nil)))
       (names-to-avoid (if (and gen-alpha
                                do-verify-guards)
                           (rcons base-guard-thm-name? names-to-avoid)
                         names-to-avoid))
       ((mv old-to-new-thm-event
            old-to-new-thm-name) (tailrec-old-to-new-intro-event
                                  old-fn-name test base nonrec updates r
                                  variant
                                  new-fn-name
                                  names-to-avoid
                                  app-cond-thm-names
                                  domain-of-old-thm-name
                                  domain-of-ground-base-thm-name?
                                  combine-left-identity-ground-thm-name?
                                  new-fn-formals
                                  new-to-old-thm-name
                                  wrld))
       (names-to-avoid (rcons old-to-new-thm-name names-to-avoid))
       ((mv wrapper-fn-local-event
            wrapper-fn-exported-event) (tailrec-wrapper-fn-intro-events
                                        old-fn-name
                                        test base nonrec updates r
                                        variant
                                        new-fn-name
                                        wrapper-fn-name wrapper-enable
                                        make-non-executable do-verify-guards
                                        app-cond-thm-names
                                        domain-of-ground-base-thm-name?
                                        base-guard-thm-name?
                                        new-fn-formals
                                        wrld))
       ((mv wrapper-fn-unnorm-event
            wrapper-fn-unnorm-name) (install-not-norm-event wrapper-fn-name
                                                            t
                                                            names-to-avoid
                                                            wrld))
       ((mv
         old-to-wrapper-thm-local-event
         old-to-wrapper-thm-exported-event) (tailrec-old-to-wrapper-intro-events
                                             old-fn-name
                                             wrapper-fn-name
                                             old-to-wrapper-thm-name
                                             thm-enable
                                             old-to-new-thm-name
                                             wrapper-fn-unnorm-name
                                             wrld))
       (new-fn-numbered-name-event `(add-numbered-name-in-use
                                     ,new-fn-name))
       (wrapper-fn-numbered-name-event `(add-numbered-name-in-use
                                         ,wrapper-fn-name))
       (encapsulate-events
        `((logic)
          (set-ignore-ok t)
          (set-irrelevant-formals-ok t)
          ,@app-cond-thm-events
          (set-default-hints nil)
          (set-override-hints nil)
          ,old-fn-unnorm-event
          ,domain-of-old-thm-event
          ,new-fn-local-event
          ,new-fn-unnorm-event
          ,new-to-old-thm-event
          ,@(and gen-alpha
                 (list alpha-fn-event?))
          ,@(and gen-alpha
                 (list test-of-alpha-thm-event?))
          ,@(and gen-alpha
                 do-verify-guards
                 (list old-guard-of-alpha-thm-event?))
          ,@(and gen-alpha
                 (list domain-of-ground-base-thm-event?))
          ,@(and gen-alpha
                 (list combine-left-identity-ground-thm-event?))
          ,@(and gen-alpha
                 do-verify-guards
                 (list base-guard-thm-event?))
          ,old-to-new-thm-event
          ,wrapper-fn-local-event
          ,wrapper-fn-unnorm-event
          ,old-to-wrapper-thm-local-event
          ,new-fn-exported-event
          ,wrapper-fn-exported-event
          ,old-to-wrapper-thm-exported-event
          ,new-fn-numbered-name-event
          ,wrapper-fn-numbered-name-event))
       (encapsulate `(encapsulate () ,@encapsulate-events))
       (expand-output-p (if (member-eq :expand print$) t nil))
       ((when show-only)
        (if expand-output-p
            (cw "~%~x0~|" encapsulate)
          (cw "~x0~|" encapsulate))
        '(value-triple :invisible))
       (submit-output-p (if (member-eq :submit print$) t nil))
       (encapsulate+ (restore-output? submit-output-p encapsulate))
       (transformation-table-event (record-transformation-call-event
                                    call encapsulate wrld))
       (result-output-p (if (member-eq :result print$) t nil))
       (print-events (if result-output-p
                         `(,@(and (or expand-output-p submit-output-p)
                                  '((cw-event "~%")))
                           (cw-event "~x0~|" ',new-fn-exported-event)
                           (cw-event "~x0~|" ',wrapper-fn-exported-event)
                           (cw-event "~x0~|"
                                     ',old-to-wrapper-thm-exported-event))
                       nil)))
    `(progn
       ,encapsulate+
       ,transformation-table-event
       ,@print-events
       (value-triple :invisible))))

(define tailrec-fn
  ((old "Input to the transformation.")
   (variant "Input to the transformation.")
   (domain "Input to the transformation.")
   (new-name "Input to the transformation.")
   (new-enable "Input to the transformation.")
   (wrapper-name "Input to the transformation.")
   (wrapper-enable "Input to the transformation.")
   (thm-name "Input to the transformation.")
   (thm-enable "Input to the transformation.")
   (non-executable "Input to the transformation.")
   (verify-guards "Input to the transformation.")
   (hints "Input to the transformation.")
   (print "Input to the transformation.")
   (show-only "Input to the transformation.")
   (call pseudo-event-formp "Call to the transformation.")
   (ctx "Context for errors.")
   state)
  :returns (mv (erp "@(tsee booleanp) flag of the
                     <see topic='@(url acl2::error-triple)'>error
                     triple</see>.")
               (event "A @(tsee pseudo-event-formp).")
               state)
  :mode :program
  :short "Validate the inputs,
          prove the applicability conditions, and
          generate the event form to submit."
  :long
  "<p>
   If this call to the transformation is redundant,
   a message to that effect is printed on the screen.
   If the transformation is redundant and @(':show-only') is @('t'),
   the @(tsee encapsulate), retrieved from the table, is shown on screen.
   </p>"
  (b* ((encapsulate? (previous-transformation-expansion call (w state)))
       ((when encapsulate?)
        (b* (((run-when show-only) (cw "~x0~|" encapsulate?)))
          (cw "~%The transformation ~x0 is redundant.~%" call)
          (value '(value-triple :invisible))))
       ((er (list old-fn-name
                  test
                  base
                  nonrec
                  updates
                  combine
                  q
                  r
                  domain$
                  new-fn-name
                  new-fn-enable
                  wrapper-fn-name
                  old-to-wrapper-thm-name
                  make-non-executable
                  do-verify-guards
                  hints-alist
                  print$)) (tailrec-check-inputs old
                                                 variant
                                                 domain
                                                 new-name
                                                 new-enable
                                                 wrapper-name
                                                 wrapper-enable
                                                 thm-name
                                                 thm-enable
                                                 non-executable
                                                 verify-guards
                                                 hints
                                                 print
                                                 show-only
                                                 ctx state))
       (app-conds (tailrec-app-conds
                   old-fn-name test base nonrec combine q r variant domain$
                   do-verify-guards
                   state))
       ((er &) (ensure-named-formulas app-conds
                                      hints-alist
                                      (if (member-eq :expand print$) t nil)
                                      t nil ctx state))
       (event (tailrec-event
               old-fn-name test base nonrec updates combine q r
               variant domain$
               new-fn-name new-fn-enable
               wrapper-fn-name wrapper-enable
               old-to-wrapper-thm-name thm-enable
               make-non-executable do-verify-guards
               hints-alist print$ show-only app-conds
               call state)))
    (value event)))

(defsection tailrec-implementation
  :parents (implementation tailrec)
  :short "Implementation of the tail recursion transformation."
  :long
  "<p>
   Submit the event form generated by @(tsee tailrec-fn),.
   </p>
   @(def tailrec)"
  (defmacro tailrec (&whole
                     call
                     ;; mandatory inputs:
                     old
                     ;; optional inputs:
                     &key
                     (variant ':monoid)
                     (domain ':auto)
                     (new-name ':auto)
                     (new-enable ':auto)
                     (wrapper-name ':auto)
                     (wrapper-enable 't)
                     (thm-name ':auto)
                     (thm-enable 't)
                     (non-executable ':auto)
                     (verify-guards ':auto)
                     (hints 'nil)
                     (print ':result)
                     (show-only 'nil))
    `(make-event-terse (tailrec-fn ',old
                                   ',variant
                                   ',domain
                                   ',new-name
                                   ',new-enable
                                   ',wrapper-name
                                   ',wrapper-enable
                                   ',thm-name
                                   ',thm-enable
                                   ',non-executable
                                   ',verify-guards
                                   ',hints
                                   ',print
                                   ',show-only
                                   ',call
                                   (cons 'tailrec ',old)
                                   state))))
