; APT (Automated Program Transformations) Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "APT")

(include-book "kestrel/error-checking/ensure-function-is-defined" :dir :system)
(include-book "kestrel/error-checking/ensure-function-is-guard-verified" :dir :system)
(include-book "kestrel/error-checking/ensure-function-is-logic-mode" :dir :system)
(include-book "kestrel/error-checking/ensure-value-is-boolean" :dir :system)
(include-book "kestrel/error-checking/ensure-value-is-not-in-list" :dir :system)
(include-book "kestrel/error-checking/ensure-value-is-symbol" :dir :system)
(include-book "kestrel/event-macros/applicability-conditions" :dir :system)
(include-book "kestrel/event-macros/event-generation" :dir :system)
(include-book "kestrel/event-macros/input-processing" :dir :system)
(include-book "kestrel/event-macros/intro-macros" :dir :system)
(include-book "kestrel/event-macros/proof-preparation" :dir :system)
(include-book "kestrel/event-macros/restore-output" :dir :system)
(include-book "kestrel/event-macros/xdoc-constructors" :dir :system)
(include-book "kestrel/std/system/fresh-logical-name-with-dollars-suffix" :dir :system)
(include-book "kestrel/std/system/install-not-normalized-event" :dir :system)
(include-book "kestrel/utilities/error-checking/top" :dir :system)
(include-book "kestrel/utilities/keyword-value-lists" :dir :system)
(include-book "kestrel/utilities/orelse" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

(include-book "utilities/defaults-table")
(include-book "utilities/input-processing")
(include-book "utilities/transformation-table")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-implementation

 tailrec

 :items

 (xdoc::*evmac-topic-implementation-item-state*

  xdoc::*evmac-topic-implementation-item-wrld*

  xdoc::*evmac-topic-implementation-item-ctx*

  "@('old'),
   @('variant'),
   @('domain'),
   @('new-name'),
   @('new-enable'),
   @('wrapper'),
   @('wrapper-name'),
   @('wrapper-enable'),
   @('old-to-new-name'),
   @('old-to-new-enable'),
   @('new-to-old-name'),
   @('new-to-old-enable'),
   @('old-to-wrapper-name'),
   @('old-to-wrapper-enable'),
   @('wrapper-to-old-name'),
   @('wrapper-to-old-enable'),
   @('verify-guards'),
   @('hints'),
   @('print'), and
   @('show-only')
   are the homonymous inputs to @(tsee tailrec),
   before being processed.
   These formal parameters have no types because they may be any values."

  "@('wrapper-name-present'),
   @('wrapper-enable-present'),
   @('old-to-new-name-present'),
   @('old-to-new-enable-present'),
   @('new-to-old-name-present'),
   @('new-to-old-enable-present'),
   @('old-to-wrapper-name-present'),
   @('old-to-wrapper-enable-present')
   @('wrapper-to-old-name-present'), and
   @('wrapper-to-old-enable-present')
   are boolean flags indicating whether the corresponding inputs
   (whose name is obtained by removing @('-present') from these)
   are present (i.e. supplied by the user) or not."

  "@('call') is the call to @(tsee tailrec) supplied by the user."

  "@('old$'),
   @('variant$'),
   @('domain$'),
   @('new-name$'),
   @('new-enable$'),
   @('wrapper$'),
   @('wrapper-name$'),
   @('wrapper-enable$'),
   @('old-to-new-name$'),
   @('old-to-new-enable$'),
   @('new-to-old-name$'),
   @('new-to-old-enable$'),
   @('old-to-wrapper-name$'),
   @('wrapper-to-old-name$'),
   @('verify-guards$'),
   @('hints$'),
   @('print$'), and
   @('show-only$')
   are the results of processing
   the homonymous inputs (without the @('$')) to @(tsee tailrec).
   Some are identical to the corresponding inputs,
   but they have types implied by their successful validation,
   performed when they are processed."

  "@('test') is the term @('test<x1,...,xn>') described in the documentation."

  "@('base') is the term @('base<x1,...,xn>') described in the documentation."

  "@('rec-branch') is the recursive branch of the target function,
   namely the term @('combine<nonrec<x1,...,xn>,
                     (old update-x1<x1,...,xn>
                          ...
                          update-xn<x1,...,xn>)>')
   described in the documentation."

  "@('nonrec') is the term @('nonrec<x1,...,xn>')
   described in the documentation."

  "@('updates') is the list of terms
   @('update-x1<x1,...,xn>'), ..., @('update-xn<x1,...,xn>')
   described in the documentation."

  "@('r') is the homonymous fresh variable described in the documentation."

  "@('q') is the homonymous fresh variable described in the documentation."

  "@('combine-nonrec') is the term @('combine<nonrec<x1,...,xn>,r>')
   described in the documentation."

  "@('combine') is the term @('combine<q,r>') described in the documentation."

  "@('a') is the homonymous accumulator variable
   described in the documentation."

  "@('verbose') is a flag saying
   whether to print certain informative messages or not."

  "@('appcond-thm-names') is an alist
   from the keywords that identify the applicability conditions
   to the corresponding generated theorem names."

  "@('old-unnorm-name') is the name of the generated theorem
   that installs the non-normalized definition of the target function."

  "@('new-unnorm-name') is the name of the generated theorem
   that installs the non-normalized definition of the new function."

  "@('wrapper-unnorm-name') is the name of the generated theorem
   that installs the non-normalized definition of the wrapper function."

  "@('new-formals') are the formal parameters of the new function."

  "@('domain-of-old-name') is the name of the theorem
   generated by @(tsee tailrec-gen-domain-of-old-thm)."

  "@('alpha-name') is the name of the function
   generated by @(tsee tailrec-gen-alpha-fn)."

  "@('test-of-alpha-name') is the name of the theorem
   generated by @(tsee tailrec-gen-test-of-alpha-thm)."

  "@('old-guard-of-alpha-name') is the name of the theorem
   generated by @(tsee tailrec-gen-old-guard-of-alpha-thm)."

  "@('domain-of-ground-base-name') is the name of the theorem
   generated by @(tsee tailrec-gen-domain-of-ground-base-thm)."

  "@('combine-left-identity-ground-name') is the name of the theorem
   generated by @(tsee tailrec-gen-combine-left-identity-ground-thm)."

  "@('base-guard-name') is the name of the theorem
   generated by @(tsee tailrec-gen-base-guard-thm)."

  "@('names-to-avoid') is a cumulative list of names of generated events,
   used to ensure the absence of name clashes in the generated events."))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-input-processing tailrec)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tailrec-check-nonrec-conditions
  ((combine-nonrec pseudo-termp)
   (nonrec? pseudo-termp "Candidate @('nonrec<x1,...,xn>') to check.")
   (r symbolp)
   (q symbolp))
  :returns
  (mv (yes/no booleanp)
      (combine "The @(tsee pseudo-termp) @('combine<q,r>')
                described in the documentation,
                if @('yes/no') is @('t');
                otherwise @('nil')."))
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines tailrec-find-nonrec-term-in-term/terms
  :short "Decompose @('combine<nonrec<x1,...,xn>,r>') into
          @('nonrec<x1,...,xn>') and @('combine<q,r>'),
          as described in the documentation."
  :verify-guards nil

  (define tailrec-find-nonrec-term
    ((combine-nonrec pseudo-termp)
     (term-to-try pseudo-termp "Subterm of @('combine<nonrec<x1,...,xn>,r>')
                                to examine next.")
     (r symbolp)
     (q symbolp))
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
    ((combine-nonrec pseudo-termp)
     (terms-to-try pseudo-term-listp "Subterms of @('combine-nonrec')
                                      to examine next.")
     (r symbolp)
     (q symbolp))
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tailrec-decompose-recursive-branch ((old$ symbolp)
                                            (rec-branch pseudo-termp)
                                            ctx
                                            state)
  :returns (mv erp
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
  (b* ((rec-calls (all-calls (list old$) rec-branch nil nil))
       (rec-calls (remove-duplicates-equal rec-calls))
       ((when (/= (len rec-calls) 1))
        (er-soft+ ctx t nil
                  "After translation and LET expansion, ~
                   the recursive branch ~x0 of the target function ~x1 ~
                   must not contain different calls to ~x1."
                  rec-branch old$))
       (rec-call (car rec-calls))
       ((when (equal rec-call rec-branch))
        (er-soft+ ctx t nil
                  "The target function ~x0 is already tail-recursive."
                  old$))
       (updates (fargs rec-call))
       (formals (formals old$ (w state)))
       (r (genvar old$ "R" nil formals))
       (q (genvar old$ "Q" nil formals))
       (combine-nonrec (subst-expr r rec-call rec-branch))
       ((er &) (ensure-term-not-call-of$
                combine-nonrec
                'if
                (msg "After translation and LET expansion, ~
                      and after replacing the calls to ~x0 ~
                      with a fresh variable ~x1, ~
                      the recursive branch ~x2 of the target function ~x0"
                     old$ r combine-nonrec)
                t nil))
       ((mv found nonrec combine)
        (tailrec-find-nonrec-term combine-nonrec combine-nonrec r q))
       ((unless found)
        (er-soft+ ctx t nil
                  "Unable to decompose the recursive branch ~x0 ~
                   of the target function ~x1." rec-branch old$)))
    (value (list nonrec updates combine q r))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tailrec-process-old (old
                             variant
                             verify-guards
                             (verbose booleanp)
                             ctx
                             state)
  :returns (mv erp
               (result "A tuple @('(old$
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
                        where @('old$') is the name
                        of the target function of the transformation
                        (denoted by the @('old') input)
                        and the other components
                        are described in the documentation.")
               state)
  :mode :program
  :short "Process the @('old') input."
  :long
  "<p>
   Show the components of the function denoted by @('old')
   if @('verbose') is @('t').
   </p>"
  (b* ((wrld (w state))
       ((er old$) (ensure-function-name-or-numbered-wildcard$
                   old "The first input" t nil))
       (description (msg "The target function ~x0" old$))
       ((er &) (ensure-function-is-logic-mode$ old$ description t nil))
       ((er &) (ensure-function-is-defined$ old$ description t nil))
       ((er &) (ensure-function-number-of-results$ old$ 1
                                                   description t nil))
       ((er &) (ensure-function-no-stobjs$ old$ description t nil))
       ((er &) (ensure-function-singly-recursive$ old$
                                                  description t nil))
       ((er &) (ensure-function-known-measure$ old$ description t nil))
       (body (if (non-executablep old$ wrld)
                 (unwrapped-nonexec-body old$ wrld)
               (ubody old$ wrld)))
       (body (remove-lambdas body))
       ((er (list test then else))
        (ensure-term-if-call$ body
                              (msg "After translation and LET expansion, ~
                                    the body ~x0 of the target function ~x1"
                                   body old$)
                              t nil))
       (then-calls-old-p (ffnnamep old$ then))
       (else-calls-old-p (ffnnamep old$ else))
       ((when (and then-calls-old-p else-calls-old-p))
        (er-soft+ ctx t nil
                  "After translation and LET expansion, ~
                   the body ~x0 of the target fuction ~x1 ~
                   must have one non-recursive top-level IF branch;
                   however, both branches call ~x1."
                  body old$))
       ((mv test base combine-nonrec-reccall)
        (if then-calls-old-p
            (mv (dumb-negate-lit test) else then)
          (mv test then else)))
       ((er &) (ensure-term-does-not-call$
                test old$
                (msg "After translation and LET expansion, ~
                      the exit test ~x0 ~
                      of the target function ~x1"
                     test old$)
                t nil))
       ((er &) (if (member-eq variant '(:monoid :monoid-alt))
                   (ensure-term-ground$
                    base
                    (msg "Since the :VARIANT input is ~s0~x1, ~
                          after translation and LET expansion, ~
                          the non-recursive branch ~x2 ~
                          of the target function ~x3"
                         (if (eq variant :monoid)
                             "(perhaps by default) "
                           "")
                         variant
                         base
                         old$)
                    t nil)
                 (value nil)))
       ((er (list nonrec updates combine q r))
        (tailrec-decompose-recursive-branch
         old$ combine-nonrec-reccall ctx state))
       ((er &) (if (eq verify-guards t)
                   (ensure-function-is-guard-verified$
                    old$
                    (msg "Since the :VERIFY-GUARDS input is T, ~
                          the target function ~x0" old$)
                    t nil)
                 (value nil)))
       ((run-when verbose)
        (cw "~%")
        (cw "Components of the target function ~x0:~%" old$)
        (cw "- Exit test: ~x0.~%" (untranslate test nil wrld))
        (cw "- Base value: ~x0.~%" (untranslate base nil wrld))
        (cw "- Non-recursive computation: ~x0.~%" (untranslate nonrec nil wrld))
        (cw "- Argument updates: ~x0.~%" (untranslate-lst updates nil wrld))
        (cw "- Combination operator: ~x0.~%" (untranslate combine nil wrld))
        (cw "- Fresh variable for non-recursive computation: ~x0.~%" q)
        (cw "- Fresh variable for recursive call: ~x0.~%" r)))
    (value (list old$ test base nonrec updates combine q r))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defenum tailrec-variantp (:assoc :assoc-alt :monoid :monoid-alt)
  :short "Variants of the tail recursion transformation.")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-error-checker tailrec-process-variant (variant)
  :short "Process the @('variant') input."
  :body
  (((tailrec-variantp variant)
    "~@0 must be :MONOID, :MONOID-ALT, :ASSOC or :ASSOC-ALT." description)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tailrec-infer-domain ((combine pseudo-termp)
                              (q symbolp)
                              (r symbolp)
                              (variant$ tailrec-variantp)
                              (verbose booleanp)
                              (wrld plist-worldp))
  :returns (domain "A @(tsee pseudo-termfnp).")
  :verify-guards nil
  :short "Infer the domain over which some applicability conditions must hold."
  :long
  (xdoc::topstring-p
   "This is used when the @(':domain') input is @(':auto').
    A domain is inferred as described in the documentation.")
  (b* ((default '(lambda (x) 't))
       (domain
        (if (member-eq variant$ '(:monoid :monoid-alt))
            (case-match combine
              ((op . args)
               (b* (((unless (symbolp op)) default)
                    ((unless (or (equal args (list q r))
                                 (equal args (list r q))))
                     default)
                    ((list y1 y2) (formals op wrld))
                    (guard (uguard op wrld)))
                 (case-match guard
                   (('if (dom !y1) (dom !y2) *nil*)
                    (if (symbolp dom)
                        dom
                      default))
                   (('if (dom !y2) (dom !y1) *nil*)
                    (if (symbolp dom)
                        dom
                      default))
                   ((dom !y1)
                    (if (symbolp dom)
                        dom
                      default))
                   ((dom !y2)
                    (if (symbolp dom)
                        dom
                      default))
                   (& default))))
              (& default))
          default))
       ((run-when verbose)
        (cw "~%")
        (cw "Inferred domain for the applicability conditions: ~x0.~%" domain)))
    domain))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tailrec-process-domain (domain
                                (old$ symbolp)
                                (combine pseudo-termp)
                                (q symbolp)
                                (r symbolp)
                                (variant$ tailrec-variantp)
                                (verify-guards$ booleanp)
                                (verbose booleanp)
                                ctx
                                state)
  :returns (mv erp
               (domain$ "A @(tsee pseudo-termfnp) that is
                         the predicate denoted by @('domain').")
               state)
  :mode :program
  :short "Process the @(':domain') input."
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
        (value (tailrec-infer-domain combine q r variant$ verbose wrld)))
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
       ((er &) (if verify-guards$
                   (ensure-function/lambda-guard-verified-exec-fns$
                    fn/lambda
                    (msg "Since either the :VERIFY-GUARDS input is T, ~
                          or it is (perhaps by default) :AUTO ~
                          and the target function ~x0 is guard-verified, ~@1"
                         old$ (msg-downcase-first description))
                    t nil)
                 (value nil)))
       ((er &) (if (symbolp fn/lambda)
                   (ensure-symbol-different$ fn/lambda
                                             old$
                                             (msg "the target function ~x0"
                                                  old$)
                                             description t nil)
                 (ensure-term-does-not-call$ (lambda-body fn/lambda)
                                             old$
                                             description t nil))))
    (value fn/lambda)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tailrec-process-accumulator (accumulator
                                     (old$ symbolp)
                                     (r symbolp)
                                     ctx
                                     state)
  :returns (mv erp (a symbolp) state)
  :short "Process the @(':accumulator') input."
  (if (eq accumulator :auto)
      (value (mbe :logic (acl2::symbol-fix r) :exec r))
    (b* (((unless (legal-variablep accumulator))
          (er-soft+ ctx t nil
                    "The :ACCUMULATOR input must be a legal variable name,
                     but ~x0 is not a legal variable name."
                    accumulator))
         (x1...xn (formals+ old$ (w state)))
         ((er &) (ensure-value-is-not-in-list$
                  accumulator
                  x1...xn
                  (msg "one of the formal arguments ~&0 of ~x1" x1...xn old$)
                  (msg "The :ACCUMULATOR input ~x0" accumulator)
                  t
                  nil)))
      (value accumulator))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tailrec-process-inputs (old
                                variant
                                domain
                                new-name
                                new-enable
                                accumulator
                                wrapper
                                wrapper-name
                                (wrapper-name-present booleanp)
                                wrapper-enable
                                (wrapper-enable-present booleanp)
                                old-to-new-name
                                (old-to-new-name-present booleanp)
                                old-to-new-enable
                                (old-to-new-enable-present booleanp)
                                new-to-old-name
                                (new-to-old-name-present booleanp)
                                new-to-old-enable
                                (new-to-old-enable-present booleanp)
                                old-to-wrapper-name
                                (old-to-wrapper-name-present booleanp)
                                old-to-wrapper-enable
                                (old-to-wrapper-enable-present booleanp)
                                wrapper-to-old-name
                                (wrapper-to-old-name-present booleanp)
                                wrapper-to-old-enable
                                (wrapper-to-old-enable-present booleanp)
                                verify-guards
                                hints
                                print
                                show-only
                                ctx
                                state)
  :returns (mv erp
               (result "A tuple @('(old$
                                    test<x1,...,xn>
                                    base<x1,...,xn>
                                    nonrec<x1,...,xn>
                                    (... update-xi<x1...,xn> ...)
                                    combine<q,r>
                                    q
                                    r
                                    domain$
                                    new-name$
                                    new-enable$
                                    a
                                    wrapper-name$
                                    wrapper-enable$
                                    old-to-new-name$
                                    old-to-new-enable$
                                    new-to-old-name$
                                    new-to-old-enable$
                                    old-to-wrapper-name$
                                    old-to-wrapper-enable$
                                    wrapper-to-old-name$
                                    wrapper-to-old-enable$
                                    verify-guards$
                                    hints$
                                    names-to-avoid)')
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
                                         symbolp
                                         booleanp
                                         symbolp
                                         booleanp
                                         symbolp
                                         booleanp
                                         symbolp
                                         booleanp
                                         booleanp
                                         evmac-input-hints-p
                                         symbol-listp
                                         result)').")
               state)
  :mode :program
  :short "Process all the inputs."
  (b* (((er &) (evmac-process-input-print print ctx state))
       (verbose (and (member-eq print '(:info :all)) t))
       ((er (list old$ test base nonrec updates combine q r))
        (tailrec-process-old old variant verify-guards verbose ctx state))
       ((er &) (tailrec-process-variant$ variant "The :VARIANT input" t nil))
       ((er verify-guards$) (process-input-verify-guards verify-guards
                                                         old$
                                                         ctx
                                                         state))
       ((er domain$) (tailrec-process-domain domain
                                             old$
                                             combine
                                             q
                                             r
                                             variant
                                             verify-guards$
                                             verbose
                                             ctx
                                             state))
       ((er &) (ensure-value-is-boolean$ wrapper "The :WRAPPER input" t nil))
       ((er (list new-name$ wrapper-name$ names-to-avoid))
        (process-input-new/wrapper-names new-name
                                         wrapper-name
                                         wrapper-name-present
                                         wrapper
                                         old$
                                         nil
                                         ctx
                                         state))
       ((er new-enable$) (process-input-new-enable new-enable old$ ctx state))
       ((er a) (tailrec-process-accumulator accumulator old$ r ctx state))
       ((er wrapper-enable$)
        (process-input-wrapper-enable wrapper-enable
                                      wrapper-enable-present
                                      wrapper
                                      ctx
                                      state))
       ((er (list old-to-new-name$ names-to-avoid))
        (process-input-old-to-new-name old-to-new-name
                                       old-to-new-name-present
                                       old$
                                       new-name$
                                       names-to-avoid
                                       ctx
                                       state))
       ((er old-to-new-enable$)
        (process-input-old-to-new-enable old-to-new-enable
                                         old-to-new-enable-present
                                         ctx
                                         state))
       ((er (list new-to-old-name$ names-to-avoid))
        (process-input-new-to-old-name new-to-old-name
                                       new-to-old-name-present
                                       old$
                                       new-name$
                                       names-to-avoid
                                       ctx
                                       state))
       ((er new-to-old-enable$)
        (process-input-new-to-old-enable new-to-old-enable
                                         new-to-old-enable-present
                                         ctx
                                         state))
       ((er (list old-to-wrapper-name$ names-to-avoid))
        (process-input-old-to-wrapper-name old-to-wrapper-name
                                           old-to-wrapper-name-present
                                           wrapper
                                           old$
                                           wrapper-name$
                                           names-to-avoid
                                           ctx
                                           state))
       ((er old-to-wrapper-enable$)
        (process-input-old-to-wrapper-enable old-to-wrapper-enable
                                             old-to-wrapper-enable-present
                                             wrapper
                                             ctx
                                             state))
       ((er (list wrapper-to-old-name$ names-to-avoid))
        (process-input-wrapper-to-old-name wrapper-to-old-name
                                           wrapper-to-old-name-present
                                           wrapper
                                           old$
                                           wrapper-name$
                                           names-to-avoid
                                           ctx
                                           state))
       ((er wrapper-to-old-enable$)
        (process-input-wrapper-to-old-enable wrapper-to-old-enable
                                             wrapper-to-old-enable-present
                                             wrapper
                                             ctx
                                             state))
       ((when (and old-to-new-enable$
                   new-to-old-enable$))
        (er-soft+ ctx t nil
                  "The :OLD-TO-NEW-ENABLE and :NEW-TO-OLD-ENABLE inputs ~
                   are (perhaps by default, for one of them) both T. ~
                   This is disallowed."))
       ((when (and wrapper
                   old-to-wrapper-enable$
                   wrapper-to-old-enable$))
        (er-soft+ ctx t nil
                  "The :OLD-TO-WRAPPER-ENABLE ~
                   and :WRAPPER-TO-OLD-ENABLE inputs ~
                   are (perhaps by default, for one of them) both T. ~
                   This is disallowed."))
       ((er hints$) (evmac-process-input-hints hints ctx state))
       ((er &) (evmac-process-input-show-only show-only ctx state)))
    (value (list old$
                 test
                 base
                 nonrec
                 updates
                 combine
                 q
                 r
                 domain$
                 new-name$
                 new-enable$
                 a
                 wrapper-name$
                 wrapper-enable$
                 old-to-new-name$
                 old-to-new-enable$
                 new-to-old-name$
                 new-to-old-enable$
                 old-to-wrapper-name$
                 old-to-wrapper-enable$
                 wrapper-to-old-name$
                 wrapper-to-old-enable$
                 verify-guards$
                 hints$
                 names-to-avoid))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-event-generation tailrec
                                    :some-local-nonlocal-p t
                                    :some-local-p t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tailrec-gen-var-u ((old$ symbolp))
  :returns (u "A @(tsee symbolp).")
  :mode :program
  :short "Generate the variable @('u') to use in the
          @(':domain-of-combine'),
          @(':domain-of-combine-uncond'),
          @(':combine-associativity'), and
          @(':combine-associativity-uncond')
          applicability conditions."
  (genvar old$ "U" nil nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tailrec-gen-var-v ((old$ symbolp))
  :returns (v "A @(tsee symbolp).")
  :mode :program
  :short "Generate the variable @('u') to use in the
          @(':domain-of-combine'),
          @(':domain-of-combine-uncond'),
          @(':combine-associativity'), and
          @(':combine-associativity-uncond')
          applicability conditions."
  (genvar old$ "V" nil nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tailrec-gen-var-w ((old$ symbolp))
  :returns (w "A @(tsee symbolp).")
  :mode :program
  :short "Generate the variable @('u') to use in the
          @(':combine-associativity') and
          @(':combine-associativity-uncond')
          applicability conditions."
  (genvar old$ "W" nil nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tailrec-gen-id-var-u ((old$ symbolp) (wrld plist-worldp))
  :returns (u "A @(tsee symbolp).")
  :mode :program
  :short "Generate the variable @('u') to use in the
          @(':combine-left-identity') and
          @(':combine-right-identity')
          applicability conditions."
  :long
  "<p>
   This must be distinct from the formals of the old function.
   </p>"
  (genvar old$ "U" nil (formals old$ wrld)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tailrec-gen-combine-op ((combine pseudo-termp)
                                (q symbolp)
                                (r symbolp))
  :returns (combine-op pseudo-lambdap
                       :hyp :guard
                       :hints (("Goal" :in-theory (enable pseudo-lambdap))))
  :short "Generate the combination operator."
  :long
  "<p>
   This is obtained by abstracting @('combine<q,r>') over @('q') and @('r').
   </p>"
  (make-lambda (list q r) combine))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tailrec-gen-appconds ((old$ symbolp)
                              (test pseudo-termp)
                              (base pseudo-termp)
                              (nonrec pseudo-termp)
                              (combine pseudo-termp)
                              (q symbolp)
                              (r symbolp)
                              (domain$ pseudo-termfnp)
                              (variant$ tailrec-variantp)
                              (verify-guards$ booleanp)
                              state)
  :returns (appconds "A @(tsee evmac-appcond-listp).")
  :short "Generate the applicability conditions."
  :mode :program
  (b* ((wrld (w state))
       (u (tailrec-gen-var-u old$))
       (v (tailrec-gen-var-v old$))
       (w (tailrec-gen-var-w old$))
       (u1 (tailrec-gen-id-var-u old$ wrld))
       (combine-op (tailrec-gen-combine-op combine q r)))
    (append
     (make-evmac-appcond?
      :domain-of-base
      (implicate test
                 (apply-term* domain$ base))
      :when (member-eq variant$ '(:monoid :monoid-alt :assoc)))
     (make-evmac-appcond?
      :domain-of-nonrec
      (implicate (dumb-negate-lit test)
                 (apply-term* domain$ nonrec))
      :when (member-eq variant$ '(:monoid :assoc)))
     (make-evmac-appcond?
      :domain-of-combine
      (implicate (conjoin2 (apply-term* domain$ u)
                           (apply-term* domain$ v))
                 (apply-term* domain$
                              (apply-term* combine-op u v)))
      :when (member-eq variant$ '(:monoid :assoc :assoc-alt)))
     (make-evmac-appcond?
      :domain-of-combine-uncond
      (apply-term* domain$
                   (apply-term* combine-op u v))
      :when (eq variant$ :monoid-alt))
     (make-evmac-appcond?
      :combine-associativity
      (implicate
       (conjoin (list (apply-term* domain$ u)
                      (apply-term* domain$ v)
                      (apply-term* domain$ w)))
       `(equal ,(apply-term* combine-op
                             u
                             (apply-term* combine-op v w))
               ,(apply-term* combine-op
                             (apply-term* combine-op u v)
                             w)))
      :when (member-eq variant$ '(:monoid :assoc)))
     (make-evmac-appcond?
      :combine-associativity-uncond
      `(equal ,(apply-term* combine-op
                            u
                            (apply-term* combine-op v w))
              ,(apply-term* combine-op
                            (apply-term* combine-op u v)
                            w))
      :when (member-eq variant$ '(:monoid-alt :assoc-alt)))
     (make-evmac-appcond?
      :combine-left-identity
      (implicate (conjoin2 test
                           (apply-term* domain$ u1))
                 `(equal ,(apply-term* combine-op base u1)
                         ,u1))
      :when (member-eq variant$ '(:monoid :monoid-alt)))
     (make-evmac-appcond?
      :combine-right-identity
      (implicate (conjoin2 test
                           (apply-term* domain$ u1))
                 `(equal ,(apply-term* combine-op u1 base)
                         ,u1))
      :when (member-eq variant$ '(:monoid :monoid-alt)))
     (make-evmac-appcond?
      :domain-guard
      (if (symbolp domain$)
          (guard domain$ nil wrld)
        (term-guard-obligation (lambda-body domain$) state))
      :when verify-guards$)
     (make-evmac-appcond?
      :combine-guard
      (implicate (conjoin2 (apply-term* domain$ q)
                           (apply-term* domain$ r))
                 (term-guard-obligation combine state))
      :when verify-guards$)
     (make-evmac-appcond?
      :domain-of-base-when-guard
      (implicate (conjoin2 (guard old$ nil wrld)
                           test)
                 (apply-term* domain$ base))
      :when (and (eq variant$ :assoc-alt)
                 verify-guards$))
     (make-evmac-appcond?
      :domain-of-nonrec-when-guard
      (implicate (conjoin2 (guard old$ nil wrld)
                           (dumb-negate-lit test))
                 (apply-term* domain$ nonrec))
      :when (and (member-eq variant$ '(:monoid-alt :assoc-alt))
                 verify-guards$)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tailrec-gen-domain-of-old-thm ((old$ symbolp)
                                       (test pseudo-termp)
                                       (nonrec pseudo-termp)
                                       (updates pseudo-term-listp)
                                       (variant$ tailrec-variantp)
                                       (domain$ pseudo-termfnp)
                                       (names-to-avoid symbol-listp)
                                       (appcond-thm-names symbol-symbol-alistp)
                                       (old-unnorm-name symbolp)
                                       (wrld plist-worldp))
  :returns (mv (event "A @(tsee pseudo-event-formp).")
               (name "A @(tsee symbolp) that names the theorem.")
               (updated-names-to-avoid "A @(tsee symbol-listp)."))
  :mode :program
  :short "Generate the theorem asserting that
          the old function always yields values in the domain
          (@($D{}f$) in the design notes)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is generated only if the variant is
     @(':monoid'), @(':monoid-alt'), or @(':assoc').")
   (xdoc::p
    "The theorem's formula is @('(domain (old x1 ... xn))').
     This is just @('t') if @('domain') is @('(lambda (x) t)')
     (e.g. as default).")
   (xdoc::p
    "The hints follow the proofs in the design notes.")
   (xdoc::p
    "This theorem event is local,
    because it is a lemma used to prove the exported main theorem."))
  (b* (((mv name names-to-avoid)
        (fresh-logical-name-with-$s-suffix 'domain-of-old
                                           nil
                                           names-to-avoid
                                           wrld))
       (formula (untranslate (apply-term* domain$
                                          (apply-term old$
                                                      (formals old$
                                                               wrld)))
                             t wrld))
       (hints
        (case variant$
          ((:monoid :assoc)
           (b* ((domain-of-base-thm
                 (cdr (assoc-eq :domain-of-base appcond-thm-names)))
                (domain-of-nonrec-thm
                 (cdr (assoc-eq :domain-of-nonrec appcond-thm-names)))
                (domain-of-combine-thm
                 (cdr (assoc-eq :domain-of-combine appcond-thm-names)))
                (domain-of-combine-instance
                 `(:instance ,domain-of-combine-thm
                   :extra-bindings-ok
                   (,(tailrec-gen-var-u old$)
                    ,nonrec)
                   (,(tailrec-gen-var-v old$)
                    (,old$ ,@updates)))))
             `(("Goal"
                :in-theory '(,old-unnorm-name
                             (:induction ,old$))
                :induct (,old$ ,@(formals old$ wrld)))
               '(:use (,domain-of-base-thm
                       ,domain-of-nonrec-thm
                       ,domain-of-combine-instance)))))
          (:monoid-alt
           (b* ((domain-of-base-thm
                 (cdr (assoc-eq :domain-of-base appcond-thm-names)))
                (domain-of-combine-uncond-thm
                 (cdr (assoc-eq :domain-of-combine-uncond appcond-thm-names)))
                (domain-of-combine-uncond-instance
                 `(:instance ,domain-of-combine-uncond-thm
                   :extra-bindings-ok
                   (,(tailrec-gen-var-u old$)
                    ,nonrec)
                   (,(tailrec-gen-var-v old$)
                    (,old$ ,@updates)))))
             `(("Goal"
                :in-theory '(,old-unnorm-name)
                :cases (,test))
               '(:use (,domain-of-base-thm
                       ,domain-of-combine-uncond-instance)))))
          (:assoc-alt
           (raise "Internal error: called when variant is :ASSOC-ALT."))
          (t (impossible))))
       (event `(local (defthm ,name
                        ,formula
                        :rule-classes nil
                        :hints ,hints))))
    (mv event name names-to-avoid)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tailrec-gen-new-fn ((old$ symbolp)
                            (test pseudo-termp)
                            (base pseudo-termp)
                            (nonrec pseudo-termp)
                            (updates pseudo-term-listp)
                            (combine pseudo-termp)
                            (q symbolp)
                            (r symbolp)
                            (variant$ tailrec-variantp)
                            (domain$ pseudo-termfnp)
                            (new-name$ symbolp)
                            (new-enable$ booleanp)
                            (a symbolp)
                            (verify-guards$ booleanp)
                            (appcond-thm-names symbol-symbol-alistp)
                            (wrld plist-worldp))
  :returns (mv (local-event "A @(tsee pseudo-event-formp).")
               (exported-event "A @(tsee pseudo-event-formp).")
               (new-formals "A @(tsee symbol-listp)."))
  :mode :program
  :short "Generate the new function definition."
  :long
  "<p>
   The macro used to introduce the new function is determined by
   whether the new function must be
   enabled or not, and non-executable or not.
   We make it non-executable if and only if @('old') is non-executable.
   </p>
   <p>
   The formals of the new function consist of
   the formals of the old function
   followed by the variable @('a') generated
   during the decomposition of the recursive branch of the old function.
   This variable is distinct from the formals of the old function
   by construction.
   The formals of the new function are return as one of the results.
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
   with the fact that the additional formal @('a') is in the domain,
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
  (b* ((macro (function-intro-macro new-enable$ (non-executablep old$ wrld)))
       (new-formals (rcons a (formals old$ wrld)))
       (body
        (b* ((combine-op (tailrec-gen-combine-op combine q r))
             (nonrec-branch (case variant$
                              ((:monoid :monoid-alt) a)
                              ((:assoc :assoc-alt)
                               (apply-term* combine-op a base))
                              (t (impossible))))
             (rec-branch (subcor-var (cons a (formals old$ wrld))
                                     (cons (apply-term* combine-op a nonrec)
                                           updates)
                                     (apply-term new-name$ new-formals)))
             (body `(if ,test
                        ,nonrec-branch
                      ,rec-branch)))
          (untranslate body nil wrld)))
       (wfrel (well-founded-relation old$ wrld))
       (measure (untranslate (measure old$ wrld) nil wrld))
       (termination-hints
        `(("Goal" :use (:termination-theorem ,old$) :in-theory nil)))
       (guard (untranslate (conjoin2 (guard old$ nil wrld)
                                     (apply-term* domain$ a))
                           t wrld))
       (guard-hints
        (case variant$
          ((:monoid :assoc)
           (b* ((z (car (if (symbolp domain$)
                            (formals domain$ wrld)
                          (lambda-formals domain$))))
                (domain-of-base-thm
                 (cdr (assoc-eq :domain-of-base appcond-thm-names)))
                (domain-of-nonrec-thm
                 (cdr (assoc-eq :domain-of-nonrec appcond-thm-names)))
                (domain-of-combine-thm
                 (cdr (assoc-eq :domain-of-combine appcond-thm-names)))
                (domain-guard-thm
                 (cdr (assoc-eq :domain-guard appcond-thm-names)))
                (combine-guard-thm
                 (cdr (assoc-eq :combine-guard appcond-thm-names)))
                (domain-of-combine-instance
                 `(:instance ,domain-of-combine-thm
                   :extra-bindings-ok
                   (,(tailrec-gen-var-u old$) ,a)
                   (,(tailrec-gen-var-v old$) ,nonrec)))
                (domain-guard-instance
                 `(:instance ,domain-guard-thm
                   :extra-bindings-ok
                   (,z ,a)))
                (combine-guard-instance-base
                 `(:instance ,combine-guard-thm
                   :extra-bindings-ok
                   (,q ,a)
                   (,r ,base)))
                (combine-guard-instance-nonrec
                 `(:instance ,combine-guard-thm
                   :extra-bindings-ok
                   (,q ,a)
                   (,r ,nonrec))))
             `(("Goal"
                :in-theory nil
                :use ((:guard-theorem ,old$)
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
                 (cdr (assoc-eq :domain-of-base appcond-thm-names)))
                (domain-of-combine-uncond-thm
                 (cdr (assoc-eq :domain-of-combine-uncond appcond-thm-names)))
                (domain-guard-thm
                 (cdr (assoc-eq :domain-guard appcond-thm-names)))
                (combine-guard-thm
                 (cdr (assoc-eq :combine-guard appcond-thm-names)))
                (domain-of-nonrec-when-guard-thm
                 (cdr (assoc-eq :domain-of-nonrec-when-guard
                        appcond-thm-names)))
                (domain-of-combine-uncond-instance
                 `(:instance ,domain-of-combine-uncond-thm
                   :extra-bindings-ok
                   (,(tailrec-gen-var-u old$) ,a)
                   (,(tailrec-gen-var-v old$) ,nonrec)))
                (domain-guard-instance
                 `(:instance ,domain-guard-thm
                   :extra-bindings-ok
                   (,z ,a)))
                (combine-guard-instance-base
                 `(:instance ,combine-guard-thm
                   :extra-bindings-ok
                   (,q ,a)
                   (,r ,base)))
                (combine-guard-instance-nonrec
                 `(:instance ,combine-guard-thm
                   :extra-bindings-ok
                   (,q ,a)
                   (,r ,nonrec))))
             `(("Goal"
                :in-theory nil
                :use ((:guard-theorem ,old$)
                      ,domain-guard-instance
                      ,domain-of-base-thm
                      ,domain-of-nonrec-when-guard-thm
                      ,combine-guard-instance-base
                      ,combine-guard-instance-nonrec
                      ,domain-of-combine-uncond-instance)))))
          (:assoc-alt
           (b* ((z (car (if (symbolp domain$)
                            (formals domain$ wrld)
                          (lambda-formals domain$))))
                (domain-of-combine-thm
                 (cdr (assoc-eq :domain-of-combine appcond-thm-names)))
                (domain-guard-thm
                 (cdr (assoc-eq :domain-guard appcond-thm-names)))
                (combine-guard-thm
                 (cdr (assoc-eq :combine-guard appcond-thm-names)))
                (domain-of-base-when-guard-thm
                 (cdr (assoc-eq :domain-of-base-when-guard
                        appcond-thm-names)))
                (domain-of-nonrec-when-guard-thm
                 (cdr (assoc-eq :domain-of-nonrec-when-guard
                        appcond-thm-names)))
                (domain-of-combine-instance
                 `(:instance ,domain-of-combine-thm
                   :extra-bindings-ok
                   (,(tailrec-gen-var-u old$) ,a)
                   (,(tailrec-gen-var-v old$) ,nonrec)))
                (domain-guard-instance
                 `(:instance ,domain-guard-thm
                   :extra-bindings-ok
                   (,z ,a)))
                (combine-guard-instance-base
                 `(:instance ,combine-guard-thm
                   :extra-bindings-ok
                   (,q ,a)
                   (,r ,base)))
                (combine-guard-instance-nonrec
                 `(:instance ,combine-guard-thm
                   :extra-bindings-ok
                   (,q ,a)
                   (,r ,nonrec))))
             `(("Goal"
                :in-theory nil
                :use ((:guard-theorem ,old$)
                      ,domain-guard-instance
                      ,domain-of-base-when-guard-thm
                      ,domain-of-nonrec-when-guard-thm
                      ,combine-guard-instance-base
                      ,combine-guard-instance-nonrec
                      ,domain-of-combine-instance)))))
          (t (impossible))))
       (local-event
        `(local
          (,macro ,new-name$ (,@new-formals)
                  (declare (xargs :well-founded-relation ,wfrel
                                  :measure ,measure
                                  :hints ,termination-hints
                                  :guard ,guard
                                  :verify-guards ,verify-guards$
                                  ,@(and verify-guards$
                                         (list :guard-hints guard-hints))))
                  ,body)))
       (exported-event
        `(,macro ,new-name$ (,@new-formals)
                 (declare (xargs :well-founded-relation ,wfrel
                                 :measure ,measure
                                 :guard ,guard
                                 :verify-guards ,verify-guards$))
                 ,body)))
    (mv local-event exported-event new-formals)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tailrec-gen-new-to-old-thm ((old$ symbolp)
                                    (nonrec pseudo-termp)
                                    (updates pseudo-term-listp)
                                    (combine pseudo-termp)
                                    (q symbolp)
                                    (r symbolp)
                                    (variant$ tailrec-variantp)
                                    (domain$ pseudo-termfnp)
                                    (new-name$ symbolp)
                                    (a symbolp)
                                    (new-to-old-name$ symbolp)
                                    (new-to-old-enable$ booleanp)
                                    (appcond-thm-names symbol-symbol-alistp)
                                    (old-unnorm-name symbolp)
                                    (domain-of-old-name symbolp)
                                    (new-formals symbol-listp)
                                    (new-unnorm-name symbolp)
                                    (wrld plist-worldp))
  :returns (mv (local-event "A @(tsee pseudo-event-formp).")
               (exported-event "A @(tsee pseudo-event-formp)."))
  :mode :program
  :short "Generate the theorem equating the new function
          to a combination of the old function with @('a')
          (@($f'{}f$) in the design notes)."
  :long
  (xdoc::topstring
   (xdoc::p
    "The theorem's formula is")
   (xdoc::codeblock
    "(implies (domain a)"
    "         (equal (new x1 ... xn a)"
    "                combine<a,(old x1 ... xn)>))")
   (xdoc::p
    "if the variant is @(':monoid'), @(':monoid-alt'), or @(':assoc'),
     while it is")
   (xdoc::codeblock
    "(equal (new x1 ... xn a)"
    "       combine<a,(old x1 ... xn)>)")
   (xdoc::p
    "if the variant is @(':assoc-alt').")
   (xdoc::p
    "The hints follow the proofs in the design notes.
     Note that @('combine-right-identity-thm?') is @('nil') iff
     the @(':combine-right-identity') applicability condition is absent,
     which happens exactly when
     the @(':variant') input to the transformation
     is @(':assoc') or @(':assoc-alt').
     In this case, no instance of that applicability condition
     is used in the proof."))
  (b* ((formula `(equal ,(apply-term new-name$ new-formals)
                        ,(apply-term* (tailrec-gen-combine-op combine q r)
                                      a
                                      (apply-term old$
                                                  (formals old$
                                                           wrld)))))
       (formula (if (eq variant$ :assoc-alt)
                    formula
                  (implicate (apply-term* domain$ a)
                             formula)))
       (formula (untranslate formula t wrld))
       (hints
        (case variant$
          ((:monoid :assoc)
           (b* ((domain-of-nonrec-thm
                 (cdr (assoc-eq :domain-of-nonrec appcond-thm-names)))
                (domain-of-combine-thm
                 (cdr (assoc-eq :domain-of-combine appcond-thm-names)))
                (combine-associativity-thm
                 (cdr (assoc-eq :combine-associativity appcond-thm-names)))
                (combine-right-identity-thm?
                 (cdr (assoc-eq :combine-right-identity appcond-thm-names)))
                (domain-of-combine-instance
                 `(:instance ,domain-of-combine-thm
                   :extra-bindings-ok
                   (,(tailrec-gen-var-u old$) ,a)
                   (,(tailrec-gen-var-v old$) ,nonrec)))
                (combine-associativity-instance
                 `(:instance ,combine-associativity-thm
                   :extra-bindings-ok
                   (,(tailrec-gen-var-u old$) ,a)
                   (,(tailrec-gen-var-v old$) ,nonrec)
                   (,(tailrec-gen-var-w old$)
                    ,(apply-term old$ updates))))
                (combine-right-identity-instance?
                 (and combine-right-identity-thm?
                      `(:instance ,combine-right-identity-thm?
                        :extra-bindings-ok
                        (,(tailrec-gen-id-var-u old$ wrld) ,a))))
                (domain-of-old-instance
                 `(:instance ,domain-of-old-name
                   :extra-bindings-ok
                   ,@(alist-to-doublets (pairlis$ (formals old$ wrld)
                                                  updates)))))
             `(("Goal"
                :in-theory '(,old-unnorm-name
                             ,new-unnorm-name
                             (:induction ,new-name$))
                :induct (,new-name$ ,@new-formals))
               '(:use (,@(and combine-right-identity-thm?
                              (list combine-right-identity-instance?))
                       ,domain-of-nonrec-thm
                       ,domain-of-combine-instance
                       ,domain-of-old-instance
                       ,combine-associativity-instance)))))
          (:monoid-alt
           (b* ((domain-of-combine-uncond-thm
                 (cdr (assoc-eq :domain-of-combine-uncond appcond-thm-names)))
                (combine-associativity-uncond-thm
                 (cdr (assoc-eq :combine-associativity-uncond
                        appcond-thm-names)))
                (combine-right-identity-thm
                 (cdr (assoc-eq :combine-right-identity appcond-thm-names)))
                (domain-of-combine-uncond-instance
                 `(:instance ,domain-of-combine-uncond-thm
                   :extra-bindings-ok
                   (,(tailrec-gen-var-u old$) ,a)
                   (,(tailrec-gen-var-v old$) ,nonrec)))
                (combine-associativity-uncond-instance
                 `(:instance ,combine-associativity-uncond-thm
                   :extra-bindings-ok
                   (,(tailrec-gen-var-u old$) ,a)
                   (,(tailrec-gen-var-v old$) ,nonrec)
                   (,(tailrec-gen-var-w old$)
                    ,(apply-term old$ updates))))
                (combine-right-identity-instance
                 `(:instance ,combine-right-identity-thm
                   :extra-bindings-ok
                   (,(tailrec-gen-id-var-u old$ wrld) ,a))))
             `(("Goal"
                :in-theory '(,old-unnorm-name
                             ,new-unnorm-name
                             (:induction ,new-name$))
                :induct (,new-name$ ,@new-formals))
               '(:use (,combine-right-identity-instance
                       ,domain-of-combine-uncond-instance
                       ,combine-associativity-uncond-instance)))))
          (:assoc-alt
           (b* ((combine-associativity-uncond-thm
                 (cdr (assoc-eq :combine-associativity-uncond
                        appcond-thm-names)))
                (combine-associativity-uncond-instance
                 `(:instance ,combine-associativity-uncond-thm
                   :extra-bindings-ok
                   (,(tailrec-gen-var-u old$) ,a)
                   (,(tailrec-gen-var-v old$) ,nonrec)
                   (,(tailrec-gen-var-w old$)
                    ,(apply-term old$ updates)))))
             `(("Goal"
                :in-theory '(,old-unnorm-name
                             ,new-unnorm-name
                             (:induction ,new-name$))
                :induct (,new-name$ ,@new-formals))
               '(:use (,combine-associativity-uncond-instance)))))
          (t (impossible)))))
    (evmac-generate-defthm new-to-old-name$
                           :formula formula
                           :hints hints
                           :enable new-to-old-enable$)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tailrec-gen-alpha-fn ((old$ symbolp)
                              (test pseudo-termp)
                              (updates pseudo-term-listp)
                              (names-to-avoid symbol-listp)
                              (wrld plist-worldp))
  :returns (mv (event "A @(tsee pseudo-event-formp).")
               (name "A @(tsee symbolp).")
               (updated-names-to-avoid "A @(tsee symbol-listp)."))
  :mode :program
  :short "Generate the definition of
          the @($\\alpha$) function of the design notes."
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
  (b* (((mv name names-to-avoid)
        (fresh-logical-name-with-$s-suffix 'alpha
                                           'function
                                           names-to-avoid
                                           wrld))
       (formals (formals old$ wrld))
       (body `(if ,test (list ,@formals) (,name ,@updates)))
       (wfrel (well-founded-relation old$ wrld))
       (measure (measure old$ wrld))
       (termination-hints
        `(("Goal" :use (:termination-theorem ,old$) :in-theory nil)))
       (event `(local
                (defun ,name ,formals
                  (declare (xargs :well-founded-relation ,wfrel
                                  :measure ,measure
                                  :hints ,termination-hints
                                  :guard t
                                  :verify-guards nil
                                  :normalize nil))
                  ,body))))
    (mv event name names-to-avoid)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tailrec-gen-alpha-component-terms ((alpha-name symbolp)
                                           (old$ symbolp)
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
  (b* ((formals (formals old$ wrld))
       (n (len formals)))
    (tailrec-gen-alpha-component-terms-aux n alpha-name formals nil))

  :prepwork
  ((define tailrec-gen-alpha-component-terms-aux ((i natp)
                                                  (alpha-name symbolp)
                                                  (formals symbol-listp)
                                                  (terms pseudo-term-listp))
     :returns (final-terms) ; PSEUDO-TERM-LISTP
     :verify-guards nil
     (if (zp i)
         terms
       (b* ((i-1 (1- i))
            (term `(nth ',i-1 (,alpha-name ,@formals))))
         (tailrec-gen-alpha-component-terms-aux i-1
                                                alpha-name
                                                formals
                                                (cons term terms)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tailrec-gen-test-of-alpha-thm ((old$ symbolp)
                                       (test pseudo-termp)
                                       (alpha-name symbolp)
                                       (names-to-avoid symbol-listp)
                                       (wrld plist-worldp))
  :returns (mv (event "A @(tsee pseudo-event-formp).")
               (name "A @(tsee symbolp) that names the theorem.")
               (updated-names-to-avoid "A @(tsee symbol-listp)."))
  :mode :program
  :short "Generate the theorem asserting that
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
   This theorem is local,
   because it is just a lemma used to prove other theorems.
   </p>"
  (b* (((mv name names-to-avoid)
        (fresh-logical-name-with-$s-suffix 'test-of-alpha
                                           nil
                                           names-to-avoid
                                           wrld))
       (formals (formals old$ wrld))
       (alpha-component-terms (tailrec-gen-alpha-component-terms alpha-name
                                                                 old$
                                                                 wrld))
       (formula (subcor-var formals alpha-component-terms test))
       (hints `(("Goal"
                 :in-theory '(,alpha-name nth-0-cons nth-add1)
                 :induct (,alpha-name ,@formals))))
       (event `(local (defthm ,name
                        ,formula
                        :rule-classes nil
                        :hints ,hints))))
    (mv event name names-to-avoid)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tailrec-gen-old-guard-of-alpha-thm ((old$ symbolp)
                                            (alpha-name symbolp)
                                            (names-to-avoid symbol-listp)
                                            (wrld plist-worldp))
  :returns (mv (event "A @(tsee pseudo-event-formp).")
               (name "A @(tsee symbolp) that names the theorem.")
               (updated-names-to-avoid "A @(tsee symbol-listp)."))
  :mode :program
  :short "Generate the theorem asserting that
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
   This theorem is local,
   because it is just a lemma used to prove other theorems.
   </p>"
  (b* (((mv name names-to-avoid)
        (fresh-logical-name-with-$s-suffix 'old-guard-of-alpha
                                           nil
                                           names-to-avoid
                                           wrld))
       (formals (formals old$ wrld))
       (alpha-component-terms (tailrec-gen-alpha-component-terms alpha-name
                                                                 old$
                                                                 wrld))
       (old-guard (guard old$ nil wrld))
       (formula (implicate old-guard
                           (subcor-var
                            formals alpha-component-terms old-guard)))
       (hints `(("Goal"
                 :in-theory '(,alpha-name nth-0-cons nth-add1)
                 :induct (,alpha-name ,@formals))
                '(:use (:guard-theorem ,old$))))
       (event `(local (defthm ,name
                        ,formula
                        :rule-classes nil
                        :hints ,hints))))
    (mv event name names-to-avoid)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tailrec-gen-domain-of-ground-base-thm
  ((old$ symbolp)
   (base pseudo-termp)
   (domain$ pseudo-termfnp)
   (appcond-thm-names symbol-symbol-alistp)
   (alpha-name symbolp)
   (test-of-alpha-name symbolp)
   (names-to-avoid symbol-listp)
   (wrld plist-worldp))
  :returns (mv (event "A @(tsee pseudo-event-formp).")
               (name "A @(tsee symbolp) that names the theorem.")
               (updated-names-to-avoid "A @(tsee symbol-listp)."))
  :mode :program
  :short "Generate the theorem asserting that
          the base value of the recursion is in the domain
          (@($D{}b_0$) in the design notes)."
  :long
  "<p>
   The hints follow the proof in the design notes.
   </p>
   <p>
   This theorem event is local,
   because it is just a lemma used to prove other theorems.
   </p>"
  (b* (((mv name names-to-avoid)
        (fresh-logical-name-with-$s-suffix 'domain-of-ground-base
                                           nil
                                           names-to-avoid
                                           wrld))
       (formula (apply-term* domain$ base))
       (domain-of-base-thm
        (cdr (assoc-eq :domain-of-base appcond-thm-names)))
       (formals (formals old$ wrld))
       (alpha-comps (tailrec-gen-alpha-component-terms alpha-name
                                                       old$
                                                       wrld))
       (hints `(("Goal"
                 :in-theory nil
                 :use (,test-of-alpha-name
                       (:instance ,domain-of-base-thm
                        :extra-bindings-ok
                        ,@(alist-to-doublets (pairlis$ formals
                                                       alpha-comps)))))))
       (event `(local (defthm ,name
                        ,formula
                        :rule-classes nil
                        :hints ,hints))))
    (mv event name names-to-avoid)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tailrec-gen-combine-left-identity-ground-thm
  ((old$ symbolp)
   (base pseudo-termp)
   (combine pseudo-termp)
   (q symbolp)
   (r symbolp)
   (domain$ pseudo-termfnp)
   (appcond-thm-names symbol-symbol-alistp)
   (alpha-name symbolp)
   (test-of-alpha-name symbolp)
   (names-to-avoid symbol-listp)
   (wrld plist-worldp))
  :returns (mv (event "A @(tsee pseudo-event-formp).")
               (name "A @(tsee symbolp) that names the theorem.")
               (updated-names-to-avoid "A @(tsee symbol-listp)."))
  :mode :program
  :short "Generate the theorem asserting that
          the base value of the recursion
          is left identity of the combination operator
          (@($L{}I_0$) in the design notes)."
  :long
  "<p>
   The hints follow the proof in the design notes.
   </p>
   <p>
   This theorem is local,
   because it is just a lemma used to prove other theorems.
   </p>"
  (b* (((mv name names-to-avoid)
        (fresh-logical-name-with-$s-suffix 'combine-left-identity-ground
                                           nil
                                           names-to-avoid
                                           wrld))
       (u (tailrec-gen-var-u old$))
       (combine-op (tailrec-gen-combine-op combine q r))
       (formula (implicate (apply-term* domain$ u)
                           `(equal ,(apply-term* combine-op base u)
                                   ,u)))
       (combine-left-identity-thm
        (cdr (assoc-eq :combine-left-identity appcond-thm-names)))
       (formals (formals old$ wrld))
       (alpha-comps (tailrec-gen-alpha-component-terms alpha-name
                                                       old$
                                                       wrld))
       (hints `(("Goal"
                 :in-theory nil
                 :use (,test-of-alpha-name
                       (:instance ,combine-left-identity-thm
                        :extra-bindings-ok
                        ,@(alist-to-doublets (pairlis$ formals
                                                       alpha-comps)))))))
       (event `(local (defthm ,name
                        ,formula
                        :rule-classes nil
                        :hints ,hints))))
    (mv event name names-to-avoid)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tailrec-gen-base-guard-thm ((old$ symbolp)
                                    (base pseudo-termp)
                                    (alpha-name symbolp)
                                    (test-of-alpha-name symbolp)
                                    (old-guard-of-alpha-name symbolp)
                                    (names-to-avoid symbol-listp)
                                    state)
  :returns (mv (event "A @(tsee pseudo-event-formp).")
               (name "A @(tsee symbolp) that names the theorem.")
               (updated-names-to-avoid "A @(tsee symbol-listp)."))
  :mode :program
  :short "Generate the theorem asserting that
          the guard of the base term is satisfied
          if the guard of the target function is
          (@($G{}b$) in the design notes)."
  :long
  "<p>
   The hints follow the proof in the design notes.
   </p>
   <p>
   This theorem is local,
   because it is just a lemma used to prove other theorems.
   </p>"
  (b* ((wrld (w state))
       ((mv name names-to-avoid)
        (fresh-logical-name-with-$s-suffix 'base-guard
                                           nil
                                           names-to-avoid
                                           wrld))
       (formula (implicate (guard old$ nil wrld)
                           (term-guard-obligation base state)))
       (formals (formals old$ wrld))
       (alpha-comps (tailrec-gen-alpha-component-terms alpha-name
                                                       old$
                                                       wrld))
       (hints `(("Goal"
                 :in-theory nil
                 :use (,old-guard-of-alpha-name
                       ,test-of-alpha-name
                       (:instance (:guard-theorem ,old$)
                        :extra-bindings-ok
                        ,@(alist-to-doublets (pairlis$ formals
                                                       alpha-comps)))))))
       (event `(local (defthm ,name
                        ,formula
                        :rule-classes nil
                        :hints ,hints))))
    (mv event name names-to-avoid)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tailrec-gen-old-as-new-term ((old$ symbolp)
                                     (test pseudo-termp)
                                     (base pseudo-termp)
                                     (nonrec pseudo-termp)
                                     (updates pseudo-term-listp)
                                     (a symbolp)
                                     (variant$ tailrec-variantp)
                                     (new-name$ symbolp)
                                     (new-formals symbol-listp)
                                     (wrld plist-worldp))
  :returns (term "An untranslated term.")
  :mode :program
  :short "Generate the term that
          rephrases (a generic call to) the old function
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
  (untranslate (case variant$
                 ((:assoc :assoc-alt)
                  `(if ,test
                       ,base
                     ,(subcor-var (cons a (formals old$ wrld))
                                  (cons nonrec updates)
                                  (apply-term new-name$ new-formals))))
                 ((:monoid :monoid-alt)
                  (subst-var base a (apply-term new-name$ new-formals)))
                 (t (impossible)))
               nil wrld))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tailrec-gen-old-to-new-thm ((old$ symbolp)
                                    (test pseudo-termp)
                                    (base pseudo-termp)
                                    (nonrec pseudo-termp)
                                    (updates pseudo-term-listp)
                                    (a symbolp)
                                    (variant$ tailrec-variantp)
                                    (new-name$ symbolp)
                                    (old-to-new-name$ symbolp)
                                    (old-to-new-enable$ booleanp)
                                    (appcond-thm-names symbol-symbol-alistp)
                                    (domain-of-old-name symbolp)
                                    (domain-of-ground-base-name symbolp)
                                    (combine-left-identity-ground-name symbolp)
                                    (new-formals symbol-listp)
                                    (new-to-old-name$ symbolp)
                                    (wrld plist-worldp))
  :returns (mv (local-event "A @(tsee pseudo-event-formp).")
               (exported-event "A @(tsee pseudo-event-formp)."))
  :mode :program
  :short "Generate the theorem that relates
          the old function to the new function
          (@($f{}f'$) and @($f{}f'_0$) in the design notes)."
  :long
  (xdoc::topstring
   (xdoc::p
    "The theorem is
     @($f{}f'$) when the variant is @(':assoc') or @(':assoc-alt'),
     (in this case, left identity does not hold),
     and @($f{}f'_0$) when the variant is @(':monoid') or @(':monoid-alt')
     (in this case, left identity holds,
     and we are in the special case of a ground base term).")
   (xdoc::p
    "The hints follow the proof in the design notes,
     for the case in which left identity holds
     when the variant is @(':monoid') or @(':monoid-alt'),
     and for the case in which left identity does not hold
     when the variant is @(':assoc') and @(':assoc-alt').
     In the first case,
     the proof is for the special case of a ground base term.")
   (xdoc::p
    "For the @(':assoc') and @(':assoc-alt') variants,
     since the old function is recursive,
     we use an explicit @(':expand') hint
     instead of just enabling the definition of old function."))
  (b* ((formula `(equal ,(apply-term old$ (formals old$ wrld))
                        ,(tailrec-gen-old-as-new-term
                          old$ test base nonrec updates a variant$
                          new-name$ new-formals wrld)))
       (hints
        (case variant$
          ((:monoid :monoid-alt)
           (b* ((combine-left-identity-ground-instance
                 `(:instance ,combine-left-identity-ground-name
                   :extra-bindings-ok
                   (,(tailrec-gen-id-var-u old$ wrld)
                    ,(apply-term old$ (formals old$ wrld)))))
                (new-to-old-instance
                 `(:instance ,new-to-old-name$
                   :extra-bindings-ok
                   (,a ,base))))
             `(("Goal"
                :in-theory nil
                :use (,domain-of-ground-base-name
                      ,domain-of-old-name
                      ,new-to-old-instance
                      ,combine-left-identity-ground-instance)))))
          (:assoc
           (b* ((formals (formals old$ wrld))
                (domain-of-nonrec-thm
                 (cdr (assoc-eq :domain-of-nonrec appcond-thm-names)))
                (new-to-old-instance
                 `(:instance ,new-to-old-name$
                   :extra-bindings-ok
                   (,a ,nonrec)
                   ,@(alist-to-doublets (pairlis$ formals updates)))))
             `(("Goal"
                :in-theory nil
                :expand ((,old$ ,@formals))
                :use (,domain-of-nonrec-thm
                      ,new-to-old-instance)))))
          (:assoc-alt
           (b* ((formals (formals old$ wrld))
                (new-to-old-instance
                 `(:instance ,new-to-old-name$
                   :extra-bindings-ok
                   (,a ,nonrec)
                   ,@(alist-to-doublets (pairlis$ formals updates)))))
             `(("Goal"
                :in-theory nil
                :expand ((,old$ ,@formals))
                :use (,new-to-old-instance)))))
          (t (impossible)))))
    (evmac-generate-defthm old-to-new-name$
                           :formula formula
                           :hints hints
                           :enable old-to-new-enable$)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tailrec-gen-wrapper-fn ((old$ symbolp)
                                (test pseudo-termp)
                                (base pseudo-termp)
                                (nonrec pseudo-termp)
                                (updates pseudo-term-listp)
                                (a symbolp)
                                (variant$ tailrec-variantp)
                                (new-name$ symbolp)
                                (wrapper-name$ symbolp)
                                (wrapper-enable$ booleanp)
                                (verify-guards$ booleanp)
                                (appcond-thm-names symbol-symbol-alistp)
                                (domain-of-ground-base-name symbolp)
                                (base-guard-name symbolp)
                                (new-formals symbol-listp)
                                (wrld plist-worldp))
  :returns (mv (local-event "A @(tsee pseudo-event-formp).")
               (exported-event "A @(tsee pseudo-event-formp)."))
  :mode :program
  :short "Generate the wrapper function definition."
  :long
  "<p>
   The macro used to introduce the new function is determined by
   whether the new function must be enabled or not.
   We always make it executable, since there seems to be no reason not to.
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
   </p>
   <p>
   This function is called only if the @(':wrapper') input is @('t').
   </p>"
  (b* ((formals (formals old$ wrld))
       (body (tailrec-gen-old-as-new-term
              old$ test base nonrec updates a variant$
              new-name$ new-formals wrld))
       (guard (untranslate (guard old$ nil wrld) t wrld))
       (guard-hints
        (case variant$
          ((:monoid :monoid-alt)
           `(("Goal"
              :in-theory nil
              :use ((:guard-theorem ,old$)
                    ,domain-of-ground-base-name
                    ,base-guard-name))))
          (:assoc
           (b* ((domain-of-nonrec-thm
                 (cdr (assoc-eq :domain-of-nonrec appcond-thm-names))))
             `(("Goal"
                :in-theory nil
                :use ((:guard-theorem ,old$)
                      ,domain-of-nonrec-thm)))))
          (:assoc-alt
           (b* ((domain-of-nonrec-when-guard-thm
                 (cdr (assoc-eq :domain-of-nonrec-when-guard
                        appcond-thm-names))))
             `(("Goal"
                :in-theory nil
                :use ((:guard-theorem ,old$)
                      ,domain-of-nonrec-when-guard-thm)))))
          (t (impossible)))))
    (evmac-generate-defun
     wrapper-name$
     :formals formals
     :guard guard
     :body body
     :verify-guards verify-guards$
     :guard-hints guard-hints
     :enable wrapper-enable$)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tailrec-gen-old-to-wrapper-thm ((old$ symbolp)
                                        (wrapper-name$ symbolp)
                                        (old-to-wrapper-name$ symbolp)
                                        (old-to-wrapper-enable$ booleanp)
                                        (old-to-new-name$ symbolp)
                                        (wrapper-unnorm-name symbolp)
                                        (wrld plist-worldp))
  :returns (mv (local-event "A @(tsee pseudo-event-formp).")
               (exported-event "A @(tsee pseudo-event-formp)."))
  :mode :program
  :short "Generate the theorem
          that relates the old function to the wrapper function
          (@($f{}\\tilde{f}$) in the design notes)."
  :long
  "<p>
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
   </p>
   <p>
   This function is called only if the @(':wrapper') input is @('t').
   </p>"
  (b* ((formals (formals old$ wrld))
       (formula (untranslate `(equal ,(apply-term old$ formals)
                                     ,(apply-term wrapper-name$ formals))
                             t wrld))
       (hints `(("Goal"
                 :in-theory '(,wrapper-unnorm-name)
                 :use ,old-to-new-name$))))
    (evmac-generate-defthm old-to-wrapper-name$
                           :formula formula
                           :hints hints
                           :enable old-to-wrapper-enable$)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tailrec-gen-wrapper-to-old-thm ((old$ symbolp)
                                        (wrapper-name$ symbolp)
                                        (wrapper-to-old-name$ symbolp)
                                        (wrapper-to-old-enable$ booleanp)
                                        (old-to-new-name$ symbolp)
                                        (wrapper-unnorm-name symbolp)
                                        (wrld plist-worldp))
  :returns (mv (local-event "A @(tsee pseudo-event-formp).")
               (exported-event "A @(tsee pseudo-event-formp)."))
  :mode :program
  :short "Generate the theorem
          that relates the old function to the wrapper function
          (@($f{}\\tilde{f}$) in the design notes)."
  :long
  "<p>
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
   </p>
   <p>
   This function is called only if the @(':wrapper') input is @('t').
   </p>"
  (b* ((formals (formals old$ wrld))
       (formula (untranslate `(equal ,(apply-term old$ formals)
                                     ,(apply-term wrapper-name$ formals))
                             t wrld))
       (hints `(("Goal"
                 :in-theory '(,wrapper-unnorm-name)
                 :use ,old-to-new-name$))))
    (evmac-generate-defthm wrapper-to-old-name$
                           :formula formula
                           :hints hints
                           :enable wrapper-to-old-enable$)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tailrec-gen-everything
  ((old$ symbolp)
   (test pseudo-termp)
   (base pseudo-termp)
   (nonrec pseudo-termp)
   (updates pseudo-term-listp)
   (combine pseudo-termp)
   (q symbolp)
   (r symbolp)
   (variant$ tailrec-variantp)
   (domain$ pseudo-termfnp)
   (new-name$ symbolp)
   (new-enable$ booleanp)
   (a symbolp)
   (wrapper$ booleanp)
   (wrapper-name$ symbolp)
   (wrapper-enable$ booleanp)
   (old-to-new-name$ symbolp)
   (old-to-new-enable$ booleanp)
   (new-to-old-name$ symbolp)
   (new-to-old-enable$ booleanp)
   (old-to-wrapper-name$ symbolp)
   (old-to-wrapper-enable$ booleanp)
   (wrapper-to-old-name$ symbolp)
   (wrapper-to-old-enable$ booleanp)
   (verify-guards$ booleanp)
   (hints$ symbol-alistp)
   (print$ evmac-input-print-p)
   (show-only$ booleanp)
   (call pseudo-event-formp)
   (names-to-avoid symbol-listp)
   ctx
   state)
  :returns (mv erp (event "A @(tsee pseudo-event-formp).") state)
  :mode :program
  :short "Generate the top-level event."
  :long
  "<p>
   This is a @(tsee progn) that consists of
   the expansion of @(tsee tailrec) (the @(tsee encapsulate)),
   followed by an event to extend the transformation table,
   optionally followed by events to print the exported events
   (if specified by the @(':print') input).
   The @(tsee progn) ends with @(':invisible') to avoid printing a return value.
   </p>
   <p>
   The @(tsee encapsulate) starts with some implicitly local events to
   ensure logic mode and
   avoid errors due to ignored or irrelevant formals in the generated functions.
   Other implicitly local event forms remove any default and override hints,
   to prevent such hints from sabotaging the generated proofs;
   this removal is done after proving the applicability conditions,
   in case their proofs rely on the default or override hints.
   </p>
   <p>
   The @(tsee encapsulate) also includes events
   to locally install the non-normalized definitions
   of the old, new, and (if generated) wrapper functions,
   because the generated proofs are based on the unnormalized bodies.
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
   If @(':print') is @(':all'),
   the @(tsee encapsulate) is wrapped to show ACL2's output
   in response to the submitted events.
   If @(':print') is @(':result') or @(':info') or @(':all'),
   the @(tsee progn) includes events to print
   the exported events on the screen without hints;
   these are the same event forms
   that are introduced non-locally and redundantly in the @(tsee encapsulate).
   If @(':print') is @(':info') or @(':all'),
   a blank line is printed just before the result, for visual separation;
   if @(':print') is @(':result'),
   the blank line is not printed.
   </p>
   <p>
   If @(':show-only') is @('t'),
   the @(tsee encapsulate) is just printed on the screen
   and not returned as part of the event to submit,
   which in this case is just an @(':invisible') form.
   In this case, if @(':print') is @(':info') or @(':all'),
   a blank line is printed just before the @(tsee encapsulate),
   for visual separation.
   </p>"
  (b* ((wrld (w state))
       (appconds (tailrec-gen-appconds old$
                                       test
                                       base
                                       nonrec
                                       combine
                                       q
                                       r
                                       domain$
                                       variant$
                                       verify-guards$
                                       state))
       ((er (list appcond-thm-events
                  appcond-thm-names
                  names-to-avoid))
        (evmac-appcond-theorems-no-extra-hints
         appconds hints$ names-to-avoid print$ ctx state))
       ((mv old-unnorm-event
            old-unnorm-name
            names-to-avoid)
        (install-not-normalized-event old$
                                      t
                                      names-to-avoid
                                      wrld))
       ((mv domain-of-old-event?
            domain-of-old-name?
            names-to-avoid)
        (if (member-eq variant$ '(:monoid :monoid-alt :assoc))
            (tailrec-gen-domain-of-old-thm old$ test nonrec updates
                                           variant$ domain$
                                           names-to-avoid
                                           appcond-thm-names
                                           old-unnorm-name
                                           wrld)
          (mv nil nil names-to-avoid)))
       ((mv new-fn-local-event
            new-fn-exported-event
            new-formals)
        (tailrec-gen-new-fn old$
                            test base nonrec updates combine q r
                            variant$ domain$
                            new-name$ new-enable$ a
                            verify-guards$
                            appcond-thm-names
                            wrld))
       ((mv new-unnorm-event
            new-unnorm-name
            names-to-avoid)
        (install-not-normalized-event new-name$
                                      t
                                      names-to-avoid
                                      wrld))
       ((mv new-to-old-thm-local-event
            new-to-old-thm-exported-event)
        (tailrec-gen-new-to-old-thm old$ nonrec updates combine q r
                                    variant$ domain$
                                    new-name$
                                    a
                                    new-to-old-name$
                                    new-to-old-enable$
                                    appcond-thm-names
                                    old-unnorm-name
                                    domain-of-old-name?
                                    new-formals
                                    new-unnorm-name
                                    wrld))
       (gen-alpha (member-eq variant$ '(:monoid :monoid-alt)))
       ((mv alpha-event?
            alpha-name?
            names-to-avoid)
        (if gen-alpha
            (tailrec-gen-alpha-fn old$ test updates names-to-avoid wrld)
          (mv nil nil names-to-avoid)))
       ((mv test-of-alpha-event?
            test-of-alpha-name?
            names-to-avoid)
        (if gen-alpha
            (tailrec-gen-test-of-alpha-thm old$ test
                                           alpha-name?
                                           names-to-avoid wrld)
          (mv nil nil names-to-avoid)))
       ((mv old-guard-of-alpha-event?
            old-guard-of-alpha-name?
            names-to-avoid)
        (if (and gen-alpha
                 verify-guards$)
            (tailrec-gen-old-guard-of-alpha-thm old$
                                                alpha-name?
                                                names-to-avoid
                                                wrld)
          (mv nil nil names-to-avoid)))
       ((mv domain-of-ground-base-event?
            domain-of-ground-base-name?
            names-to-avoid)
        (if gen-alpha
            (tailrec-gen-domain-of-ground-base-thm old$
                                                   base
                                                   domain$
                                                   appcond-thm-names
                                                   alpha-name?
                                                   test-of-alpha-name?
                                                   names-to-avoid
                                                   wrld)
          (mv nil nil names-to-avoid)))
       ((mv combine-left-identity-ground-event?
            combine-left-identity-ground-name?
            names-to-avoid)
        (if gen-alpha
            (tailrec-gen-combine-left-identity-ground-thm old$
                                                          base
                                                          combine
                                                          q
                                                          r
                                                          domain$
                                                          appcond-thm-names
                                                          alpha-name?
                                                          test-of-alpha-name?
                                                          names-to-avoid
                                                          wrld)
          (mv nil nil names-to-avoid)))
       ((mv base-guard-event?
            base-guard-name?
            names-to-avoid)
        (if (and gen-alpha
                 verify-guards$)
            (tailrec-gen-base-guard-thm old$ base
                                        alpha-name? test-of-alpha-name?
                                        old-guard-of-alpha-name?
                                        names-to-avoid state)
          (mv nil nil names-to-avoid)))
       ((mv old-to-new-thm-local-event
            old-to-new-thm-exported-event)
        (tailrec-gen-old-to-new-thm old$ test base nonrec updates a
                                    variant$
                                    new-name$
                                    old-to-new-name$
                                    old-to-new-enable$
                                    appcond-thm-names
                                    domain-of-old-name?
                                    domain-of-ground-base-name?
                                    combine-left-identity-ground-name?
                                    new-formals
                                    new-to-old-name$
                                    wrld))
       ((mv wrapper-fn-local-event?
            wrapper-fn-exported-event?)
        (if wrapper$
            (tailrec-gen-wrapper-fn old$
                                    test base nonrec updates a
                                    variant$
                                    new-name$
                                    wrapper-name$ wrapper-enable$
                                    verify-guards$
                                    appcond-thm-names
                                    domain-of-ground-base-name?
                                    base-guard-name?
                                    new-formals
                                    wrld)
          (mv nil nil)))
       ((mv wrapper-unnorm-event?
            wrapper-unnorm-name?
            &)
        (if wrapper$
            (install-not-normalized-event wrapper-name$
                                          t
                                          names-to-avoid
                                          wrld)
          (mv nil nil names-to-avoid)))
       ((mv
         old-to-wrapper-thm-local-event?
         old-to-wrapper-thm-exported-event?)
        (if wrapper$
            (tailrec-gen-old-to-wrapper-thm old$
                                            wrapper-name$
                                            old-to-wrapper-name$
                                            old-to-wrapper-enable$
                                            old-to-new-name$
                                            wrapper-unnorm-name?
                                            wrld)
          (mv nil nil)))
       ((mv
         wrapper-to-old-thm-local-event?
         wrapper-to-old-thm-exported-event?)
        (if wrapper$
            (tailrec-gen-wrapper-to-old-thm old$
                                            wrapper-name$
                                            wrapper-to-old-name$
                                            wrapper-to-old-enable$
                                            old-to-new-name$
                                            wrapper-unnorm-name?
                                            wrld)
          (mv nil nil)))
       (theory-invariants (append
                           `((theory-invariant
                              (incompatible
                               (:rewrite ,old-to-new-name$)
                               (:rewrite ,new-to-old-name$))))
                           (and wrapper$
                                `((theory-invariant
                                   (incompatible
                                    (:rewrite ,old-to-wrapper-name$)
                                    (:rewrite ,wrapper-to-old-name$)))))))
       (new-fn-numbered-name-event `(add-numbered-name-in-use
                                     ,new-name$))
       (wrapper-fn-numbered-name-event? (if wrapper$
                                            `(add-numbered-name-in-use
                                              ,wrapper-name$)
                                          nil))
       (encapsulate-events
        `((logic)
          (set-ignore-ok t)
          (set-irrelevant-formals-ok t)
          ,@appcond-thm-events
          (evmac-prepare-proofs)
          ,old-unnorm-event
          ,@(and domain-of-old-name?
                 (list domain-of-old-event?))
          ,new-fn-local-event
          ,new-unnorm-event
          ,new-to-old-thm-local-event
          ,@(and gen-alpha
                 (list alpha-event?))
          ,@(and gen-alpha
                 (list test-of-alpha-event?))
          ,@(and gen-alpha
                 verify-guards$
                 (list old-guard-of-alpha-event?))
          ,@(and gen-alpha
                 (list domain-of-ground-base-event?))
          ,@(and gen-alpha
                 (list combine-left-identity-ground-event?))
          ,@(and gen-alpha
                 verify-guards$
                 (list base-guard-event?))
          ,old-to-new-thm-local-event
          ,@(and wrapper$ (list wrapper-fn-local-event?))
          ,@(and wrapper$ (list wrapper-unnorm-event?))
          ,@(and wrapper$ (list old-to-wrapper-thm-local-event?))
          ,@(and wrapper$ (list wrapper-to-old-thm-local-event?))
          ,new-fn-exported-event
          ,@(and wrapper$ (list wrapper-fn-exported-event?))
          ,old-to-new-thm-exported-event
          ,new-to-old-thm-exported-event
          ,@(and wrapper$ (list old-to-wrapper-thm-exported-event?))
          ,@(and wrapper$ (list wrapper-to-old-thm-exported-event?))
          ,@theory-invariants
          ,new-fn-numbered-name-event
          ,@(and wrapper$ (list wrapper-fn-numbered-name-event?))))
       (encapsulate `(encapsulate () ,@encapsulate-events))
       ((when show-only$)
        (if (member-eq print$ '(:info :all))
            (cw "~%~x0~|" encapsulate)
          (cw "~x0~|" encapsulate))
        (value '(value-triple :invisible)))
       (encapsulate+ (restore-output? (eq print$ :all) encapsulate))
       (transformation-table-event (record-transformation-call-event
                                    call encapsulate wrld))
       (print-result (and
                      (member-eq print$ '(:result :info :all))
                      `(,@(and (member-eq print$ '(:info :all))
                               '((cw-event "~%")))
                        (cw-event "~x0~|" ',new-fn-exported-event)
                        ,@(and wrapper$
                               (list `(cw-event "~x0~|"
                                                ',wrapper-fn-exported-event?)))
                        (cw-event "~x0~|" ',old-to-new-thm-exported-event)
                        (cw-event "~x0~|" ',new-to-old-thm-exported-event)
                        ,@(and wrapper$
                               (list
                                `(cw-event
                                  "~x0~|"
                                  ',old-to-wrapper-thm-exported-event?)
                                `(cw-event
                                  "~x0~|"
                                  ',wrapper-to-old-thm-exported-event?)))))))
    (value
     `(progn
        ,encapsulate+
        ,transformation-table-event
        ,@print-result
        (value-triple :invisible)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tailrec-fn (old
                    variant
                    domain
                    new-name
                    new-enable
                    accumulator
                    wrapper
                    wrapper-name
                    (wrapper-name-present booleanp)
                    wrapper-enable
                    (wrapper-enable-present booleanp)
                    old-to-new-name
                    (old-to-new-name-present booleanp)
                    old-to-new-enable
                    (old-to-new-enable-present booleanp)
                    new-to-old-name
                    (new-to-old-name-present booleanp)
                    new-to-old-enable
                    (new-to-old-enable-present booleanp)
                    old-to-wrapper-name
                    (old-to-wrapper-name-present booleanp)
                    old-to-wrapper-enable
                    (old-to-wrapper-enable-present booleanp)
                    wrapper-to-old-name
                    (wrapper-to-old-name-present booleanp)
                    wrapper-to-old-enable
                    (wrapper-to-old-enable-present booleanp)
                    verify-guards
                    hints
                    print
                    show-only
                    (call pseudo-event-formp)
                    ctx
                    state)
  :returns (mv erp
               (event "A @(tsee pseudo-event-formp).")
               state)
  :mode :program
  :parents (tailrec-implementation)
  :short "Check redundancy,
          process the inputs, and
          generate the event to submit."
  :long
  (xdoc::topstring-p
   "If this call to the transformation is redundant,
    a message to that effect is printed on the screen.
    If the transformation is redundant and @(':show-only') is @('t'),
    the @(tsee encapsulate), retrieved from the table, is shown on the screen.")
  (b* ((encapsulate? (previous-transformation-expansion call (w state)))
       ((when encapsulate?)
        (b* (((run-when show-only) (cw "~x0~|" encapsulate?)))
          (cw "~%The transformation ~x0 is redundant.~%" call)
          (value '(value-triple :invisible))))
       ((er (list old$
                  test
                  base
                  nonrec
                  updates
                  combine
                  q
                  r
                  domain$
                  new-name$
                  new-enable$
                  a
                  wrapper-name$
                  wrapper-enable$
                  old-to-new-name$
                  old-to-new-enable$
                  new-to-old-name$
                  new-to-old-enable$
                  old-to-wrapper-name$
                  old-to-wrapper-enable$
                  wrapper-to-old-name$
                  wrapper-to-old-enable$
                  verify-guards$
                  hints$
                  names-to-avoid))
        (tailrec-process-inputs old
                                variant
                                domain
                                new-name
                                new-enable
                                accumulator
                                wrapper
                                wrapper-name
                                wrapper-name-present
                                wrapper-enable
                                wrapper-enable-present
                                old-to-new-name
                                old-to-new-name-present
                                old-to-new-enable
                                old-to-new-enable-present
                                new-to-old-name
                                new-to-old-name-present
                                new-to-old-enable
                                new-to-old-enable-present
                                old-to-wrapper-name
                                old-to-wrapper-name-present
                                old-to-wrapper-enable
                                old-to-wrapper-enable-present
                                wrapper-to-old-name
                                wrapper-to-old-name-present
                                wrapper-to-old-enable
                                wrapper-to-old-enable-present
                                verify-guards
                                hints
                                print
                                show-only
                                ctx
                                state))
       ((er event) (tailrec-gen-everything old$
                                           test
                                           base
                                           nonrec
                                           updates
                                           combine
                                           q
                                           r
                                           variant
                                           domain$
                                           new-name$
                                           new-enable$
                                           a
                                           wrapper
                                           wrapper-name$
                                           wrapper-enable$
                                           old-to-new-name$
                                           old-to-new-enable$
                                           new-to-old-name$
                                           new-to-old-enable$
                                           old-to-wrapper-name$
                                           old-to-wrapper-enable$
                                           wrapper-to-old-name$
                                           wrapper-to-old-enable$
                                           verify-guards$
                                           hints$
                                           print
                                           show-only
                                           call
                                           names-to-avoid
                                           ctx
                                           state)))
    (value event)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection tailrec-macro-definition
  :parents (tailrec-implementation)
  :short "Definition of the @(tsee tailrec) macro."
  :long
  "<p>
   Submit the event form generated by @(tsee tailrec-fn).
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
                     (accumulator ':auto)
                     (wrapper 'nil)
                     (wrapper-name ':auto wrapper-name-present)
                     (wrapper-enable ':irrelevant
                                     wrapper-enable-present)
                     (old-to-new-name ':irrelevant
                                      old-to-new-name-present)
                     (old-to-new-enable ':irrelevant
                                        old-to-new-enable-present)
                     (new-to-old-name ':irrelevant
                                      new-to-old-name-present)
                     (new-to-old-enable ':irrelevant
                                        new-to-old-enable-present)
                     (old-to-wrapper-name ':irrelevant
                                          old-to-wrapper-name-present)
                     (old-to-wrapper-enable ':irrelevant
                                            old-to-wrapper-enable-present)
                     (wrapper-to-old-name ':irrelevant
                                          wrapper-to-old-name-present)
                     (wrapper-to-old-enable ':irrelevant
                                            wrapper-to-old-enable-present)
                     (verify-guards ':auto)
                     (hints 'nil)
                     (print ':result)
                     (show-only 'nil))
    `(make-event-terse (tailrec-fn ',old
                                   ',variant
                                   ',domain
                                   ',new-name
                                   ',new-enable
                                   ',accumulator
                                   ',wrapper
                                   ',wrapper-name
                                   ',wrapper-name-present
                                   ',wrapper-enable
                                   ',wrapper-enable-present
                                   ',old-to-new-name
                                   ',old-to-new-name-present
                                   ',old-to-new-enable
                                   ',old-to-new-enable-present
                                   ',new-to-old-name
                                   ',new-to-old-name-present
                                   ',new-to-old-enable
                                   ',new-to-old-enable-present
                                   ',old-to-wrapper-name
                                   ',old-to-wrapper-name-present
                                   ',old-to-wrapper-enable
                                   ',old-to-wrapper-enable-present
                                   ',wrapper-to-old-name
                                   ',wrapper-to-old-name-present
                                   ',wrapper-to-old-enable
                                   ',wrapper-to-old-enable-present
                                   ',verify-guards
                                   ',hints
                                   ',print
                                   ',show-only
                                   ',call
                                   (cons 'tailrec ',old)
                                   state)
                       :suppress-errors ,(not print))))
