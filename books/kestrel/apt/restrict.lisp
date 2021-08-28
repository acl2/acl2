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
(include-book "kestrel/error-checking/ensure-value-is-symbol" :dir :system)
(include-book "kestrel/error-checking/ensure-value-is-untranslated-term" :dir :system)
(include-book "kestrel/event-macros/applicability-conditions" :dir :system)
(include-book "kestrel/event-macros/event-generation" :dir :system)
(include-book "kestrel/event-macros/input-processing" :dir :system)
(include-book "kestrel/event-macros/intro-macros" :dir :system)
(include-book "kestrel/event-macros/proof-preparation" :dir :system)
(include-book "kestrel/event-macros/restore-output" :dir :system)
(include-book "kestrel/event-macros/xdoc-constructors" :dir :system)
(include-book "kestrel/std/basic/mbt-dollar" :dir :system)
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

 restrict

 :items

 (xdoc::*evmac-topic-implementation-item-state*

  xdoc::*evmac-topic-implementation-item-wrld*

  xdoc::*evmac-topic-implementation-item-ctx*

  (xdoc::evmac-topic-implementation-item-input-untyped/typed "old")

  (xdoc::evmac-topic-implementation-item-input-untyped/typed "restriction")

  (xdoc::evmac-topic-implementation-item-input-untyped/typed "undefined")

  (xdoc::evmac-topic-implementation-item-input "new-name")

  (xdoc::evmac-topic-implementation-item-input-untyped/typed "new-enable")

  (xdoc::evmac-topic-implementation-item-input "old-to-new-name")

  (xdoc::evmac-topic-implementation-item-input-untyped/typed "old-to-new-enable")

  (xdoc::evmac-topic-implementation-item-input "new-to-old-name")

  (xdoc::evmac-topic-implementation-item-input-untyped/typed "new-to-old-enable")

  (xdoc::evmac-topic-implementation-item-input-untyped/typed "verify-guards")

  (xdoc::evmac-topic-implementation-item-input-untyped/typed "hints")

  (xdoc::evmac-topic-implementation-item-input "print")

  (xdoc::evmac-topic-implementation-item-input "show-only")

  xdoc::*evmac-topic-implementation-item-call*

  (xdoc::evmac-topic-implementation-item-fn-doc "new")

  (xdoc::evmac-topic-implementation-item-thm-doc "old-to-new")

  (xdoc::evmac-topic-implementation-item-thm-doc "new-to-old")

  "@('stub?') is the stub called @('?f') in the documentation
   if @('old') is a reflexive function,
   or @('nil') otherwise."

  xdoc::*evmac-topic-implementation-item-appcond-thm-names*

  "@('old-unnorm') is the name of the generated theorem
   that installs the non-normalized definition of the target function."

  "@('new-unnorm') is the name of the generated theorem
   that installs the non-normalized definition of the new function."

  xdoc::*evmac-topic-implementation-item-names-to-avoid*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-input-processing restrict)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define restrict-process-old (old verify-guards ctx state)
  :returns (mv erp
               (old "A @(tsee symbolp) that is
                     the name of the target function
                     of the transformation,
                     denoted by the @('old') input.")
               state)
  :mode :program
  :short "Process the @('old') input."
  (b* ((wrld (w state))
       ((er old) (ensure-function-name-or-numbered-wildcard$
                  old "The first input" t nil))
       (description (msg "The target function ~x0" old))
       ((er &) (ensure-function-is-logic-mode$ old description t nil))
       ((er &) (ensure-function-is-defined$ old description t nil))
       ((er &) (ensure-function-has-args$ old description t nil))
       ((er &) (ensure-function-number-of-results$ old 1
                                                   description t nil))
       ((er &) (ensure-function-no-stobjs$ old description t nil))
       (recursive (recursivep old nil wrld))
       ((er &) (if recursive
                   (ensure-function-singly-recursive$ old
                                                      description t nil)
                 (value nil)))
       ((er &) (if recursive
                   (ensure-function-known-measure$ old
                                                   description t nil)
                 (value nil)))
       ((er &) (if (eq verify-guards t)
                   (ensure-function-is-guard-verified$
                    old
                    (msg "Since the :VERIFY-GUARDS input is T, ~
                          the target function ~x0" old)
                    t nil)
                 (value nil))))
    (value old)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define restrict-process-restriction (restriction
                                      (old symbolp)
                                      (verify-guards booleanp)
                                      ctx
                                      state)
  :returns (mv erp
               (restriction "A @(tsee pseudo-termp) that is
                             the translation of @('restriction').")
               state)
  :mode :program
  :short "Process the @('restriction') input."
  (b* ((wrld (w state))
       (restriction (if (equal restriction ':guard)
                        (guard old nil wrld)
                      restriction))
       ((er (list term stobjs-out))
        (ensure-value-is-untranslated-term$ restriction
                                            "The second input" t nil))
       (description (msg "The term ~x0 that denotes the restricting predicate"
                         restriction))
       ((er &) (ensure-term-free-vars-subset$ term
                                              (formals old wrld)
                                              description t nil))
       ((er &) (ensure-term-logic-mode$ term description t nil))
       ((er &) (ensure-function/lambda/term-number-of-results$ stobjs-out 1
                                                               description
                                                               t nil))
       ((er &) (ensure-term-no-stobjs$ stobjs-out description t nil))
       ((er &) (if (eq verify-guards t)
                   (ensure-term-guard-verified-exec-fns$
                    term
                    (msg "Since either the :VERIFY-GUARDS input is T, ~
                          or it is (perhaps by default) :AUTO ~
                          and the target function ~x0 is guard-verified, ~@1"
                         old (msg-downcase-first description))
                    t nil)
                 (value nil)))
       ((er &) (ensure-term-does-not-call$ term old
                                           description t nil)))
    (value term)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define restrict-process-undefined (undefined
                                    (old symbolp)
                                    ctx
                                    state)
  :returns (mv erp
               (undefined "A @(tsee pseudo-termp) that is
                           the translation of @('undefined').")
               state)
  :mode :program
  :short "Process the @(':undefined') input."
  (b* ((wrld (w state))
       ((er (list term stobjs-out))
        (ensure-value-is-untranslated-term$ undefined
                                            "The :UNDEFINED input" t nil))
       (description (msg "The term ~x0 that denotes the undefined value"
                         undefined))
       ((er &) (ensure-term-free-vars-subset$ term
                                              (formals old wrld)
                                              description t nil))
       ((er &) (ensure-term-logic-mode$ term description t nil))
       ((er &) (ensure-function/lambda/term-number-of-results$ stobjs-out 1
                                                               description
                                                               t nil))
       ((er &) (ensure-term-no-stobjs$ stobjs-out description t nil))
       ((er &) (ensure-term-does-not-call$ term old
                                           description t nil)))
    (value term)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define restrict-process-inputs (old
                                 restriction
                                 undefined
                                 new-name
                                 new-enable
                                 old-to-new-name (old-to-new-name? booleanp)
                                 old-to-new-enable (old-to-new-enable? booleanp)
                                 new-to-old-name (new-to-old-name? booleanp)
                                 new-to-old-enable (new-to-old-enable? booleanp)
                                 verify-guards
                                 hints
                                 print
                                 show-only
                                 ctx
                                 state)
  :returns (mv erp
               (result "A @('(tuple (old symbolp)
                                    (restriction pseudo-termp)
                                    (undefined pseudo-termp)
                                    (new symbolp)
                                    (new-enable booleanp)
                                    (old-to-new symbolp)
                                    (old-to-new-enable symbolp)
                                    (new-to-old symbolp)
                                    (new-to-old-enable symbolp)
                                    (verify-guards booleanp)
                                    (hints evmac-input-hints-p)
                                    (names-to-avoid symbol-listp)
                                    result)').")
               state)
  :mode :program
  :short "Process all the inputs."
  (b* (((er old) (restrict-process-old old verify-guards ctx state))
       ((er verify-guards) (process-input-verify-guards verify-guards
                                                        old
                                                        ctx
                                                        state))
       ((er restriction) (restrict-process-restriction restriction
                                                       old
                                                       verify-guards
                                                       ctx
                                                       state))
       ((er undefined) (restrict-process-undefined undefined old ctx state))
       ((er (list new names-to-avoid))
        (process-input-new-name new-name old nil ctx state))
       ((er new-enable) (process-input-new-enable new-enable old ctx state))
       ((er (list old-to-new names-to-avoid))
        (process-input-old-to-new-name old-to-new-name
                                       old-to-new-name?
                                       old
                                       new
                                       names-to-avoid
                                       ctx
                                       state))
       ((er old-to-new-enable) (process-input-old-to-new-enable
                                old-to-new-enable
                                old-to-new-enable?
                                ctx
                                state))
       ((er (list new-to-old names-to-avoid))
        (process-input-new-to-old-name new-to-old-name
                                       new-to-old-name?
                                       old
                                       new
                                       names-to-avoid
                                       ctx
                                       state))
       ((er new-to-old-enable) (process-input-new-to-old-enable
                                new-to-old-enable
                                new-to-old-enable?
                                ctx
                                state))
       ((er hints) (evmac-process-input-hints hints ctx state))
       ((er &) (evmac-process-input-print print ctx state))
       ((er &) (evmac-process-input-show-only show-only ctx state)))
    (value (list old
                 restriction
                 undefined
                 new
                 new-enable
                 old-to-new
                 old-to-new-enable
                 new-to-old
                 new-to-old-enable
                 verify-guards
                 hints
                 names-to-avoid))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-event-generation restrict
                                    :some-local-nonlocal-p t
                                    :some-local-p t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define restrict-gen-restriction-of-rec-calls-consequent-term
  ((old symbolp)
   (rec-calls-with-tests pseudo-tests-and-call-listp
                         "Recursive calls, with controlling tests,
                          of the old function.")
   (restriction pseudo-termp)
   (stub? symbolp)
   (wrld plist-worldp))
  :returns (consequent "A @(tsee pseudo-termp).")
  :mode :program
  :short "Generate the consequent of
          the @(':restriction-of-rec-calls') applicability condition."
  :long
  "<p>
   This is the term
   </p>
   @({
     (and (implies context1<x1,...,xn,?f>
                   restriction<update1-x1<x1,...,xn,?f>,
                               ...,
                               update1-xn<x1,...,xn,?f>>)
          ...
          (implies contextm<x1,...,xn>
                   restriction<updatem-x1<x1,...,xn,?f>,
                               ...,
                               updatem-xn<x1,...,xn,?f>>))
   })
   <p>
   If the function is reflexive (i.e. if @('stub?') is not @('nil'),
   we replace every occurrence of @('old') with the stub.
   </p>"
  (conjoin
   (restrict-gen-restriction-of-rec-calls-consequent-term-aux
    old rec-calls-with-tests restriction stub? nil wrld))

  :prepwork
  ((define restrict-gen-restriction-of-rec-calls-consequent-term-aux
     ((old symbolp)
      (rec-calls-with-tests pseudo-tests-and-call-listp)
      (restriction pseudo-termp)
      (stub? symbolp)
      (rev-conjuncts pseudo-term-listp)
      (wrld plist-worldp))
     :returns (conjuncts) ; PSEUDO-TERM-LISTP
     :mode :program
     (if (endp rec-calls-with-tests)
         (reverse rev-conjuncts)
       (b* ((tests-and-call (car rec-calls-with-tests))
            (tests (access tests-and-call tests-and-call :tests))
            (call (access tests-and-call tests-and-call :call))
            (context (conjoin tests))
            (context (if stub?
                         (sublis-fn-simple (acons old stub? nil) context)
                       context))
            (restriction-of-update (subcor-var (formals old wrld)
                                               (fargs call)
                                               restriction))
            (restriction-of-update (if stub?
                                       (sublis-fn-simple (acons old stub? nil)
                                                         restriction-of-update)
                                     restriction-of-update)))
         (restrict-gen-restriction-of-rec-calls-consequent-term-aux
          old
          (cdr rec-calls-with-tests)
          restriction
          stub?
          (cons (implicate context restriction-of-update)
                rev-conjuncts)
          wrld))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define restrict-gen-appconds ((old symbolp)
                               (restriction pseudo-termp)
                               (verify-guards booleanp)
                               (stub? symbolp)
                               state)
  :returns (appconds "A @(tsee evmac-appcond-listp).")
  :mode :program
  :short "Generate the applicability conditions."
  (b* ((wrld (w state)))
    (append
     (make-evmac-appcond?
      :restriction-of-rec-calls
      (b* ((rec-calls-with-tests (recursive-calls old wrld))
           (consequent
            (restrict-gen-restriction-of-rec-calls-consequent-term
             old rec-calls-with-tests restriction stub? wrld)))
        (implicate restriction
                   consequent))
      :when (recursivep old nil wrld))
     (make-evmac-appcond?
      :restriction-guard
      (b* ((old-guard (guard old nil wrld))
           (restriction-guard
            (term-guard-obligation restriction state)))
        (implicate old-guard
                   restriction-guard))
      :when verify-guards))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define restrict-gen-new ((old symbolp)
                          (restriction pseudo-termp)
                          (undefined pseudo-termp)
                          (new symbolp)
                          (new-enable booleanp)
                          (verify-guards booleanp)
                          (wrld plist-worldp))
  :returns (mv (local-event "A @(tsee pseudo-event-formp).")
               (exported-event "A @(tsee pseudo-event-formp)."))
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
   The new function has the same formal arguments as the old function.
   </p>
   <p>
   The body of the new function is obtained
   from the body of the old function
   by replacing every occurrence of the old function
   with the new function
   (a no-op if the old function is not recursive),
   and then wrapping the resulting term with a conditional
   that tests the restricting predicate,
   as described in the documentation.
   Thus, the new function is recursive iff the old function is.
   If the old function is non-executable,
   the non-executable wrapper is removed first.
   </p>
   <p>
   If the new function is recursive,
   its well-founded relation and measure are the same as the old function's.
   Following the design notes,
   the termination of the new function is proved
   in the empty theory, using the termination theorem of the old function;
   this should work also if the function is reflexive,
   because of the automatic functional instantiation described in (6) of the
   <see topic='@(url acl2::lemma-instance)'>lemma instance documentation</see>.
   The new function uses all ruler extenders,
   in case the old function's termination depends on any ruler extender.
   </p>
   <p>
   The guard of the new function is obtained
   by conjoining the restricting predicate
   after the guard of the old function,
   as described in the documentation.
   Since the restriction test follows from the guard,
   it is wrapped with @(tsee mbt$).
   </p>
   <p>
   Guard verification is deferred;
   see @(tsee restrict-gen-verify-guards).
   </p>"
  (b* ((macro (function-intro-macro new-enable (non-executablep old wrld)))
       (formals (formals old wrld))
       (old-body (if (non-executablep old wrld)
                     (unwrapped-nonexec-body old wrld)
                   (ubody old wrld)))
       (new-body-core (sublis-fn-simple (acons old new nil)
                                        old-body))
       (new-body `(if (mbt$ ,restriction) ,new-body-core ,undefined))
       (new-body (untranslate new-body nil wrld))
       (recursive (recursivep old nil wrld))
       (wfrel? (and recursive
                    (well-founded-relation old wrld)))
       (measure? (and recursive
                      (untranslate (measure old wrld) nil wrld)))
       (termination-hints? (and recursive
                                `(("Goal"
                                   :in-theory nil
                                   :use (:termination-theorem ,old)))))
       (old-guard (guard old nil wrld))
       (new-guard (if (equal old-guard restriction)
                      old-guard
                    (conjoin2 old-guard restriction))) ; Could produce a simpler version
       (new-guard (untranslate new-guard t wrld))
       (local-event
        `(local
          (,macro ,new (,@formals)
                  (declare (xargs ,@(and recursive
                                         (list :well-founded-relation wfrel?
                                               :measure measure?
                                               :hints termination-hints?
                                               :ruler-extenders :all))
                                  :guard ,new-guard
                                  :verify-guards nil))
                  ,new-body)))
       (exported-event
        `(,macro ,new (,@formals)
                 (declare (xargs ,@(and recursive
                                        (list :well-founded-relation wfrel?
                                              :measure measure?
                                              :ruler-extenders :all))
                                 :guard ,new-guard
                                 :verify-guards ,verify-guards))
                 ,new-body)))
    (mv local-event exported-event)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define restrict-gen-old-to-new ((old symbolp)
                                 (restriction pseudo-termp)
                                 (new symbolp)
                                 (old-to-new symbolp)
                                 (old-to-new-enable booleanp)
                                 (appcond-thm-names symbol-symbol-alistp)
                                 (stub? symbolp)
                                 (old-unnorm symbolp)
                                 (new-unnorm symbolp)
                                 (wrld plist-worldp))
  :returns (mv (local-event "A @(tsee pseudo-event-formp).")
               (exported-event "A @(tsee pseudo-event-formp)."))
  :mode :program
  :short "Generate the theorem that relates the old and new functions."
  :long
  "<p>
   The macro used to introduce the theorem is determined by
   whether the theorem must be enabled or not.
   </p>
   <p>
   The formula of the theorem equates old and new functions
   under the restricting predicate,
   as described in the documentation.
   </p>
   <p>
   If the old and new functions are not recursive,
   then, following the design notes, the theorem is proved
   in the theory consisting of
   the two theorems that install the non-normalized definitions of the functions
   and the induction rule of the old function.
   If the old and new functions are recursive,
   then, following the design notes, the theorem is proved
   by induction on the old function,
   in the theory consisting of
   the two theorems that install the non-normalized definitions of the functions
   and the induction rule of the old function,
   and using the @(':restriction-of-rec-calls') applicability condition.
   If the old and new functions are reflexive,
   we functionally instantiate the stub in that applicability condition.
   </p>"
  (b* ((formals (formals old wrld))
       (formula (implicate restriction
                           `(equal (,old ,@formals)
                                   (,new ,@formals))))
       (formula (untranslate formula t wrld))
       (recursive (recursivep old nil wrld))
       (hints (if recursive
                  (b* ((lemma-name (cdr (assoc-eq :restriction-of-rec-calls
                                          appcond-thm-names)))
                       (lemma-instance (if stub?
                                           `(:functional-instance ,lemma-name
                                             (,stub? ,new))
                                         lemma-name)))
                    `(("Goal"
                       :in-theory '(,old-unnorm
                                    ,new-unnorm
                                    (:induction ,old))
                       :induct (,old ,@formals))
                      '(:use ,lemma-instance)))
                `(("Goal"
                   :in-theory '(,old-unnorm
                                ,new-unnorm))))))
    (evmac-generate-defthm old-to-new
                           :formula formula
                           :hints hints
                           :enable old-to-new-enable)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define restrict-gen-new-to-old ((old symbolp)
                                 (restriction pseudo-termp)
                                 (new symbolp)
                                 (new-to-old symbolp)
                                 (new-to-old-enable booleanp)
                                 (old-to-new symbolp)
                                 (wrld plist-worldp))
  :returns (mv (local-event "A @(tsee pseudo-event-formp).")
               (exported-event "A @(tsee pseudo-event-formp)."))
  :mode :program
  :short "Generate the theorem that relates the new and old functions."
  :long
  "<p>
   The macro used to introduce the theorem is determined by
   whether the theorem must be enabled or not.
   </p>
   <p>
   The formula of the theorem equates new and old functions
   under the restricting predicate,
   as described in the documentation.
   </p>
   <p>
   The theorem is easily proved from the @('old-to-new') one.
   </p>"
  (b* ((formals (formals old wrld))
       (formula (implicate restriction
                           `(equal (,new ,@formals)
                                   (,old ,@formals))))
       (formula (untranslate formula t wrld))
       (hints `(("Goal" :in-theory '(,old-to-new)))))
    (evmac-generate-defthm new-to-old
                           :formula formula
                           :hints hints
                           :enable new-to-old-enable)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define restrict-gen-verify-guards ((old symbolp)
                                    (new symbolp)
                                    (old-to-new symbolp)
                                    (appcond-thm-names symbol-symbol-alistp)
                                    (stub? symbolp)
                                    (wrld plist-worldp))
  :returns (local-event pseudo-event-formp)
  :verify-guards nil
  :short "Generate the event to verify the guards of the new function."
  :long
  "<p>
   As mentioned in @(tsee restrict-gen-new),
   the verification of the guards of the new function,
   when it has to take place,
   is deferred when the function is introduced.
   The reason is that, as shown in the design notes,
   the guard verification proof for the recursive case
   uses the theorem that relates the old and new functions:
   thus, the theorem must be proved before guard verification,
   and the new function must be introduced before proving the theorem.
   In the non-recursive case, we could avoid deferring guard verification,
   but we defer it anyhow for uniformity.
   </p>
   <p>
   Following the design notes, the guards are verified
   using the guard theorem of the old function
   and the @(':restriction-guard') applicability condition.
   This suffices for the non-recursive case (in the empty theory).
   For the recursive case,
   we also use the @(':restriction-of-rec-calls') applicability condition,
   and we carry out the proof in the theory consisting of
   the theorem that relates the old and new functions:
   this theorem rewrites all the recursive calls of the old function,
   in the old function's guard theorem,
   to corresponding recursive calls of the new function
   (the design notes cover the representative case of a single recursive call,
   but the transformation covers functions with multiple recursive calls).
   If the old and new functions are reflexive,
   we functionally instantiate the stub
   in the @(':restriction-of-rec-calls') applicability condition.
   </p>
   <p>
   The guard verification event is local;
   the exported function definition has @(':verify-guards') set to @('t')
   (when it must be guard-verified).
   </p>"
  (b* ((recursive (recursivep old nil wrld))
       (hints (if recursive
                  `(("Goal"
                     :in-theory '(,old-to-new)
                     :use ((:guard-theorem ,old)
                           ,(cdr (assoc-eq :restriction-guard
                                   appcond-thm-names))
                           ,(if stub?
                                `(:functional-instance
                                  ,(cdr (assoc-eq :restriction-of-rec-calls
                                          appcond-thm-names))
                                  (,stub? ,new))
                              (cdr (assoc-eq :restriction-of-rec-calls
                                     appcond-thm-names))))))
                `(("Goal"
                   :in-theory nil
                   :use ((:guard-theorem ,old)
                         ,(cdr (assoc-eq :restriction-guard
                                 appcond-thm-names)))))))
       (event `(local (verify-guards ,new :hints ,hints))))
    event))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define restrict-gen-everything ((old symbolp)
                                 (restriction pseudo-termp)
                                 (undefined pseudo-termp)
                                 (new symbolp)
                                 (new-enable booleanp)
                                 (old-to-new symbolp)
                                 (old-to-new-enable booleanp)
                                 (new-to-old symbolp)
                                 (new-to-old-enable booleanp)
                                 (verify-guards booleanp)
                                 (hints symbol-alistp)
                                 (print evmac-input-print-p)
                                 (show-only booleanp)
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
   the expansion of @(tsee restrict) (the @(tsee encapsulate)),
   followed by an event to extend the transformation table,
   optionally followed by events to print the exported events
   (if specified by the @(':print') input).
   The @(tsee progn) ends with @(':invisible') to avoid printing a return value.
   </p>
   <p>
   The @(tsee encapsulate) starts with some implicitly local events to
   ensure logic mode and
   avoid errors due to ignored or irrelevant formals in the generated function.
   Other implicitly local events remove any default and override hints,
   to prevent such hints from sabotaging the generated proofs;
   this removal is done after proving the applicability conditions,
   in case their proofs rely on the default or override hints.
   </p>
   <p>
   If the old and new functions are reflexive,
   i.e. if the old function occurs in its termination theorem,
   just before the applicability conditions
   we introduce the @('n')-ary stub described in the documentation,
   which is used in the @(':restriction-of-rec-calls') applicability condition.
   </p>
   <p>
   The @(tsee encapsulate) also includes events
   to locally install the non-normalized definitions
   of the old and new functions,
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
       (recursivep (recursivep old nil wrld))
       (reflexivep
        (and recursivep
             (member-eq old
                        (all-ffn-symbs (termination-theorem old (w state))
                                       nil))))
       ((mv stub? names-to-avoid)
        (if reflexivep
            (fresh-logical-name-with-$s-suffix
             (intern-in-package-of-symbol
              "?F" (pkg-witness (symbol-package-name old)))
             'constrained-function
             names-to-avoid
             wrld)
          (mv nil names-to-avoid)))
       (stub-event? (and stub?
                         (list `(defstub ,stub?
                                  ,(repeat (arity old wrld) '*) => *))))
       (appconds (restrict-gen-appconds old
                                        restriction
                                        verify-guards
                                        stub?
                                        state))
       ((er (list appcond-thm-events
                  appcond-thm-names
                  names-to-avoid))
        (evmac-appcond-theorems-no-extra-hints appconds
                                               hints
                                               names-to-avoid
                                               print
                                               ctx
                                               state))
       ((mv old-unnorm-event
            old-unnorm
            names-to-avoid)
        (install-not-normalized-event old t names-to-avoid wrld))
       ((mv new-local-event
            new-exported-event)
        (restrict-gen-new old
                          restriction
                          undefined
                          new
                          new-enable
                          verify-guards
                          wrld))
       ((mv new-unnorm-event
            new-unnorm
            &)
        (install-not-normalized-event new t names-to-avoid wrld))
       ((mv old-to-new-local-event
            old-to-new-exported-event)
        (restrict-gen-old-to-new old
                                 restriction
                                 new
                                 old-to-new
                                 old-to-new-enable
                                 appcond-thm-names
                                 stub?
                                 old-unnorm
                                 new-unnorm
                                 wrld))
       ((mv new-to-old-local-event
            new-to-old-exported-event)
        (restrict-gen-new-to-old old
                                 restriction
                                 new
                                 new-to-old
                                 new-to-old-enable
                                 old-to-new
                                 wrld))
       (verify-guards-event? (and verify-guards
                                  (list
                                   (restrict-gen-verify-guards
                                    old
                                    new
                                    old-to-new
                                    appcond-thm-names
                                    stub?
                                    wrld))))
       (theory-inv-event `(theory-invariant (incompatible
                                             (:rewrite ,old-to-new)
                                             (:rewrite ,new-to-old))))
       (numbered-name-event `(add-numbered-name-in-use ,new))
       (encapsulate-events `((logic)
                             (set-ignore-ok t)
                             (set-irrelevant-formals-ok t)
                             ,@stub-event?
                             ,@appcond-thm-events
                             (evmac-prepare-proofs)
                             ,old-unnorm-event
                             ,new-local-event
                             ,new-unnorm-event
                             ,old-to-new-local-event
                             ,new-to-old-local-event
                             ,@verify-guards-event?
                             ,new-exported-event
                             ,old-to-new-exported-event
                             ,new-to-old-exported-event
                             ,theory-inv-event
                             ,numbered-name-event))
       (encapsulate `(encapsulate () ,@encapsulate-events))
       ((when show-only)
        (if (member-eq print '(:info :all))
            (cw "~%~x0~|" encapsulate)
          (cw "~x0~|" encapsulate))
        (value '(value-triple :invisible)))
       (encapsulate+ (restore-output? (eq print :all) encapsulate))
       (transformation-table-event (record-transformation-call-event
                                    call encapsulate wrld))
       (print-result (and
                      (member-eq print '(:result :info :all))
                      `(,@(and (member-eq print '(:info :all))
                               '((cw-event "~%")))
                        (cw-event "~x0~|" ',new-exported-event)
                        (cw-event "~x0~|" ',old-to-new-exported-event)
                        (cw-event "~x0~|" ',new-to-old-exported-event)))))
    (value
     `(progn
        ,encapsulate+
        ,transformation-table-event
        ,@print-result
        (value-triple :invisible)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define restrict-fn (old
                     restriction
                     undefined
                     new-name
                     new-enable
                     old-to-new-name (old-to-new-name? booleanp)
                     old-to-new-enable (old-to-new-enable? booleanp)
                     new-to-old-name (new-to-old-name? booleanp)
                     new-to-old-enable (new-to-old-enable? booleanp)
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
  :parents (restrict-implementation)
  :short "Check redundancy,
          process the inputs, and
          generate the event to submit."
  :long
  "<p>
   If this call to the transformation is redundant,
   a message to that effect is printed on the screen.
   If the transformation is redundant and @(':show-only') is @('t'),
   the @(tsee encapsulate), retrieved from the table, is shown on the screen.
   </p>"
  (b* ((encapsulate? (previous-transformation-expansion call (w state)))
       ((when encapsulate?)
        (b* (((run-when show-only) (cw "~x0~|" encapsulate?)))
          (cw "~%The transformation ~x0 is redundant.~%" call)
          (value '(value-triple :invisible))))
       ((er (list old
                  restriction
                  undefined
                  new
                  new-enable
                  old-to-new
                  old-to-new-enable
                  new-to-old
                  new-to-old-enable
                  verify-guards
                  hints
                  names-to-avoid))
        (restrict-process-inputs old
                                 restriction
                                 undefined
                                 new-name
                                 new-enable
                                 old-to-new-name old-to-new-name?
                                 old-to-new-enable old-to-new-enable?
                                 new-to-old-name new-to-old-name?
                                 new-to-old-enable new-to-old-enable?
                                 verify-guards
                                 hints
                                 print
                                 show-only
                                 ctx
                                 state))
       ((er event) (restrict-gen-everything old
                                            restriction
                                            undefined
                                            new
                                            new-enable
                                            old-to-new
                                            old-to-new-enable
                                            new-to-old
                                            new-to-old-enable
                                            verify-guards
                                            hints
                                            print
                                            show-only
                                            call
                                            names-to-avoid
                                            ctx
                                            state)))
    (value event)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection restrict-macro-definition
  :parents (restrict-implementation)
  :short "Definition of the @(tsee restrict) macro."
  :long
  "<p>
   Submit the event form generated by @(tsee restrict-fn).
   </p>
   @(def restrict)"
  (defmacro restrict (&whole
                      call
                      ;; mandatory inputs:
                      old
                      restriction
                      ;; optional inputs:
                      &key
                      (undefined ':undefined)
                      (new-name ':auto)
                      (new-enable ':auto)
                      (old-to-new-name 'nil old-to-new-name?)
                      (old-to-new-enable 'nil old-to-new-enable?)
                      (new-to-old-name 'nil new-to-old-name?)
                      (new-to-old-enable 'nil new-to-old-enable?)
                      (verify-guards ':auto)
                      (hints 'nil)
                      (print ':result)
                      (show-only 'nil))
    `(make-event-terse (restrict-fn ',old
                                    ',restriction
                                    ',undefined
                                    ',new-name
                                    ',new-enable
                                    ',old-to-new-name
                                    ',old-to-new-name?
                                    ',old-to-new-enable
                                    ',old-to-new-enable?
                                    ',new-to-old-name
                                    ',new-to-old-name?
                                    ',new-to-old-enable
                                    ',new-to-old-enable?
                                    ',verify-guards
                                    ',hints
                                    ',print
                                    ',show-only
                                    ',call
                                    (cons 'restrict ',old)
                                    state)
                       :suppress-errors ,(not print))))
