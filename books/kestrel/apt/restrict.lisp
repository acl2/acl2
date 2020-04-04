; APT (Automated Program Transformations) Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "APT")

(include-book "kestrel/event-macros/applicability-conditions" :dir :system)
(include-book "kestrel/event-macros/input-processing" :dir :system)
(include-book "kestrel/event-macros/intro-macros" :dir :system)
(include-book "kestrel/event-macros/xdoc-constructors" :dir :system)
(include-book "kestrel/std/system/fresh-logical-name-with-dollars-suffix" :dir :system)
(include-book "kestrel/std/system/install-not-normalized-event" :dir :system)
(include-book "kestrel/utilities/error-checking/top" :dir :system)
(include-book "kestrel/utilities/keyword-value-lists" :dir :system)
(include-book "kestrel/utilities/orelse" :dir :system)
(include-book "kestrel/utilities/system/paired-names" :dir :system)
(include-book "kestrel/utilities/user-interface" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

(include-book "utilities/input-processing")
(include-book "utilities/transformation-table")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-implementation

 restrict

 :item-state t

 :item-wrld t

 :item-ctx t

 :items

 ("@('old'),
   @('restriction'),
   @('undefined'),
   @('new-name'),
   @('new-enable'),
   @('thm-name'),
   @('thm-enable'),
   @('non-executable'),
   @('verify-guards'),
   @('hints'),
   @('print'), and
   @('show-only')
   are the homonymous inputs to @(tsee restrict),
   before being processed.
   These formal parameters have no types because they may be any values."

  "@('call') is the call to @(tsee restrict) supplied by the user."

  "@('old$'),
   @('restriction$'),
   @('undefined$'),
   @('new-name$'),
   @('new-enable$'),
   @('thm-name$'),
   @('thm-enable$'),
   @('non-executable$'),
   @('verify-guards$'),
   @('hints$'),
   @('print$'), and
   @('show-only$')
   are the results of processing
   the homonymous inputs (without the @('$')) to @(tsee restrict).
   Some are identical to the corresponding inputs,
   but they have types implied by their successful validation,
   performed when they are processed."

  "@('stub?') is the stub called @('?f') in the documentation
   if @('old') is a reflexive function,
   or @('nil') otherwise."

  "@('appcond-thm-names') is an alist
   from the keywords that identify the applicability conditions
   to the corresponding generated theorem names."

  "@('old-unnorm-name') is the name of the generated theorem
   that installs the non-normalized definition of the target function."

  "@('new-unnorm-name') is the name of the generated theorem
   that installs the non-normalized definition of the new function."

  "@('names-to-avoid') is a cumulative list of names of generated events,
   used to ensure the absence of name clashes in the generated events."))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-input-processing restrict)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define restrict-process-old (old verify-guards ctx state)
  :returns (mv erp
               (old$ "A @(tsee symbolp) that is
                      the name of the target function
                      of the transformation,
                      denoted by the @('old') input.")
               state)
  :mode :program
  :short "Process the @('old') input."
  (b* ((wrld (w state))
       ((er old$) (ensure-function-name-or-numbered-wildcard$
                   old "The first input" t nil))
       (description (msg "The target function ~x0" old$))
       ((er &) (ensure-function-logic-mode$ old$ description t nil))
       ((er &) (ensure-function-defined$ old$ description t nil))
       ((er &) (ensure-function-has-args$ old$ description t nil))
       ((er &) (ensure-function-number-of-results$ old$ 1
                                                   description t nil))
       ((er &) (ensure-function-no-stobjs$ old$ description t nil))
       (recursive (recursivep old$ nil wrld))
       ((er &) (if recursive
                   (ensure-function-singly-recursive$ old$
                                                      description t nil)
                 (value nil)))
       ((er &) (if recursive
                   (ensure-function-known-measure$ old$
                                                   description t nil)
                 (value nil)))
       ((er &) (if (eq verify-guards t)
                   (ensure-function-guard-verified$
                    old$
                    (msg "Since the :VERIFY-GUARDS input is T, ~
                          the target function ~x0" old$)
                    t nil)
                 (value nil))))
    (value old$)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define restrict-process-restriction (restriction
                                      (old$ symbolp)
                                      (verify-guards$ booleanp)
                                      ctx
                                      state)
  :returns (mv erp
               (restriction$ "A @(tsee pseudo-termp) that is
                              the translation of @('restriction').")
               state)
  :mode :program
  :short "Process the @('restriction') input."
  (b* ((wrld (w state))
       ((er (list term stobjs-out)) (ensure-term$ restriction
                                                  "The second input" t nil))
       (description (msg "The term ~x0 that denotes the restricting predicate"
                         restriction))
       ((er &) (ensure-term-free-vars-subset$ term
                                              (formals old$ wrld)
                                              description t nil))
       ((er &) (ensure-term-logic-mode$ term description t nil))
       ((er &) (ensure-function/lambda/term-number-of-results$ stobjs-out 1
                                                               description
                                                               t nil))
       ((er &) (ensure-term-no-stobjs$ stobjs-out description t nil))
       ((er &) (if verify-guards$
                   (ensure-term-guard-verified-exec-fns$
                    term
                    (msg "Since either the :VERIFY-GUARDS input is T, ~
                          or it is (perhaps by default) :AUTO ~
                          and the target function ~x0 is guard-verified, ~@1"
                         old$ (msg-downcase-first description))
                    t nil)
                 (value nil)))
       ((er &) (ensure-term-does-not-call$ term old$
                                           description t nil)))
    (value term)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define restrict-process-undefined (undefined
                                    (old$ symbolp)
                                    ctx
                                    state)
  :returns (mv erp
               (undefined$ "A @(tsee pseudo-termp) that is
                            the translation of @('undefined').")
               state)
  :mode :program
  :short "Process the @(':undefined') input."
  (b* ((wrld (w state))
       ((er (list term stobjs-out)) (ensure-term$ undefined
                                                  "The :UNDEFINED input" t nil))
       (description (msg "The term ~x0 that denotes the undefined value"
                         undefined))
       ((er &) (ensure-term-free-vars-subset$ term
                                              (formals old$ wrld)
                                              description t nil))
       ((er &) (ensure-term-logic-mode$ term description t nil))
       ((er &) (ensure-function/lambda/term-number-of-results$ stobjs-out 1
                                                               description
                                                               t nil))
       ((er &) (ensure-term-no-stobjs$ stobjs-out description t nil))
       ((er &) (ensure-term-does-not-call$ term old$
                                           description t nil)))
    (value term)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define restrict-process-thm-name (thm-name
                                   (old$ symbolp)
                                   (new-name$ symbolp)
                                   ctx
                                   state)
  :returns (mv erp
               (thm-name$ "A @(tsee symbolp)
                           to use for the theorem
                           that relates the old and new functions.")
               state)
  :mode :program
  :short "Process the @(':thm-name') input."
  (b* (((er &) (ensure-symbol$ thm-name "The :THM-NAME input" t nil))
       (name (if (eq thm-name :auto)
                 (make-paired-name old$ new-name$ 2 (w state))
               thm-name))
       (description (msg "The name ~x0 of the theorem ~
                          that relates the target function ~x1 ~
                          to the new function ~x2, ~
                          ~@3,"
                         name old$ new-name$
                         (if (eq thm-name :auto)
                             "automatically generated ~
                              since the :THM-NAME input ~
                              is (perhaps by default) :AUTO"
                           "supplied as the :THM-NAME input")))
       ((er &) (ensure-symbol-new-event-name$ name description t nil))
       ((er &) (ensure-symbol-different$
                name new-name$
                (msg "the name ~x0 of the new function ~
                      (determined by the :NEW-NAME input)." new-name$)
                description
                t nil)))
    (value name)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define restrict-process-inputs (old
                                 restriction
                                 undefined
                                 new-name
                                 new-enable
                                 thm-name
                                 thm-enable
                                 non-executable
                                 verify-guards
                                 hints
                                 print
                                 show-only
                                 ctx
                                 state)
  :returns (mv erp
               (result "A tuple @('(old$
                                    restriction$
                                    undefined$
                                    new-name$
                                    new-enable$
                                    thm-name$
                                    non-executable$
                                    verify-guards$
                                    hints$)')
                        satisfying
                        @('(typed-tuplep symbolp
                                         pseudo-termp
                                         pseudo-termp
                                         symbolp
                                         booleanp
                                         symbolp
                                         booleanp
                                         booleanp
                                         evmac-input-hints-p
                                         result)'),
                        where @('old$') is
                        the result of @(tsee restrict-process-old),
                        @('restriction$') is
                        the result of @(tsee restrict-process-restriction),
                        @('undefined$') is
                        the result of @(tsee restrict-process-undefined),
                        @('new-name$') is
                        the result of @(tsee process-input-new-name),
                        @('new-enable$') indicates whether
                        the new function should be enabled or not,
                        @('thm-name$') is
                        the result of @(tsee restrict-process-thm-name),
                        @('non-executable$') indicates whether
                        the new function should be
                        non-executable or not,
                        @('verify-guards$') indicates whether the guards of
                        the new function should be verified or not, and
                        @('hints$') is
                        the result of @(tsee evmac-process-input-hints).")
               state)
  :mode :program
  :short "Process all the inputs."
  :long
  "<p>
   The inputs are processed
   in the order in which they appear in the documentation,
   except that @(':verify-guards') is processed just before @('restriction')
   because the result of processing @(':verify-guards')
   is used to process @('restriction').
   @('old') is processed before @(':verify-guards')
   because the result of processing @('old')
   is used to process @(':verify-guards').
   @(':verify-guards') is also used to process @('old'),
   but it is only tested for equality with @('t')
   (see @(tsee restrict-process-old)).
   </p>"
  (b* ((wrld (w state))
       ((er old$) (restrict-process-old old verify-guards ctx state))
       ((er verify-guards$) (ensure-boolean-or-auto-and-return-boolean$
                             verify-guards
                             (guard-verified-p old$ wrld)
                             "The :VERIFY-GUARDS input" t nil))
       ((er restriction$) (restrict-process-restriction
                           restriction old$ verify-guards$ ctx state))
       ((er undefined$) (restrict-process-undefined
                         undefined old$ ctx state))
       ((er new-name$) (process-input-new-name new-name old$ ctx state))
       ((er new-enable$) (ensure-boolean-or-auto-and-return-boolean$
                          new-enable
                          (fundef-enabledp old state)
                          "The :NEW-ENABLE input" t nil))
       ((er thm-name$) (restrict-process-thm-name
                        thm-name old$ new-name$ ctx state))
       ((er &) (ensure-boolean$ thm-enable "The :THM-ENABLE input" t nil))
       ((er non-executable$) (ensure-boolean-or-auto-and-return-boolean$
                              non-executable
                              (non-executablep old wrld)
                              "The :NON-EXECUTABLE input" t nil))
       ((er hints$) (evmac-process-input-hints hints ctx state))
       ((er &) (evmac-process-input-print print ctx state))
       ((er &) (evmac-process-input-show-only show-only ctx state)))
    (value (list old$
                 restriction$
                 undefined$
                 new-name$
                 new-enable$
                 thm-name$
                 non-executable$
                 verify-guards$
                 hints$))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-event-generation restrict
                                    :some-local-nonlocal-p t
                                    :some-local-p t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define restrict-gen-restriction-of-rec-calls-consequent-term
  ((old$ symbolp)
   (rec-calls-with-tests pseudo-tests-and-call-listp
                         "Recursive calls, with controlling tests,
                          of the old function.")
   (restriction$ pseudo-termp)
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
    old$ rec-calls-with-tests restriction$ stub? nil wrld))

  :prepwork
  ((define restrict-gen-restriction-of-rec-calls-consequent-term-aux
     ((old$ symbolp)
      (rec-calls-with-tests pseudo-tests-and-call-listp)
      (restriction$ pseudo-termp)
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
                         (sublis-fn-simple (acons old$ stub? nil) context)
                       context))
            (restriction-of-update (subcor-var (formals old$ wrld)
                                               (fargs call)
                                               restriction$))
            (restriction-of-update (if stub?
                                       (sublis-fn-simple (acons old$ stub? nil)
                                                         restriction-of-update)
                                     restriction-of-update)))
         (restrict-gen-restriction-of-rec-calls-consequent-term-aux
          old$
          (cdr rec-calls-with-tests)
          restriction$
          stub?
          (cons (implicate context restriction-of-update)
                rev-conjuncts)
          wrld))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define restrict-gen-appconds ((old$ symbolp)
                               (restriction$ pseudo-termp)
                               (verify-guards$ booleanp)
                               (stub? symbolp)
                               state)
  :returns (appconds "A @(tsee evmac-appcond-listp).")
  :mode :program
  :short "Generate the applicability conditions."
  (b* ((wrld (w state)))
    (append
     (make-evmac-appcond?
      :restriction-of-rec-calls
      (b* ((rec-calls-with-tests (recursive-calls old$ wrld))
           (consequent
            (restrict-gen-restriction-of-rec-calls-consequent-term
             old$ rec-calls-with-tests restriction$ stub? wrld)))
        (implicate restriction$
                   consequent))
      :when (recursivep old$ nil wrld))
     (make-evmac-appcond?
      :restriction-guard
      (b* ((old-guard (guard old$ nil wrld))
           (restriction-guard
            (term-guard-obligation restriction$ state)))
        (implicate old-guard
                   restriction-guard))
      :when verify-guards$)
     (make-evmac-appcond?
      :restriction-boolean
      (apply-term* 'booleanp restriction$)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define restrict-gen-new-fn ((old$ symbolp)
                             (restriction$ pseudo-termp)
                             (undefined$ pseudo-termp)
                             (new-name$ symbolp)
                             (new-enable$ booleanp)
                             (non-executable$ booleanp)
                             (verify-guards$ booleanp)
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
   it is wrapped with @(tsee mbt).
   </p>
   <p>
   Guard verification is deferred;
   see @(tsee restrict-gen-new-fn-verify-guards).
   </p>"
  (b* ((macro (function-intro-macro new-enable$ non-executable$))
       (formals (formals old$ wrld))
       (old-body (if (non-executablep old$ wrld)
                     (unwrapped-nonexec-body old$ wrld)
                   (ubody old$ wrld)))
       (new-body-core (sublis-fn-simple (acons old$ new-name$ nil)
                                        old-body))
       (new-body `(if (mbt ,restriction$) ,new-body-core ,undefined$))
       (new-body (untranslate new-body nil wrld))
       (recursive (recursivep old$ nil wrld))
       (wfrel? (and recursive
                    (well-founded-relation old$ wrld)))
       (measure? (and recursive
                      (untranslate (measure old$ wrld) nil wrld)))
       (termination-hints? (and recursive
                                `(("Goal"
                                   :in-theory nil
                                   :use (:termination-theorem ,old$)))))
       (old-guard (guard old$ nil wrld))
       (new-guard (conjoin2 old-guard restriction$))
       (new-guard (untranslate new-guard t wrld))
       (local-event
        `(local
          (,macro ,new-name$ (,@formals)
                  (declare (xargs ,@(and recursive
                                         (list :well-founded-relation wfrel?
                                               :measure measure?
                                               :hints termination-hints?
                                               :ruler-extenders :all))
                                  :guard ,new-guard
                                  :verify-guards nil))
                  ,new-body)))
       (exported-event
        `(,macro ,new-name$ (,@formals)
                 (declare (xargs ,@(and recursive
                                        (list :well-founded-relation wfrel?
                                              :measure measure?
                                              :ruler-extenders :all))
                                 :guard ,new-guard
                                 :verify-guards ,verify-guards$))
                 ,new-body)))
    (mv local-event exported-event)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define restrict-gen-old-to-new-thm ((old$ symbolp)
                                     (restriction$ pseudo-termp)
                                     (new-name$ symbolp)
                                     (thm-name$ symbolp)
                                     (thm-enable$ booleanp)
                                     (appcond-thm-names symbol-symbol-alistp)
                                     (stub? symbolp)
                                     (old-unnorm-name symbolp)
                                     (new-unnorm-name symbolp)
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
  (b* ((macro (theorem-intro-macro thm-enable$))
       (formals (formals old$ wrld))
       (formula (implicate restriction$
                           `(equal (,old$ ,@formals)
                                   (,new-name$ ,@formals))))
       (formula (untranslate formula t wrld))
       (recursive (recursivep old$ nil wrld))
       (hints (if recursive
                  (b* ((lemma-name (cdr (assoc-eq :restriction-of-rec-calls
                                          appcond-thm-names)))
                       (lemma-instance (if stub?
                                           `(:functional-instance ,lemma-name
                                             (,stub? ,new-name$))
                                         lemma-name)))
                    `(("Goal"
                       :in-theory '(,old-unnorm-name
                                    ,new-unnorm-name
                                    (:induction ,old$))
                       :induct (,old$ ,@formals))
                      '(:use ,lemma-instance)))
                `(("Goal"
                   :in-theory '(,old-unnorm-name
                                ,new-unnorm-name)))))
       (local-event `(local
                      (,macro ,thm-name$
                              ,formula
                              :hints ,hints)))
       (exported-event `(,macro ,thm-name$
                                ,formula)))
    (mv local-event exported-event)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define restrict-gen-new-fn-verify-guards
  ((old$ symbolp)
   (new-name$ symbolp)
   (thm-name$ symbolp)
   (appcond-thm-names symbol-symbol-alistp)
   (stub? symbolp)
   (wrld plist-worldp))
  :returns (local-event pseudo-event-formp)
  :verify-guards nil
  :short "Generate the event to verify the guards of the new function."
  :long
  "<p>
   As mentioned in @(tsee restrict-gen-new-fn),
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
   </p>
   <p>
   The guard verification involves proving that
   the restriction test inside @(tsee mbt) is equal to @('t').
   The guard itself implies that it is non-@('nil'),
   and  the applicability condition @(':restriction-boolean')
   is used to prove that, therefore, it is @('t').
   </p>"
  (b* ((recursive (recursivep old$ nil wrld))
       (hints (if recursive
                  `(("Goal"
                     :in-theory '(,thm-name$)
                     :use ((:guard-theorem ,old$)
                           ,(cdr (assoc-eq :restriction-guard
                                   appcond-thm-names))
                           ,(if stub?
                                `(:functional-instance
                                  ,(cdr (assoc-eq :restriction-of-rec-calls
                                         appcond-thm-names))
                                  (,stub? ,new-name$))
                              (cdr (assoc-eq :restriction-of-rec-calls
                                     appcond-thm-names)))
                           ,(cdr (assoc-eq :restriction-boolean
                                   appcond-thm-names)))))
                `(("Goal"
                   :in-theory nil
                   :use ((:guard-theorem ,old$)
                         ,(cdr (assoc-eq :restriction-guard
                                 appcond-thm-names))
                         ,(cdr (assoc-eq :restriction-boolean
                                 appcond-thm-names)))))))
       (event `(local (verify-guards ,new-name$ :hints ,hints))))
    event))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define restrict-gen-everything
  ((old$ symbolp)
   (restriction$ pseudo-termp)
   (undefined$ pseudo-termp)
   (new-name$ symbolp)
   (new-enable$ booleanp)
   (thm-name$ symbolp)
   (thm-enable$ booleanp)
   (non-executable$ booleanp)
   (verify-guards$ booleanp)
   (hints$ symbol-alistp)
   (print$ evmac-input-print-p)
   (show-only$ booleanp)
   (call pseudo-event-formp)
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
       (names-to-avoid (list new-name$ thm-name$))
       (recursivep (recursivep old$ nil wrld))
       (reflexivep
        (and recursivep
             (member-eq old$
                        (all-ffn-symbs (termination-theorem old$ (w state))
                                       nil))))
       (stub? (and reflexivep
                   (fresh-logical-name-with-$s-suffix
                    (intern-in-package-of-symbol
                     "?F" (pkg-witness (symbol-package-name old$)))
                    'constrained-function
                    names-to-avoid
                    wrld)))
       (names-to-avoid (if stub? (rcons stub? names-to-avoid) names-to-avoid))
       (stub-event? (and stub?
                         (list `(defstub ,stub?
                                  ,(repeat (arity old$ wrld) '*) => *))))
       (appconds (restrict-gen-appconds old$
                                        restriction$
                                        verify-guards$
                                        stub?
                                        state))
       ((er (list appcond-thm-events
                  appcond-thm-names
                  names-to-avoid))
        (evmac-appcond-theorems-no-extra-hints
         appconds hints$ names-to-avoid print$ ctx state))
       ((mv old-unnorm-event
            old-unnorm-name) (install-not-normalized-event old$
            t
            names-to-avoid
            wrld))
       (names-to-avoid (cons old-unnorm-name names-to-avoid))
       ((mv new-fn-local-event
            new-fn-exported-event) (restrict-gen-new-fn
            old$
            restriction$
            undefined$
            new-name$
            new-enable$
            non-executable$
            verify-guards$
            wrld))
       ((mv new-unnorm-event
            new-unnorm-name) (install-not-normalized-event new-name$
            t
            names-to-avoid
            wrld))
       ((mv old-to-new-thm-local-event
            old-to-new-thm-exported-event) (restrict-gen-old-to-new-thm
            old$
            restriction$
            new-name$
            thm-name$
            thm-enable$
            appcond-thm-names
            stub?
            old-unnorm-name
            new-unnorm-name
            wrld))
       (new-fn-verify-guards-event? (and verify-guards$
                                         (list
                                          (restrict-gen-new-fn-verify-guards
                                           old$
                                           new-name$
                                           thm-name$
                                           appcond-thm-names
                                           stub?
                                           wrld))))
       (new-fn-numbered-name-event `(add-numbered-name-in-use ,new-name$))
       (encapsulate-events `((logic)
                             (set-ignore-ok t)
                             (set-irrelevant-formals-ok t)
                             ,@stub-event?
                             ,@appcond-thm-events
                             (set-default-hints nil)
                             (set-override-hints nil)
                             ,old-unnorm-event
                             ,new-fn-local-event
                             ,new-unnorm-event
                             ,old-to-new-thm-local-event
                             ,@new-fn-verify-guards-event?
                             ,new-fn-exported-event
                             ,old-to-new-thm-exported-event
                             ,new-fn-numbered-name-event))
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
                        (cw-event "~x0~|" ',old-to-new-thm-exported-event)))))
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
                     thm-name
                     thm-enable
                     non-executable
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
       ((er (list old$
                  restriction$
                  undefined$
                  new-name$
                  new-enable$
                  thm-name$
                  non-executable$
                  verify-guards$
                  hints$))
        (restrict-process-inputs old
                                 restriction
                                 undefined
                                 new-name
                                 new-enable
                                 thm-name
                                 thm-enable
                                 non-executable
                                 verify-guards
                                 hints
                                 print
                                 show-only
                                 ctx state))
       ((er event) (restrict-gen-everything old$
                                            restriction$
                                            undefined$
                                            new-name$
                                            new-enable$
                                            thm-name$
                                            thm-enable
                                            non-executable$
                                            verify-guards$
                                            hints$
                                            print
                                            show-only
                                            call
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
                      (thm-name ':auto)
                      (thm-enable 't)
                      (non-executable ':auto)
                      (verify-guards ':auto)
                      (hints 'nil)
                      (print ':result)
                      (show-only 'nil))
    `(make-event-terse (restrict-fn ',old
                                    ',restriction
                                    ',undefined
                                    ',new-name
                                    ',new-enable
                                    ',thm-name
                                    ',thm-enable
                                    ',non-executable
                                    ',verify-guards
                                    ',hints
                                    ',print
                                    ',show-only
                                    ',call
                                    (cons 'restrict ',old)
                                    state)
                      :suppress-errors ,(not print))))
