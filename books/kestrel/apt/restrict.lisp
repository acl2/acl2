; APT Domain Restriction Transformation -- Implementation
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

(local (xdoc::set-default-parents restrict-implementation))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define restrict-check-old
  ((old "Input to the transformation.")
   (verify-guards "Input to the transformation.")
   (ctx "Context for errors.")
   state)
  :returns (mv (erp "@(tsee booleanp) flag of the
                     <see topic='@(url acl2::error-triple)'>error
                     triple</see>.")
               (old-fn-name "A @(tsee symbolp) that is
                             the name of the target function
                             of the transformation,
                             denoted by the @('old') input.")
               state)
  :mode :program
  :short "Ensure that the @('old') input to the transformation is valid."
  (b* ((wrld (w state))
       ((er old-fn-name) (ensure-function-name-or-numbered-wildcard$
                          old "The first input" t nil))
       (description (msg "The target function ~x0" old-fn-name))
       ((er &) (ensure-function-logic-mode$ old-fn-name description t nil))
       ((er &) (ensure-function-defined$ old-fn-name description t nil))
       ((er &) (ensure-function-has-args$ old-fn-name description t nil))
       ((er &) (ensure-function-number-of-results$ old-fn-name 1
                                                   description t nil))
       ((er &) (ensure-function-no-stobjs$ old-fn-name description t nil))
       (recursive (recursivep old-fn-name nil wrld))
       ((er &) (if recursive
                   (ensure-function-singly-recursive$ old-fn-name
                                                      description t nil)
                 (value nil)))
       ((er &) (if recursive
                   (ensure-function-known-measure$ old-fn-name
                                                   description t nil)
                 (value nil)))
       ((er &) (if recursive
                   (ensure-function-not-in-termination-thm$ old-fn-name
                                                            description t nil)
                 (value nil)))
       ((er &) (if (eq verify-guards t)
                   (ensure-function-guard-verified$
                    old-fn-name
                    (msg "Since the :VERIFY-GUARDS input is T, ~
                          the target function ~x0" old-fn-name)
                    t nil)
                 (value nil))))
    (value old-fn-name)))

(define restrict-check-restriction
  ((restriction "Input to the transformation.")
   (old-fn-name symbolp "Result of @(tsee restrict-check-old).")
   (do-verify-guards booleanp
                     "Result of validating
                      the @(':verify-guards') input to the transformation
                      (in @(tsee restrict-check-inputs)).")
   (ctx "Context for errors.")
   state)
  :returns (mv (erp "@(tsee booleanp) flag of the
                     <see topic='@(url acl2::error-triple)'>error
                     triple</see>.")
               (restriction$ "A @(tsee pseudo-termp) that is
                              the translation of @('restriction').")
               state)
  :mode :program
  :short "Ensure that the @('restriction') input to the transformation
          is valid."
  (b* ((wrld (w state))
       ((er (list term stobjs-out)) (ensure-term$ restriction
                                                  "The second input" t nil))
       (description (msg "The term ~x0 that denotes the restricting predicate"
                         restriction))
       ((er &) (ensure-term-free-vars-subset$ term
                                              (formals old-fn-name wrld)
                                              description t nil))
       ((er &) (ensure-term-logic-mode$ term description t nil))
       ((er &) (ensure-function/lambda/term-number-of-results$ stobjs-out 1
                                                               description
                                                               t nil))
       ((er &) (ensure-term-no-stobjs$ stobjs-out description t nil))
       ((er &) (if do-verify-guards
                   (ensure-term-guard-verified-exec-fns$
                    term
                    (msg "Since either the :VERIFY-GUARDS input is T, ~
                          or it is (perhaps by default) :AUTO ~
                          and the target function ~x0 is guard-verified, ~@1"
                         old-fn-name (msg-downcase-first description))
                    t nil)
                 (value nil)))
       ((er &) (ensure-term-does-not-call$ term old-fn-name
                                           description t nil)))
    (value term)))

(define restrict-check-undefined
  ((undefined "Input to the transformation.")
   (old-fn-name symbolp "Result of @(tsee restrict-check-old).")
   (ctx "Context for errors.")
   state)
  :returns (mv (erp "@(tsee booleanp) flag of the
                     <see topic='@(url acl2::error-triple)'>error
                     triple</see>.")
               (undefined$ "A @(tsee pseudo-termp) that is
                            the translation of @('undefined').")
               state)
  :mode :program
  :short "Ensure that the @(':undefined') input to the transformation
          is valid."
  (b* ((wrld (w state))
       ((er (list term stobjs-out)) (ensure-term$ undefined
                                                  "The :UNDEFINED input" t nil))
       (description (msg "The term ~x0 that denotes the undefined value"
                         undefined))
       ((er &) (ensure-term-free-vars-subset$ term
                                              (formals old-fn-name wrld)
                                              description t nil))
       ((er &) (ensure-term-logic-mode$ term description t nil))
       ((er &) (ensure-function/lambda/term-number-of-results$ stobjs-out 1
                                                               description
                                                               t nil))
       ((er &) (ensure-term-no-stobjs$ stobjs-out description t nil))
       ((er &) (ensure-term-does-not-call$ term old-fn-name
                                           description t nil)))
    (value term)))

(define restrict-check-new-name
  ((new-name "Input to the transformation.")
   (old-fn-name symbolp "Result of @(tsee restrict-check-old).")
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

(define restrict-check-thm-name
  ((thm-name "Input to the transformation.")
   (old-fn-name symbolp "Result of @(tsee restrict-check-old).")
   (new-fn-name symbolp "Result of @(tsee restrict-check-new-name).")
   (ctx "Context for errors.")
   state)
  :returns (mv (erp "@(tsee booleanp) flag of the
                     <see topic='@(url acl2::error-triple)'>error
                     triple</see>.")
               (old-to-new-thm-name "A @(tsee symbolp)
                                     to use for the theorem
                                     that relates the old and new functions.")
               state)
  :mode :program
  :short "Ensure that the @(':thm-name') input to the transformation
          is valid."
  (b* (((er &) (ensure-symbol$ thm-name "The :THM-NAME input" t nil))
       (name (if (eq thm-name :auto)
                 (make-paired-name old-fn-name new-fn-name 2 (w state))
               thm-name))
       (description (msg "The name ~x0 of the theorem ~
                          that relates the target function ~x1 ~
                          to the new function ~x2, ~
                          ~@3,"
                         name old-fn-name new-fn-name
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
                t nil)))
    (value name)))

(defval *restrict-app-cond-names*
  :short "Names of all the applicability conditions."
  '(:restriction-of-rec-calls
    :restriction-guard
    :restriction-boolean)
  ///

  (defruled symbol-listp-of-*restrict-app-cond-names*
    (symbol-listp *restrict-app-cond-names*))

  (defruled no-duplicatesp-eq-of-*restrict-app-cond-names*
    (no-duplicatesp-eq *restrict-app-cond-names*)))

(define restrict-check-hints
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
       ((er &) (ensure-list-subset$ keys *restrict-app-cond-names*
                                    description t nil)))
    (value alist)))

(define restrict-check-inputs ((old "Input to the transformation.")
                               (restriction "Input to the transformation.")
                               (undefined "Input to the transformation.")
                               (new-name "Input to the transformation.")
                               (new-enable "Input to the transformation.")
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
                                    restriction$
                                    undefined$
                                    new-fn-name
                                    new-fn-enable
                                    old-to-new-thm-name
                                    make-non-executable
                                    do-verify-guards
                                    hints-alist
                                    print$)')
                        satisfying
                        @('(typed-tuplep symbolp
                                         pseudo-termp
                                         pseudo-termp
                                         symbolp
                                         booleanp
                                         symbolp
                                         booleanp
                                         booleanp
                                         symbol-alistp
                                         canonical-print-specifier-p
                                         result)'),
                        where @('old-fn-name') is
                        the result of @(tsee restrict-check-old),
                        @('restriction$') is
                        the result of @(tsee restrict-check-restriction),
                        @('undefined$') is
                        the result of @(tsee restrict-check-undefined),
                        @('new-fn-name') is
                        the result of @(tsee restrict-check-new-name),
                        @('new-fn-enable') indicates whether
                        the new function should be enabled or not,
                        @('old-to-new-thm-name') is
                        the result of @(tsee restrict-check-thm-name),
                        @('make-non-executable') indicates whether
                        the new function should be
                        non-executable or not,
                        @('do-verify-guards') indicates whether the guards of
                        the new function should be verified or not,
                        @('hints-alist') is
                        the result of @(tsee restrict-check-hints), and
                        @('print$') is a canonicalized version of
                        the @(':print') input.")
               state)
  :mode :program
  :short "Ensure that all the inputs to the transformation are valid."
  :long
  "<p>
   The inputs are validated
   in the order in which they appear in the documentation,
   except that @(':verify-guards') is validated just before @('restriction')
   because the result of validating @(':verify-guards')
   is used to validate @('restriction').
   @('old') is validated before @(':verify-guards')
   because the result of validating @('old')
   is used to validate @(':verify-guards').
   @(':verify-guards') is also used to validate @('old'),
   but it is only tested for equality with @('t')
   (see @(tsee restrict-check-old)).
   </p>"
  (b* (((er old-fn-name) (restrict-check-old old verify-guards ctx state))
       ((er do-verify-guards) (ensure-boolean-or-auto-and-return-boolean$
                               verify-guards
                               (guard-verified-p old-fn-name (w state))
                               "The :VERIFY-GUARDS input" t nil))
       ((er restriction$) (restrict-check-restriction
                           restriction old-fn-name do-verify-guards ctx state))
       ((er undefined$) (restrict-check-undefined
                         undefined old-fn-name ctx state))
       ((er new-fn-name) (restrict-check-new-name
                          new-name old-fn-name ctx state))
       ((er new-fn-enable) (ensure-boolean-or-auto-and-return-boolean$
                            new-enable
                            (fundef-enabledp old state)
                            "The :NEW-ENABLE input" t nil))
       ((er old-to-new-thm-name) (restrict-check-thm-name
                                  thm-name old-fn-name new-fn-name ctx state))
       ((er &) (ensure-boolean$ thm-enable "The :THM-ENABLE input" t nil))
       ((er make-non-executable) (ensure-boolean-or-auto-and-return-boolean$
                                  non-executable
                                  (non-executablep old (w state))
                                  "The :NON-EXECUTABLE input" t nil))
       ((er hints-alist) (restrict-check-hints hints ctx state))
       ((er print$) (ensure-is-print-specifier$ print "The :PRINT input" t nil))
       ((er &) (ensure-boolean$ show-only "The :SHOW-ONLY input" t nil)))
    (value (list old-fn-name
                 restriction$
                 undefined$
                 new-fn-name
                 new-fn-enable
                 old-to-new-thm-name
                 make-non-executable
                 do-verify-guards
                 hints-alist
                 print$))))

(define restrict-restriction-of-rec-calls-consequent
  ((old-fn-name symbolp "Result of @(tsee restrict-check-inputs).")
   (rec-calls-with-tests pseudo-tests-and-call-listp
                         "Recursive calls, with controlling tests,
                          of the old function.")
   (restriction$ pseudo-termp "Result of @(tsee restrict-check-inputs).")
   (wrld plist-worldp))
  :returns (consequent "A @(tsee pseudo-termp).")
  :verify-guards nil
  :short "Consequent of the
          @(':restriction-of-rec-calls') applicability condition."
  :long
  "<p>
   This is the term
   </p>
   @({
     (and (implies context1<x1,...,xn>
                   restriction<update1-x1<x1,...,xn>,
                               ...,
                               update1-xn<x1,...,xn>>)
          ...
          (implies contextm<x1,...,xn>
                   restriction<updatem-x1<x1,...,xn>,
                               ...,
                               updatem-xn<x1,...,xn>>))
   })"
  (conjoin
   (restrict-restriction-of-rec-calls-consequent-aux old-fn-name
                                                     rec-calls-with-tests
                                                     restriction$
                                                     nil
                                                     wrld))

  :prepwork
  ((define restrict-restriction-of-rec-calls-consequent-aux
     ((old-fn-name symbolp)
      (rec-calls-with-tests pseudo-tests-and-call-listp)
      (restriction$ pseudo-termp)
      (rev-conjuncts pseudo-term-listp)
      (wrld plist-worldp))
     :returns (conjuncts) ; PSEUDO-TERM-LISTP
     :verify-guards nil
     (if (endp rec-calls-with-tests)
         (reverse rev-conjuncts)
       (b* ((tests-and-call (car rec-calls-with-tests))
            (tests (access tests-and-call tests-and-call :tests))
            (call (access tests-and-call tests-and-call :call))
            (context (conjoin tests)))
         (restrict-restriction-of-rec-calls-consequent-aux
          old-fn-name
          (cdr rec-calls-with-tests)
          restriction$
          (cons (implicate context
                           (subcor-var (formals old-fn-name wrld)
                                       (fargs call)
                                       restriction$))
                rev-conjuncts)
          wrld))))))

(define restrict-app-cond-formula
  ((name (member-eq name *restrict-app-cond-names*)
         "Name of the applicability condition.")
   (old-fn-name symbolp "Result of @(tsee restrict-check-inputs).")
   (restriction$ pseudo-termp "Result of @(tsee restrict-check-inputs).")
   state)
  :returns (formula "An untranslated term.")
  :mode :program
  :short "Formula of the named applicability condition."
  (let ((wrld (w state)))
    (case name
      (:restriction-of-rec-calls
       (b* ((rec-calls-with-tests (recursive-calls old-fn-name wrld))
            (consequent (restrict-restriction-of-rec-calls-consequent
                         old-fn-name rec-calls-with-tests restriction$ wrld))
            (formula-trans (implicate restriction$ consequent)))
         (untranslate formula-trans t wrld)))
      (:restriction-guard
       (b* ((old-guard (guard old-fn-name nil wrld))
            (restriction-guard (term-guard-obligation restriction$ state))
            (formula-trans (implicate old-guard restriction-guard)))
         (untranslate formula-trans t wrld)))
      (:restriction-boolean
       (b* ((formula-trans (apply-term* 'acl2::booleanp restriction$)))
         (untranslate formula-trans t wrld)))
      (t (impossible)))))

(define restrict-app-cond-present-p
  ((name (member-eq name *restrict-app-cond-names*)
         "Name of the applicability condition.")
   (old-fn-name symbolp "Result of @(tsee restrict-check-inputs).")
   (do-verify-guards booleanp "Result of @(tsee restrict-check-inputs).")
   (wrld plist-worldp))
  :returns (yes/no booleanp :hyp (booleanp do-verify-guards))
  :short "Check if the named applicability condition is present."
  (case name
    (:restriction-of-rec-calls (if (recursivep old-fn-name nil wrld) t nil))
    (:restriction-guard do-verify-guards)
    (:restriction-boolean t)
    (t (impossible))))

(define restrict-app-conds
  ((old-fn-name symbolp "Result of @(tsee restrict-check-inputs).")
   (restriction$ pseudo-termp "Result of @(tsee restrict-check-inputs).")
   (do-verify-guards booleanp "Result of @(tsee restrict-check-inputs).")
   state)
  :returns (app-conds "A @(tsee symbol-alistp).")
  :mode :program
  :short "Generate the applicability conditions that must hold."
  (restrict-app-conds-aux *restrict-app-cond-names*
                          old-fn-name restriction$ do-verify-guards nil state)

  :prepwork
  ((define restrict-app-conds-aux
     ((names (subsetp-eq names *restrict-app-cond-names*))
      (old-fn-name symbolp)
      (restriction$ pseudo-termp)
      (do-verify-guards booleanp)
      (rev-app-conds symbol-alistp)
      state)
     :returns (app-conds) ; SYMBOL-ALISTP
     :mode :program
     :parents nil
     (if (endp names)
         (reverse rev-app-conds)
       (b* ((name (car names))
            ((unless (restrict-app-cond-present-p
                      name old-fn-name do-verify-guards (w state)))
             (restrict-app-conds-aux (cdr names)
                                     old-fn-name
                                     restriction$
                                     do-verify-guards
                                     rev-app-conds
                                     state))
            (formula (restrict-app-cond-formula
                      name
                      old-fn-name
                      restriction$
                      state)))
         (restrict-app-conds-aux (cdr names)
                                 old-fn-name
                                 restriction$
                                 do-verify-guards
                                 (acons name formula rev-app-conds)
                                 state))))))

(define restrict-new-fn-intro-events
  ((old-fn-name symbolp "Result of @(tsee restrict-check-inputs).")
   (restriction$ pseudo-termp "Result of @(tsee restrict-check-inputs).")
   (undefined$ pseudo-termp "Result of @(tsee restrict-check-inputs).")
   (new-fn-name symbolp "Result of @(tsee restrict-check-inputs).")
   (new-fn-enable booleanp "Result of @(tsee restrict-check-inputs).")
   (make-non-executable booleanp "Result of @(tsee restrict-check-inputs).")
   (do-verify-guards booleanp "Result of @(tsee restrict-check-inputs).")
   (wrld plist-worldp))
  :returns (mv (new-fn-local-event "A @(tsee pseudo-event-formp).")
               (new-fn-exported-event "A @(tsee pseudo-event-formp)."))
  :mode :program
  :short "Local and exported events to introduce the new function."
  :long
  "<p>
   In the @(tsee encapsulate) generated by @(tsee restrict-event),
   the new function is introduced via a local event first,
   then via a redundant non-local (i.e. exported) event.
   The local event includes the hints for the termination proof,
   and does not perform guard verification
   (even if guard verification must take place:
   guard verification is deferred in this case;
   see @(tsee restrict-new-fn-verify-guards-event)).
   The exported event has no termination proof hints
   and includes guard verification iff guard verification must take place.
   This keeps the event history after the transformation ``clean'',
   without implementation-specific termination hints
   and with the correct @(':verify-guards') in the declarations.
   </p>
   <p>
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
   in the empty theory, using the termination theorem of the old function.
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
   </p>"
  (b* ((macro (function-intro-macro new-fn-enable make-non-executable))
       (formals (formals old-fn-name wrld))
       (old-body (if (non-executablep old-fn-name wrld)
                     (unwrapped-nonexec-body old-fn-name wrld)
                   (ubody old-fn-name wrld)))
       (new-body-core (sublis-fn-simple (acons old-fn-name new-fn-name nil)
                                        old-body))
       (new-body `(if (mbt ,restriction$) ,new-body-core ,undefined$))
       (new-body (untranslate new-body nil wrld))
       (recursive (recursivep old-fn-name nil wrld))
       (wfrel? (and recursive
                    (well-founded-relation old-fn-name wrld)))
       (measure? (and recursive
                      (untranslate (measure old-fn-name wrld) nil wrld)))
       (termination-hints? (and recursive
                                `(("Goal"
                                   :in-theory nil
                                   :use (:termination-theorem ,old-fn-name)))))
       (old-guard (guard old-fn-name nil wrld))
       (new-guard (conjoin2 old-guard restriction$))
       (new-guard (untranslate new-guard t wrld))
       (local-event
        `(local
          (,macro ,new-fn-name (,@formals)
                  (declare (xargs ,@(and recursive
                                         (list :well-founded-relation wfrel?
                                               :measure measure?
                                               :hints termination-hints?
                                               :ruler-extenders :all))
                                  :guard ,new-guard
                                  :verify-guards nil))
                  ,new-body)))
       (exported-event
        `(,macro ,new-fn-name (,@formals)
                 (declare (xargs ,@(and recursive
                                        (list :well-founded-relation wfrel?
                                              :measure measure?
                                              :ruler-extenders :all))
                                 :guard ,new-guard
                                 :verify-guards ,do-verify-guards))
                 ,new-body)))
    (mv local-event exported-event)))

(define restrict-old-to-new-intro-events
  ((old-fn-name symbolp "Result of @(tsee restrict-check-inputs).")
   (restriction$ pseudo-termp "Result of @(tsee restrict-check-inputs).")
   (new-fn-name symbolp "Result of @(tsee restrict-check-inputs).")
   (old-to-new-thm-name symbolp "Result of @(tsee restrict-check-inputs).")
   (thm-enable booleanp "Input to the transformation, after validation.")
   (app-cond-thm-names symbol-symbol-alistp
                       "Map from the names of the applicability conditions
                        to the corresponding theorems
                        (calculated in @(tsee restrict-event)).")
   (old-fn-unnorm-name symbolp "Name of the theorem that installs
                                the non-normalized definition
                                of the old function.")
   (new-fn-unnorm-name symbolp "Name of the theorem that installs
                                the non-normalized definition
                                of the new function.")
   (wrld plist-worldp))
  :returns (mv (old-to-new-local-event "A @(tsee pseudo-event-formp).")
               (old-to-new-exported-event "A @(tsee pseudo-event-formp)."))
  :mode :program
  :short "Local and exported events to introduce
          the theorem that relates the old and new functions."
  :long
  "<p>
   In the @(tsee encapsulate) generated by @(tsee restrict-event),
   the theorem that relates the old and new functions
   is introduced via a local event first,
   then via a redundant non-local (i.e. exported) event.
   The local event includes the hints for the proof.
   The exported event has no proof hints.
   This keeps the event history after the transformation ``clean'',
   without implementation-specific proof hints
   that may refer to local events of the @(tsee encapsulate)
   that do not exist in the history after the transformation.
   </p>
   <p>
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
   </p>"
  (b* ((macro (theorem-intro-macro thm-enable))
       (formals (formals old-fn-name wrld))
       (formula (implicate restriction$
                           `(equal (,old-fn-name ,@formals)
                                   (,new-fn-name ,@formals))))
       (formula (untranslate formula t wrld))
       (recursive (recursivep old-fn-name nil wrld))
       (hints (if recursive
                  `(("Goal"
                     :in-theory '(,old-fn-unnorm-name
                                  ,new-fn-unnorm-name
                                  (:induction ,old-fn-name))
                     :induct (,old-fn-name ,@formals))
                    '(:use ,(cdr (assoc-eq :restriction-of-rec-calls
                                           app-cond-thm-names))))
                `(("Goal"
                   :in-theory '(,old-fn-unnorm-name
                                ,new-fn-unnorm-name)))))
       (local-event `(local
                      (,macro ,old-to-new-thm-name
                              ,formula
                              :hints ,hints)))
       (exported-event `(,macro ,old-to-new-thm-name
                                ,formula)))
    (mv local-event exported-event)))

(define restrict-new-fn-verify-guards-event
  ((old-fn-name symbolp "Result of @(tsee restrict-check-inputs).")
   (new-fn-name symbolp "Result of @(tsee restrict-check-inputs).")
   (old-to-new-thm-name symbolp "Result of @(tsee restrict-check-inputs).")
   (app-cond-thm-names symbol-symbol-alistp
                       "Map from the names of the applicability conditions
                        to the corresponding theorems
                        (calculated in @(tsee restrict-event)).")
   (wrld plist-worldp))
  :returns (new-fn-verify-guards-event pseudo-event-formp)
  :verify-guards nil
  :short "Event to verify the guards of the new function."
  :long
  "<p>
   As mentioned in @(tsee restrict-new-fn-intro-events),
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
   </p>
   <p>
   The guard verification event
   is local to the @(tsee encapsulate) generated by the transformation.
   This keeps the event history after the transformation ``clean'',
   without implementation-specific proof hints
   that may refer to local events of the @(tsee encapsulate)
   that do not exist in the history after the transformation.
   </p>
   <p>
   The guard verification involves proving that
   the restriction test inside @(tsee mbt) is equal to @('t').
   The guard itself implies that it is non-@('nil'),
   and  the applicability condition @(':restriction-boolean')
   is used to prove that, therefore, it is @('t').
   </p>"
  (b* ((recursive (recursivep old-fn-name nil wrld))
       (hints (if recursive
                  `(("Goal"
                     :in-theory '(,old-to-new-thm-name)
                     :use ((:guard-theorem ,old-fn-name)
                           ,(cdr (assoc-eq :restriction-guard
                                   app-cond-thm-names))
                           ,(cdr (assoc-eq :restriction-of-rec-calls
                                   app-cond-thm-names))
                           ,(cdr (assoc-eq :restriction-boolean
                                   app-cond-thm-names)))))
                `(("Goal"
                   :in-theory nil
                   :use ((:guard-theorem ,old-fn-name)
                         ,(cdr (assoc-eq :restriction-guard
                                 app-cond-thm-names))
                         ,(cdr (assoc-eq :restriction-boolean
                                 app-cond-thm-names)))))))
       (event `(local (verify-guards ,new-fn-name :hints ,hints))))
    event))

(define restrict-event
  ((old-fn-name symbolp "Result of @(tsee restrict-check-inputs).")
   (restriction$ pseudo-termp "Result of @(tsee restrict-check-inputs).")
   (undefined$ pseudo-termp "Result of @(tsee restrict-check-inputs).")
   (new-fn-name symbolp "Result of @(tsee restrict-check-inputs).")
   (new-fn-enable booleanp "Result of @(tsee restrict-check-inputs).")
   (old-to-new-thm-name symbolp "Result of @(tsee restrict-check-inputs).")
   (thm-enable booleanp "Input to the transformation, after validation.")
   (make-non-executable booleanp "Result of @(tsee restrict-check-inputs).")
   (do-verify-guards booleanp "Result of @(tsee restrict-check-inputs).")
   (hints-alist symbol-alistp "Result of @(tsee restrict-check-inputs).")
   (print$ booleanp "Result of @(tsee restrict-check-inputs).")
   (show-only booleanp "Input to the transformation, after validation.")
   (app-conds symbol-alistp "Result of @(tsee restrict-app-conds).")
   (call pseudo-event-formp "Call to the transformation.")
   (wrld plist-worldp))
  :returns (event "A @(tsee pseudo-event-formp).")
  :mode :program
  :short "Event form generated by the transformation."
  :long
  "<p>
   This is a @(tsee progn) that starts with
   a (trivial) @(tsee encapsulate) that includes the events for
   the applicability conditions,
   the new function,
   the theorem that relates the old and new functions,
   and the recording of the generated numbered name.
   The @(tsee encapsulate) is followed by events
   for the recording in the transformation table,
   and possibly for printing the transformation results on the screen.
   </p>
   <p>
   The @(tsee encapsulate) starts with some implicitly local event forms to
   ensure logic mode and
   avoid errors due to ignored or irrelevant formals in the generated function.
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
   of the old and new functions,
   because the generated proofs are based on the unnormalized bodies.
   </p>
   <p>
   As explained in @(tsee restrict-new-fn-intro-events)
   and @(tsee restrict-old-to-new-intro-events),
   the events for the new function
   and for the theorem that relates the old and new functions
   are introduced locally first, then redundantly non-locally
   (with slight variations).
   As explained in @(tsee restrict-new-fn-verify-guards-event),
   if the guards of the new function must be verified,
   the event to verify them is generated
   after the theorem that relates the old and new functions.
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
  (b* ((names-to-avoid (list new-fn-name old-to-new-thm-name))
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
       (names-to-avoid (rcons names-to-avoid old-fn-unnorm-name))
       ((mv new-fn-local-event
            new-fn-exported-event) (restrict-new-fn-intro-events
                                    old-fn-name
                                    restriction$
                                    undefined$
                                    new-fn-name
                                    new-fn-enable
                                    make-non-executable
                                    do-verify-guards
                                    wrld))
       ((mv new-fn-unnorm-event
            new-fn-unnorm-name) (install-not-norm-event new-fn-name
                                                        t
                                                        names-to-avoid
                                                        wrld))
       ((mv old-to-new-thm-local-event
            old-to-new-thm-exported-event) (restrict-old-to-new-intro-events
                                            old-fn-name
                                            restriction$
                                            new-fn-name
                                            old-to-new-thm-name
                                            thm-enable
                                            app-cond-thm-names
                                            old-fn-unnorm-name
                                            new-fn-unnorm-name
                                            wrld))
       (new-fn-verify-guards-event? (and do-verify-guards
                                         (list
                                          (restrict-new-fn-verify-guards-event
                                           old-fn-name
                                           new-fn-name
                                           old-to-new-thm-name
                                           app-cond-thm-names
                                           wrld))))
       (new-fn-numbered-name-event `(add-numbered-name-in-use ,new-fn-name))
       (encapsulate-events `((logic)
                             (set-ignore-ok t)
                             (set-irrelevant-formals-ok t)
                             ,@app-cond-thm-events
                             (set-default-hints nil)
                             (set-override-hints nil)
                             ,old-fn-unnorm-event
                             ,new-fn-local-event
                             ,new-fn-unnorm-event
                             ,old-to-new-thm-local-event
                             ,@new-fn-verify-guards-event?
                             ,new-fn-exported-event
                             ,old-to-new-thm-exported-event
                             ,new-fn-numbered-name-event))
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
                           (cw-event "~x0~|" ',old-to-new-thm-exported-event))
                       nil)))
    `(progn
       ,encapsulate+
       ,transformation-table-event
       ,@print-events
       (value-triple :invisible))))

(define restrict-fn
  ((old "Input to the transformation.")
   (restriction "Input to the transformation.")
   (undefined "Input to the transformation.")
   (new-name "Input to the transformation.")
   (new-enable "Input to the transformation.")
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
                  restriction$
                  undefined$
                  new-fn-name
                  new-fn-enable
                  old-to-new-thm-name
                  make-non-executable
                  do-verify-guards
                  hints-alist
                  print$)) (restrict-check-inputs old
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
       (app-conds (restrict-app-conds old-fn-name
                                      restriction$
                                      do-verify-guards
                                      state))
       ((er &) (ensure-named-formulas app-conds
                                      hints-alist
                                      (if (member-eq :expand print$) t nil)
                                      t nil ctx state))
       (event (restrict-event old-fn-name
                              restriction$
                              undefined$
                              new-fn-name
                              new-fn-enable
                              old-to-new-thm-name
                              thm-enable
                              make-non-executable
                              do-verify-guards
                              hints-alist
                              print$
                              show-only
                              app-conds
                              call
                              (w state))))
    (value event)))

(defsection restrict-implementation
  :parents (implementation restrict)
  :short "Implementation of the domain restriction transformation."
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
                                    state))))
