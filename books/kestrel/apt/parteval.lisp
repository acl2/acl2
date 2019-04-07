; APT Partial Evaluation Transformation -- Implementation
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "APT")

(include-book "kestrel/utilities/doublets" :dir :system)
(include-book "kestrel/utilities/error-checking/top" :dir :system)
(include-book "kestrel/utilities/event-macros/input-processing" :dir :system)
(include-book "kestrel/utilities/system/paired-names" :dir :system)
(include-book "kestrel/utilities/user-interface" :dir :system)
(include-book "kestrel/utilities/xdoc/defxdoc-plus" :dir :system)
(include-book "utilities/transformation-table")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ parteval-implementation
  :parents (implementation parteval)
  :short "Implementation of @(tsee parteval)."
  :long
  (xdoc::topstring
   (xdoc::p
    "The implementation functions have parameters
     consistently named as follows:")
   (xdoc::ul
    (xdoc::li
     "@('state') is the ACL2 @(see state).")
    (xdoc::li
     "@('wrld') is the ACL2 @(see world).")
    (xdoc::li
     "@('ctx') is the context used for errors.")
    (xdoc::li
     "@('old'),
      @('static'),
      @('new-name'),
      @('new-enable'),
      @('thm-name'),
      @('thm-enable'),
      @('verify-guards'),
      @('print'), and
      @('show-only')
      are the homonymous inputs to @(tsee parteval),
      before being processed.
      These parameters have no types because they may be any values.")
    (xdoc::li
     "@('old$'),
      @('static$'),
      @('new-name$'),
      @('new-enable$'),
      @('thm-name$'),
      @('thm-enable$'),
      @('verify-guards$'),
      @('print$'), and
      @('show-only$')
      are the results of processing
      the homonymous inputs (without the @('$')) to @(tsee parteval).
      Some are identical to the corresponding inputs,
      but they have types implied by their successful validation,
      performed when they are processed.")
    (xdoc::li
     "@('new-formals') are the formal parameters of the new function.")
    (xdoc::li
     "@('call') is the call to @(tsee restrict) supplied by the user."))
   (xdoc::p
    "The parameters of implementation functions that are not listed above
     are described in, or clear from, those functions' documentation."))
  :order-subtopics t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ parteval-input-processing
  :parents (parteval-implementation)
  :short "Input processing performed by @(tsee parteval)."
  :long
  (xdoc::topstring-p
   "This involves validating the inputs.
    When validation fails, <see topic='@(url er)'>soft errors</see> occur.
    Thus, generally the input processing functions return
    <see topic='@(url acl2::error-triple)'>error triples</see>.")
  :order-subtopics t
  :default-parent t)

(define parteval-process-old (old verify-guards ctx state)
  :returns (mv erp
               (old$ symbolp "The name of the target function
                              of the transformation,
                              denoted by the @('old') input.")
               state)
  :verify-guards nil
  :short "Process the @('old') input."
  (b* (((er old$) (ensure-function-name-or-numbered-wildcard$
                   old "The first input" t nil))
       (description (msg "The target function ~x0" old$))
       ((er &) (ensure-function-logic-mode$ old$ description t nil))
       ((er &) (ensure-function-defined$ old$ description t nil))
       ((er &) (ensure-function-number-of-results$ old$ 1
                                                   description t nil))
       ((er &) (ensure-function-no-stobjs$ old$ description t nil))
       ((er &) (if (eq verify-guards t)
                   (ensure-function-guard-verified$
                    old$
                    (msg "Since the :VERIFY-GUARDS input is T, ~
                          the target function ~x0" old$)
                    t nil)
                 (value :this-is-irrelevant))))
    (value old$)))

(define parteval-process-static-terms
  ((cj...cm true-listp "List @('(c1 ... cm)') initially,
                        then a tail of that in the recursive calls.")
   (yj...ym symbol-listp "List @('(y1 ... ym)') initially,
                          then a tail of that in the recursive calls.")
   (old$ symbolp)
   (verify-guards$ booleanp)
   ctx
   state)
  :guard (equal (len cj...cm) (len yj...ym))
  :mode :program
  :returns (mv erp
               (yj...ym$ "The @(tsee pseudo-term-listp) list
                          of terms @('cj...cm'), in translated form.")
               state)
  :short "Process the @('c1'), ..., @('cm') parts of the @('static') input."
  (b* (((when (endp cj...cm)) (value nil))
       (yj (car yj...ym))
       (cj (car cj...cm))
       (description
        (msg "The term ~x0 assigned to the static parameter ~x1" cj yj))
       ((er (list cj$ stobjs-out)) (ensure-term$ cj description t nil))
       ((er &) (ensure-term-ground$ cj$ description t nil))
       ((er &) (ensure-term-logic-mode$ cj$ description t nil))
       ((er &) (ensure-function/lambda/term-number-of-results$ stobjs-out 1
                                                               description
                                                               t nil))
       ((er &) (ensure-term-no-stobjs$ stobjs-out description t nil))
       ((er &) (if verify-guards$
                   (ensure-term-guard-verified-exec-fns$
                    cj$
                    (msg "Since either the :VERIFY-GUARDS input is T, ~
                          or it is (perhaps by default) :AUTO ~
                          and the target function ~x0 is guard-verified, ~@1"
                         old$ (msg-downcase-first description))
                    t nil)
                 (value :this-is-irrelevant)))
       ((er &) (ensure-term-does-not-call$ cj$ old$ description t nil))
       (cj+1...cm (cdr cj...cm))
       (yj+1...ym (cdr yj...ym))
       ((er cj+1...cm$) (parteval-process-static-terms
                         cj+1...cm yj+1...ym old$ verify-guards$ ctx state)))
    (value (cons cj$ cj+1...cm$))))

(define parteval-process-static (static
                                 (old$ symbolp)
                                 (verify-guards$ booleanp)
                                 ctx
                                 state)
  :returns (mv erp
               (static$ "A @(tsee symbol-alistp)
                       from @('y1'), ..., @('ym')
                       to the translated @('c1'), ..., @('cm').")
               state)
  :mode :program
  :short "Process the @('static') input."
  (b* (((er &) (ensure-doublet-list$ static "The second input" t nil))
       (alist (doublets-to-alist static))
       (y1...ym (strip-cars alist))
       (description
        (msg "The list ~x0 of static parameters" y1...ym))
       ((when (null y1...ym))
        (er-soft+ ctx t nil "~@0 must not be empty." description))
       ((er &) (ensure-list-no-duplicates$ y1...ym description t nil))
       ((er &) (ensure-symbol-list$ y1...ym description t nil))
       ((er &) (ensure-list-subset$ y1...ym (formals old$ (w state))
                                    description t nil))
       (c1...cm (strip-cdrs alist))
       ((er c1...cm$) (parteval-process-static-terms c1...cm y1...ym
                                                     old$ verify-guards$
                                                     ctx state))
       (static$ (pairlis$ y1...ym c1...cm$)))
    (value static$)))

(define parteval-process-new-name (new-name
                                   (old$ symbolp)
                                   ctx
                                   state)
  :returns (mv erp
               (new-name$ "A @(tsee symbolp)
                           to use as the name for the new function.")
               state)
  :mode :program
  :short "Process the @(':new-name') input."
  (b* (((er &) (ensure-symbol$ new-name "The :NEW-NAME input" t nil))
       (name (if (eq new-name :auto)
                 (next-numbered-name old$ (w state))
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

(define parteval-process-thm-name (thm-name
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

(define parteval-process-inputs (old
                                 static
                                 new-name
                                 new-enable
                                 thm-name
                                 thm-enable
                                 verify-guards
                                 print
                                 show-only
                                 ctx
                                 state)
  :returns (mv erp
               (result "A tuple @('(old$
                                    static$
                                    new-name$
                                    new-enable$
                                    thm-name$
                                    verify-guards$)')
                        satisfying
                        @('(typed-tuplep symbolp
                                         symbol-alistp
                                         symbolp
                                         booleanp
                                         symbolp
                                         booleanp
                                         result)'),
                        where @('old$') is
                        the result of @(tsee parteval-process-old),
                        @('static$') is
                        the result of @(tsee parteval-process-static),
                        @('new-name$') is
                        the result of @(tsee parteval-process-new-name),
                        @('new-enable$') indicates whether
                        the new function should be enabled or not,
                        @('thm-name$') is
                        the result of @(tsee parteval-process-thm-name), and
                        @('verify-guards$') indicates whether the guards of
                        the new function should be verified or not.")
               state)
  :mode :program
  :short "Process all the inputs."
  :long
  (xdoc::topstring-p
   "The inputs are processed
    in the order in which they appear in the documentation,
    except that @(':verify-guards') is processed just before @('static')
    because the result of processing @(':verify-guards')
    is used to process @('static').
    @('old') is processed before @(':verify-guards')
    because the result of processing @('old')
    is used to process @(':verify-guards').
    @(':verify-guards') is also used to process @('old'),
    but it is only tested for equality with @('t')
    (see @(tsee parteval-process-old)).")
  (b* ((wrld (w state))
       ((er old$) (parteval-process-old old verify-guards ctx state))
       ((er verify-guards$) (ensure-boolean-or-auto-and-return-boolean$
                             verify-guards
                             (guard-verified-p old$ wrld)
                             "The :VERIFY-GUARDS input" t nil))
       ((er static$) (parteval-process-static
                      static old$ verify-guards$ ctx state))
       ((er new-name$) (parteval-process-new-name
                        new-name old$ ctx state))
       ((er new-enable$) (ensure-boolean-or-auto-and-return-boolean$
                          new-enable
                          (fundef-enabledp old$ state)
                          "The :NEW-ENABLE input" t nil))
       ((er thm-name$) (parteval-process-thm-name
                        thm-name old$ new-name$ ctx state))
       ((er &) (ensure-boolean$ thm-enable "The :THM-ENABLE input" t nil))
       ((when (and (acl2::irecursivep old$ wrld)
                   new-enable$
                   thm-enable))
        (er-soft+ ctx t nil
                  "Since (i) the target function ~x0 is recursive, ~
                   (ii) either the :NEW-ENABLE input is T, ~
                   or it is (perhaps by default) :AUTO ~
                   and (iii) the target function is enabled, ~
                   the :THM-ENABLE input cannot be T."
                  old$))
       ((er &) (evmac-process-input-print print ctx state))
       ((er &) (evmac-process-input-show-only show-only ctx state)))
    (value (list old$
                 static$
                 new-name$
                 new-enable$
                 thm-name$
                 verify-guards$))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ parteval-event-generation
  :parents (parteval-implementation)
  :short "Event generation performed by @(tsee parteval)."
  :long
  (xdoc::topstring
   (xdoc::p
    "Some events are generated in two slightly different forms:
     a form that is local to the generated @(tsee encapsulate),
     and a form that is exported from the @(tsee encapsulate).
     Proof hints are in the former but not in the latter,
     thus keeping the ACL2 history ``clean''."))
  :order-subtopics t
  :default-parent t)

(define parteval-gen-new-fn ((old$ symbolp)
                             (static$ symbol-alistp)
                             (new-name$ symbolp)
                             (new-enable$ booleanp)
                             (verify-guards$ booleanp)
                             (wrld plist-worldp))
  :returns (mv (local-event "A @(tsee pseudo-event-formp).")
               (exported-event "A @(tsee pseudo-event-formp).")
               (new-formals "A @(tsee symbol-listp)."))
  :mode :program
  :short "Generate the new function definition."
  :long
  (xdoc::topstring
   (xdoc::p
    "The macro used to introduce the new function is determined by
     whether the new function must be enabled or not.")
   (xdoc::p
    "The parameters of the new function are
     the dynamic parameters of the old function,
     obtained by removing the static parameters from the old function.
     The parameters of the new function are returned as one of the results.")
   (xdoc::p
    "If the old function is not recursive,
     the body of the new function is obtained by replacing,
     in the body of the old function,
     the static parameters with the corresponding ground terms.
     Otherwise, if the old function is recursive,
     the body of the new function is obtained by replacing,
     in a generic call of the old function,
     the static parameters with the corresponding ground terms.")
   (xdoc::p
    "The guard of the new function is obtained similarly,
     from the guard of the old function.")
   (xdoc::p
    "If guards must be verified, the guard hints follow
     the design notes and the template in @('parteval-template.lisp').")
   (xdoc::p
    "Note that the new function is never recursive."))
  (b* ((macro (function-intro-macro new-enable$ nil))
       (old-formals (formals old$ wrld))
       (new-formals (set-difference-eq old-formals (strip-cars static$)))
       (old-call-or-body (if (acl2::irecursivep old$ wrld)
                             `(,old$ ,@old-formals)
                           (ubody old$ wrld)))
       (new-body (acl2::fsublis-var static$ old-call-or-body))
       (new-body (untranslate new-body nil wrld))
       (old-guard (uguard old$ wrld))
       (new-guard (acl2::fsublis-var static$ old-guard))
       (new-guard (untranslate new-guard nil wrld))
       (new-guard-hints `(("Goal"
                           :in-theory nil
                           :use (:instance
                                 (:guard-theorem ,old$)
                                 :extra-bindings-ok
                                 ,@(alist-to-doublets static$)))))
       (local-event
        `(local
          (,macro ,new-name$ (,@new-formals)
                  (declare (xargs :guard ,new-guard
                                  :verify-guards ,verify-guards$
                             ,@(and verify-guards$
                                    `(:guard-hints ,new-guard-hints))))
                  ,new-body)))
       (exported-event
        `(,macro ,new-name$ (,@new-formals)
                 (declare (xargs :guard ,new-guard
                                 :verify-guards ,verify-guards$))
                 ,new-body)))
    (mv local-event exported-event new-formals)))

(define parteval-gen-static-equalities ((static$ symbol-alistp))
  :returns (equalities "A @(tsee pseudo-term-listp).")
  :short "Generate the equalities whose conjunction forms
          the antecedent of the theorem relating old and new function."
  :long
  (xdoc::topstring-p
   "Each equality has the form @('(equal yj cj)').")
  (b* (((when (endp static$)) nil)
       ((cons arg$ static$) static$)
       (equality `(equal ,(car arg$) ,(cdr arg$)))
       (equalities (parteval-gen-static-equalities static$)))
    (cons equality equalities)))

(define parteval-gen-old-to-new-thm ((old$ symbolp)
                                     (static$ symbol-alistp)
                                     (new-name$ symbolp)
                                     (thm-name$ symbolp)
                                     (thm-enable$ booleanp)
                                     (new-formals symbol-listp)
                                     (wrld plist-worldp))
  :returns (mv (local-event "A @(tsee pseudo-event-formp).")
               (exported-event "A @(tsee pseudo-event-formp)."))
  :mode :program
  :short "Generate the theorem that relates the old and new function."
  :long
  (xdoc::topstring
   (xdoc::p
    "The macro used to introduce the theorem is determined by
     whether the theorem must be enabled or not.")
   (xdoc::p
    "The theorem is an implication,
     whose antecedent is @('(and (equal y1 c1) ... (equal ym cm))')
     and whose consequent is (using the notation in the documentation)
     @('(equal (old x1 ... xn y1 ... ym) (new x1 ... xn))').")
   (xdoc::p
    "The hints follow the proof
     in the design notes and in @('parteval-template.lisp').
     There is a slight difference between
     the case in which the old function is recursive
     and the case in which it is not:
     in the former case, only the definition of the new function is used;
     in the latter case, also the definitino of the old function is used."))
  (b* ((macro (theorem-intro-macro thm-enable$))
       (equalities (parteval-gen-static-equalities static$))
       (antecedent (conjoin equalities))
       (consequent `(equal (,old$ ,@(formals old$ wrld))
                           (,new-name$ ,@new-formals)))
       (formula (implicate antecedent consequent))
       (formula (untranslate formula t wrld))
       (used (if (acl2::irecursivep old$ wrld)
                 (list new-name$)
               (list new-name$ old$)))
       (hints `(("Goal" :in-theory nil :use ,used)))
       (local-event `(local (,macro ,thm-name$ ,formula :hints ,hints)))
       (exported-event `(,macro ,thm-name$ ,formula)))
    (mv local-event exported-event)))

(define parteval-gen-everything ((old$ symbolp)
                                 (static$ symbol-alistp)
                                 (new-name$ symbolp)
                                 (new-enable$ booleanp)
                                 (thm-name$ symbolp)
                                 (thm-enable$ booleanp)
                                 (verify-guards$ booleanp)
                                 (print$ evmac-input-print-p)
                                 (show-only$ booleanp)
                                 (call pseudo-event-formp)
                                 (wrld plist-worldp))
  :returns (event "A @(tsee pseudo-event-formp).")
  :mode :program
  :short "Generate the top-level event."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a @(tsee progn) that consists of
     the expansion of @(tsee parteval) (the @(tsee encapsulate)),
     followed by an event to extend the transformation table,
     optionally followed by events to print the exported events
     (if specified by the @(':print') input).
     The @(tsee progn) ends with @(':invisible')
     to avoid printing a return value.")
   (xdoc::p
    "The @(tsee encapsulate) starts with some implicitly local events to
     ensure logic mode and
     avoid errors due to ignored or irrelevant formals
     in the generated function.
     Other implicitly local events remove any default and override hints,
     to prevent such hints from sabotaging the generated proofs.")
   (xdoc::p
    "The @(tsee encapsulate) is stored into the transformation table,
     associated to the call to the transformation.
     Thus, the table event and (if present) the screen output events
     (which are in the @(tsee progn) but not in the @(tsee encapsulate))
     are not stored into the transformation table,
     because they carry no additional information,
     and because otherwise the table event would have to contain itself.")
   (xdoc::p
    "If @(':print') is @(':all'),
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
     the blank line is not printed.")
   (xdoc::p
    "If @(':show-only') is @('t'),
     the @(tsee encapsulate) is just printed on the screen
     and not returned as part of the event to submit,
     which in this case is just an @(':invisible') form.
     In this case, if @(':print') is @(':info') or @(':all'),
     a blank line is printed just before the @(tsee encapsulate),
     for visual separation."))
  (b* (((mv new-fn-local-event
            new-fn-exported-event
            new-formals) (parteval-gen-new-fn old$
                                              static$
                                              new-name$
                                              new-enable$
                                              verify-guards$
                                              wrld))
       ((mv old-to-new-thm-local-event
            old-to-new-thm-exported-event) (parteval-gen-old-to-new-thm
                                            old$
                                            static$
                                            new-name$
                                            thm-name$
                                            thm-enable$
                                            new-formals
                                            wrld))
       (new-fn-numbered-name-event `(add-numbered-name-in-use ,new-name$))
       (encapsulate-events `((logic)
                             (set-ignore-ok t)
                             (set-irrelevant-formals-ok t)
                             (set-default-hints nil)
                             (set-override-hints nil)
                             ,new-fn-local-event
                             ,old-to-new-thm-local-event
                             ,new-fn-exported-event
                             ,old-to-new-thm-exported-event
                             ,new-fn-numbered-name-event))
       (encapsulate `(encapsulate () ,@encapsulate-events))
       ((when show-only$)
        (if (member-eq print$ '(:info :all))
            (cw "~%~x0~|" encapsulate)
          (cw "~x0~|" encapsulate))
        '(value-triple :invisible))
       (encapsulate+ (restore-output? (eq print$ :all) encapsulate))
       (transformation-table-event (record-transformation-call-event
                                    call encapsulate wrld))
       (print-result (and
                      (member-eq print$ '(:result :info :all))
                      `(,@(and (member-eq print$ '(:info :all))
                               '((cw-event "~%")))
                        (cw-event "~x0~|" ',new-fn-exported-event)
                        (cw-event "~x0~|" ',old-to-new-thm-exported-event)))))
    `(progn
       ,encapsulate+
       ,transformation-table-event
       ,@print-result
       (value-triple :invisible))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define parteval-fn (old
                     static
                     new-name
                     new-enable
                     thm-name
                     thm-enable
                     verify-guards
                     print
                     show-only
                     (call pseudo-event-formp)
                     ctx
                     state)
  :returns (mv erp
               (event "A @(tsee pseudo-event-formp).")
               state)
  :mode :program
  :parents (parteval-implementation)
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
                  static$
                  new-name$
                  new-enable$
                  thm-name$
                  verify-guards$)) (parteval-process-inputs
                                    old
                                    static
                                    new-name
                                    new-enable
                                    thm-name
                                    thm-enable
                                    verify-guards
                                    print
                                    show-only
                                    ctx state))
       (event (parteval-gen-everything old$
                                       static$
                                       new-name$
                                       new-enable$
                                       thm-name$
                                       thm-enable
                                       verify-guards$
                                       print
                                       show-only
                                       call
                                       (w state))))
    (value event)))

(defsection parteval-macro-definition
  :parents (parteval-implementation)
  :short "Definition of the @(tsee parteval) macro."
  :long
  (xdoc::topstring
   (xdoc::p
    "Submit the event form generated by @(tsee parteval-fn).")
   (xdoc::@def "parteval"))
  (defmacro parteval (&whole
                      call
                      ;; mandatory inputs:
                      old
                      static
                      ;; optional inputs:
                      &key
                      (new-name ':auto)
                      (new-enable ':auto)
                      (thm-name ':auto)
                      (thm-enable 't)
                      (verify-guards ':auto)
                      (print ':result)
                      (show-only 'nil))
    `(make-event-terse (parteval-fn ',old
                                    ',static
                                    ',new-name
                                    ',new-enable
                                    ',thm-name
                                    ',thm-enable
                                    ',verify-guards
                                    ',print
                                    ',show-only
                                    ',call
                                    (cons 'parteval ',old)
                                    state)
                       :suppress-errors ,(not print))))
