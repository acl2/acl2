; Standard Utilities Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/error-checking/ensure-list-has-no-duplicates" :dir :system)
(include-book "kestrel/error-checking/ensure-value-is-boolean" :dir :system)
(include-book "kestrel/error-checking/ensure-value-is-not-in-list" :dir :system)
(include-book "kestrel/error-checking/ensure-value-is-symbol" :dir :system)
(include-book "kestrel/error-checking/ensure-value-is-symbol-list" :dir :system)
(include-book "kestrel/error-checking/ensure-value-is-untranslated-term" :dir :system)
(include-book "kestrel/event-macros/cw-event" :dir :system)
(include-book "kestrel/event-macros/make-event-terse" :dir :system)
(include-book "kestrel/event-macros/proof-preparation" :dir :system)
(include-book "kestrel/event-macros/restore-output" :dir :system)
(include-book "kestrel/std/system/fresh-logical-name-with-dollars-suffix" :dir :system)
(include-book "kestrel/std/system/pseudo-event-form-listp" :dir :system)
(include-book "kestrel/utilities/error-checking/top" :dir :system)
(include-book "kestrel/utilities/trans-eval-error-triple" :dir :system)
(include-book "std/util/defaggregate" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ defarbrec-implementation
  :parents (defarbrec)
  :short "Implementation of @(tsee defarbrec)."
  :long
  (xdoc::topstring
   (xdoc::p
    "The implementation functions have formal parameters
     consistently named as follows:")
   (xdoc::ul
    (xdoc::li
     "@('state') is the ACL2's @(see state).")
    (xdoc::li
     "@('wrld') is the ACL2's @(see world).")
    (xdoc::li
     "@('ctx') is the context used for errors.")
    (xdoc::li
     "@('fn'),
      @('x1...xn'),
      @('body'),
      @('update-names'),
      @('terminates-name'),
      @('measure-name'),
      @('nonterminating'),
      @('print'), and
      @('show-only')
      are the homonymous inputs to @(tsee defarbrec)
      (where @('x1...xn') is for the input @('(x1 ... xn)'))
      before being processed.
      These formal parameters have no types because they may be any values.")
    (xdoc::li
     "@('call') is the call of @(tsee defarbrec) supplied by the user.")
    (xdoc::li
     "@('call$') is the result of removing
      @(':print') and @(':show-only') from @('call').")
    (xdoc::li
     "@('fn$'),
      @('x1...xn$'),
      @('update-names$'),
      @('terminates-name$'),
      @('measure-name$'),
      @('nonterminating$'),
      @('print$'), and
      @('show-only$')
      are the results of processing
      the homonymous (without the @('$')) inputs to @(tsee defarbrec).
      Some are identical to the corresponding inputs,
      but they have types implied by their successful validation,
      performed when they are processed.")
    (xdoc::li
     "@('terminates-witness-name') is the name of the witness function
      generated along with the termination testing predicate,
      via @(tsee defun-sk).")
    (xdoc::li
     "@('terminated-rewrite-name') is the name of the rewrite rule
      generated along with the termination testing predicate,
      via @(tsee defun-sk).")
    (xdoc::li
     "@('xi...xn$') is a suffix of @('x1...xn$'),
      while @(tsee cdr)ing down the list in a recursion.")
    (xdoc::li
     "@('body$') is the unnormalized body that defines
      the program-mode function temporarily recorded in the @(see world).
      It is a translated term.")
    (xdoc::li
     "@('test') is the exit test of the program-mode function.")
    (xdoc::li
     "@('updates') is the list of
      argument updates in the recursive call of the program-mode function.")
    (xdoc::li
     "@('k') is a variable that counts the number of iterated argument udpates,
      used as a formal parameter of the iterated argument update functions,
      as a bound variable of the termination testing predicate,
      and as a formal parameter of the measure function.
      It is also used in generated local lemmas.")
    (xdoc::li
     "@('l') is another variable that counts
      the number of iterated argument udpates,
      used in generated local lemmas.")
    (xdoc::li
     "@('update-fns-lemma-name') is
      the name of the generated local lemma
      about the iterated argument update functions.")
    (xdoc::li
     "@('measure-fn-natp-lemma-name') is
      the name of the first generated local lemma
      about the generated measure function.")
    (xdoc::li
     "@('measure-fn-end-lemma-name') is
      the name of the second generated local lemma
      about the generated measure function.")
    (xdoc::li
     "@('measure-fn-min-lemma-name') is
      the name of the third generated local lemma
      about the generated measure function.")
    (xdoc::li
     "@('names-to-avoid') is a list of symbols already committed
      to use for some functions and theorems to be generated;
      symbols to use for additional functions and theorems to be generated
      must be therefore distinct from them.")
    (xdoc::li
     "@('expansion') is the @(tsee encapsulate)
      generated by @(tsee defarbrec)."))
   (xdoc::p
    "The parameters of implementation functions that are not listed above
    are described in, or clear from, those functions' documentation."))
  :order-subtopics t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ defarbrec-table
  :parents (defarbrec-implementation)
  :short "@(csee table) of @(tsee defarbrec) functions."
  :long
  (xdoc::topstring
   (xdoc::p
    "For each successful call of @(tsee defarbrec)
     whose @(':show-only') is not @('t'),
     this table includes a pair
     whose key is the name of the generated logic-mode function
     and whose value contains information about the call
     (see @(tsee defarbrec-infop)).")
   (xdoc::p
    "This table is used to support the redundancy check
     in @(tsee defarbrec-check-redundancy)."))
  :order-subtopics t
  :default-parent t)

(defval *defarbrec-table-name*
  'defarbrec-table
  :short "Name of the @(tsee defarbrec) table.")

(std::defaggregate defarbrec-info
  :short "Information about a @(tsee defarbrec) call,
          recorded as a pair's value in the @(tsee defarbrec) table."
  :long
  (xdoc::topstring
   (xdoc::p
    "The name of the generated recursive logic-mode function
     is the key of the pair in the table.")
   (xdoc::p
    "The call of @(tsee defarbrec) is stored
     without any @(':print') and @(':show-only') options
     because, as explained in the documentation,
     redundancy checking ignores those options."))
  ((call$ "The call of @(tsee defarbrec), after @(tsee defarbrec-filter-call)."
          pseudo-event-formp)
   (expansion "The @(tsee encapsulate) generated from
               the call of @(tsee defarbrec)."
              pseudo-event-formp)
   (x1...xn "Formal arguments of the function.")
   (body "Translated unnormalized body of the program-mode function.")
   (update-fns "The names of the generated iterated argument update functions."
               symbol-listp)
   (terminates-fn "The name of the generated termination testing predicate."
                  symbolp)
   (measure-fn "The name of the generated measure function."
               symbolp))
  :pred defarbrec-infop)

(make-event
 `(table ,*defarbrec-table-name* nil nil
    :guard (and (symbolp key) ; name of the recursive logic-mode function
                (defarbrec-infop val))))

(define defarbrec-filter-call ((call pseudo-event-formp))
  :guard (and (>= (len call) 4)
              (eq 'defarbrec (car call)))
  :returns (call$ "A @(tsee pseudo-event-formp).")
  :verify-guards nil
  :short "Remove any @(':print') and @(':show-only') options
          from a call of @(tsee defarbrec)."
  :long
  (xdoc::topstring-p
   "As explained in the documentation,
    these two options are ignored when checking redundancy.")
  (b* ((number-of-required-args 3)
       (number-of-elements-before-options (1+ number-of-required-args))
       (options (nthcdr number-of-elements-before-options call))
       (options (remove-keyword :print options))
       (options (remove-keyword :show-only options))
       (call$ (append (take number-of-elements-before-options call) options)))
    call$))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ defarbrec-input-processing
  :parents (defarbrec-implementation)
  :short "Input processing performed by @(tsee defarbrec)."
  :long
  (xdoc::topstring-p
   "This involves validating the inputs.
    When validation fails, "
   (xdoc::seetopic "er" "soft errors")
   " occur. Thus, generally the input processing functions return "
   (xdoc::seetopic "acl2::error-triple" "error triples")
   ".")
  :order-subtopics t
  :default-parent t)

(define defarbrec-process-fn (fn ctx state)
  :returns (mv erp (nothing null) state)
  :verify-guards nil
  :short "Process the @('fn') input."
  (b* ((description "The first input")
       ((er &) (ensure-value-is-symbol$ fn description t nil))
       ((er &) (ensure-symbol-new-event-name$ fn description t nil)))
    (value nil)))

(define defarbrec-process-x1...xn (x1...xn ctx state)
  :returns (mv erp (nothing null) state)
  :verify-guards nil
  :short "Process the @('(x1 ... xn)') input."
  (b* ((description "The second input")
       ((er &) (ensure-value-is-symbol-list$ x1...xn description t nil))
       ((er &) (ensure-list-has-no-duplicates$ x1...xn description t nil)))
    (value nil)))

(define defarbrec-process-body (body fn$ x1...xn$ ctx state)
  :returns (mv erp
               (result "A tuple @('(body$ test updates)')
                        satisfying
                        @('(typed-tuplep pseudo-termp
                                         pseudo-termp
                                         pseudo-term-listp
                                         result)').")
               state)
  :mode :program
  :short "Process the @('body') input."
  :long
  (xdoc::topstring
   (xdoc::p
    "We submit the program-mode function to ACL2,
     so that any errors in the body will be caught
     and will stop execution with an error.
     If the submission succeeds, the ACL2 state now includes the function,
     which we further validate and decompose.")
   (xdoc::p
    "If the function has the form
     assumed in the documentation of @(tsee defarbrec),
     the exit test is @('test<x1,...,xn>')
     and the updated arguments are
     @('update-x1<x1,...,xn>'), ..., @('update-xn<x1,...xn>').
     If the function has a different form,
     the exit test is the negation of the conjunction of
     the tests that control the recursive call.")
   (xdoc::p
    "Note that the @('wrld') variable is bound
     after calling @(tsee trans-eval-error-triple),
     to ensure that the program-mode function is in that world."))
  (b* ((program-mode-fn `(defun ,fn$ ,x1...xn$
                           (declare (xargs :mode :program))
                           ,body))
       ((er &) (trans-eval-error-triple program-mode-fn ctx state))
       (wrld (w state))
       (body$ (ubody fn$ wrld))
       (description (msg "The function ~x0" fn$))
       ((er &) (ensure-function-number-of-results$ fn$ 1 description t nil))
       ((er &) (ensure-function-no-stobjs$ fn$ description t nil))
       (rec-calls-with-tests (recursive-calls fn$ wrld))
       (num-rec-calls (len rec-calls-with-tests))
       ((when (/= num-rec-calls 1))
        (er-soft+ ctx t nil
                  "The function ~x0 must make exactly one recursive call, ~
                   but it makes ~x1 recursive calls instead."
                  fn$ num-rec-calls))
       (program-mode-fns (all-program-ffn-symbs body$ nil wrld))
       (program-mode-fns (remove-eq fn$ program-mode-fns))
       ((unless (null program-mode-fns))
        (er-soft+ ctx t nil
                  "The function ~x0 must call ~
                   only logic-mode functions besides itself, ~
                   but it also calls the program-mode ~@1 instead."
                  fn$
                  (if (= (len program-mode-fns) 1)
                      (msg "function ~x0" (car program-mode-fns))
                    (msg "functions ~&0" program-mode-fns))))
       (rec-call-with-tests (car rec-calls-with-tests))
       (tests (access tests-and-call rec-call-with-tests :tests))
       (rec-call (access tests-and-call rec-call-with-tests :call))
       (test (dumb-negate-lit (conjoin tests)))
       (updates (fargs rec-call)))
    (value (list body$ test updates))))

(define defarbrec-default-update-names ((x1...xn$ symbol-listp) (fn$ symbolp))
  :returns (names symbol-listp)
  :short "Default names of the iterated argument update functions."
  :long
  (xdoc::topstring-p
   "These are used when the @(':update-names') input is @('nil').
     They are as described in the documentation.")
  (defarbrec-default-update-names-aux x1...xn$ fn$)

  :prepwork
  ((define defarbrec-default-update-names-aux ((xi...xn$ symbol-listp)
                                               (fn$ symbolp))
     :returns (names symbol-listp)
     :parents nil ; avoid XDOC topic
     (if (endp xi...xn$)
         nil
       (cons (add-suffix-to-fn fn$
                               (str::cat "-" (symbol-name (car xi...xn$)) "*"))
             (defarbrec-default-update-names-aux (cdr xi...xn$) fn$))))))

(define defarbrec-process-update-names (update-names
                                        (fn$ symbolp)
                                        (x1...xn$ symbol-listp)
                                        ctx
                                        state)
  :returns (mv erp (update-names$ "A @(tsee symbol-listp).") state)
  :verify-guards nil
  :short "Process the @(':update-names') input."
  :long
  (xdoc::topstring-p
   "Return the names to use for the iterated argument update functions,
    in the same order as the function's formal arguments.")
  (b* (((er &) (ensure-value-is-symbol-list$ update-names
                                             "The :UPDATE-NAMES input"
                                             t nil))
       (symbols (or update-names (defarbrec-default-update-names x1...xn$ fn$)))
       ((er &) (ensure-list-has-no-duplicates$
                symbols
                "The list of symbols supplied as the :UPDATE-NAMES input"
                t nil))
       ((when (/= (len symbols) (len x1...xn$)))
        (er-soft+ ctx t nil
                  "The length of the list of symbols ~
                   supplied as the :UPDATE-NAME input ~
                   must be equal to the arity of the function ~x0."
                  fn$))
       ((er &) (defarbrec-process-update-names-aux
                 symbols fn$ x1...xn$ ctx state))
       ((er &) (ensure-value-is-not-in-list$
                fn$
                symbols
                (if (= 1 (len symbols))
                    (msg "the name ~x0 of ~
                          the iterated argument update function, ~
                          determined (perhaps by default) by ~
                          the :UPDATE-NAMES input"
                         (car symbols))
                  (msg "any of the names ~&0 of ~
                        the iterated argument update functions, ~
                        determined (perhaps by default) by ~
                        the :UPDATE-NAMES input"
                       symbols))
                (msg "The name ~x0 of the function to generate" fn$)
                t nil)))
    (value symbols))

  :prepwork
  ((define defarbrec-process-update-names-aux ((symbols symbol-listp)
                                               (fn$ symbolp)
                                               (xi...xn$ symbol-listp)
                                               ctx
                                               state)
     :returns (mv erp (nothing null) state)
     :verify-guards nil
     :parents nil ; avoid XDOC topic
     (b* (((when (endp symbols)) (value nil))
          (symbol (car symbols))
          ((er &) (ensure-symbol-new-event-name$
                   symbol
                   (msg "The name ~x0 of ~
                         the iterated argument update function for ~
                         the ~x1 argument of ~x2, ~
                         determined (perhaps by default) by ~
                         the :UPDATE-NAMES input,"
                        symbol (car xi...xn$) fn$)
                   t nil)))
       (defarbrec-process-update-names-aux (cdr symbols)
         fn$
         (cdr xi...xn$)
         ctx
         state)))))

(define defarbrec-process-terminates-name (terminates-name
                                           (fn$ symbolp)
                                           (update-names$ symbol-listp)
                                           ctx
                                           state)
  :returns (mv erp
               (result
                "A tuple
                 @('(terminates-name$
                     terminates-witness-name
                     terminates-rewrite-name)')
                 satisfying
                 @('(typed-tuplep symbolp symbolp symbolp result)').")
               state)
  :verify-guards nil
  :short "Process the @(':terminates-name') input."
  :long
  (xdoc::topstring
   (xdoc::p
    "Return the names to use for
     the termination testing predicate,
     the associated witness,
     and the associated rewrite rule.")
   (xdoc::p
    "Since the predicate is introduced via a @(tsee defun-sk),
     we must ensure that the associated witness name and rewrite rule name
     are also new and distinct from other names
     introduced by @(tsee defarbrec).")
   (xdoc::p
    "For now we use, for witness and rewrite rule,
     the same names that @(tsee defun-sk) would generate by default.
     But this might change in the future."))
  (b* (((er &) (ensure-value-is-symbol$
                terminates-name "The :TERMINATES-NAME input" t nil))
       (symbol (or terminates-name (add-suffix-to-fn fn$ "-TERMINATES")))
       (symbol-witness (add-suffix symbol "-WITNESS"))
       (symbol-rewrite (add-suffix symbol "-SUFF"))
       (symbol-description
        (msg "The name ~x0 of the termination testing predicate, ~
              determined (perhaps by default) by the :TERMINATES-NAME input,"
             symbol))
       (symbol-witness-description
        (msg "The name ~x0 of the witness function associated to ~
              the termination testing predicate, ~
              determined (perhaps by default) by the :TERMINATES-NAME input,"
             symbol-witness))
       (symbol-rewrite-description
        (msg "The name ~x0 of the rewrite rule associated to ~
              the termination testing predicate, ~
              determined (perhaps by default) by the :TERMINATES-NAME input,"
             symbol-rewrite))
       (fn-description
        (msg "the name ~x0 of the function to generate." fn$))
       (update-names$-description
        (if (= 1 (len update-names$))
            (msg "the name ~x0 of the iterated argument update function, ~
                  determined (perhaps by default) by the :UPDATE-NAMES input"
                 (car update-names$))
          (msg "the names ~&0 of the iterated argument update functions, ~
                determined (perhaps by default) by the :UPDATE-NAMES input"
               update-names$)))
       ((er &) (ensure-symbol-new-event-name$
                symbol symbol-description t nil))
       ((er &) (ensure-symbol-new-event-name$
                symbol-witness symbol-witness-description t nil))
       ((er &) (ensure-symbol-new-event-name$
                symbol-rewrite symbol-rewrite-description t nil))
       ((er &) (ensure-symbol-different$
                symbol fn$
                fn-description symbol-description
                t nil))
       ((er &) (ensure-symbol-different$
                symbol-witness fn$
                fn-description symbol-witness-description
                t nil))
       ((er &) (ensure-symbol-different$
                symbol-rewrite fn$
                fn-description symbol-rewrite-description
                t nil))
       ((er &) (ensure-value-is-not-in-list$
                symbol update-names$
                update-names$-description symbol-description
                t nil))
       ((er &) (ensure-value-is-not-in-list$
                symbol-witness update-names$
                update-names$-description symbol-witness-description
                t nil))
       ((er &) (ensure-value-is-not-in-list$
                symbol-rewrite update-names$
                update-names$-description symbol-rewrite-description
                t nil)))
    (value (list symbol symbol-witness symbol-rewrite))))

(define defarbrec-process-measure-name (measure-name
                                        (fn$ symbolp)
                                        (update-names$ symbol-listp)
                                        (terminates-name$ symbolp)
                                        (terminates-witness-name symbolp)
                                        (terminates-rewrite-name symbolp)
                                        ctx
                                        state)
  :returns (mv erp (measure-name$ "A @(tsee symbolp).") state)
  :verify-guards nil
  :short "Process the @(':measure-name') input."
  :long
  (xdoc::topstring-p
   "Return the name to use for the measure function.")
  (b* (((er &) (ensure-value-is-symbol$ measure-name
                                        "The :MEASURE-NAME input" t nil))
       (symbol (or measure-name (add-suffix-to-fn fn$ "-MEASURE")))
       (description (msg "The name ~x0 of the measure function, ~
                          determined (perhaps by default) by ~
                          the :MEASURE-NAME input,"
                         symbol))
       ((er &) (ensure-symbol-new-event-name$ symbol description t nil))
       ((er &) (ensure-symbol-different$
                symbol
                fn$
                (msg "the name ~x0 of the function to generate" fn$)
                description
                t nil))
       ((er &) (ensure-value-is-not-in-list$
                symbol
                update-names$
                (if (= 1 (len update-names$))
                    (msg "the name ~x0 of ~
                          the iterated argument update function, ~
                          determined (perhaps by default) by ~
                          the :UPDATE-NAMES input"
                         (car update-names$))
                  (msg "the name ~&0 of ~
                        the iterated argument update functions, ~
                        determined (perhaps by default) by ~
                        the :UPDATE-NAMES input"
                       update-names$))
                description
                t nil))
       ((er &) (ensure-symbol-different$
                symbol
                terminates-name$
                (msg "the name ~x0 of the termination testing predicate, ~
                      determined (perhaps by default) by ~
                      the :TERMINATES-NAME input"
                     terminates-name$)
                description
                t nil))
       ((er &) (ensure-symbol-different$
                symbol
                terminates-witness-name
                (msg "the name ~x0 of the witness function associated to ~
                      the termination testing predicate, ~
                      determined (perhaps by default) by ~
                      the :TERMINATES-NAME input"
                     terminates-witness-name)
                description
                t nil))
       ((er &) (ensure-symbol-different$
                symbol
                terminates-rewrite-name
                (msg "the name ~x0 of the rewrite rule associated to ~
                      the termination testing predicate, ~
                      determined (perhaps by default) by ~
                      the :TERMINATES-NAME input"
                     terminates-rewrite-name)
                description
                t nil)))
    (value symbol)))

(define defarbrec-process-nonterminating (nonterminating
                                          (x1...xn$ symbol-listp)
                                          ctx
                                          state)
  :returns (mv erp (nonterminating$ "A @(tsee pseudo-termp).") state)
  :mode :program
  :short "Process the @(':nonterminating') input."
  :long
  (xdoc::topstring
   (xdoc::p
    "Return the translated form of the term.")
   (xdoc::p
    "Note that the check that the term calls only logic-mode functions
     ensures that the term does not call the program-mode function @('fn')."))
  (b* (((er (list term stobjs-out))
        (ensure-value-is-untranslated-term$ nonterminating
                                            "The :NONTERMINATING input"
                                            t nil))
       (description (msg "The term ~x0 supplied as the :NONTERMINATING input"
                         nonterminating))
       ((er &) (ensure-term-free-vars-subset$ term x1...xn$ description t nil))
       ((er &) (ensure-term-logic-mode$ term description t nil))
       ((er &) (ensure-function/lambda/term-number-of-results$ stobjs-out 1
                                                               description
                                                               t nil))
       ((er &) (ensure-term-no-stobjs$ stobjs-out description t nil)))
    (value term)))

(std::defenum defarbrec-printp (nil :error :result :all)
  :short "Recognize the allowed values of the @(':print') input.")

(define defarbrec-process-print (print ctx state)
  :returns (mv erp (nothing null) state)
  :short "Process the @(':print') input."
  (if (defarbrec-printp print)
      (value nil)
    (er-soft+ ctx t nil
              "The :PRINT input must be NIL, :ERROR, :RESULT, or :ALL.")))

(define defarbrec-process-show-only (show-only ctx state)
  :returns (mv erp (nothing "Always @('nil').") state)
  :short "Process the @(':show-only') input."
  (ensure-value-is-boolean$ show-only "The :SHOW-ONLY input" t nil))

(define defarbrec-process-inputs (fn
                                  x1...xn
                                  body
                                  update-names
                                  terminates-name
                                  measure-name
                                  nonterminating
                                  print
                                  show-only
                                  ctx
                                  state)
  :returns (mv erp
               (result "A tuple @('(body$
                                    test
                                    updates
                                    update-names$
                                    terminates-name$
                                    terminates-witness-name
                                    terminates-rewrite-name
                                    measure-name$
                                    nonterminating$)')
                        satisfying
                        @('(typed-tuplep pseudo-termp
                                         pseudo-termp
                                         pseudo-term-listp
                                         symbol-listp
                                         symbolp
                                         symbolp
                                         symbolp
                                         symbolp
                                         pseudo-termp
                                         result)').")
               state)
  :mode :program
  :short "Process all the inputs."
  :long
  (xdoc::topstring-p
   "If validation is successful,
     return the results from the input validation functions called.")
  (b* (((er &) (defarbrec-process-fn fn ctx state))
       ((er &) (defarbrec-process-x1...xn x1...xn ctx state))
       ((er (list body$
                  test
                  updates)) (defarbrec-process-body body fn x1...xn ctx state))
       ((er update-names$) (defarbrec-process-update-names
                             update-names
                             fn
                             x1...xn
                             ctx
                             state))
       ((er (list terminates-name$
                  terminates-witness-name
                  terminates-rewrite-name))
        (defarbrec-process-terminates-name
          terminates-name
          fn
          update-names$
          ctx
          state))
       ((er measure-name$) (defarbrec-process-measure-name
                             measure-name
                             fn
                             update-names$
                             terminates-name$
                             terminates-witness-name
                             terminates-rewrite-name
                             ctx
                             state))
       ((er nonterminating$) (defarbrec-process-nonterminating
                               nonterminating
                               x1...xn
                               ctx
                               state))
       ((er &) (defarbrec-process-print print ctx state))
       ((er &) (defarbrec-process-show-only show-only ctx state)))
    (value (list body$
                 test
                 updates
                 update-names$
                 terminates-name$
                 terminates-witness-name
                 terminates-rewrite-name
                 measure-name$
                 nonterminating$))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ defarbrec-event-generation
  :parents (defarbrec-implementation)
  :short "Event generation performed by @(tsee defarbrec)."
  :long
  (xdoc::topstring
   (xdoc::p
    "Some events are generated in two slightly different forms:
     a form that is local to the generated @(tsee encapsulate),
     and a form that is exported from the @(tsee encapsulate).
     Proof hints are in the former but not in the latter,
     thus keeping the ACL2 history ``clean''.")
   (xdoc::p
    "Other events are generated only locally in the @(tsee encapsulate),
     without any exported counterparts.
     These have automatically generated fresh names:
     the names used so far
     are threaded through the event generation functions below.")
   (xdoc::p
    "Other events are only exported from the @(tsee encapsulate),
     without any local counterparts.")
   (xdoc::p
    "The generated events, and particularly the proofs hints,
     follow the template in the file @('defarbrec-template.lisp'),
     which is referred to as `template'
     in the documentation of the event generation functions below."))
  :order-subtopics t
  :default-parent t)

(define defarbrec-gen-var-k ((fn$ symbolp)
                             (x1...xn$ symbol-listp))
  :returns (k "A @(tsee symbolp).")
  :mode :program
  :short "Generate the variable @('k') that counts
          the iterated updates of the arguments."
  :long
  (xdoc::topstring-p
   "This is used as
    a formal parameter of the iterated argument update functions,
    the bound variable in the termination testing predicate,
    and a formal parameter of the measure function.
    This variable must be distinct from the formal parameters of @('fn').")
  (genvar fn$ "K" nil x1...xn$))

(define defarbrec-gen-var-l ((fn$ symbolp)
                             (x1...xn$ symbol-listp)
                             (k symbolp))
  :returns (l "A @(tsee symbolp).")
  :mode :program
  :short "Generate the variable @('l') that counts
          the iterated updates of the arguments."
  :long
  (xdoc::topstring-p
   "This is used in one of the generated local lemmas
    about the measure function.
    This variable must be distinct from the formal parameters of @('fn')
    as well as from the variable @('k').")
  (genvar fn$ "L" nil (cons k x1...xn$)))

(define defarbrec-gen-test-of-updates-term ((x1...xn$ symbol-listp)
                                            (test pseudo-termp)
                                            (update-names$ symbol-listp)
                                            (iterations pseudo-termp))
  :returns (terms "A @(tsee pseudo-termp).")
  :verify-guards nil
  :short "Generate the instantiation of the exit test of @('fn')
          with calls to the iterated argument update functions."
  :long
  (xdoc::topstring-p
   "This is the term
    @('test<(update*-x1 iterations x1 ... xn),
            ...,
            (update*-xn iterations x1 ... xn)>'),
    where the @('iterations') term is passed as argument to this function.")
  (subcor-var x1...xn$
              (apply-terms-same-args update-names$ (cons iterations x1...xn$))
              test))

(define defarbrec-gen-update-fns ((x1...xn$ symbol-listp)
                                  (updates pseudo-term-listp)
                                  (update-names$ symbol-listp)
                                  (k symbolp)
                                  (wrld plist-worldp))
  :guard (equal (len updates) (len update-names$))
  :returns (mv (local-events "A @(tsee pseudo-event-form-listp).")
               (exported-events "A @(tsee pseudo-event-form-listp)."))
  :mode :program
  :short "Generate the iterated argument update function definitions."
  :long
  (xdoc::topstring-p
   "These are the functions @('update*-x1'), ..., @('update*-xn')
    in the documentation.
    They correspond to the function @('d*') in the template,
    where @('f') has just one argument.")
  (defarbrec-gen-update-fns-aux x1...xn$ updates update-names$ k 0 wrld)

  :prepwork
  ((define defarbrec-gen-update-fns-aux ((x1...xn$ symbol-listp)
                                         (updates pseudo-term-listp)
                                         (update-names$ symbol-listp)
                                         (k symbolp)
                                         (i (integer-range-p
                                             0 (len update-names$) i))
                                         (wrld plist-worldp))
     :guard (equal (len updates) (len update-names$))
     :returns (mv local-events ; PSEUDO-EVENT-FORM-LISTP
                  exported-events) ; PSEUDO-EVENT-FORM-LISTP
     :parents nil ; avoid separate XDOC topic
     :mode :program
     (b* ((i (mbe :logic (nfix i) :exec i))
          ((when (>= i (len update-names$))) (mv nil nil))
          (name (nth i update-names$))
          (xi (nth i x1...xn$))
          (formals `(,k ,@x1...xn$))
          (updates (untranslate-lst updates nil wrld))
          (body `(if (zp ,k)
                     ,xi
                   (,name (1- ,k) ,@updates)))
          (measure `(acl2-count ,k))
          (hints '(("Goal" :in-theory nil)))
          (local-event
           `(local
             (defun ,name ,formals
               (declare (xargs :measure ,measure
                               :well-founded-relation o<
                               :hints ,hints))
               ,body)))
          (exported-event
           `(defun ,name ,formals
              (declare (xargs :measure ,measure
                              :well-founded-relation o<))
              ,body))
          ((mv local-events exported-events)
           (defarbrec-gen-update-fns-aux
             x1...xn$ updates update-names$ k (1+ i) wrld)))
       (mv (cons local-event local-events)
           (cons exported-event exported-events)))
     :measure (nfix (- (len update-names$) (nfix i))))))

(define defarbrec-gen-update-fns-lemma ((fn$ symbolp)
                                        (x1...xn$ symbol-listp)
                                        (test pseudo-termp)
                                        (update-names$ symbol-listp)
                                        (k symbolp)
                                        (names-to-avoid symbol-listp)
                                        (wrld plist-worldp))
  :returns (mv (event "A @(tsee pseudo-event-formp).")
               (name "A @(tsee symbolp) that is the name of the lemma."))
  :mode :program
  :short "Generate the local lemma
          about the iterated argument udpate functions."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to the theorem @('d*-lemma') in the template.
     Its formula has the following form in general:")
   (xdoc::codeblock
    "(implies (and test<(update*-x1 k x1 ... xn),...,(update*-xn k x1 ... xn)>"
    "              (not (natp k)))"
    "         test<(update*-x1 0 x1 ... xn),...,(update*-xn 0 x1 ... xn)>)"))
  (b* ((name (add-suffix fn$ "-UPDATE*-LEMMA"))
       ((mv name &)
        (fresh-logical-name-with-$s-suffix name nil names-to-avoid wrld))
       (test-of-updates-k (defarbrec-gen-test-of-updates-term
                            x1...xn$ test update-names$ k))
       (test-of-updates-0 (defarbrec-gen-test-of-updates-term
                            x1...xn$ test update-names$ '0))
       (formula `(implies (and ,test-of-updates-k
                               (not (natp ,k)))
                          ,test-of-updates-0))
       (formula (untranslate formula t wrld))
       (event
        `(local
          (defthm ,name
            ,formula
            :hints (("Goal" :in-theory '(,@update-names$ natp zp)))
            :rule-classes nil))))
    (mv event name)))

(define defarbrec-gen-terminates-fn ((x1...xn$ symbol-listp)
                                     (test pseudo-termp)
                                     (update-names$ symbol-listp)
                                     (terminates-name$ symbolp)
                                     (terminates-witness-name$ symbolp)
                                     (terminates-rewrite-name$ symbolp)
                                     (k symbolp)
                                     (wrld plist-worldp))
  :returns (event "A @(tsee pseudo-event-formp).")
  :mode :program
  :short "Generate the termination testing predicate definition."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the predicate @('terminates') in the documentation.
     It corresponds to the function @('tt') in the template.")
   (xdoc::p
    "The names of the witness and rewrite rule
     calculated by @(tsee defarbrec-process-terminates-name)
     are the same as the @(tsee defun-sk) default ones.
     But by setting them explicitly,
     we make them easier to change in the future.")
   (xdoc::p
    "We set @(':quant-ok') to @('t'), in case."))
  (b* ((test-of-updates-k (defarbrec-gen-test-of-updates-term
                            x1...xn$ test update-names$ k))
       (test-of-updates-k (untranslate test-of-updates-k nil wrld)))
    `(defun-sk ,terminates-name$ ,x1...xn$
       (exists ,k ,test-of-updates-k)
       :skolem-name ,terminates-witness-name$
       :thm-name ,terminates-rewrite-name$
       :quant-ok t)))

(define defarbrec-gen-measure-fn ((x1...xn$ symbol-listp)
                                  (test pseudo-termp)
                                  (update-names$ symbol-listp)
                                  (terminates-witness-name$ symbolp)
                                  (measure-name$ symbolp)
                                  (k symbolp)
                                  (wrld plist-worldp))
  :returns (mv (local-event "A @(tsee pseudo-event-formp).")
               (exported-event "A @(tsee pseudo-event-formp)."))
  :mode :program
  :short "Generate the measure function definition."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the function @('measure') in the documentation.
     It corresponds to the function @('nu') in the template.")
   (xdoc::p
    "We do not generate a function corresponding to @('mu') in the template.
     We directly use the equivalent of @('(nu x 0)')
     for the measure of the logic-mode @('fn')
     (see @(tsee defarbrec-gen-fn-fn))."))
  (b* ((test-of-updates-k (defarbrec-gen-test-of-updates-term
                            x1...xn$ test update-names$ k))
       (test-of-updates-k (untranslate test-of-updates-k nil wrld))
       (formals `(,@x1...xn$ ,k))
       (body `(let ((,k (nfix ,k)))
                (if (or ,test-of-updates-k
                        (>= ,k (nfix (,terminates-witness-name$ ,@x1...xn$))))
                    ,k
                  (,measure-name$ ,@x1...xn$ (1+ ,k)))))
       (measure `(nfix (- (,terminates-witness-name$ ,@x1...xn$) (nfix ,k))))
       (hints '(("Goal" :in-theory '(o-p o-finp o< nfix natp))))
       (local-event
        `(local
          (defun ,measure-name$ ,formals
            (declare (xargs :measure ,measure
                            :well-founded-relation o<
                            :hints ,hints))
            ,body)))
       (exported-event
        `(defun ,measure-name$ ,formals
           (declare (xargs :measure ,measure
                           :well-founded-relation o<))
           ,body)))
    (mv local-event exported-event)))

(define defarbrec-gen-measure-fn-natp-lemma ((x1...xn$ symbol-listp)
                                             (measure-name$ symbolp)
                                             (k symbolp)
                                             (names-to-avoid symbol-listp)
                                             (wrld plist-worldp))
  :returns (mv (event "A @(tsee pseudo-event-formp).")
               (name "A @(tsee symbolp) that is the name of the lemma."))
  :mode :program
  :short "Generate the local lemma about the generated measure function
          that asserts that the measure function returns a natural number."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to the theorem @('nu-natp') in the template.
     Its formula has the following form in general:")
   (xdoc::codeblock
    "(natp (measure x1 ... xn k))")
   (xdoc::p
    "We generate this theorem without rule classes
     (instead of a rewrite rule as in the template)
     because we do not generate a function corresponding to @('mu') here
     and we use this theorem only with @(':use') hints."))
  (b* ((name (add-suffix measure-name$ "-NATP"))
       ((mv name &)
        (fresh-logical-name-with-$s-suffix name nil names-to-avoid wrld))
       (event
        `(local
          (defthm ,name
            (natp (,measure-name$ ,@x1...xn$ ,k))
            :hints (("Goal"
                     :in-theory
                     '((:type-prescription ,measure-name$)
                       (:compound-recognizer natp-compound-recognizer))))
            :rule-classes nil))))
    (mv event name)))

(define defarbrec-gen-measure-fn-end-lemma ((x1...xn$ symbol-listp)
                                            (test pseudo-termp)
                                            (update-names$ symbol-listp)
                                            (terminates-name$ symbolp)
                                            (terminates-witness-name$ symbolp)
                                            (measure-name$ symbolp)
                                            (k symbolp)
                                            (update-fns-lemma-name symbolp)
                                            (names-to-avoid symbol-listp)
                                            (wrld plist-worldp))
  :returns (mv (event "A @(tsee pseudo-event-formp).")
               (name "A @(tsee symbolp) that is the name of the lemma."))
  :mode :program
  :short "Generate the local lemma about the generated measure function
          that asserts that
          iterating the argument updates on terminating arguments
          for the number indicated by the generated measure function
          yields values satisfying the exit test."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to the theorem @('nu-end') in the template.
     Its formula has the following form in general:")
   (xdoc::codeblock
    "(implies (and (terminates x1 ... xn)"
    "              (natp k)"
    "              (<= k (nfix (terminates-witness x1 ... xn))))"
    "         test<(update*-x1 (measure x1 ... xn k) x1 ... xn),"
    "              ...,"
    "              (update*-xn (measure x1 ... xn k) x1 ... xn)>)")
   (xdoc::p
    "We generate this theorem without rule classes
     (instead of a rewrite rule as in the template)
     because we do not generate a function corresponding to @('mu') here
     and we use this theorem only with @(':use') hints."))
  (b* ((name (add-suffix measure-name$ "-END"))
       ((mv name &)
        (fresh-logical-name-with-$s-suffix name nil names-to-avoid wrld))
       (iterations (apply-term measure-name$ `(,@x1...xn$ ,k)))
       (test-of-updates-measure (defarbrec-gen-test-of-updates-term
                                  x1...xn$ test update-names$ iterations))
       (test-of-updates-measure (untranslate test-of-updates-measure nil wrld))
       (event
        `(local
          (defthm ,name
            (implies (and (,terminates-name$ ,@x1...xn$)
                          (natp ,k)
                          (<= ,k (nfix (,terminates-witness-name$ ,@x1...xn$))))
                     ,test-of-updates-measure)
            :hints (("Goal"
                     :in-theory '(,measure-name$ ,terminates-name$ natp nfix)
                     :induct (,measure-name$ ,@x1...xn$ ,k))
                    '(:use (:instance ,update-fns-lemma-name
                            (,k (,terminates-witness-name$ ,@x1...xn$)))))
            :rule-classes nil))))
    (mv event name)))

(define defarbrec-gen-measure-fn-min-lemma ((x1...xn$ symbol-listp)
                                            (test pseudo-termp)
                                            (update-names$ symbol-listp)
                                            (measure-name$ symbolp)
                                            (k symbolp)
                                            (l symbolp)
                                            (names-to-avoid symbol-listp)
                                            (wrld plist-worldp))
  :returns (mv (event "A @(tsee pseudo-event-formp).")
               (name "A @(tsee symbolp) that is the name of the lemma."))
  :mode :program
  :short "Generate the local lemma about the generated measure function
          that asserts that the value of the measure function is
          the minimum number of iterations of the argument update functions
          that turn terminating arguments into values satisfying the exit test."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to the theorem @('nu-min') in the template.
     Its formula has the following form in general:")
   (xdoc::codeblock
    "(implies (and (natp l)"
    "              (natp k)"
    "              (>= l k)"
    "              test<(update*-x1 l x1 ... xn),"
    "                   ...,"
    "                   (update*-xn l x1 ... xn)>)"
    "         (>= l (measure x1 ... xn k)))")
   (xdoc::p
    "We generate this theorem without rule classes
     (instead of a rewrite rule as in the template)
     because we do not generate a function corresponding to @('mu') here
     and we use this theorem only with @(':use') hints."))
  (b* ((name (add-suffix measure-name$ "-MIN"))
       ((mv name &)
        (fresh-logical-name-with-$s-suffix name nil names-to-avoid wrld))
       (test-of-updates-l (defarbrec-gen-test-of-updates-term
                            x1...xn$ test update-names$ l))
       (test-of-updates-l (untranslate test-of-updates-l nil wrld))
       (event
        `(local
          (defthm ,name
            (implies (and (natp ,l)
                          (natp ,k)
                          (>= ,l ,k)
                          ,test-of-updates-l)
                     (>= l (,measure-name$ ,@x1...xn$ ,k)))
            :hints (("Goal"
                     :in-theory '(,measure-name$ natp nfix)
                     :induct (,measure-name$ ,@x1...xn$ ,k)))
            :rule-classes nil))))
    (mv event name)))

(define defarbrec-gen-fn-fn ((fn$ symbolp)
                             (x1...xn$ symbol-listp)
                             (body$ pseudo-termp)
                             (updates pseudo-term-listp)
                             (update-names$ symbol-listp)
                             (terminates-name$ symbolp)
                             (measure-name$ symbolp)
                             (nonterminating$ pseudo-termp)
                             (k symbolp)
                             (l symbolp)
                             (measure-fn-natp-lemma-name symbolp)
                             (measure-fn-end-lemma-name symbolp)
                             (measure-fn-min-lemma-name symbolp)
                             (wrld plist-worldp))
  :returns (mv (local-event "A @(tsee pseudo-event-formp).")
               (exported-event "A @(tsee pseudo-event-formp)."))
  :mode :program
  :short "Generate the definition of the @('lfn') function."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is as described in the documentation.
     We wrap the body of the program-mode function
     into a check with the termination testing predicate.")
   (xdoc::p
    "This corresponds to the function @('f^') in the template,
     but we directly use @('measure'), which corresponds to @('nu').
     The termination proof hints are adapted accordingly,
     by instantiating the argument @('k') of @('measure') with @('0')
     and by including @(tsee nfix) in the theory
     (since it is included in the theories that prove
     @('mu-end') and @('mu-min') in the template)."))
  (b* ((measure `(,measure-name$ ,@x1...xn$ 0))
       (doublets (alist-to-doublets (pairlis$ x1...xn$ updates)))
       (hints `(("Goal"
                 :in-theory '(o-p o-finp natp o< zp nfix ,@update-names$)
                 :use ((:instance ,measure-fn-natp-lemma-name
                        (,k 0))
                       (:instance ,measure-fn-natp-lemma-name
                        ,@doublets
                        (,k 0))
                       (:instance ,measure-fn-end-lemma-name
                        (,k 0))
                       (:instance ,measure-fn-min-lemma-name
                        (,l (1- (,measure-name$ ,@x1...xn$ 0)))
                        ,@doublets
                        (,k 0))))))
       (body `(if (,terminates-name$ ,@x1...xn$)
                  ,body$
                ,nonterminating$))
       (body (untranslate body nil wrld))
       (local-event
        `(local
          (defun ,fn$ ,x1...xn$
            (declare (xargs :measure ,measure
                            :well-founded-relation o<
                            :hints ,hints))
            ,body)))
       (exported-event
        `(defun ,fn$ ,x1...xn$
           (declare (xargs :measure ,measure
                           :well-founded-relation o<))
           ,body)))
    (mv local-event exported-event)))

(define defarbrec-gen-extend-table ((fn$ symbolp)
                                    (x1...xn$ symbol-listp)
                                    (body$ pseudo-termp)
                                    (update-names$ symbol-listp)
                                    (terminates-name$ symbolp)
                                    (measure-name$ symbolp)
                                    (call$ pseudo-event-formp)
                                    (expansion pseudo-event-formp))
  :returns (event pseudo-event-formp)
  :short "Generate the event that extends the @(tsee defarbrec) table."
  (b* ((info (make-defarbrec-info
              :call$ call$
              :expansion expansion
              :x1...xn x1...xn$
              :body body$
              :update-fns update-names$
              :terminates-fn terminates-name$
              :measure-fn measure-name$)))
    `(table ,*defarbrec-table-name* ',fn$ ',info)))

(define defarbrec-gen-print-result ((events pseudo-event-form-listp))
  :returns (cw-events pseudo-event-form-listp)
  :short "Generate the events that print the results."
  :long
  (xdoc::topstring-p
   "This is used when @(':print') is @(':result') or @(':all').")
  (if (endp events)
      nil
    (cons `(cw-event "~x0~|" ',(car events))
          (defarbrec-gen-print-result (cdr events)))))

(define defarbrec-gen-everything ((fn$ symbolp)
                                  (x1...xn$ symbol-listp)
                                  (body$ pseudo-termp)
                                  (test pseudo-termp)
                                  (updates pseudo-term-listp)
                                  (update-names$ symbol-listp)
                                  (terminates-name$ symbolp)
                                  (terminates-witness-name$ symbolp)
                                  (terminates-rewrite-name$ symbolp)
                                  (measure-name$ symbolp)
                                  (nonterminating$ pseudo-termp)
                                  (print$ defarbrec-printp)
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
     the expansion of @(tsee defarbrec) (the @(tsee encapsulate)),
     followed by an event to extend the @(tsee defarbrec) table,
     optionally followed by events to print the exported functions
     (if specified by the @(':print') input).
     The @(tsee progn) ends with @(':invisible')
     to avoid printing a return value.")
   (xdoc::p
    "The expansion starts with some implicitly local events to
     ensure logic mode,
     avoid errors due to ignored or irrelevant formals
     in the generated functions,
     and prevent default and override hints from sabotaging the generated proofs.
     Then all the local and exported function and lemma events are introduced.
     The @('names-to-avoid') variable is
     initialized with the names of the exported events
     and extended as local names are generated.")
   (xdoc::p
    "If the @(':print') input is @(':all'),
     the expansion is wrapped to show ACL2's output
     in response to the submitted events.
     In this case, a blank line is printed before printing the result,
     for visual separation.")
   (xdoc::p
    "If @(':show-only') is @('t'),
     the expansion is printed on the screen
     and not returned as part of the event to submit,
     which is in this case is just an @(':invisible') form."))
  (b* ((names-to-avoid `(,fn$
                         ,@update-names$
                         terminates-name$
                         terminates-witness-name$
                         terminates-rewrite-name$
                         measure-name$))
       (k (defarbrec-gen-var-k fn$ x1...xn$))
       (l (defarbrec-gen-var-l fn$ x1...xn$ k))
       ((mv local-update-fns
            exported-update-fns) (defarbrec-gen-update-fns
                                   x1...xn$
                                   updates
                                   update-names$
                                   k
                                   wrld))
       ((mv update-fns-lemma
            update-fns-lemma-name) (defarbrec-gen-update-fns-lemma
                                     fn$
                                     x1...xn$
                                     test
                                     update-names$
                                     k
                                     names-to-avoid
                                     wrld))
       (names-to-avoid (cons update-fns-lemma-name names-to-avoid))
       (terminates-fn (defarbrec-gen-terminates-fn
                        x1...xn$
                        test
                        update-names$
                        terminates-name$
                        terminates-witness-name$
                        terminates-rewrite-name$
                        k
                        wrld))
       ((mv local-measure-fn
            exported-measure-fn) (defarbrec-gen-measure-fn
                                   x1...xn$
                                   test
                                   update-names$
                                   terminates-witness-name$
                                   measure-name$
                                   k
                                   wrld))
       ((mv measure-fn-natp-lemma
            measure-fn-natp-lemma-name) (defarbrec-gen-measure-fn-natp-lemma
                                          x1...xn$
                                          measure-name$
                                          k
                                          names-to-avoid
                                          wrld))
       (names-to-avoid (cons measure-fn-natp-lemma-name names-to-avoid))
       ((mv measure-fn-end-lemma
            measure-fn-end-lemma-name) (defarbrec-gen-measure-fn-end-lemma
                                         x1...xn$
                                         test
                                         update-names$
                                         terminates-name$
                                         terminates-witness-name$
                                         measure-name$
                                         k
                                         update-fns-lemma-name
                                         names-to-avoid
                                         wrld))
       (names-to-avoid (cons measure-fn-end-lemma-name names-to-avoid))
       ((mv measure-fn-min-lemma
            measure-fn-min-lemma-name) (defarbrec-gen-measure-fn-min-lemma
                                         x1...xn$
                                         test
                                         update-names$
                                         measure-name$
                                         k
                                         l
                                         names-to-avoid
                                         wrld))
       ((mv local-fn-fn
            exported-fn-fn) (defarbrec-gen-fn-fn
                              fn$
                              x1...xn$
                              body$
                              updates
                              update-names$
                              terminates-name$
                              measure-name$
                              nonterminating$
                              k
                              l
                              measure-fn-natp-lemma-name
                              measure-fn-end-lemma-name
                              measure-fn-min-lemma-name
                              wrld))
       (expansion `(encapsulate
                     ()
                     (logic)
                     (set-ignore-ok t)
                     (set-irrelevant-formals-ok t)
                     (evmac-prepare-proofs)
                     ,@local-update-fns
                     ,@exported-update-fns
                     ,update-fns-lemma
                     ,terminates-fn
                     ,local-measure-fn
                     ,exported-measure-fn
                     ,measure-fn-natp-lemma
                     ,measure-fn-end-lemma
                     ,measure-fn-min-lemma
                     ,local-fn-fn
                     ,exported-fn-fn))
       ((when show-only$)
        (cw "~x0~|" expansion)
        '(value-triple :invisible))
       (expansion-output-p (if (eq print$ :all) t nil))
       (expansion+ (restore-output? expansion-output-p expansion))
       (call$ (defarbrec-filter-call call))
       (extend-table (defarbrec-gen-extend-table
                       fn$
                       x1...xn$
                       body$
                       update-names$
                       terminates-name$
                       measure-name$
                       call$
                       expansion))
       (print-result (and (member-eq print$ '(:result :all))
                          (append
                           (and expansion-output-p '((cw-event "~%")))
                           (defarbrec-gen-print-result
                             `(,@exported-update-fns
                               ,terminates-fn
                               ,exported-measure-fn
                               ,exported-fn-fn))))))
    `(progn
       ,expansion+
       ,extend-table
       ,@print-result
       (value-triple :invisible))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defarbrec-check-redundancy (fn
                                    print
                                    show-only
                                    (call pseudo-event-formp)
                                    ctx
                                    state)
  :returns (mv erp (yes/no "A @(tsee booleanp).") state)
  :verify-guards nil
  :parents (defarbrec-implementation)
  :short "Check if a call of @(tsee defarbrec) is redundant."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the @(tsee defarbrec) table has no entry for @('fn'),
     we return @('nil'); the call is not redundant.")
   (xdoc::p
    "If the table has an entry for @('fn') but the call differs,
     an error occurs.")
   (xdoc::p
    "If the call is redundant,
     we know that all the inputs except possibly @(':print') and @(':show-only')
     are valid
     (because they are the same as the ones of the recorded successful call);
     we validate these two inputs, for better error checking.
     If @(':show-only') is @('t'),
     we print the recorded expansion of the call.
     Unless @(':print') is @('nil'),
     we print a message saying that the call is redundant."))
  (b* ((table (table-alist *defarbrec-table-name* (w state)))
       (pair (assoc-equal fn table))
       ((unless pair) (value nil))
       (info (cdr pair))
       (call$ (defarbrec-filter-call call))
       ((unless (equal call$ (defarbrec-info->call$ info)))
        (er-soft+ ctx t nil
                  "The function ~x0 has already been defined ~
                   by a different call of DEFARBREC."
                  fn))
       ((er &) (defarbrec-process-print print ctx state))
       ((er &) (defarbrec-process-show-only show-only ctx state))
       ((run-when show-only)
        (cw "~x0~|" (defarbrec-info->expansion info)))
       ((run-when print)
        (cw "~%The call ~x0 is redundant.~%" call)))
    (value t)))

(define defarbrec-fn (fn
                      x1...xn
                      body
                      update-names
                      terminates-name
                      measure-name
                      nonterminating
                      print
                      show-only
                      (call pseudo-event-formp)
                      ctx
                      state)
  :returns (mv erp (event "A @(tsee pseudo-event-formp).") state)
  :mode :program
  :parents (defarbrec-implementation)
  :short "Check redundancy,
          process the inputs,
          and generate the event to submit."
  (b* (((er redundant?) (defarbrec-check-redundancy
                          fn print show-only call ctx state))
       ((when redundant?) (value '(value-triple :invisible)))
       ((er (list body$
                  test
                  updates
                  update-names$
                  terminates-name$
                  teminates-witness-name$
                  terminates-rewrite-name$
                  measure-name$
                  nonterminating$))
        (defarbrec-process-inputs
          fn
          x1...xn
          body
          update-names
          terminates-name
          measure-name
          nonterminating
          print
          show-only
          ctx
          state))
       (event (defarbrec-gen-everything
                fn
                x1...xn
                body$
                test
                updates
                update-names$
                terminates-name$
                teminates-witness-name$
                terminates-rewrite-name$
                measure-name$
                nonterminating$
                print
                show-only
                call
                (w state))))
    (value event)))

(defsection defarbrec-macro-definition
  :parents (defarbrec-implementation)
  :short "Definition of the @(tsee defarbrec) macro."
  :long
  (xdoc::topstring
   (xdoc::p
    "Submit the event form generated by @(tsee defarbrec-fn).")
   (xdoc::@def "defarbrec"))
  (defmacro defarbrec (&whole
                       call
                       ;; mandatory inputs:
                       fn
                       x1...xn
                       body
                       ;; optional inputs:
                       &key
                       update-names
                       terminates-name
                       measure-name
                       (nonterminating ':nonterminating)
                       (print ':result)
                       show-only)
    `(make-event-terse (defarbrec-fn
                         ',fn
                         ',x1...xn
                         ',body
                         ',update-names
                         ',terminates-name
                         ',measure-name
                         ',nonterminating
                         ',print
                         ',show-only
                         ',call
                         (cons 'defarbrec ',fn)
                         state)
                       :suppress-errors ,(not print))))
