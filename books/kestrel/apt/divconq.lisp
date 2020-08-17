; APT (Automated Program Transformations) Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "APT")

(include-book "kestrel/error-checking/ensure-value-is-in-list" :dir :system)
(include-book "kestrel/error-checking/ensure-value-is-legal-variable-name" :dir :system)
(include-book "kestrel/error-checking/ensure-value-is-not-in-list" :dir :system)
(include-book "kestrel/error-checking/ensure-value-is-symbol" :dir :system)
(include-book "kestrel/event-macros/input-processing" :dir :system)
(include-book "kestrel/event-macros/proof-preparation" :dir :system)
(include-book "kestrel/event-macros/xdoc-constructors" :dir :system)
(include-book "kestrel/soft/implementation" :dir :system)
(include-book "kestrel/std/system/defun-sk-queries" :dir :system)
(include-book "kestrel/std/system/fresh-logical-name-with-dollars-suffix" :dir :system)
(include-book "kestrel/utilities/error-checking/top" :dir :system)
(include-book "kestrel/utilities/typed-tuples" :dir :system)

(include-book "utilities/input-processing")
(include-book "utilities/transformation-table")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-implementation

 divconq

 :items

 (xdoc::*evmac-topic-implementation-item-state*

  xdoc::*evmac-topic-implementation-item-wrld*

  xdoc::*evmac-topic-implementation-item-ctx*

  "@('old') is the homonymous input to @(tsee divconq) when it has no type;
   otherwise, it is the function symbol denoted by that input."

  "@('schema') is the homonymous input to @(tsee divconq)."

  "@('list-input') is the homonymous input to @(tsee divconq)."

  "@('fvar-atom-name') is the homonymous input to @(tsee divconq)."

  "@('fvar-cons-name') is the homonymous input to @(tsee divconq)."

  "@('fold-name') is the homonymous input to @(tsee divconq)."

  "@('fold-enable') is the homonymous input to @(tsee divconq)."

  "@('spec-atom-name') is the homonymous input to @(tsee divconq)."

  "@('spec-atom-enable') is the homonymous input to @(tsee divconq)."

  "@('spec-cons-name') is the homonymous input to @(tsee divconq)."

  "@('spec-cons-enable') is the homonymous input to @(tsee divconq)."

  "@('equal-fold-name') is the homonymous input to @(tsee divconq)."

  "@('equal-fold-enable') is the homonymous input to @(tsee divconq)."

  "@('cdr-output') is the homonymous input to @(tsee divconq)
   when it has no type;
   otherwise, it is the variable symbol @('y')
   described in the user documentation."

  "@('new-name') is the homonymous input to @(tsee divconq)."

  "@('new-enable') is the homonymous input to @(tsee divconq)
   if it has no type;
   otherwise, it is the boolean resulting from processing that input."

  "@('old-if-new-name') is the homonymous input to @(tsee divconq)."

  "@('old-if-new-enable') is the homonymous input to @(tsee divconq)
   if it has no type;
   otherwise, it is the boolean resulting from processing that input."

  "@('verify-guards') is the homonymous input to @(tsee divconq)
   if it has no type;
   otherwise, it is the boolean resulting from processing that input."

  "@('print') is the homonymous input to @(tsee divconq)."

  "@('show-only') is the homonymous input to @(tsee divconq)."

  "@('inputs') is the list of variable symbols @('(x0 x1 ... xn)')
   described in the user documentation."

  "@('x0') is the homonymous variable symbol
   described in the user documentation."

  "@('iorel') is the homonymous function symbol
   described in the user documentation."

  "@('?f') is the function variable that @('old') depends on,
   as described in the user documentation."

  "@('?g') is the homonymous function symbol
   described in the user documentation."

  "@('?h') is the homonymous function symbol
   described in the user documentation."

  "@('fold') is the function symbol @('fold[?g][?h]')
   described in the user documentation."

  "@('spec-atom') is the function symbol @('spec-atom[?g]')
   described in the user documentation."

  "@('spec-cons') is the function symbol @('spec-cons[?g]')
   described in the user documentation."

  "@('equal-fold') is the function symbol @('equal[?f][fold[?g][?h]]')
   described in the user documentation."

  "@('new') is the homonymous function symbol
   described in the user documentation."

  "@('old-if-new') is the homonymous theorem symbol
   described in the user documentation."))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-input-processing divconq)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define divconq-process-old (old verify-guards ctx state)
  :returns (mv erp
               (result "A tuple @('(old ?f inputs iorel) satisfying
                        @('(typed-tuplep symbolp
                                         symbolp
                                         symbol-listp
                                         symbolp
                                         result)').")
               state)
  :mode :program
  :short "Process the @('old') input."
  (b* ((wrld (w state))
       ((er old) (ensure-function-name-or-numbered-wildcard$
                  old "The first input" t nil))
       ((when (and (eq verify-guards t)
                   (not (guard-verified-p old wrld))))
        (er-soft+ ctx t nil
                  "Since the :VERIFY-GUARDS input is T, ~
                   the target function ~x0 must be guard-verified, ~
                   but it is not."
                  old))
       ((unless (soft::quant-sofunp old wrld))
        (er-soft+ ctx t nil
                  "The target function ~x0 ~
                   must be a SOFT quantifier function."
                  old))
       (funvars (soft::sofun-funvars old wrld))
       ((unless (= (len funvars) 1))
        (er-soft+ ctx t nil
                  "The target function ~x0 ~
                   must depend on exactly one function variable, ~
                   but instead it depends on ~x1."
                  old funvars))
       (??f (car funvars))
       ((when (consp (formals old wrld)))
        (er-soft+ ctx t nil
                  "The target function ~x0 ~
                   must have no parameters, but instead it has parameters ~x1."
                  old (formals old wrld)))
       ((unless (eq (defun-sk-quantifier old wrld) 'acl2::forall))
        (er-soft+ ctx t nil
                  "The quantifier of the target function ~x0 ~
                   must be universal, but it is existential instead."
                  old))
       (inputs (defun-sk-bound-vars old wrld))
       (matrix (defun-sk-matrix old wrld))
       ((when (variablep matrix))
        (er-soft+ ctx t nil
                  "The matrix of the target function ~x0 ~
                   must be a function call, ~
                   but it is the variable ~x1 instead."
                  old matrix))
       ((when (fquotep matrix))
        (er-soft+ ctx t nil
                  "The matrix of the target function ~x0 ~
                   must be a function call, ~
                   but it is the quoted constant ~x1 instead."
                  old matrix))
       (iorel (ffn-symb matrix))
       ((unless (symbolp iorel))
        (er-soft+ ctx t nil
                  "The matrix of the target function ~x0 ~
                   must be a call of a function symbol, ~
                   but instead it is a call of a lambda expression ~x1."
                  old iorel))
       (args (fargs matrix))
       (required-args (append inputs (list (fcons-term ?f inputs))))
       ((unless (equal args required-args))
        (er-soft+ ctx t nil
                  "The arguments of the matrix of the target function ~x0 ~
                   must be ~x1, but they are ~x2 instead."
                  old required-args args)))
    (value (list old ?f inputs iorel))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define divconq-process-schema (schema ctx state)
  :returns (mv erp (nothing null) state)
  :short "Process the @(':schema') input."
  (if (eq schema :list-fold)
      (value nil)
    (er-soft+ ctx t nil
              "The :SCHEMA input must be :LIST-FOLD, ~
               but it is ~x0 instead. ~
               More schemas will be supported in the future."
              schema)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define divconq-process-list-input (list-input
                                    (old symbolp)
                                    (inputs symbol-listp)
                                    ctx
                                    state)
  :returns (mv erp
               (x0 symbolp
                   :hyp (symbol-listp inputs)
                   :hints (("Goal"
                            :in-theory
                            (enable acl2::ensure-value-is-in-list))))
               state)
  :short "Process the @(':list-input') input."
  (b* (((when (eq list-input :auto))
        (value (car inputs)))
       ((er &) (ensure-value-is-in-list$
                list-input
                inputs
                (msg "one of bonund variables ~x0 of ~x1" inputs old)
                "The :LIST-INPUT input"
                t nil)))
    (value list-input)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define divconq-process-fvar-atom-name (fvar-atom-name
                                        (?f symbolp)
                                        (names-to-avoid symbol-listp)
                                        ctx
                                        state)
  :returns (mv erp
               (result "A tuple @('(?g updated-names-to-avoid)')
                        satisfying @('(typed-tuplep symbolp
                                                    symbol-listp
                                                    result)').")
               state)
  :mode :program
  :short "Process the @(':fvar-atom-name') input."
  (b* ((wrld (w state))
       ((er &) (ensure-value-is-symbol$ fvar-atom-name
                                        "The :FVAR-ATOM-NAME input"
                                        t nil))
       (??g (if (eq fvar-atom-name :auto)
                (add-suffix ?f "-ATOM")
              fvar-atom-name))
       (msg/nil (fresh-namep-msg-weak ?g 'function wrld))
       ((when msg/nil)
        (er-soft+ ctx t nil
                  "The name ~x0 specified by :FVAR-ATOM-NAME ~
                   is already in use.  ~@1"
                  ?g msg/nil))
       ((when (member-eq ?g names-to-avoid))
        (er-soft+ ctx t nil
                  "The name ~x0 specified by :FVAR-ATOM-NAME ~
                   must be distinct form the names ~&1 ~
                   that are also being generated."
                  ?g names-to-avoid)))
    (value (list ?g names-to-avoid))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define divconq-process-fvar-cons-name (fvar-cons-name
                                        (?f symbolp)
                                        (names-to-avoid symbol-listp)
                                        ctx
                                        state)
  :returns (mv erp
               (result "A tuple @('(?h updated-names-to-avoid)')
                        satisfying @('(typed-tuplep symbolp
                                                    symbol-listp
                                                    result)').")
               state)
  :mode :program
  :short "Process the @(':fvar-cons-name') input."
  (b* ((wrld (w state))
       ((er &) (ensure-value-is-symbol$ fvar-cons-name
                                        "The :FVAR-CONS-NAME input"
                                        t nil))
       (??h (if (eq fvar-cons-name :auto)
                (add-suffix ?f "-CONS")
              fvar-cons-name))
       (msg/nil (fresh-namep-msg-weak ?h 'function wrld))
       ((when msg/nil)
        (er-soft+ ctx t nil
                  "The name ~x0 specified by :FVAR-CONS-NAME ~
                   is already in use.  ~@1"
                  ?h msg/nil))
       ((when (member-eq ?h names-to-avoid))
        (er-soft+ ctx t nil
                  "The name ~x0 specified by :FVAR-CONS-NAME ~
                   must be distinct form the names ~&1 ~
                   that are also being generated."
                  ?h names-to-avoid)))
    (value (list ?h names-to-avoid))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define divconq-process-fold-name (fold-name
                                   (old symbolp)
                                   (?g symbolp)
                                   (?h symbolp)
                                   (names-to-avoid symbol-listp)
                                   ctx
                                   state)
  :returns (mv erp
               (result "A tuple @('(fold updated-names-to-avoid)')
                        satisfying @('(typed-tuplep symbolp
                                                    symbol-listp
                                                    result)').")
               state)
  :mode :program
  :short "Process the @(':fold-name') input."
  (b* ((wrld (w state))
       ((er &) (ensure-value-is-symbol$ fold-name
                                        "The :FOLD-NAME input"
                                        t nil))
       (fold (if (eq fold-name :auto)
                 (packn-pos (list "FOLD[" ?g "][" ?h "]") old)
               fold-name))
       (msg/nil (fresh-namep-msg-weak fold 'function wrld))
       ((when msg/nil)
        (er-soft+ ctx t nil
                  "The name ~x0 specified by :FOLD-NAME ~
                   is already in use.  ~@1"
                  fold msg/nil))
       ((when (member-eq fold names-to-avoid))
        (er-soft+ ctx t nil
                  "The name ~x0 specified by :FOLD-NAME ~
                   must be distinct form the names ~&1 ~
                   that are also being generated."
                  fold names-to-avoid)))
    (value (list fold names-to-avoid))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define divconq-process-spec-atom-name (spec-atom-name
                                        (old symbolp)
                                        (?g symbolp)
                                        (names-to-avoid symbol-listp)
                                        ctx
                                        state)
  :returns (mv erp
               (result "A tuple @('(spec-atom updated-names-to-avoid)')
                        satisfying @('(typed-tuplep symbolp
                                                    symbol-listp
                                                    result)').")
               state)
  :mode :program
  :short "Process the @(':spec-atom-name') input."
  (b* ((wrld (w state))
       ((er &) (ensure-value-is-symbol$ spec-atom-name
                                        "The :SPEC-ATOM-NAME input"
                                        t nil))
       (spec-atom (if (eq spec-atom-name :auto)
                      (packn-pos (list "SPEC-ATOM[" ?g "]") old)
                    spec-atom-name))
       (msg/nil (fresh-namep-msg-weak spec-atom 'function wrld))
       ((when msg/nil)
        (er-soft+ ctx t nil
                  "The name ~x0 specified by :SPEC-ATOM-NAME ~
                   is already in use.  ~@1"
                  spec-atom msg/nil))
       ((when (member-eq spec-atom names-to-avoid))
        (er-soft+ ctx t nil
                  "The name ~x0 specified by :SPEC-ATOM-NAME ~
                   must be distinct form the names ~&1 ~
                   that are also being generated."
                  spec-atom names-to-avoid)))
    (value (list spec-atom names-to-avoid))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define divconq-process-spec-cons-name (spec-cons-name
                                        (old symbolp)
                                        (?h symbolp)
                                        (names-to-avoid symbol-listp)
                                        ctx
                                        state)
  :returns (mv erp
               (result "A tuple @('(spec-cons updated-names-to-avoid)')
                        satisfying @('(typed-tuplep symbolp
                                                    symbol-listp
                                                    result)').")
               state)
  :mode :program
  :short "Process the @(':spec-cons-name') input."
  (b* ((wrld (w state))
       ((er &) (ensure-value-is-symbol$ spec-cons-name
                                        "The :SPEC-CONS-NAME input"
                                        t nil))
       (spec-cons (if (eq spec-cons-name :auto)
                      (packn-pos (list "SPEC-CONS[" ?h "]") old)
                    spec-cons-name))
       (msg/nil (fresh-namep-msg-weak spec-cons 'function wrld))
       ((when msg/nil)
        (er-soft+ ctx t nil
                  "The name ~x0 specified by :SPEC-CONS-NAME ~
                   is already in use.  ~@1"
                  spec-cons msg/nil))
       ((when (member-eq spec-cons names-to-avoid))
        (er-soft+ ctx t nil
                  "The name ~x0 specified by :SPEC-CONS-NAME ~
                   must be distinct form the names ~&1 ~
                   that are also being generated."
                  spec-cons names-to-avoid)))
    (value (list spec-cons names-to-avoid))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define divconq-process-equal-fold-name (equal-fold-name
                                         (old symbolp)
                                         (?f symbolp)
                                         (fold symbolp)
                                         (names-to-avoid symbol-listp)
                                         ctx
                                         state)
  :returns (mv erp
               (result "A tuple @('(equal-fold updated-names-to-avoid)')
                        satisfying @('(typed-tuplep symbolp
                                                    symbol-listp
                                                    result)').")
               state)
  :mode :program
  :short "Process the @(':equal-fold-name') input."
  (b* ((wrld (w state))
       ((er &) (ensure-value-is-symbol$ equal-fold-name
                                        "The :EQUAL-FOLD-NAME input"
                                        t nil))
       (equal-fold (if (eq equal-fold-name :auto)
                       (packn-pos (list "EQUAL[" ?f "][" fold "]") old)
                     equal-fold-name))
       (msg/nil (fresh-namep-msg-weak equal-fold 'function wrld))
       ((when msg/nil)
        (er-soft+ ctx t nil
                  "The name ~x0 specified by :EQUAL-FOLD-NAME ~
                   is already in use.  ~@1"
                  equal-fold msg/nil))
       ((when (member-eq equal-fold names-to-avoid))
        (er-soft+ ctx t nil
                  "The name ~x0 specified by :EQUAL-FOLD-NAME ~
                   must be distinct form the names ~&1 ~
                   that are also being generated."
                  equal-fold names-to-avoid)))
    (value (list equal-fold names-to-avoid))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define divconq-process-cdr-output (cdr-output
                                    (old symbolp)
                                    (inputs symbol-listp)
                                    ctx
                                    state)
  :returns (mv erp
               (cdr-output$ symbolp
                            :hyp (symbol-listp inputs)
                            :hints (("Goal"
                                     :in-theory
                                     (enable
                                      acl2::ensure-value-is-legal-variable-name
                                      acl2::ensure-value-is-not-in-list))))
               state)
  :short "Process the @(':cdr-output') input."
  (b* ((cdr-output (if (eq cdr-output :auto)
                       (intern-in-package-of-symbol "CDR-OUTPUT" old)
                     cdr-output))
       ((er &) (ensure-value-is-legal-variable-name$ cdr-output
                                                     "The :CDR-OUTPUT input"
                                                     t nil))
       ((er &) (ensure-value-is-not-in-list$
                cdr-output
                inputs
                (msg "one of bonund variables ~x0 of ~x1" inputs old)
                "The :CDR-OUTPUT input"
                t nil)))
    (value cdr-output)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define divconq-process-inputs (old
                                schema
                                fvar-atom-name
                                fvar-cons-name
                                fold-name
                                fold-enable
                                spec-atom-name
                                spec-atom-enable
                                spec-cons-name
                                spec-cons-enable
                                equal-fold-name
                                equal-fold-enable
                                list-input
                                cdr-output
                                new-name
                                new-enable
                                old-if-new-name
                                (old-if-new-name-present booleanp)
                                old-if-new-enable
                                (old-if-new-enable-present booleanp)
                                verify-guards
                                print
                                show-only
                                ctx
                                state)
  :returns (mv erp
               (result "A tuple @('(old$
                                    inputs
                                    x0
                                    iorel
                                    ?f
                                    ?g
                                    ?h
                                    fold
                                    spec-atom
                                    spec-cons
                                    equal-fold
                                    cdr-output
                                    new
                                    new-enable$
                                    old-if-new
                                    old-if-new-enable$
                                    verify-guards$
                                    names-to-avoid)')
                        satisfying
                        @('(typed-tuplep symbolp
                                         symbol-listp
                                         symbolp
                                         symbolp
                                         symbolp
                                         symbolp
                                         symbolp
                                         symbolp
                                         symbolp
                                         symbolp
                                         symbolp
                                         symbolp
                                         symbolp
                                         booleanp
                                         symbolp
                                         booleanp
                                         booleanp
                                         symbol-listp
                                         result)').")
               state)
  :mode :program
  :short "Process all the inputs."
  (b* ((wrld (w state))
       (names-to-avoid nil)
       ((er (list old ??f inputs iorel)) (divconq-process-old old
                                                              verify-guards
                                                              ctx
                                                              state))
       ((er &) (divconq-process-schema schema ctx state))
       ((er x0) (divconq-process-list-input list-input
                                            old
                                            inputs
                                            ctx
                                            state))
       ((er (list ??g names-to-avoid)) (divconq-process-fvar-atom-name
                                        fvar-atom-name
                                        ?f
                                        names-to-avoid
                                        ctx
                                        state))
       ((er (list ??h names-to-avoid)) (divconq-process-fvar-cons-name
                                        fvar-cons-name
                                        ?f
                                        names-to-avoid
                                        ctx
                                        state))
       ((er (list fold names-to-avoid)) (divconq-process-fold-name
                                         fold-name
                                         old
                                         ?g
                                         ?h
                                         names-to-avoid
                                         ctx
                                         state))
       ((er &) (ensure-value-is-boolean$ fold-enable
                                         "The :FOLD-ENABLE input"
                                         t
                                         nil))
       ((er (list spec-atom names-to-avoid)) (divconq-process-spec-atom-name
                                              spec-atom-name
                                              old
                                              ?g
                                              names-to-avoid
                                              ctx
                                              state))
       ((er &) (ensure-value-is-boolean$ spec-atom-enable
                                         "The :SPEC-ATOM-ENABLE input"
                                         t
                                         nil))
       ((er (list spec-cons names-to-avoid)) (divconq-process-spec-cons-name
                                              spec-cons-name
                                              old
                                              ?h
                                              names-to-avoid
                                              ctx
                                              state))
       ((er &) (ensure-value-is-boolean$ spec-cons-enable
                                         "The :SPEC-CONS-ENABLE input"
                                         t
                                         nil))
       ((er (list equal-fold names-to-avoid)) (divconq-process-equal-fold-name
                                               equal-fold-name
                                               old
                                               ?f
                                               fold
                                               names-to-avoid
                                               ctx
                                               state))
       ((er &) (ensure-value-is-boolean$ equal-fold-enable
                                         "The :EQUAL-FOLD-ENABLE input"
                                         t
                                         nil))
       ((er cdr-output) (divconq-process-cdr-output cdr-output
                                                    old
                                                    inputs
                                                    ctx
                                                    state))
       ((er (list new names-to-avoid)) (process-input-new-name new-name
                                                               old
                                                               names-to-avoid
                                                               ctx
                                                               state))
       ((er new-enable) (ensure-boolean-or-auto-and-return-boolean$
                         new-enable
                         (fundef-enabledp old state)
                         "The :NEW-ENABLE input" t nil))
       ((er (list old-if-new names-to-avoid)) (process-old-if-new-name
                                               old-if-new-name
                                               old-if-new-name-present
                                               old
                                               new
                                               names-to-avoid
                                               ctx
                                               state))
       ((er old-if-new-enable) (process-old-if-new-enable old-if-new-enable
                                                          old-if-new-enable-present
                                                          ctx
                                                          state))
       ((er verify-guards) (ensure-boolean-or-auto-and-return-boolean$
                            verify-guards
                            (guard-verified-p old wrld)
                            "The :VERIFY-GUARDS input" t nil))
       ((er &) (evmac-process-input-print print ctx state))
       ((er &) (evmac-process-input-show-only show-only ctx state)))
    (value (list old
                 inputs
                 x0
                 iorel
                 ?f
                 ?g
                 ?h
                 fold
                 spec-atom
                 spec-cons
                 equal-fold
                 cdr-output
                 new
                 new-enable
                 old-if-new
                 old-if-new-enable
                 verify-guards
                 names-to-avoid))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-event-generation divconq
                                    :some-local-nonlocal-p t
                                    :some-local-p t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define divconq-gen-?g-fvar ((?g symbolp) (inputs symbol-listp))
  :returns (event pseudo-event-formp)
  :short "Generate the @('?g') function variable
          described in the user documentation."
  `(soft::defunvar ,?g ,(repeat (len inputs) '*) => *))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define divconq-gen-?h-fvar ((?h symbolp) (inputs symbol-listp))
  :returns (event pseudo-event-formp)
  :short "Generate the @('?h') function variable
          described in the user documentation."
  `(soft::defunvar ,?h ,(repeat (1+ (len inputs)) '*) => *))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define divconq-gen-inputs-with-car ((inputs symbol-listp) (x0 symbolp))
  :returns (inputs-with-car pseudo-term-listp :hyp :guard)
  :short "Apply @(tsee car) to the list input within all the inputs."
  :long
  (xdoc::topstring-p
   "Using the notation in the user documentation,
    this function takes @('(x0 x1 ... xn)') as input
    and returns @('((car x0) x1 ... xn)') as output.
    However, note that @('x0') is not necessarily the first input,
    so we need to go through the list until we find it.")
  (cond ((endp inputs) nil)
        ((eq (car inputs) x0) (cons (fcons-term 'car (list x0)) (cdr inputs)))
        (t (cons (car inputs) (divconq-gen-inputs-with-car (cdr inputs) x0))))
  :prepwork
  ((local (include-book "std/typed-lists/pseudo-term-listp" :dir :system))
   (local (include-book "std/typed-lists/symbol-listp" :dir :system))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define divconq-gen-inputs-with-cdr ((inputs symbol-listp) (x0 symbolp))
  :returns (inputs-with-cdr pseudo-term-listp :hyp :guard)
  :short "Apply @(tsee cdr) to the list input within all the inputs."
  :long
  (xdoc::topstring-p
   "Using the notation in the user documentation,
    this function takes @('(x0 x1 ... xn)') as input
    and returns @('((cdr x0) x1 ... xn)') as output.
    However, note that @('x0') is not necessarily the first input,
    so we need to go through the list until we find it.")
  (cond ((endp inputs) nil)
        ((eq (car inputs) x0) (cons (fcons-term 'cdr (list x0)) (cdr inputs)))
        (t (cons (car inputs) (divconq-gen-inputs-with-cdr (cdr inputs) x0))))
  :prepwork
  ((local (include-book "std/typed-lists/pseudo-term-listp" :dir :system))
   (local (include-book "std/typed-lists/symbol-listp" :dir :system))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define divconq-gen-fold-fn ((fold symbolp)
                             (fold-enable booleanp)
                             (inputs symbol-listp)
                             (x0 symbolp)
                             (?g symbolp)
                             (?h symbolp)
                             (verify-guards booleanp))
  :returns (mv (local-events pseudo-event-form-listp)
               (exported-events pseudo-event-form-listp)
               (event-to-print pseudo-event-formp))
  :short "Generate the @('fold[?g][?h]') function
          described in the user documentation."
  (b* ((inputs-with-car (divconq-gen-inputs-with-car inputs x0))
       (inputs-with-cdr (divconq-gen-inputs-with-cdr inputs x0))
       (body `(cond ((atom ,x0) (,?g ,@inputs))
                    (t (,?h ,@inputs-with-car
                            (,fold ,@inputs-with-cdr)))))
       (event-to-print `(soft::defun2 ,fold ,inputs
                          (declare (xargs :measure (acl2-count ,x0)))
                          ,body))
       (verify-guards-event? (and verify-guards
                                  `((local
                                     (verify-guards ,fold
                                       :hints (("Goal" :in-theory nil)))))))
       (local-events `((local
                        (soft::defun2 ,fold ,inputs
                          (declare (xargs :measure (acl2-count ,x0)
                                          :hints (("Goal" :in-theory nil))))
                          ,body))
                       ,@verify-guards-event?))
       (disable-event? (and (not fold-enable)
                            `((in-theory (disable ,fold)))))
       (exported-events `(,event-to-print
                          ,@(and verify-guards `((verify-guards ,fold)))
                          ,@disable-event?)))
    (mv local-events exported-events event-to-print)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define divconq-gen-spec-atom-fn ((spec-atom symbolp)
                                  (spec-atom-enable booleanp)
                                  (inputs symbol-listp)
                                  (x0 symbolp)
                                  (iorel symbolp)
                                  (?g symbolp)
                                  (verify-guards booleanp))
  :returns (mv (local-events pseudo-event-form-listp)
               (exported-events pseudo-event-form-listp)
               (event-to-print pseudo-event-formp))
  :short "Generate the @('spec-atom[?g]') function
          described in the user documentation."
  (b* ((body `(forall ,inputs
                      (impliez (atom ,x0)
                               (,iorel ,@inputs (,?g ,@inputs)))))
       (event-to-print `(soft::defun-sk2 ,spec-atom () ,body))
       (verify-guards-event? (and verify-guards
                                  `((local
                                     (verify-guards ,spec-atom
                                       :hints (("Goal" :in-theory nil)))))))
       (local-events `((local ,event-to-print)
                       ,@verify-guards-event?))
       (spec-atom-necc (add-suffix spec-atom "-NECC"))
       (disable-event? (and (not spec-atom-enable)
                            `((in-theory (disable ,spec-atom
                                                  ,spec-atom-necc)))))
       (exported-events `(,event-to-print
                          ,@(and verify-guards `((verify-guards ,spec-atom)))
                          ,@disable-event?)))
    (mv local-events exported-events event-to-print)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define divconq-gen-spec-cons-fn ((spec-cons symbolp)
                                  (spec-cons-enable booleanp)
                                  (inputs symbol-listp)
                                  (x0 symbolp)
                                  (iorel symbolp)
                                  (?h symbolp)
                                  (cdr-output symbolp)
                                  (verify-guards booleanp))
  :returns (mv (local-events pseudo-event-form-listp)
               (exported-events pseudo-event-form-listp)
               (event-to-print pseudo-event-formp))
  :short "Generate the @('spec-cons[?h]') function
          described in the user documentation."
  (b* ((inputs-with-car (divconq-gen-inputs-with-car inputs x0))
       (inputs-with-cdr (divconq-gen-inputs-with-cdr inputs x0))
       (body `(forall (,@inputs ,cdr-output)
                      (impliez (and (consp ,x0)
                                    (,iorel ,@inputs-with-cdr ,cdr-output))
                               (,iorel ,@inputs
                                       (,?h ,@inputs-with-car ,cdr-output)))))
       (event-to-print `(soft::defun-sk2 ,spec-cons () ,body))
       (verify-guards-event? (and verify-guards
                                  `((local
                                     (verify-guards ,spec-cons
                                       :hints (("Goal" :in-theory nil)))))))
       (local-events `((local ,event-to-print)
                       ,@verify-guards-event?))
       (spec-cons-necc (add-suffix spec-cons "-NECC"))
       (disable-event? (and (not spec-cons-enable)
                            `((in-theory (disable ,spec-cons
                                                  ,spec-cons-necc)))))
       (exported-events `(,event-to-print
                          ,@(and verify-guards `((verify-guards ,spec-cons)))
                          ,@disable-event?)))
    (mv local-events exported-events event-to-print)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define divconq-gen-equal-fold-fn ((equal-fold symbolp)
                                   (equal-fold-enable booleanp)
                                   (inputs symbol-listp)
                                   (?f symbolp)
                                   (fold symbolp)
                                   (verify-guards booleanp))
  :returns (mv (local-events pseudo-event-form-listp)
               (exported-events pseudo-event-form-listp)
               (event-to-print pseudo-event-formp))
  :short "Generate the @('equal[?f][fold[?g][?h]]') function
          described in the user documentation."
  (b* ((body `(forall ,inputs
                      (equal (,?f ,@inputs)
                             (,fold ,@inputs))))
       (event-to-print `(soft::defun-sk2 ,equal-fold () ,body))
       (verify-guards-event? (and verify-guards
                                  `((local
                                     (verify-guards ,equal-fold
                                       :hints (("Goal" :in-theory nil)))))))
       (local-events `((local ,event-to-print)
                       ,@verify-guards-event?))
       (equal-fold-necc (add-suffix equal-fold "-NECC"))
       (disable-event? (and (not equal-fold-enable)
                            `((in-theory (disable ,equal-fold
                                                  ,equal-fold-necc)))))
       (exported-events `(,event-to-print
                          ,@(and verify-guards `((verify-guards ,equal-fold)))
                          ,@disable-event?)))
    (mv local-events exported-events event-to-print)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define divconq-gen-new-fn ((new symbolp)
                            (new-enable booleanp)
                            (spec-atom symbolp)
                            (spec-cons symbolp)
                            (equal-fold symbolp)
                            (verify-guards booleanp))
  :returns (mv (local-events pseudo-event-form-listp)
               (exported-events pseudo-event-form-listp)
               (event-to-print pseudo-event-formp))
  :short "Generate the @('new') function
          described in the user documentation."
  (b* ((body `(and (,equal-fold)
                   (,spec-atom)
                   (,spec-cons)))
       (event-to-print `(soft::defun2 ,new () ,body))
       (verify-guards-event? (and verify-guards
                                  `((local
                                     (verify-guards ,new
                                       :hints (("Goal" :in-theory nil)))))))
       (local-events `((local ,event-to-print)
                       ,@verify-guards-event?))
       (disable-event? (and (not new-enable)
                            `((in-theory (disable ,new)))))
       (exported-events `(,event-to-print
                          ,@(and verify-guards `((verify-guards ,new)))
                          ,@disable-event?)))
    (mv local-events exported-events event-to-print)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define divconq-gen-fold-correct ((inputs symbol-listp)
                                  (x0 symbolp)
                                  (iorel symbolp)
                                  (fold symbolp)
                                  (spec-atom symbolp)
                                  (spec-cons symbolp)
                                  (cdr-output symbolp)
                                  (names-to-avoid symbol-listp)
                                  (wrld plist-worldp))
  :returns (mv (event "A @(tsee pseudo-event-formp).")
               (name "A @(tsee symbolp).")
               (updated-names-to-avoid "A @(tsee symbol-listp)."))
  :mode :program
  :short "Generate a local theorem asserting
          the correctness of the @('fold[?g][?h]') function."
  :long
  (xdoc::topstring-p
   "This is the theorem @($\\mathit{COR}$) in the design notes.")
  (b* (((mv name names-to-avoid)
        (fresh-logical-name-with-$s-suffix 'fold-correct
                                           nil
                                           names-to-avoid
                                           wrld))
       (spec-atom-necc (add-suffix spec-atom "-NECC"))
       (spec-cons-necc (add-suffix spec-cons "-NECC"))
       (inputs-with-cdr (divconq-gen-inputs-with-cdr inputs x0))
       (hints `(("Goal"
                 :in-theory '(len atom ,fold)
                 :induct (len ,x0))
                '(:use (,spec-atom-necc
                        (:instance ,spec-cons-necc
                         (,cdr-output (,fold ,@inputs-with-cdr)))))))
       (event
        `(local
          (defthm ,name
            (implies (and (,spec-atom)
                          (,spec-cons))
                     (,iorel ,@inputs (,fold ,@inputs)))
            :rule-classes nil
            :hints ,hints))))
    (mv event name names-to-avoid)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define divconq-gen-old-if-new-thm ((old-if-new symbolp)
                                    (old-if-new-enable booleanp)
                                    (old symbolp)
                                    (inputs symbol-listp)
                                    (x0 symbolp)
                                    (equal-fold symbolp)
                                    (new symbolp)
                                    (fold-correct symbolp))
  :returns (mv (local-event pseudo-event-formp)
               (exported-event pseudo-event-formp))
  :short "Generate the theorem @('old-if-new')
          described in the user documentation."
  (b* ((formula `(implies (,new) (,old)))
       (old-witness (add-suffix-to-fn old "-WITNESS"))
       (equal-fold-necc (add-suffix equal-fold "-NECC"))
       (instantiation (if (>= (len inputs) 2)
                          (divconq-gen-old-if-new-thm-aux inputs 0 old-witness)
                        `((,x0 (,old-witness)))))
       (hints `(("Goal"
                 :in-theory '(,old ,new)
                 :use ((:instance ,equal-fold-necc ,@instantiation)
                       (:instance ,fold-correct ,@instantiation)))))
       (defthm/defthmd (if old-if-new-enable 'defthm 'defthmd))
       (local-event `(local
                      (,defthm/defthmd ,old-if-new
                        ,formula
                        :hints ,hints)))
       (exported-event `(,defthm/defthmd ,old-if-new
                          ,formula)))
    (mv local-event exported-event))

  :prepwork
  ((define divconq-gen-old-if-new-thm-aux ((inputs symbol-listp)
                                           (index natp)
                                           (old-witness symbolp))
     :returns (instantiation doublet-listp)
     (cond ((endp inputs) nil)
           (t (cons `(,(car inputs) (mv-nth ,index (,old-witness)))
                    (divconq-gen-old-if-new-thm-aux (cdr inputs)
                                                    (1+ index)
                                                    old-witness)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define divconq-gen-everything ((old symbolp)
                                (inputs symbol-listp)
                                (x0 symbolp)
                                (iorel symbolp)
                                (?f symbolp)
                                (?g symbolp)
                                (?h symbolp)
                                (fold symbolp)
                                (fold-enable booleanp)
                                (spec-atom symbolp)
                                (spec-atom-enable booleanp)
                                (spec-cons symbolp)
                                (spec-cons-enable booleanp)
                                (equal-fold symbolp)
                                (equal-fold-enable booleanp)
                                (cdr-output symbolp)
                                (new symbolp)
                                (new-enable booleanp)
                                (old-if-new symbolp)
                                (old-if-new-enable booleanp)
                                (verify-guards booleanp)
                                (print evmac-input-print-p)
                                (show-only booleanp)
                                (call pseudo-event-formp)
                                (names-to-avoid symbol-listp)
                                (wrld plist-worldp))
  :returns (event "A @(tsee pseudo-event-formp).")
  :mode :program
  :short "Generate the top-level event."
  (b* ((??g-event (divconq-gen-?g-fvar ?g inputs))
       (??h-event (divconq-gen-?h-fvar ?h inputs))
       ((mv fold-local-events
            fold-exported-events
            fold-event-to-print)
        (divconq-gen-fold-fn fold fold-enable inputs x0 ?g ?h verify-guards))
       ((mv spec-atom-local-events
            spec-atom-exported-events
            spec-atom-event-to-print)
        (divconq-gen-spec-atom-fn spec-atom spec-atom-enable
                                  inputs x0 iorel ?g verify-guards))
       ((mv spec-cons-local-events
            spec-cons-exported-events
            spec-cons-event-to-print)
        (divconq-gen-spec-cons-fn spec-cons spec-cons-enable
                                  inputs x0 iorel ?h cdr-output verify-guards))
       ((mv equal-fold-local-events
            equal-fold-exported-events
            equal-fold-event-to-print)
        (divconq-gen-equal-fold-fn equal-fold equal-fold-enable
                                   inputs ?f fold verify-guards))
       ((mv new-local-events
            new-exported-events
            new-event-to-print)
        (divconq-gen-new-fn new new-enable
                            spec-atom spec-cons equal-fold verify-guards))
       ((mv fold-correct-event fold-correct &)
        (divconq-gen-fold-correct inputs x0 iorel fold spec-atom spec-cons
                                  cdr-output names-to-avoid wrld))
       ((mv old-if-new-local-event
            old-if-new-exported-event)
        (divconq-gen-old-if-new-thm old-if-new old-if-new-enable
                                    old inputs x0 equal-fold new fold-correct))
       (encapsulate-events
        `((logic)
          (evmac-prepare-proofs)
          ,?g-event
          ,?h-event
          ,@fold-local-events
          ,@spec-atom-local-events
          ,@spec-cons-local-events
          ,@equal-fold-local-events
          ,@new-local-events
          ,fold-correct-event
          ,old-if-new-local-event
          ,@fold-exported-events
          ,@spec-atom-exported-events
          ,@spec-cons-exported-events
          ,@equal-fold-exported-events
          ,@new-exported-events
          ,old-if-new-exported-event))
       (encapsulate `(encapsulate () ,@encapsulate-events))
       ((when show-only)
        (if (member-eq print '(:info :all))
            (cw "~%~x0~|" encapsulate)
          (cw "~x0~|" encapsulate))
        '(value-triple :invisible))
       (encapsulate+ (restore-output? (eq print :all) encapsulate))
       (transformation-table-event (record-transformation-call-event
                                    call encapsulate wrld))
       (print-result (and
                      (member-eq print '(:result :info :all))
                      `(,@(and (member-eq print '(:info :all))
                               '((cw-event "~%")))
                        (cw-event "~x0~|" ',fold-event-to-print)
                        (cw-event "~x0~|" ',spec-atom-event-to-print)
                        (cw-event "~x0~|" ',spec-cons-event-to-print)
                        (cw-event "~x0~|" ',equal-fold-event-to-print)
                        (cw-event "~x0~|" ',new-event-to-print)
                        (cw-event "~x0~|" ',old-if-new-exported-event)))))
    `(progn
       ,encapsulate+
       ,transformation-table-event
       ,@print-result
       (value-triple :invisible))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define divconq-fn (old
                    schema
                    list-input
                    fvar-atom-name
                    fvar-cons-name
                    fold-name
                    fold-enable
                    spec-atom-name
                    spec-atom-enable
                    spec-cons-name
                    spec-cons-enable
                    equal-fold-name
                    equal-fold-enable
                    cdr-output
                    new-name
                    new-enable
                    old-if-new-name
                    (old-if-new-name-present booleanp)
                    old-if-new-enable
                    (old-if-new-enable-present booleanp)
                    verify-guards
                    print
                    show-only
                    (call pseudo-event-formp)
                    ctx
                    state)
  :returns (mv erp (event "A @(tsee pseudo-event-formp).") state)
  :mode :program
  :parents (divconq-implementation)
  :short "Check redundancy, process the inputs, and generate the event."
  (b* ((encapsulate? (previous-transformation-expansion call (w state)))
       ((when encapsulate?)
        (b* (((run-when show-only) (cw "~x0~|" encapsulate?)))
          (cw "~%The transformation ~x0 is redundant.~%" call)
          (value '(value-triple :invisible))))
       ((er (list old
                  inputs
                  x0
                  iorel
                  ??f
                  ??g
                  ??h
                  fold
                  spec-atom
                  spec-cons
                  equal-fold
                  cdr-output
                  new
                  new-enable
                  old-if-new
                  old-if-new-enable
                  verify-guards
                  names-to-avoid))
        (divconq-process-inputs old
                                schema
                                fvar-atom-name
                                fvar-cons-name
                                fold-name
                                fold-enable
                                spec-atom-name
                                spec-atom-enable
                                spec-cons-name
                                spec-cons-enable
                                equal-fold-name
                                equal-fold-enable
                                list-input
                                cdr-output
                                new-name
                                new-enable
                                old-if-new-name
                                old-if-new-name-present
                                old-if-new-enable
                                old-if-new-enable-present
                                verify-guards
                                print
                                show-only
                                ctx
                                state))
       (event (divconq-gen-everything old
                                      inputs
                                      x0
                                      iorel
                                      ?f
                                      ?g
                                      ?h
                                      fold
                                      fold-enable
                                      spec-atom
                                      spec-atom-enable
                                      spec-cons
                                      spec-cons-enable
                                      equal-fold
                                      equal-fold-enable
                                      cdr-output
                                      new
                                      new-enable
                                      old-if-new
                                      old-if-new-enable
                                      verify-guards
                                      print
                                      show-only
                                      call
                                      names-to-avoid
                                      (w state))))
    (value event)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection divconq-macro-definition
  :parents (divconq-implementation)
  :short "Definition of the @(tsee divconq) macro."
  :long
  (xdoc::topstring
   (xdoc::p
    "Submit the event form generated by @(tsee divconq-fn).")
   (xdoc::@def "divconq"))
  (defmacro divconq (&whole
                     call
                     ;; mandatory inputs:
                     old
                     ;; optional inputs:
                     &key
                     (schema ':list-fold)
                     (list-input ':auto)
                     (fvar-atom-name ':auto)
                     (fvar-cons-name ':auto)
                     (fold-name ':auto)
                     (fold-enable 'nil)
                     (spec-atom-name ':auto)
                     (spec-atom-enable 'nil)
                     (spec-cons-name ':auto)
                     (spec-cons-enable 'nil)
                     (equal-fold-name ':auto)
                     (equal-fold-enable 'nil)
                     (cdr-output ':auto)
                     (new-name ':auto)
                     (new-enable ':auto)
                     (old-if-new-name ':irrelevant old-if-new-name-present)
                     (old-if-new-enable ':irrelevant old-if-new-enable-present)
                     (verify-guards ':auto)
                     (print ':result)
                     (show-only 'nil))
    `(make-event-terse (divconq-fn ',old
                                   ',schema
                                   ',list-input
                                   ',fvar-atom-name
                                   ',fvar-cons-name
                                   ',fold-name
                                   ',fold-enable
                                   ',spec-atom-name
                                   ',spec-atom-enable
                                   ',spec-cons-name
                                   ',spec-cons-enable
                                   ',equal-fold-name
                                   ',equal-fold-enable
                                   ',cdr-output
                                   ',new-name
                                   ',new-enable
                                   ',old-if-new-name
                                   ',old-if-new-name-present
                                   ',old-if-new-enable
                                   ',old-if-new-enable-present
                                   ',verify-guards
                                   ',print
                                   ',show-only
                                   ',call
                                   (cons 'divconq ',old)
                                   state)
                       :suppress-errors ,(not print))))
