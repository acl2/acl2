; APT (Automated Program Transformations) Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "APT")

(include-book "kestrel/error-checking/ensure-symbol-is-fresh-event-name" :dir :system)
(include-book "kestrel/error-checking/ensure-value-is-in-list" :dir :system)
(include-book "kestrel/error-checking/ensure-value-is-legal-variable-name" :dir :system)
(include-book "kestrel/error-checking/ensure-value-is-not-in-list" :dir :system)
(include-book "kestrel/error-checking/ensure-value-is-symbol" :dir :system)
(include-book "kestrel/event-macros/input-processing" :dir :system)
(include-book "kestrel/event-macros/proof-preparation" :dir :system)
(include-book "kestrel/event-macros/restore-output" :dir :system)
(include-book "kestrel/event-macros/xdoc-constructors" :dir :system)
(include-book "kestrel/soft/defunvar" :dir :system)
(include-book "kestrel/soft/defun2" :dir :system)
(include-book "kestrel/soft/defund2" :dir :system)
(include-book "kestrel/soft/defun-sk2" :dir :system)
(include-book "kestrel/soft/defund-sk2" :dir :system)
(include-book "kestrel/std/system/defun-sk-queries" :dir :system)
(include-book "kestrel/std/system/fresh-logical-name-with-dollars-suffix" :dir :system)
(include-book "kestrel/std/util/tuple" :dir :system)
(include-book "kestrel/utilities/error-checking/top" :dir :system)
(include-book "projects/apply/top" :dir :system)

(include-book "utilities/input-processing")
(include-book "utilities/transformation-table")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defwarrant sublis-var)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-implementation

 divconq

 :items

 (xdoc::*evmac-topic-implementation-item-state*

  xdoc::*evmac-topic-implementation-item-wrld*

  xdoc::*evmac-topic-implementation-item-ctx*

  "@('old') is the homonymous input to @(tsee divconq) when it has no type;
   otherwise, it is the function symbol denoted by that input."

  (xdoc::evmac-topic-implementation-item-input "schema" "divconq")

  (xdoc::evmac-topic-implementation-item-input "list-input" "divconq")

  (xdoc::evmac-topic-implementation-item-input "fvar-atom-name" "divconq")

  (xdoc::evmac-topic-implementation-item-input "fvar-cons-name" "divconq")

  (xdoc::evmac-topic-implementation-item-input "fold-name" "divconq")

  (xdoc::evmac-topic-implementation-item-input "fold-enable" "divconq")

  (xdoc::evmac-topic-implementation-item-input "spec-atom-name" "divconq")

  (xdoc::evmac-topic-implementation-item-input "spec-atom-enable" "divconq")

  (xdoc::evmac-topic-implementation-item-input "spec-cons-name" "divconq")

  (xdoc::evmac-topic-implementation-item-input "spec-cons-enable" "divconq")

  (xdoc::evmac-topic-implementation-item-input "equal-fold-name" "divconq")

  (xdoc::evmac-topic-implementation-item-input "equal-fold-enable" "divconq")

  (xdoc::evmac-topic-implementation-item-input "cdr-output" "divconq")

  (xdoc::evmac-topic-implementation-item-input "new-name" "divconq")

  "@('new-enable') is the homonymous input to @(tsee divconq)
   if it has no type;
   otherwise, it is the boolean resulting from processing that input."

  (xdoc::evmac-topic-implementation-item-input "old-if-new-name" "divconq")

  "@('old-if-new-enable') is the homonymous input to @(tsee divconq)
   if it has no type;
   otherwise, it is the boolean resulting from processing that input."

  "@('verify-guards') is the homonymous input to @(tsee divconq)
   if it has no type;
   otherwise, it is the boolean resulting from processing that input."

  (xdoc::evmac-topic-implementation-item-input "print" "divconq")

  (xdoc::evmac-topic-implementation-item-input "show-only" "divconq")

  "@('x-x1...xn') is the list of variable symbols @('(x x1 ... xn)')
   described in the user documentation."

  "@('x-a1...am') is the list of terms @('(x a1<x1,...,xn> ... am<x1,...,xn>)')
   described in the user documentation."

  "@('x-z1...zm') is the list of variable symbols @('(x z1 ... zm)')
   described in the user documentation."

  (xdoc::evmac-topic-implementation-item-var-doc "x")

  (xdoc::evmac-topic-implementation-item-var-doc "y")

  "@('iorel') is the lambda expression
   @('(lambda (x x1 ... xn y) iorel<x,x1,...,xn,y>)')
   described in the user documentation."

  (xdoc::evmac-topic-implementation-item-fn-doc "?f")

  (xdoc::evmac-topic-implementation-item-fn-doc "?g")

  (xdoc::evmac-topic-implementation-item-fn-doc "?h")

  "@('fold') is the function symbol @('fold[?g][?h]')
   described in the user documentation."

  "@('spec-atom') is the function symbol @('spec-atom[?g]')
   described in the user documentation."

  "@('spec-cons') is the function symbol @('spec-cons[?g]')
   described in the user documentation."

  "@('equal-fold') is the function symbol @('equal[?f][fold[?g][?h]]')
   described in the user documentation."

  (xdoc::evmac-topic-implementation-item-fn-doc "new")

  (xdoc::evmac-topic-implementation-item-thm-doc "old-if-new")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-input-processing divconq)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define divconq-process-old-and-cdr-output (old
                                            cdr-output
                                            verify-guards
                                            ctx
                                            state)
  :returns (mv erp
               (result "A @('(tuple (old symbolp)
                                    (?f symbolp)
                                    (x-x1...xn symbol-listp)
                                    (x-a1...am pseudo-term-listp)
                                    (y symbolp)
                                    (iorel pseudo-lambdap))').")
               state)
  :mode :program
  :short "Process the @('old') and @(':cdr-output') inputs."
  :long
  (xdoc::topstring-p
   "We process these two inputs together because
    (1) we want to use the variable name specified by @(':cdr-output')
    as a variable of the @('iorel') lambda expression
    when processing the @('old') input, and
    (2) we need to ensure that that variable is distinct from
    @('x'), @('x1'), ...., @('xn').")
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
       ((unless (eq (defun-sk-quantifier old wrld) 'forall))
        (er-soft+ ctx t nil
                  "The quantifier of the target function ~x0 ~
                   must be universal, but it is existential instead."
                  old))
       (x-x1...xn (defun-sk-bound-vars old wrld))
       (matrix (defun-sk-matrix old wrld))
       (??f-calls (all-calls (list ?f) matrix nil nil))
       ((unless (= (len ?f-calls) 1))
        (er-soft+ ctx t nil
                  "The matrix ~x0 of the target function ~x1 ~
                   must have exactly one call of the function variable ~x2, ~
                   but it has ~x3 calls instead."
                  matrix old ?f (len ?f-calls)))
       (??f-call (car ?f-calls))
       (x-a1...am (fargs ?f-call))
       ((unless (consp x-a1...am))
        (er-soft+ ctx t nil
                  "The call ~x0 in the matrix ~x1 of ~x2 ~
                   must have at least one argument, ~
                   but it has none instead."
                  ?f-call matrix old))
       (y (if (eq cdr-output :auto)
              (intern-in-package-of-symbol "CDR-OUTPUT" old)
            cdr-output))
       ((er &) (ensure-value-is-legal-variable-name$ y
                                                     "The :CDR-OUTPUT input"
                                                     t
                                                     nil))
       ((er &) (ensure-value-is-not-in-list$
                y
                x-x1...xn
                (msg "one of bound variables ~x0 of ~x1" x-x1...xn old)
                "The :CDR-OUTPUT input"
                t
                nil))
       (iorel-body (subst-expr y ?f-call matrix))
       (iorel (make-lambda (append x-x1...xn (list y)) iorel-body)))
    (value (list old ?f x-x1...xn x-a1...am y iorel))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define divconq-process-schema (schema (schema? booleanp) ctx state)
  :returns (mv erp (nothing null) state)
  :short "Process the @(':schema') input."
  (if (eq schema :list-fold)
      (value nil)
    (if schema?
        (er-soft+ ctx t nil
                  "The :SCHEMA input must be :LIST-FOLD, ~
                   but it is ~x0 instead. ~
                   More schemas will be supported in the future."
                  schema)
      (er-soft+ ctx t nil
                "The :SCHEMA input must be supplied."))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define divconq-process-list-input (list-input
                                    (old symbolp)
                                    (?f symbolp)
                                    (x-x1...xn symbol-listp)
                                    (x-a1...am pseudo-term-listp)
                                    ctx
                                    state)
  :returns (mv erp
               (x symbolp
                  :hyp (symbol-listp inputs)
                  :hints (("Goal"
                           :in-theory
                           (enable acl2::ensure-value-is-in-list))))
               state)
  :short "Process the @(':list-input') input."
  (b* (((er x) (if (eq list-input :auto)
                   (if (= (len x-a1...am) 1)
                       (value (car x-a1...am))
                     (er-soft+ ctx t nil
                               "The :LIST-INPUT is ~
                                (perhaps by default) :AUTO, ~
                                but this is allowed only if ~
                                the call of ~x0 in ~x1 ~
                                has exactly one argument, ~
                                but it has ~x2 arguments instead."
                               ?f old (len x-a1...am)))
                 (b* (((er &) (ensure-value-is-in-list$
                               list-input
                               x-a1...am
                               (msg "one of the arguments ~x0 of ~
                                     the call of ~x1 in ~x2"
                                    x-a1...am ?f old)
                               "The :LIST-INPUT input"
                               t
                               nil)))
                   (value list-input))))
       ((unless (symbolp x))
        (er-soft+ ctx t nil
                  "The argument ~x0 of the call of ~x1 in ~x2, ~
                   specified (perhaps by default) by the :LIST-INPUT, ~
                   must be a variable, but it is not."
                  x ?f old))
       ((unless (member-eq x x-x1...xn))
        (value (raise "Internal error: ~
                       the variable ~x0 in the call of ~x1 in ~x2 ~
                       is not among the bound variables ~x3."
                      x ?f old x-x1...xn)))
       (a1...am (remove1-eq x x-a1...am))
       ((when (member-eq x (all-vars (cons 'dummy a1...am))))
        (er-soft+ ctx t nil
                  "Aside from the argument ~x0 itself, ~
                   the other arguments ~x1 of the call of ~x2 ~
                   must not depend on ~x0, but they do."
                  x a1...am ?f)))
    (value x))
  :prepwork
  ((local (include-book "kestrel/std/system/all-vars" :dir :system))
   (defrulel lemma
     (implies (pseudo-term-listp x)
              (pseudo-term-listp (remove1-equal a x))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define divconq-process-fvar-atom-name (fvar-atom-name
                                        (?f symbolp)
                                        (names-to-avoid symbol-listp)
                                        ctx
                                        state)
  :returns (mv erp
               (result "A @('(tuple (?g symbolp)
                                    (updated-names-to-avoid symbol-listp))').")
               state)
  :mode :program
  :short "Process the @(':fvar-atom-name') input."
  (b* (((er &) (ensure-value-is-symbol$ fvar-atom-name
                                        "The :FVAR-ATOM-NAME input"
                                        t nil))
       (??g (if (eq fvar-atom-name :auto)
                (add-suffix ?f "-ATOM")
              fvar-atom-name))
       ((er names-to-avoid)
        (ensure-symbol-is-fresh-event-name$
         ?g
         (msg "The name ~x0 specified by :FVAR-ATOM-NAME" ?g)
         'function
         names-to-avoid
         t
         nil)))
    (value (list ?g names-to-avoid))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define divconq-process-fvar-cons-name (fvar-cons-name
                                        (?f symbolp)
                                        (names-to-avoid symbol-listp)
                                        ctx
                                        state)
  :returns (mv erp
               (result "A @('(tuple (?h symbolp)
                                    (updated-names-to-avoid symbol-listp))').")
               state)
  :mode :program
  :short "Process the @(':fvar-cons-name') input."
  (b* (((er &) (ensure-value-is-symbol$ fvar-cons-name
                                        "The :FVAR-CONS-NAME input"
                                        t nil))
       (??h (if (eq fvar-cons-name :auto)
                (add-suffix ?f "-CONS")
              fvar-cons-name))
       ((er names-to-avoid)
        (ensure-symbol-is-fresh-event-name$
         ?h
         (msg "The name ~x0 specified by :FVAR-CONS-NAME" ?h)
         'function
         names-to-avoid
         t
         nil)))
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
               (result "A @('(tuple (fold symbolp)
                                    (updated-names-to-avoid symbol-listp))').")
               state)
  :mode :program
  :short "Process the @(':fold-name') input."
  (b* (((er &) (ensure-value-is-symbol$ fold-name
                                        "The :FOLD-NAME input"
                                        t nil))
       (fold (if (eq fold-name :auto)
                 (packn-pos (list "FOLD[" ?g "][" ?h "]") old)
               fold-name))
       ((er names-to-avoid)
        (ensure-symbol-is-fresh-event-name$
         fold
         (msg "The name ~x0 specified by :FOLD-NAME" fold)
         'function
         names-to-avoid
         t
         nil)))
    (value (list fold names-to-avoid))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define divconq-process-spec-atom-name (spec-atom-name
                                        (old symbolp)
                                        (?g symbolp)
                                        (names-to-avoid symbol-listp)
                                        ctx
                                        state)
  :returns (mv erp
               (result "A @('(tuple (spec-atom symbolp)
                                    (updated-names-to-avoid symbol-listp))').")
               state)
  :mode :program
  :short "Process the @(':spec-atom-name') input."
  (b* (((er &) (ensure-value-is-symbol$ spec-atom-name
                                        "The :SPEC-ATOM-NAME input"
                                        t nil))
       (spec-atom (if (eq spec-atom-name :auto)
                      (packn-pos (list "SPEC-ATOM[" ?g "]") old)
                    spec-atom-name))
       ((er names-to-avoid)
        (ensure-symbol-is-fresh-event-name$
         spec-atom
         (msg "The name ~x0 specified by :SPEC-ATOM-NAME" spec-atom)
         'function
         names-to-avoid
         t
         nil)))
    (value (list spec-atom names-to-avoid))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define divconq-process-spec-cons-name (spec-cons-name
                                        (old symbolp)
                                        (?h symbolp)
                                        (names-to-avoid symbol-listp)
                                        ctx
                                        state)
  :returns (mv erp
               (result "A @('(tuple (spec-cons symbolp)
                                    (updated-names-to-avoid symbol-listp))').")
               state)
  :mode :program
  :short "Process the @(':spec-cons-name') input."
  (b* (((er &) (ensure-value-is-symbol$ spec-cons-name
                                        "The :SPEC-CONS-NAME input"
                                        t nil))
       (spec-cons (if (eq spec-cons-name :auto)
                      (packn-pos (list "SPEC-CONS[" ?h "]") old)
                    spec-cons-name))
       ((er names-to-avoid)
        (ensure-symbol-is-fresh-event-name$
         spec-cons
         (msg "The name ~x0 specified by :SPEC-CONS-NAME" spec-cons)
         'function
         names-to-avoid
         t
         nil)))
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
               (result "A @('(tuple (equal-fold symbolp)
                                    (updated-names-to-avoid symbol-listp))').")
               state)
  :mode :program
  :short "Process the @(':equal-fold-name') input."
  (b* (((er &) (ensure-value-is-symbol$ equal-fold-name
                                        "The :EQUAL-FOLD-NAME input"
                                        t nil))
       (equal-fold (if (eq equal-fold-name :auto)
                       (packn-pos (list "EQUAL[" ?f "][" fold "]") old)
                     equal-fold-name))
       ((er names-to-avoid)
        (ensure-symbol-is-fresh-event-name$
         equal-fold
         (msg "The name ~x0 specified by :EQUAL-FOLD-NAME" equal-fold)
         'function
         names-to-avoid
         t
         nil)))
    (value (list equal-fold names-to-avoid))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define divconq-process-inputs (old
                                schema
                                (schema? booleanp)
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
                                (old-if-new-name? booleanp)
                                old-if-new-enable
                                (old-if-new-enable? booleanp)
                                verify-guards
                                print
                                show-only
                                ctx
                                state)
  :returns (mv erp
               (result "A @('(tuple (old$ symbolp)
                                    (?f symbolp)
                                    (x-x1...xn symbol-listp)
                                    (x-a1...am symbol-listp)
                                    (x symbolp)
                                    (y symbolp)
                                    (iorel pseudo-lambdap)
                                    (?g symbolp)
                                    (?h symbolp)
                                    (fold symbolp)
                                    (spec-atom symbolp)
                                    (spec-cons symbolp)
                                    (equal-fold symbolp)
                                    (new symbolp)
                                    (new-enable$ booleanp)
                                    (old-if-new symbolp)
                                    (old-if-new-enable$ booleanp)
                                    (verify-guards$ booleanp)
                                    (names-to-avoid symbol-listp))').")
               state)
  :mode :program
  :short "Process all the inputs."
  (b* ((wrld (w state))
       (names-to-avoid nil)
       ((er (list old ??f x-x1...xn x-a1...am y iorel))
        (divconq-process-old-and-cdr-output old
                                            cdr-output
                                            verify-guards
                                            ctx
                                            state))
       ((er &) (divconq-process-schema schema schema? ctx state))
       ((er x) (divconq-process-list-input list-input
                                           old
                                           ?f
                                           x-x1...xn
                                           x-a1...am
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
       ((er (list new names-to-avoid)) (process-input-new-name new-name
                                                               old
                                                               names-to-avoid
                                                               ctx
                                                               state))
       ((er new-enable) (ensure-boolean-or-auto-and-return-boolean$
                         new-enable
                         (fundef-enabledp old state)
                         "The :NEW-ENABLE input" t nil))
       ((er (list old-if-new names-to-avoid))
        (process-input-old-if-new-name old-if-new-name
                                       old-if-new-name?
                                       old
                                       new
                                       names-to-avoid
                                       ctx
                                       state))
       ((er old-if-new-enable)
        (process-input-old-if-new-enable old-if-new-enable
                                         old-if-new-enable?
                                         ctx
                                         state))
       ((er verify-guards) (ensure-boolean-or-auto-and-return-boolean$
                            verify-guards
                            (guard-verified-p old wrld)
                            "The :VERIFY-GUARDS input" t nil))
       ((er &) (evmac-process-input-print print ctx state))
       ((er &) (evmac-process-input-show-only show-only ctx state)))
    (value (list old
                 ?f
                 x-x1...xn
                 x-a1...am
                 x
                 y
                 iorel
                 ?g
                 ?h
                 fold
                 spec-atom
                 spec-cons
                 equal-fold
                 new
                 new-enable
                 old-if-new
                 old-if-new-enable
                 verify-guards
                 names-to-avoid))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-event-generation divconq
                                    :some-local-nonlocal-p t
                                    :some-local-p t
                                    :some-nonlocal-p t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define divconq-gen-?g ((?g symbolp) (x-a1...am symbol-listp))
  :returns (event pseudo-event-formp)
  :short "Generate the function variable @('?g')."
  `(soft::defunvar ,?g ,(repeat (len x-a1...am) '*) => *))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define divconq-gen-?h ((?h symbolp) (x-a1...am symbol-listp))
  :returns (event pseudo-event-formp)
  :short "Generate the function variable @('?h')."
  `(soft::defunvar ,?h ,(repeat (1+ (len x-a1...am)) '*) => *))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define divconq-gen-x-z1...zm ((x-a1...am pseudo-term-listp)
                               (x-x1...xn symbol-listp)
                               (x symbolp)
                               (y symbolp))
  :returns (x-z1...zm "A @(tsee symbol-listp).")
  :mode :program
  :short "Generate the list of variables @('(x z1 ... zm)')."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('zj') variables replace the @('aj<x1,...,xn>') terms
     in some of the generated events.
     If an @('aj<x1,...,xn>') term is one of the @('xi') variables,
     and it is the only one that is that variable,
     then @('zj') is just @('xi').
     In all other cases, @('zj') is a freshly generated variable.")
   (xdoc::p
    "In particular, if @('m') is @('n')
     and each @('aj<x1,...,xn>') if @('xj'),
     we use @('x1'), ..., @('xn') as @('z1'), ..., @('zm'),
     without generating new variable names.")
   (xdoc::p
    "Recall that the list @('x-a1..am')
     may contain @('x') at any position (but just at one position),
     not necessarily at the beginning.
     We return a list @('x-a1...am')
     with @('x') in the same position as @('x-a1...am'),
     and with each @('zj') in the same position as @('aj<x1,...,xn>').")
   (xdoc::p
    "We go through the list of terms @('x-a1...am'),
     and handle each as follows.
     If the term is a variable that differs from all the other terms
     (we test this by checking membership in
     the result of removing one occurrence from the list;
     this is okay since the list is expected to be small),
     then we leave it unchanged;
     this applies to @('x') in particular.
     Otherwise, we generate a new variable,
     having care that it is distinct
     from the ones generated so far,
     from all the ones in @('x-x1...xn'),
     and also from @('y')
     (because they are used in a theorem that includes @('y'))."))
  (divconq-gen-x-z1...zm-aux x-a1...am
                             nil
                             x-a1...am
                             x-x1...xn
                             x
                             y)

  :prepwork
  ((define divconq-gen-x-z1...zm-aux ((terms-to-do pseudo-term-listp)
                                      (vars-done symbol-listp)
                                      (x-a1...am pseudo-term-listp)
                                      (x-x1...xn symbol-listp)
                                      (x symbolp)
                                      (y symbolp))
     :returns (vars "A @(tsee symbol-listp).")
     :mode :program
     (b* (((when (endp terms-to-do)) nil)
          (term (car terms-to-do))
          (var (if (and (symbolp term)
                        (not (member-eq term (remove1-eq term x-a1...am))))
                   term
                 (genvar x "VAR$" nil (append vars-done x-x1...xn (list y))))))
       (cons var (divconq-gen-x-z1...zm-aux (cdr terms-to-do)
                                            (cons term vars-done)
                                            x-a1...am
                                            x-x1...xn
                                            x
                                            y))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define divconq-gen-fold ((fold symbolp)
                          (fold-enable booleanp)
                          (x-z1...zm symbol-listp)
                          (x symbolp)
                          (?g symbolp)
                          (?h symbolp)
                          (verify-guards booleanp))
  :returns (mv (local-event pseudo-event-formp)
               (exported-event pseudo-event-formp))
  :short "Generate the function @('fold[?g][?h]')."
  (b* ((car-x-z1...zm (loop$ for var of-type symbol in x-z1...zm
                             collect (if (eq var x) (list 'car var) var)))
       (cdr-x-z1...zm (loop$ for var of-type symbol in x-z1...zm
                             collect (if (eq var x) (list 'cdr var) var)))
       (macro (if fold-enable 'soft::defun2 'soft::defund2))
       (body `(cond ((atom ,x) (,?g ,@x-z1...zm))
                    (t (,?h ,@car-x-z1...zm
                            (,fold ,@cdr-x-z1...zm)))))
       (hints '(("Goal" :in-theory nil)))
       (local-event
        `(local
          (,macro ,fold ,x-z1...zm
                  (declare (xargs
                            :measure (acl2-count ,x)
                            :hints ,hints
                            ,@(and verify-guards '(:guard t))
                            ,@(and verify-guards (list :guard-hints hints))
                            :verify-guards ,verify-guards))
                  ,body)))
       (exported-event
        `(,macro ,fold ,x-z1...zm
                 (declare (xargs
                           :measure (acl2-count ,x)
                           ,@(and verify-guards '(:guard t))
                           :verify-guards ,verify-guards))
                 ,body)))
    (mv local-event exported-event)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define divconq-gen-spec-atom ((spec-atom symbolp)
                               (spec-atom-enable booleanp)
                               (old symbolp)
                               (x-x1...xn symbol-listp)
                               (x-a1...am pseudo-term-listp)
                               (x symbolp)
                               (iorel pseudo-lambdap)
                               (?g symbolp)
                               (verify-guards booleanp))
  :returns (mv (local-event pseudo-event-formp)
               (exported-event pseudo-event-formp))
  :verify-guards nil
  :short "Generate the function @('spec-atom[?g]')."
  (b* ((macro (if spec-atom-enable 'soft::defun-sk2 'soft::defund-sk2))
       (iorel-term (apply-term iorel (append x-x1...xn
                                             (list `(,?g ,@x-a1...am)))))
       (body `(forall ,x-x1...xn
                      (impliez (atom ,x) ,iorel-term)))
       (hints `(("Goal" :use (:guard-theorem ,old))))
       (local-event
        `(local
          (,macro ,spec-atom ()
                  (declare (xargs
                            ,@(and verify-guards '(:guard t))
                            ,@(and verify-guards (list :guard-hints hints))
                            :verify-guards ,verify-guards))
                  ,body)))
       (exported-event
        `(,macro ,spec-atom ()
                 (declare (xargs ,@(and verify-guards '(:guard t))
                                 :verify-guards ,verify-guards))
                 ,body)))
    (mv local-event exported-event)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define divconq-gen-spec-cons ((spec-cons symbolp)
                               (spec-cons-enable booleanp)
                               (old symbolp)
                               (x-x1...xn symbol-listp)
                               (x-a1...am pseudo-term-listp)
                               (x symbolp)
                               (y symbolp)
                               (iorel pseudo-lambdap)
                               (?h symbolp)
                               (verify-guards booleanp))
  :returns (mv (local-event pseudo-event-formp)
               (exported-event pseudo-event-formp))
  :verify-guards nil
  :short "Generate the function @('spec-cons[?h]')."
  (b* ((cdr-x-x1...xn (loop$ for var in x-x1...xn
                             collect (if (eq var x) (list 'cdr var) var)))
       (car-x-a1...am (loop$ for var in x-a1...am
                             collect (if (eq var x) (list 'car var) var)))
       (macro (if spec-cons-enable 'soft::defun-sk2 'soft::defund-sk2))
       (iorel-term1 (apply-term iorel (append cdr-x-x1...xn (list y))))
       (iorel-term2 (apply-term iorel (append x-x1...xn
                                              (list
                                               `(,?h ,@car-x-a1...am ,y)))))
       (body `(forall (,@x-x1...xn ,y)
                      (impliez (and (consp ,x) ,iorel-term1)
                               ,iorel-term2)))
       (hints `(("Goal" :use (:guard-theorem ,old))))
       (local-event
        `(local
          (,macro ,spec-cons ()
                  (declare
                   (xargs ,@(and verify-guards '(:guard t))
                          ,@(and verify-guards (list :guard-hints hints))
                          :verify-guards ,verify-guards))
                  ,body)))
       (exported-event
        `(,macro ,spec-cons ()
                 (declare (xargs ,@(and verify-guards '(:guard t))
                                 :verify-guards ,verify-guards))
                 ,body)))
    (mv local-event exported-event)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define divconq-gen-equal-fold ((equal-fold symbolp)
                                (equal-fold-enable booleanp)
                                (x-z1...zm symbol-listp)
                                (?f symbolp)
                                (fold symbolp)
                                (verify-guards booleanp))
  :returns (mv (local-event pseudo-event-formp)
               (exported-event pseudo-event-formp))
  :short "Generate the function @('equal[?f][fold[?g][?h]]')."
  (b* ((macro (if equal-fold-enable 'soft::defun-sk2 'soft::defund-sk2))
       (body `(forall ,x-z1...zm
                      (equal (,?f ,@x-z1...zm)
                             (,fold ,@x-z1...zm))))
       (hints '(("Goal" :in-theory nil)))
       (local-event
        `(local
          (,macro ,equal-fold ()
                  (declare
                   (xargs ,@(and verify-guards '(:guard t))
                          ,@(and verify-guards (list :guard-hints hints))
                          :verify-guards ,verify-guards))
                  ,body)))
       (exported-event
        `(,macro ,equal-fold ()
                 (declare (xargs ,@(and verify-guards '(:guard t))
                                 :verify-guards ,verify-guards))
                 ,body)))
    (mv local-event exported-event)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define divconq-gen-new ((new symbolp)
                         (new-enable booleanp)
                         (spec-atom symbolp)
                         (spec-cons symbolp)
                         (equal-fold symbolp)
                         (verify-guards booleanp))
  :returns (mv (local-event pseudo-event-formp)
               (exported-event pseudo-event-formp))
  :short "Generate the function @('new')."
  (b* ((macro (if new-enable 'soft::defun2 'soft::defund2))
       (body `(and (,equal-fold)
                   (,spec-atom)
                   (,spec-cons)))
       (hints '(("Goal" :in-theory nil)))
       (local-event
        `(local
          (,macro ,new ()
                  (declare
                   (xargs ,@(and verify-guards '(:guard t))
                          ,@(and verify-guards (list :guard-hints hints))
                          :verify-guards ,verify-guards))
                  ,body)))
       (exported-event
        `(,macro ,new ()
                 (declare (xargs ,@(and verify-guards '(:guard t))
                                 :verify-guards ,verify-guards))
                 ,body)))
    (mv local-event exported-event)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define divconq-gen-fold-correct ((x-x1...xn symbol-listp)
                                  (x-a1...am symbol-listp)
                                  (x symbolp)
                                  (y symbolp)
                                  (iorel pseudo-lambdap)
                                  (fold symbolp)
                                  (spec-atom symbolp)
                                  (spec-cons symbolp)
                                  (names-to-avoid symbol-listp)
                                  (wrld plist-worldp))
  :returns (mv (event "A @(tsee pseudo-event-formp).")
               (name "A @(tsee symbolp).")
               (updated-names-to-avoid "A @(tsee symbol-listp)."))
  :mode :program
  :short "Generate a local theorem asserting
          the correctness of @('fold[?g][?h]')."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the theorem @($\\mathit{COR}$) in the design notes.")
   (xdoc::p
    "This is not described in the user documentation,
     because it is locally generate."))
  (b* (((mv name names-to-avoid)
        (fresh-logical-name-with-$s-suffix 'fold-correct
                                           nil
                                           names-to-avoid
                                           wrld))
       (iorel-term (apply-term iorel (append x-x1...xn
                                             (list `(,fold ,@x-a1...am)))))
       (spec-atom-necc (add-suffix spec-atom "-NECC"))
       (spec-cons-necc (add-suffix spec-cons "-NECC"))
       (cdr-x-a1...am (loop$ for var in x-a1...am
                             collect (if (eq var x) (list 'cdr var) var)))
       (hints `(("Goal"
                 :in-theory '(len atom ,fold)
                 :induct (len ,x))
                '(:use (,spec-atom-necc
                        (:instance ,spec-cons-necc
                         (,y (,fold ,@cdr-x-a1...am)))))))
       (event
        `(local
          (defthm ,name
            (implies (and (,spec-atom)
                          (,spec-cons))
                     ,iorel-term)
            :rule-classes nil
            :hints ,hints))))
    (mv event name names-to-avoid)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define divconq-gen-old-if-new ((old-if-new symbolp)
                                (old-if-new-enable booleanp)
                                (old symbolp)
                                (x-x1...xn symbol-listp)
                                (x-z1...zm symbol-listp)
                                (x-a1...am symbol-listp)
                                (x symbolp)
                                (equal-fold symbolp)
                                (new symbolp)
                                (fold-correct symbolp))
  :returns (mv (local-event pseudo-event-formp)
               (exported-event pseudo-event-formp))
  :verify-guards nil
  :short "Generate the theorem @('old-if-new')."
  (b* ((formula `(implies (,new) (,old)))
       (old-witness (add-suffix-to-fn old "-WITNESS"))
       (equal-fold-necc (add-suffix equal-fold "-NECC"))
       (x-x1...xn-subst
        (if (>= (len x-x1...xn) 2)
            (loop$ for var in x-x1...xn
                   as i from 0 to (1- (len x-x1...xn))
                   collect (cons var `(mv-nth ,i (,old-witness))))
          (list (cons x `(,old-witness)))))
       (x-x1...xn-instantiation (alist-to-doublets x-x1...xn-subst))
       (x-z1...zm-instantiation
        (loop$ for z in x-z1...zm
               as a in x-a1...am
               collect `(,z ,(sublis-var x-x1...xn-subst a))))
       (hints `(("Goal"
                 :in-theory '(,old ,new)
                 :use ((:instance ,equal-fold-necc ,@x-z1...zm-instantiation)
                       (:instance ,fold-correct ,@x-x1...xn-instantiation)))))
       (defthm/defthmd (if old-if-new-enable 'defthm 'defthmd))
       (local-event `(local
                      (,defthm/defthmd ,old-if-new
                        ,formula
                        :hints ,hints)))
       (exported-event `(,defthm/defthmd ,old-if-new
                          ,formula)))
    (mv local-event exported-event)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define divconq-gen-everything ((old symbolp)
                                (?f symbolp)
                                (x-x1...xn symbol-listp)
                                (x-a1...am pseudo-term-listp)
                                (x symbolp)
                                (y symbolp)
                                (iorel pseudo-lambdap)
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
  (b* ((??g-event (divconq-gen-?g ?g x-a1...am))
       (??h-event (divconq-gen-?h ?h x-a1...am))
       (x-z1...zm (divconq-gen-x-z1...zm x-a1...am x-x1...xn x y))
       ((mv fold-local-event
            fold-exported-event)
        (divconq-gen-fold fold fold-enable x-z1...zm x ?g ?h verify-guards))
       ((mv spec-atom-local-event
            spec-atom-exported-event)
        (divconq-gen-spec-atom spec-atom spec-atom-enable
                               old x-x1...xn x-a1...am x
                               iorel ?g verify-guards))
       ((mv spec-cons-local-event
            spec-cons-exported-event)
        (divconq-gen-spec-cons spec-cons spec-cons-enable
                               old x-x1...xn x-a1...am x y
                               iorel ?h verify-guards))
       ((mv equal-fold-local-event
            equal-fold-exported-event)
        (divconq-gen-equal-fold equal-fold equal-fold-enable
                                x-z1...zm ?f fold verify-guards))
       ((mv new-local-event
            new-exported-event)
        (divconq-gen-new new new-enable
                         spec-atom spec-cons equal-fold verify-guards))
       ((mv fold-correct-event fold-correct &)
        (divconq-gen-fold-correct x-x1...xn x-a1...am x y
                                  iorel fold spec-atom spec-cons
                                  names-to-avoid wrld))
       ((mv old-if-new-local-event
            old-if-new-exported-event)
        (divconq-gen-old-if-new old-if-new old-if-new-enable old
                                x-x1...xn x-z1...zm x-a1...am x
                                equal-fold new fold-correct))
       (encapsulate-events
        `((logic)
          (evmac-prepare-proofs)
          ,?g-event
          ,?h-event
          ,fold-local-event
          ,spec-atom-local-event
          ,spec-cons-local-event
          ,equal-fold-local-event
          ,new-local-event
          ,fold-correct-event
          ,old-if-new-local-event
          ,fold-exported-event
          ,spec-atom-exported-event
          ,spec-cons-exported-event
          ,equal-fold-exported-event
          ,new-exported-event
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
                        (cw-event "~x0~|" ',fold-exported-event)
                        (cw-event "~x0~|" ',spec-atom-exported-event)
                        (cw-event "~x0~|" ',spec-cons-exported-event)
                        (cw-event "~x0~|" ',equal-fold-exported-event)
                        (cw-event "~x0~|" ',new-exported-event)
                        (cw-event "~x0~|" ',old-if-new-exported-event)))))
    `(progn
       ,encapsulate+
       ,transformation-table-event
       ,@print-result
       (value-triple :invisible))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define divconq-fn (old
                    schema
                    (schema? booleanp)
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
                    (old-if-new-name? booleanp)
                    old-if-new-enable
                    (old-if-new-enable? booleanp)
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
                  ??f
                  x-x1...xn
                  x-a1...am
                  x
                  y
                  iorel
                  ??g
                  ??h
                  fold
                  spec-atom
                  spec-cons
                  equal-fold
                  new
                  new-enable
                  old-if-new
                  old-if-new-enable
                  verify-guards
                  names-to-avoid))
        (divconq-process-inputs old
                                schema
                                schema?
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
                                old-if-new-name?
                                old-if-new-enable
                                old-if-new-enable?
                                verify-guards
                                print
                                show-only
                                ctx
                                state))
       (event (divconq-gen-everything old
                                      ?f
                                      x-x1...xn
                                      x-a1...am
                                      x
                                      y
                                      iorel
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
                     (schema ':no-default schema?)
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
                     (old-if-new-name ':no-default old-if-new-name?)
                     (old-if-new-enable ':no-default old-if-new-enable?)
                     (verify-guards ':auto)
                     (print ':result)
                     (show-only 'nil))
    `(make-event-terse (divconq-fn ',old
                                   ',schema
                                   ',schema?
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
                                   ',old-if-new-name?
                                   ',old-if-new-enable
                                   ',old-if-new-enable?
                                   ',verify-guards
                                   ',print
                                   ',show-only
                                   ',call
                                   (cons 'divconq ',old)
                                   state)
                       :suppress-errors ,(not print))))
