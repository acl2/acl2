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
(include-book "kestrel/error-checking/ensure-value-is-boolean" :dir :system)
(include-book "kestrel/error-checking/ensure-value-is-legal-variable-name" :dir :system)
(include-book "kestrel/error-checking/ensure-value-is-not-in-list" :dir :system)
(include-book "kestrel/event-macros/event-generation" :dir :system)
(include-book "kestrel/event-macros/event-generation-soft" :dir :system)
(include-book "kestrel/event-macros/input-processing" :dir :system)
(include-book "kestrel/event-macros/proof-preparation" :dir :system)
(include-book "kestrel/event-macros/restore-output" :dir :system)
(include-book "kestrel/event-macros/xdoc-constructors" :dir :system)
(include-book "kestrel/soft/defequal" :dir :system)
(include-book "kestrel/std/system/fresh-logical-name-with-dollars-suffix" :dir :system)

(include-book "utilities/input-processing")
(include-book "utilities/input-processing-soft")
(include-book "utilities/transformation-table")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-implementation

 schemalg

 :items

 (xdoc::*evmac-topic-implementation-item-state*

  xdoc::*evmac-topic-implementation-item-wrld*

  xdoc::*evmac-topic-implementation-item-ctx*

  "@('old') is the homonymous input to @(tsee schemalg) when it has no type;
   otherwise, it is the function symbol denoted by that input."

  (xdoc::evmac-topic-implementation-item-input "schema" "schemalg")

  (xdoc::evmac-topic-implementation-item-input "list-input" "schemalg")

  (xdoc::evmac-topic-implementation-item-input "oset-input" "schemalg")

  (xdoc::evmac-topic-implementation-item-input "cdr-output" "schemalg")

  (xdoc::evmac-topic-implementation-item-input "tail-output" "schemalg")

  (xdoc::evmac-topic-implementation-item-input "fvar-0-name" "schemalg")

  (xdoc::evmac-topic-implementation-item-input "fvar-1-name" "schemalg")

  (xdoc::evmac-topic-implementation-item-input "algo-name" "schemalg")

  (xdoc::evmac-topic-implementation-item-input "algo-enable" "schemalg")

  (xdoc::evmac-topic-implementation-item-input "spec-0-name" "schemalg")

  (xdoc::evmac-topic-implementation-item-input "spec-0-enable" "schemalg")

  (xdoc::evmac-topic-implementation-item-input "spec-1-name" "schemalg")

  (xdoc::evmac-topic-implementation-item-input "spec-1-enable" "schemalg")

  (xdoc::evmac-topic-implementation-item-input "equal-algo-name" "schemalg")

  (xdoc::evmac-topic-implementation-item-input "equal-algo-enable" "schemalg")

  (xdoc::evmac-topic-implementation-item-input "new-name" "schemalg")

  "@('new-enable') is the homonymous input to @(tsee schemalg)
   if it has no type;
   otherwise, it is the boolean resulting from processing that input."

  (xdoc::evmac-topic-implementation-item-input "old-if-new-name" "schemalg")

  "@('old-if-new-enable') is the homonymous input to @(tsee schemalg)
   if it has no type;
   otherwise, it is the boolean resulting from processing that input."

  "@('verify-guards') is the homonymous input to @(tsee schemalg)
   if it has no type;
   otherwise, it is the boolean resulting from processing that input."

  (xdoc::evmac-topic-implementation-item-input "print" "schemalg")

  (xdoc::evmac-topic-implementation-item-input "show-only" "schemalg")

  "@('x-x1...xn') is the list of variable symbols @('(x x1 ... xn)')
   described in the user documentation."

  "@('x-a1...am') is the list of terms @('(x a1<x1,...,xn> ... am<x1,...,xn>)')
   described in the user documentation."

  "@('x-z1...zm') is the list of variable symbols @('(x z1 ... zm)')
   described in the user documentation."

  (xdoc::evmac-topic-implementation-item-var-doc "x")

  "@('y') is the variable symbol specified by the @(':cdr-output') input."

  "@('out') is a variable symbol used as
   the last formal parameter of @('iorel')."

  "@('iorel') is the lambda expression
   @('(lambda (x x1 ... xn out) iorel<x,x1,...,xn,out>)')
   described in the user documentation,
   except that the variable @('y') in the user documentation
   is replaced with the variable symbol in @('out')."

  (xdoc::evmac-topic-implementation-item-fn-doc "?f")

  "@('?f1...?fp') is the list of function symbols @('?f1'), ..., @('?fp')
   described in the user documentation."

  (xdoc::evmac-topic-implementation-item-fn-doc "?g")

  (xdoc::evmac-topic-implementation-item-fn-doc "?h")

  "@('algo') is the function symbol @('algo[?f1]...[?fp]')
   described in the user documentation."

  "@('spec1...spec1') is the list of
   function symbols @('spec1'), ..., @('specq')
   described in the user documentation."

  "@('spec-0') is the function symbol @('old-0[?g]')
   described in the user documentation."

  "@('spec-1') is the function symbol @('old-1[?h]')
   described in the user documentation."

  "@('equal-algo') is the function symbol @('equal[?f][algo[?f1]...[?fp]]')
   described in the user documentation."

  (xdoc::evmac-topic-implementation-item-fn-doc "new")

  (xdoc::evmac-topic-implementation-item-thm-doc "old-if-new")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-input-processing schemalg)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *schemalg-schemas*
  :short "Allowed values of the @(':schema') input."
  '(:divconq-list-0-1
    :divconq-oset-0-1))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define schemalg-process-schema (schema (schema? booleanp) ctx state)
  :returns (mv erp (nothing null) state)
  :short "Process the @(':schema') input."
  (if (member-eq schema *schemalg-schemas*)
      (value nil)
    (if schema?
        (er-soft+ ctx t nil
                  "The :SCHEMA input must be ~v0, ~
                   but it is ~x1 instead."
                  *schemalg-schemas* schema)
      (er-soft+ ctx t nil
                "The :SCHEMA input must be supplied."))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define schemalg-process-list-input (list-input
                                     (list-input? booleanp)
                                     (schema keywordp)
                                     (old symbolp)
                                     (?f symbolp)
                                     (x-x1...xn symbol-listp)
                                     (x-a1...am pseudo-term-listp)
                                     ctx
                                     state)
  :returns (mv erp (x symbolp) state)
  :short "Process the @(':list-input') input."
  (b* ((schemas-allowed (list :divconq-list-0-1))
       ((when (and list-input?
                   (not (member-eq schema schemas-allowed))))
        (er-soft+ ctx t nil
                  "The :LIST-INPUT input can be present only if ~
                   the :SCHEMA input is ~&0, but that input is ~x1 instead."
                  schemas-allowed schema)))
    (process-input-select-old-soft-io list-input :list-input
                                      old ?f x-x1...xn x-a1...am ctx state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define schemalg-process-oset-input (oset-input
                                     (oset-input? booleanp)
                                     (schema keywordp)
                                     (old symbolp)
                                     (?f symbolp)
                                     (x-x1...xn symbol-listp)
                                     (x-a1...am pseudo-term-listp)
                                     ctx
                                     state)
  :returns (mv erp (x symbolp) state)
  :short "Process the @(':oset-input') input."
  (b* ((schemas-allowed (list :divconq-oset-0-1))
       ((when (and oset-input?
                   (not (member-eq schema schemas-allowed))))
        (er-soft+ ctx t nil
                  "The :OSET-INPUT input can be present only if ~
                   the :SCHEMA input is ~&0, but that input is ~x1 instead."
                  schemas-allowed schema)))
    (process-input-select-old-soft-io oset-input :oset-input
                                      old ?f x-x1...xn x-a1...am ctx state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define schemalg-process-cdr-output (cdr-output
                                     (cdr-output? booleanp)
                                     (schema keywordp)
                                     (old symbolp)
                                     (x-x1...xn symbol-listp)
                                     ctx
                                     state)
  :returns (mv erp
               (y symbolp
                  :hints
                  (("Goal"
                    :in-theory
                    (enable acl2::ensure-value-is-legal-variable-name))))
               state)
  :short "Process the @(':cdr-output') input."
  (b* ((schemas-allowed (list :divconq-list-0-1))
       ((when (and cdr-output?
                   (not (member-eq schema schemas-allowed))))
        (er-soft+ ctx t nil
                  "The :CDR-OUTPUT input can be present only if ~
                   the :SCHEMA input is ~&0, but that input is ~x1 instead."
                  schemas-allowed schema))
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
                nil)))
    (value y)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define schemalg-process-tail-output (tail-output
                                      (tail-output? booleanp)
                                      (schema keywordp)
                                      (old symbolp)
                                      (x-x1...xn symbol-listp)
                                      ctx
                                      state)
  :returns (mv erp
               (y symbolp
                  :hints
                  (("Goal"
                    :in-theory
                    (enable acl2::ensure-value-is-legal-variable-name))))
               state)
  :short "Process the @(':tail-output') input."
  (b* ((schemas-allowed (list :divconq-oset-0-1))
       ((when (and tail-output?
                   (not (member-eq schema schemas-allowed))))
        (er-soft+ ctx t nil
                  "The :TAIL-OUTPUT input can be present only if ~
                   the :SCHEMA input is ~&0, but that input is ~x1 instead."
                  schemas-allowed schema))
       (y (if (eq tail-output :auto)
              (intern-in-package-of-symbol "TAIL-OUTPUT" old)
            tail-output))
       ((er &) (ensure-value-is-legal-variable-name$ y
                                                     "The :TAIL-OUTPUT input"
                                                     t
                                                     nil))
       ((er &) (ensure-value-is-not-in-list$
                y
                x-x1...xn
                (msg "one of bound variables ~x0 of ~x1" x-x1...xn old)
                "The :TAIL-OUTPUT input"
                t
                nil)))
    (value y)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-process-input-fresh-function-name
 fvar-0-name
 :macro schemalg
 :other-args ((?f symbolp))
 :auto-code (add-suffix ?f "-0"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-process-input-fresh-function-name
 fvar-1-name
 :macro schemalg
 :other-args ((?f symbolp))
 :auto-code (add-suffix ?f "-1"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-process-input-fresh-function-name
 algo-name
 :macro schemalg
 :other-args ((?f symbolp)
              (?f1...?fp symbol-listp))
 :auto-code (b* ((??f-chars (explode (symbol-name ?f)))
                 (algo-chars (if (and (consp ?f-chars)
                                      (eql (car ?f-chars) #\?))
                                 (cdr ?f-chars)
                               ?f-chars))
                 ([?f1]...[?fp]-chars
                  (schemalg-process-algo-name-aux ?f1...?fp)))
              (intern-in-package-of-symbol
               (implode (append algo-chars [?f1]...[?fp]-chars))
               ?f))
 :prepwork
 ((define schemalg-process-algo-name-aux ((?f1...?fp symbol-listp))
    :returns ([?f1]...[?fp]-chars)
    ;; use this above eventually and avoid this auxiliary function:
    ;; (loop$ for ?fk in ?f1...?fp
    ;;        append (append (list #\[)
    ;;                       (explode (symbol-name ?fk))
    ;;                       (list #\])))
    (cond ((endp ?f1...?fp) nil)
          (t (append (list #\[)
                     (explode (symbol-name (car ?f1...?fp)))
                     (list #\])
                     (schemalg-process-algo-name-aux (cdr ?f1...?fp))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-process-input-fresh-function-name
 spec-0-name
 :macro schemalg
 :other-args ((old symbolp)
              (?g symbolp))
 :auto-code (packn-pos (list old "-0" "[" ?g "]") old))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-process-input-fresh-function-name
 spec-1-name
 :macro schemalg
 :other-args ((old symbolp)
              (?h symbolp))
 :auto-code (packn-pos (list old "-1" "[" ?h "]") old))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-process-input-fresh-function-name
 equal-algo-name
 :macro schemalg
 :other-args ((?f symbolp)
              (algo symbolp))
 :auto-code (packn-pos (list "EQUAL[" ?f "][" algo "]") ?f))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ schemalg-check-allowed-input (input? &rest schemas-allowed)
  (declare (xargs :guard (and (symbolp input?)
                              (keyword-listp schemas-allowed))))
  :short "Check whether an input is allowed for the current schema."
  :long
  (xdoc::topstring
   (xdoc::p
    "This macro produces a term,
     to be bound to @('(er &)') in a @(tsee b*),
     that checks whether, if an input is present,
     the keyword in the variable @('schema')
     is among a list of allowed schemas.
     The @('input?') argument must be the a variable
     that contains the boolean flag saying whether a certain input
     is present or not;
     the name of this variable must be the name of the input
     followed by a @('?').
     The @('schemas-allowed') arguments must be schemas
     for which the input is question may be present."))
  `(if (and ,input?
            (not (member-eq schema (list ,@schemas-allowed))))
       (er-soft+ ctx t nil
                 "The ~x0 input can be present only if ~
                  the :SCHEMA input is ~&1, but that input is ~x2 instead."
                 ,(b* ((input?-string (symbol-name input?))
                       (input-string (subseq input?-string
                                             0
                                             (1- (length input?-string)))))
                    (intern input-string "KEYWORD"))
                 (list ,@schemas-allowed)
                 schema)
     (value nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define schemalg-process-inputs (old
                                 schema (schema? booleanp)
                                 list-input (list-input? booleanp)
                                 oset-input (oset-input? booleanp)
                                 cdr-output (cdr-output? booleanp)
                                 tail-output (tail-output? booleanp)
                                 fvar-0-name (fvar-0-name? booleanp)
                                 fvar-1-name (fvar-1-name? booleanp)
                                 algo-name
                                 algo-enable
                                 spec-0-name (spec-0-name? booleanp)
                                 spec-0-enable (spec-0-enable? booleanp)
                                 spec-1-name (spec-1-name? booleanp)
                                 spec-1-enable (spec-1-enable? booleanp)
                                 equal-algo-name
                                 equal-algo-enable
                                 new-name
                                 new-enable
                                 old-if-new-name (old-if-new-name? booleanp)
                                 old-if-new-enable (old-if-new-enable? booleanp)
                                 verify-guards
                                 print
                                 show-only
                                 ctx
                                 state)
  :returns (mv erp
               (result "A @('(tuple (old$ symbolp)
                                    (?f symbolp)
                                    (x-x1...xn symbolp)
                                    (x-a1...am symbolp)
                                    (out symbolp)
                                    (iorel pseudo-lambdap)
                                    (x symbolp)
                                    (y symbolp)
                                    (?g symbolp)
                                    (?h symbolp)
                                    (also symbolp)
                                    (spec-0 symbolp)
                                    (spec-1 symbolp)
                                    (equal-algo symbolp)
                                    (new symbolp)
                                    (new-enable$ booleanp)
                                    (old-if-new symbolp)
                                    (old-if-new-enable$ booleanp)
                                    (verify-guards$ booleanp)
                                    (updated-names-to-avoid symbol-listp))').")
               state)
  :mode :program
  :short "Process all the inputs."
  (b* ((names-to-avoid nil)
       ((er (list old ??f x-x1...xn x-a1...am out iorel))
        (process-input-old-soft-io-sel-mod old verify-guards ctx state))
       ((er &) (schemalg-process-schema schema schema? ctx state))
       ((er &) (schemalg-check-allowed-input list-input? :divconq-list-0-1))
       ((er &) (schemalg-check-allowed-input oset-input? :divconq-oset-0-1))
       ((er x) (case schema
                 (:divconq-list-0-1 (schemalg-process-list-input
                                     list-input list-input?
                                     schema old ?f x-x1...xn x-a1...am
                                     ctx state))
                 (:divconq-oset-0-1 (schemalg-process-oset-input
                                     oset-input oset-input?
                                     schema old ?f x-x1...xn x-a1...am
                                     ctx state))
                 (t (value
                     (raise "Internal error: unknown schema ~x0." schema)))))
       ((er &) (schemalg-check-allowed-input cdr-output? :divconq-list-0-1))
       ((er &) (schemalg-check-allowed-input tail-output? :divconq-oset-0-1))
       ((er y) (case schema
                 (:divconq-list-0-1 (schemalg-process-cdr-output
                                     cdr-output cdr-output?
                                     schema old x-x1...xn
                                     ctx state))
                 (:divconq-oset-0-1 (schemalg-process-tail-output
                                     tail-output tail-output?
                                     schema old x-x1...xn
                                     ctx state))
                 (t (value
                     (raise "Internal error: unknown schema ~x0." schema)))))
       ((er &) (schemalg-check-allowed-input fvar-0-name?
                                             :divconq-list-0-1
                                             :divconq-oset-0-1))
       ((er (list ??g names-to-avoid))
        (schemalg-process-fvar-0-name fvar-0-name
                                      ?f names-to-avoid ctx state))
       ((er &) (schemalg-check-allowed-input fvar-1-name?
                                             :divconq-list-0-1
                                             :divconq-oset-0-1))
       ((er (list ??h names-to-avoid))
        (schemalg-process-fvar-1-name fvar-1-name
                                      ?f names-to-avoid ctx state))
       ((er (list algo names-to-avoid))
        (schemalg-process-algo-name algo-name
                                    ?f (list ?g ?h) names-to-avoid ctx state))
       ((er &) (ensure-value-is-boolean$ algo-enable
                                         "The :ALGO-ENABLE input"
                                         t
                                         nil))
       ((er &) (schemalg-check-allowed-input spec-0-name?
                                             :divconq-list-0-1
                                             :divconq-oset-0-1))
       ((er (list spec-0 names-to-avoid))
        (schemalg-process-spec-0-name spec-0-name
                                      old ?g names-to-avoid ctx state))
       ((er &) (schemalg-check-allowed-input spec-0-enable?
                                             :divconq-list-0-1
                                             :divconq-oset-0-1))
       ((er &) (ensure-value-is-boolean$ spec-0-enable
                                         "The :SPEC-0-ENABLE input"
                                         t
                                         nil))
       ((er &) (schemalg-check-allowed-input spec-1-name?
                                             :divconq-list-0-1
                                             :divconq-oset-0-1))
       ((er (list spec-1 names-to-avoid))
        (schemalg-process-spec-1-name spec-1-name
                                      old ?h names-to-avoid ctx state))
       ((er &) (schemalg-check-allowed-input spec-1-enable?
                                             :divconq-list-0-1
                                             :divconq-oset-0-1))
       ((er &) (ensure-value-is-boolean$ spec-1-enable
                                         "The :SPEC-1-ENABLE input"
                                         t
                                         nil))
       ((er (list equal-algo names-to-avoid))
        (schemalg-process-equal-algo-name equal-algo-name
                                          ?f algo names-to-avoid ctx state))
       ((er &) (ensure-value-is-boolean$ equal-algo-enable
                                         "The :EQUAL-ALGO-ENABLE input"
                                         t
                                         nil))
       ((er (list new names-to-avoid))
        (process-input-new-name new-name
                                old names-to-avoid ctx state))
       ((er new-enable) (process-input-new-enable new-enable old ctx state))
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
       ((er verify-guards) (process-input-verify-guards verify-guards
                                                        old
                                                        ctx
                                                        state))
       ((er &) (evmac-process-input-print print ctx state))
       ((er &) (evmac-process-input-show-only show-only ctx state)))
    (value (list old
                 ?f
                 x-x1...xn
                 x-a1...am
                 out
                 iorel
                 x
                 y
                 ?g
                 ?h
                 algo
                 spec-0
                 spec-1
                 equal-algo
                 new
                 new-enable
                 old-if-new
                 old-if-new-enable
                 verify-guards
                 names-to-avoid))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-event-generation schemalg
                                    :some-local-nonlocal-p t
                                    :some-local-p t
                                    :some-nonlocal-p t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define schemalg-gen-?f1...?fp ((schema keywordp)
                                (?g symbolp)
                                (?h symbolp)
                                (x-a1...am pseudo-term-listp))
  :returns (events pseudo-event-form-listp)
  :short "Generate the function variables @('?f1'), ..., @('?fp')."
  (case schema
    ((:divconq-list-0-1
      :divconq-oset-0-1)
     (list (evmac-generate-soft-defunvar ?g (len x-a1...am))
           (evmac-generate-soft-defunvar ?h (1+ (len x-a1...am)))))
    (t (raise "Internal error: unknown schema ~x0." schema))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define schemalg-gen-x-z1...zm ((x-a1...am pseudo-term-listp)
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
  (schemalg-gen-x-z1...zm-aux x-a1...am
                              nil
                              x-a1...am
                              x-x1...xn
                              x
                              y)

  :prepwork
  ((define schemalg-gen-x-z1...zm-aux ((terms-to-do pseudo-term-listp)
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
       (cons var (schemalg-gen-x-z1...zm-aux (cdr terms-to-do)
                                             (cons var vars-done)
                                             x-a1...am
                                             x-x1...xn
                                             x
                                             y))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define schemalg-gen-algo-divconq-list-0-1 ((algo symbolp)
                                            (algo-enable booleanp)
                                            (x-z1...zm symbol-listp)
                                            (x symbolp)
                                            (?g symbolp)
                                            (?h symbolp)
                                            (verify-guards booleanp))
  :returns (mv (local-event pseudo-event-formp)
               (exported-event pseudo-event-formp))
  :short "Generate the function @('algo[?g][?h]')
          for the @(':divconq-list-0-1') schema."
  (b* ((car-x-z1...zm (loop$ for var of-type symbol in x-z1...zm
                             collect (if (eq var x) (list 'car var) var)))
       (cdr-x-z1...zm (loop$ for var of-type symbol in x-z1...zm
                             collect (if (eq var x) (list 'cdr var) var))))
    (evmac-generate-soft-defun2
     algo
     :formals x-z1...zm
     :body `(cond ((atom ,x) (,?g ,@x-z1...zm))
                  (t (,?h ,@car-x-z1...zm
                          (,algo ,@cdr-x-z1...zm))))
     :verify-guards verify-guards
     :enable algo-enable
     :measure `(acl2-count ,x)
     :hints '(("Goal" :in-theory nil))
     :guard-hints '(("Goal" :in-theory nil)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define schemalg-gen-algo-divconq-oset-0-1 ((algo symbolp)
                                            (algo-enable booleanp)
                                            (x-z1...zm symbol-listp)
                                            (x symbolp)
                                            (?g symbolp)
                                            (?h symbolp)
                                            (verify-guards booleanp))
  :returns (mv (local-event pseudo-event-formp)
               (exported-event pseudo-event-formp))
  :short "Generate the function @('algo[?g][?h]')
          for the @(':divconq-oset-0-1') schema."
  (b* ((head-x-z1...zm (loop$ for var of-type symbol in x-z1...zm
                              collect (if (eq var x)
                                          (list 'set::head var)
                                        var)))
       (tail-x-z1...zm (loop$ for var of-type symbol in x-z1...zm
                              collect (if (eq var x)
                                          (list 'set::tail var)
                                        var))))
    (evmac-generate-soft-defun2
     algo
     :formals x-z1...zm
     :body `(cond ((or (not (set::setp ,x))
                       (set::empty ,x))
                   (,?g ,@x-z1...zm))
                  (t (,?h ,@head-x-z1...zm
                          (,algo ,@tail-x-z1...zm))))
     :verify-guards verify-guards
     :enable algo-enable
     :measure `(acl2-count ,x)
     :hints '(("Goal" :in-theory '(set::tail-count-built-in)))
     :guard-hints '(("Goal" :in-theory nil)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define schemalg-gen-algo ((schema keywordp)
                           (algo symbolp)
                           (algo-enable booleanp)
                           (x-z1...zm symbol-listp)
                           (x symbolp)
                           (?g symbolp)
                           (?h symbolp)
                           (verify-guards booleanp))
  :returns (mv (local-event pseudo-event-formp)
               (exported-event pseudo-event-formp))
  :short "Generate the function @('algo[?f1]...[?fp]')."
  (case schema
    (:divconq-list-0-1 (schemalg-gen-algo-divconq-list-0-1 algo
                                                           algo-enable
                                                           x-z1...zm
                                                           x
                                                           ?g
                                                           ?h
                                                           verify-guards))
    (:divconq-oset-0-1 (schemalg-gen-algo-divconq-oset-0-1 algo
                                                           algo-enable
                                                           x-z1...zm
                                                           x
                                                           ?g
                                                           ?h
                                                           verify-guards))
    (t (prog2$ (raise "Internal error: unknown schema ~x0." schema)
               (mv '(irrelevant) '(irrelevant))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define schemalg-gen-spec-0-divconq-list-0-1 ((spec-0 symbolp)
                                              (spec-0-enable booleanp)
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
  :short "Generate the function @('spec-0[?g]')
          for the @(':divconq-list-0-1') schema."
  (b* ((iorel-term (apply-term iorel
                               (append x-x1...xn (list `(,?g ,@x-a1...am))))))
    (evmac-generate-soft-defun-sk2
     spec-0
     :formals ()
     :guard t
     :body `(forall ,x-x1...xn
                    (impliez (atom ,x) ,iorel-term))
     :verify-guards verify-guards
     :enable spec-0-enable
     :guard-hints `(("Goal" :use (:guard-theorem ,old))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define schemalg-gen-spec-0-divconq-oset-0-1 ((spec-0 symbolp)
                                              (spec-0-enable booleanp)
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
  :short "Generate the function @('spec-0[?g]')
          for the @(':divconq-oset-0-1') schema."
  (b* ((iorel-term (apply-term iorel
                               (append x-x1...xn (list `(,?g ,@x-a1...am))))))
    (evmac-generate-soft-defun-sk2
     spec-0
     :formals ()
     :guard t
     :body `(forall ,x-x1...xn
                    (impliez (or (not (set::setp ,x))
                                 (set::empty ,x))
                             ,iorel-term))
     :verify-guards verify-guards
     :enable spec-0-enable
     :guard-hints `(("Goal" :use (:guard-theorem ,old))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define schemalg-gen-spec-0 ((schema keywordp)
                             (spec-0 symbolp)
                             (spec-0-enable booleanp)
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
  :short "Generate the function @('spec-0[?g]')."
  (case schema
    (:divconq-list-0-1 (schemalg-gen-spec-0-divconq-list-0-1 spec-0
                                                             spec-0-enable
                                                             old
                                                             x-x1...xn
                                                             x-a1...am
                                                             x
                                                             iorel
                                                             ?g
                                                             verify-guards))
    (:divconq-oset-0-1 (schemalg-gen-spec-0-divconq-oset-0-1 spec-0
                                                             spec-0-enable
                                                             old
                                                             x-x1...xn
                                                             x-a1...am
                                                             x
                                                             iorel
                                                             ?g
                                                             verify-guards))
    (t (prog2$ (raise "Internal error: unknown schema ~x0." schema)
               (mv '(irrelevant) '(irrelevant))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define schemalg-gen-spec-1-divconq-list-0-1 ((spec-1 symbolp)
                                              (spec-1-enable booleanp)
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
  :short "Generate the function @('spec-cons[?h]')
          for the @(':divconq-list-0-1') schema."
  (b* ((cdr-x-x1...xn (loop$ for var in x-x1...xn
                             collect (if (eq var x) (list 'cdr var) var)))
       (car-x-a1...am (loop$ for var in x-a1...am
                             collect (if (eq var x) (list 'car var) var)))
       (iorel-term1 (apply-term iorel (append cdr-x-x1...xn (list y))))
       (iorel-term2 (apply-term iorel (append x-x1...xn
                                              (list
                                               `(,?h ,@car-x-a1...am ,y))))))
    (evmac-generate-soft-defun-sk2
     spec-1
     :formals ()
     :guard t
     :body `(forall (,@x-x1...xn ,y)
                    (impliez (and (consp ,x) ,iorel-term1)
                             ,iorel-term2))
     :verify-guards verify-guards
     :enable spec-1-enable
     :guard-hints `(("Goal" :use (:guard-theorem ,old))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define schemalg-gen-spec-1-divconq-oset-0-1 ((spec-1 symbolp)
                                              (spec-1-enable booleanp)
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
  :short "Generate the function @('spec-cons[?h]')
          for the @(':divconq-oset-0-1') schema."
  (b* ((tail-x-x1...xn (loop$ for var in x-x1...xn
                              collect (if (eq var x)
                                          (list 'set::tail var)
                                        var)))
       (head-x-a1...am (loop$ for var in x-a1...am
                              collect (if (eq var x)
                                          (list 'set::head var)
                                        var)))
       (iorel-term1 (apply-term iorel (append tail-x-x1...xn (list y))))
       (iorel-term2 (apply-term iorel (append x-x1...xn
                                              (list
                                               `(,?h ,@head-x-a1...am ,y))))))
    (evmac-generate-soft-defun-sk2
     spec-1
     :formals ()
     :guard t
     :body `(forall (,@x-x1...xn ,y)
                    (impliez (and (set::setp ,x)
                                  (not (set::empty ,x))
                                  ,iorel-term1)
                             ,iorel-term2))
     :verify-guards verify-guards
     :enable spec-1-enable
     :guard-hints `(("Goal" :use (:guard-theorem ,old))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define schemalg-gen-spec-1 ((schema keywordp)
                             (spec-1 symbolp)
                             (spec-1-enable booleanp)
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
  :short "Generate the function @('spec-1[?h]')."
  (case schema
    (:divconq-list-0-1 (schemalg-gen-spec-1-divconq-list-0-1 spec-1
                                                             spec-1-enable
                                                             old
                                                             x-x1...xn
                                                             x-a1...am
                                                             x
                                                             y
                                                             iorel
                                                             ?h
                                                             verify-guards))
    (:divconq-oset-0-1 (schemalg-gen-spec-1-divconq-oset-0-1 spec-1
                                                             spec-1-enable
                                                             old
                                                             x-x1...xn
                                                             x-a1...am
                                                             x
                                                             y
                                                             iorel
                                                             ?h
                                                             verify-guards))
    (t (prog2$ (raise "Internal error: unknown schema ~x0." schema)
               (mv '(irrelevant) '(irrelevant))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define schemalg-gen-equal-algo ((equal-algo symbolp)
                                 (equal-algo-enable booleanp)
                                 (vars symbol-listp)
                                 (?f symbolp)
                                 (algo symbolp)
                                 (print evmac-input-print-p))
  :returns (event pseudo-event-formp)
  :short "Generate the function @('equal[?f][algo[?f1]...[?fp]]')."
  :long
  (xdoc::topstring
   (xdoc::p
    "Unless the @(':print') input of @(tsee schemalg) is @(':all'),
     we pass @(':print nil') to @(tsee soft::defequal),
     to avoid showing its expansion on the screen (see @(tsee soft::defequal)).
     Instead, the code in @(tsee schemalg-gen-everything)
     shows the @(tsee soft::defequal) form itself
     (if @(tsee schemalg)'s @(':print') is at least @(':result')).")
   (xdoc::p
    "We do not expect this @(tsee soft::defequal) event to fail
     (it would be an internal/implementation error if it did).
     So there is no need to pass @(':print :error').
     If the event actually fails, then it can be debugged
     by passing @(':all') to @(tsee schemalg),
     which in this cases also passes it to @(tsee soft::equal),
     or by passing @(':show-only t') to @(tsee schemalg)
     and examining/trying the resulting expansion."))
  `(soft::defequal ,equal-algo
                   :left ,?f
                   :right ,algo
                   :vars ,vars
                   :enable ,equal-algo-enable
                   :left-to-right-enable ,equal-algo-enable
                   :right-to-left-enable ,equal-algo-enable
                   :print ,(and (eq print :all) :all)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define schemalg-gen-new ((new symbolp)
                          (new-enable booleanp)
                          (spec1...specq symbol-listp)
                          (equal-algo symbolp)
                          (verify-guards booleanp))
  :returns (mv (local-event pseudo-event-formp)
               (exported-event pseudo-event-formp))
  :short "Generate the function @('new')."
  (b* ((spec1...specq-calls
        (loop$ for spec in spec1...specq collect (list spec))))
    (evmac-generate-soft-defun2 new
                                :formals ()
                                :guard t
                                :body `(and (,equal-algo)
                                            ,@spec1...specq-calls)
                                :verify-guards verify-guards
                                :enable new-enable
                                :guard-hints '(("Goal" :in-theory nil)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define schemalg-gen-algo-correct-divconq-list-0-1
  ((x-x1...xn symbol-listp)
   (x-a1...am symbol-listp)
   (x symbolp)
   (y symbolp)
   (iorel pseudo-lambdap)
   (algo symbolp)
   (spec-0 symbolp)
   (spec-1 symbolp)
   (names-to-avoid symbol-listp)
   (wrld plist-worldp))
  :returns (mv (event "A @(tsee pseudo-event-formp).")
               (name "A @(tsee symbolp).")
               (updated-names-to-avoid "A @(tsee symbol-listp)."))
  :mode :program
  :short "Generate a local theorem asserting
          the correctness of @('algo[?f1]...[?fp]')
          for the @(':divconq-list-0-1') schema."
  (b* (((mv name names-to-avoid)
        (fresh-logical-name-with-$s-suffix 'algo-correct
                                           nil
                                           names-to-avoid
                                           wrld))
       (iorel-term (apply-term iorel
                               (append x-x1...xn (list `(,algo ,@x-a1...am)))))
       (spec-0-necc (add-suffix spec-0 "-NECC"))
       (spec-1-necc (add-suffix spec-1 "-NECC"))
       (cdr-x-a1...am (loop$ for var in x-a1...am
                             collect (if (eq var x) (list 'cdr var) var)))
       (hints `(("Goal"
                 :in-theory '(len atom ,algo)
                 :induct (len ,x))
                '(:use (,spec-0-necc
                        (:instance ,spec-1-necc
                         (,y (,algo ,@cdr-x-a1...am)))))))
       (event
        `(local
          (defthm ,name
            (implies (and (,spec-0)
                          (,spec-1))
                     ,iorel-term)
            :rule-classes nil
            :hints ,hints))))
    (mv event name names-to-avoid)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define schemalg-gen-algo-correct-divconq-oset-0-1
  ((x-x1...xn symbol-listp)
   (x-a1...am symbol-listp)
   (x symbolp)
   (y symbolp)
   (iorel pseudo-lambdap)
   (algo symbolp)
   (spec-0 symbolp)
   (spec-1 symbolp)
   (names-to-avoid symbol-listp)
   (wrld plist-worldp))
  :returns (mv (event "A @(tsee pseudo-event-formp).")
               (name "A @(tsee symbolp).")
               (updated-names-to-avoid "A @(tsee symbol-listp)."))
  :mode :program
  :short "Generate a local theorem asserting
          the correctness of @('algo[?f1]...[?fp]')
          for the @(':divconq-oset-0-1') schema."
  (b* (((mv name names-to-avoid)
        (fresh-logical-name-with-$s-suffix 'algo-correct
                                           nil
                                           names-to-avoid
                                           wrld))
       (iorel-term (apply-term iorel
                               (append x-x1...xn (list `(,algo ,@x-a1...am)))))
       (spec-0-necc (add-suffix spec-0 "-NECC"))
       (spec-1-necc (add-suffix spec-1 "-NECC"))
       (tail-x-a1...am (loop$ for var in x-a1...am
                              collect (if (eq var x)
                                          (list 'set::tail var)
                                        var)))
       (hints `(("Goal"
                 :in-theory '(,algo)
                 :induct (,algo ,@x-a1...am))
                '(:use (,spec-0-necc
                        (:instance ,spec-1-necc
                         (,y (,algo ,@tail-x-a1...am)))))))
       (event
        `(local
          (defthm ,name
            (implies (and (,spec-0)
                          (,spec-1))
                     ,iorel-term)
            :rule-classes nil
            :hints ,hints))))
    (mv event name names-to-avoid)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define schemalg-gen-algo-correct ((schema keywordp)
                                   (x-x1...xn symbol-listp)
                                   (x-a1...am symbol-listp)
                                   (x symbolp)
                                   (y symbolp)
                                   (iorel pseudo-lambdap)
                                   (algo symbolp)
                                   (spec-0 symbolp)
                                   (spec-1 symbolp)
                                   (names-to-avoid symbol-listp)
                                   (wrld plist-worldp))
  :returns (mv (event "A @(tsee pseudo-event-formp).")
               (name "A @(tsee symbolp).")
               (updated-names-to-avoid "A @(tsee symbol-listp)."))
  :mode :program
  :short "Generate a local theorem asserting
          the correctness of @('algo[?f1]...[?fp]')."
  :long
  (xdoc::topstring-p
   "This is the theorem @($\\mathit{COR}$) in the design notes.
    It is not described in the user documentation,
    because it is generated only locally.")
  (case schema
    (:divconq-list-0-1
     (schemalg-gen-algo-correct-divconq-list-0-1 x-x1...xn
                                                 x-a1...am
                                                 x
                                                 y
                                                 iorel
                                                 algo
                                                 spec-0
                                                 spec-1
                                                 names-to-avoid
                                                 wrld))
    (:divconq-oset-0-1
     (schemalg-gen-algo-correct-divconq-oset-0-1 x-x1...xn
                                                 x-a1...am
                                                 x
                                                 y
                                                 iorel
                                                 algo
                                                 spec-0
                                                 spec-1
                                                 names-to-avoid
                                                 wrld))
    (t (prog2$ (raise "Internal error: unknown schema ~x0." schema)
               (mv '(irrelevant) nil names-to-avoid)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define schemalg-gen-old-if-new ((old-if-new symbolp)
                                 (old-if-new-enable booleanp)
                                 (old symbolp)
                                 (?f symbolp)
                                 (x-x1...xn symbol-listp)
                                 (x-z1...zm symbol-listp)
                                 (x-a1...am symbol-listp)
                                 (x symbolp)
                                 (equal-algo symbolp)
                                 (new symbolp)
                                 (algo symbolp)
                                 (algo-correct symbolp))
  :returns (mv (local-event pseudo-event-formp)
               (exported-event pseudo-event-formp))
  :verify-guards nil
  :short "Generate the theorem @('old-if-new')."
  (b* ((formula `(implies (,new) (,old)))
       (old-witness (add-suffix-to-fn old "-WITNESS"))
       (equal-algo-l2r (packn-pos (list ?f '-to- algo) equal-algo))
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
                 :use ((:instance ,equal-algo-l2r ,@x-z1...zm-instantiation)
                       (:instance ,algo-correct ,@x-x1...xn-instantiation))))))
    (evmac-generate-defthm old-if-new
                           :formula formula
                           :hints hints
                           :enable old-if-new-enable)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define schemalg-gen-everything ((old symbolp)
                                 (?f symbolp)
                                 (x-x1...xn symbol-listp)
                                 (x-a1...am pseudo-term-listp)
                                 (x symbolp)
                                 (y symbolp)
                                 (iorel pseudo-lambdap)
                                 (schema keywordp)
                                 (?g symbolp)
                                 (?h symbolp)
                                 (algo symbolp)
                                 (algo-enable booleanp)
                                 (spec-0 symbolp)
                                 (spec-0-enable booleanp)
                                 (spec-1 symbolp)
                                 (spec-1-enable booleanp)
                                 (equal-algo symbolp)
                                 (equal-algo-enable booleanp)
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
  (b* ((spec1...specq (case schema
                        (:divconq-list-0-1 (list spec-0 spec-1))
                        (:divconq-oset-0-1 (list spec-0 spec-1))
                        (t (raise "Internal error: unknown schema ~x0."
                                  schema))))
       (??f1...?fp-events (schemalg-gen-?f1...?fp schema ?g ?h x-a1...am))
       (x-z1...zm
        (case schema
          (:divconq-list-0-1 (schemalg-gen-x-z1...zm x-a1...am x-x1...xn x y))
          (:divconq-oset-0-1 (schemalg-gen-x-z1...zm x-a1...am x-x1...xn x y))
          (t (raise "Internal error: unknown schema ~x0." schema))))
       ((mv algo-local-event
            algo-exported-event)
        (schemalg-gen-algo
         schema algo algo-enable x-z1...zm x ?g ?h verify-guards))
       ((mv spec-0-local-event
            spec-0-exported-event)
        (schemalg-gen-spec-0 schema spec-0 spec-0-enable
                             old x-x1...xn x-a1...am x
                             iorel ?g verify-guards))
       ((mv spec-1-local-event
            spec-1-exported-event)
        (schemalg-gen-spec-1 schema spec-1 spec-1-enable
                             old x-x1...xn x-a1...am x y
                             iorel ?h verify-guards))
       (equal-algo-event
        (schemalg-gen-equal-algo equal-algo equal-algo-enable
                                 x-z1...zm ?f algo
                                 print))
       ((mv new-local-event
            new-exported-event)
        (schemalg-gen-new new new-enable
                          spec1...specq equal-algo verify-guards))
       ((mv algo-correct-event algo-correct &)
        (schemalg-gen-algo-correct schema x-x1...xn x-a1...am x y
                                   iorel algo spec-0 spec-1
                                   names-to-avoid wrld))
       ((mv old-if-new-local-event
            old-if-new-exported-event)
        (schemalg-gen-old-if-new old-if-new old-if-new-enable old ?f
                                 x-x1...xn x-z1...zm x-a1...am x
                                 equal-algo new algo algo-correct))
       (encapsulate-events
        `((logic)
          (evmac-prepare-proofs)
          ,@?f1...?fp-events
          ,algo-local-event
          ,algo-exported-event
          ,spec-0-local-event
          ,spec-0-exported-event
          ,spec-1-local-event
          ,spec-1-exported-event
          ,equal-algo-event
          ,new-local-event
          ,new-exported-event
          ,algo-correct-event
          ,old-if-new-local-event
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
                        (cw-event "~x0~|" ',algo-exported-event)
                        (cw-event "~x0~|" ',spec-0-exported-event)
                        (cw-event "~x0~|" ',spec-1-exported-event)
                        (cw-event "~x0~|" ',equal-algo-event)
                        (cw-event "~x0~|" ',new-exported-event)
                        (cw-event "~x0~|" ',old-if-new-exported-event)))))
    `(progn
       ,encapsulate+
       ,transformation-table-event
       ,@print-result
       (value-triple :invisible))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define schemalg-fn (old
                     schema (schema? booleanp)
                     list-input (list-input? booleanp)
                     oset-input (oset-input? booleanp)
                     cdr-output (cdr-output? booleanp)
                     tail-output (tail-output? booleanp)
                     fvar-0-name (fvar-0-name? booleanp)
                     fvar-1-name (fvar-1-name? booleanp)
                     algo-name
                     algo-enable
                     spec-0-name (spec-0-name? booleanp)
                     spec-0-enable (spec-0-enable? booleanp)
                     spec-1-name (spec-1-name? booleanp)
                     spec-1-enable (spec-1-enable? booleanp)
                     equal-algo-name
                     equal-algo-enable
                     new-name
                     new-enable
                     old-if-new-name (old-if-new-name? booleanp)
                     old-if-new-enable (old-if-new-enable? booleanp)
                     verify-guards
                     print
                     show-only
                     (call pseudo-event-formp)
                     ctx
                     state)
  :returns (mv erp (event "A @(tsee pseudo-event-formp).") state)
  :mode :program
  :parents (schemalg-implementation)
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
                  & ; OUT
                  iorel
                  x
                  y
                  ??g
                  ??h
                  algo
                  spec-0
                  spec-1
                  equal-algo
                  new
                  new-enable
                  old-if-new
                  old-if-new-enable
                  verify-guards
                  names-to-avoid))
        (schemalg-process-inputs old
                                 schema schema?
                                 list-input list-input?
                                 oset-input oset-input?
                                 cdr-output cdr-output?
                                 tail-output tail-output?
                                 fvar-0-name fvar-0-name?
                                 fvar-1-name fvar-1-name?
                                 algo-name
                                 algo-enable
                                 spec-0-name spec-0-name?
                                 spec-0-enable spec-0-enable?
                                 spec-1-name spec-1-name?
                                 spec-1-enable spec-1-enable?
                                 equal-algo-name
                                 equal-algo-enable
                                 new-name
                                 new-enable
                                 old-if-new-name old-if-new-name?
                                 old-if-new-enable old-if-new-enable?
                                 verify-guards
                                 print
                                 show-only
                                 ctx
                                 state))
       (event (schemalg-gen-everything old
                                       ?f
                                       x-x1...xn
                                       x-a1...am
                                       x
                                       y
                                       iorel
                                       schema
                                       ?g
                                       ?h
                                       algo
                                       algo-enable
                                       spec-0
                                       spec-0-enable
                                       spec-1
                                       spec-1-enable
                                       equal-algo
                                       equal-algo-enable
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

(defsection schemalg-macro-definition
  :parents (schemalg-implementation)
  :short "Definition of the @(tsee schemalg) macro."
  :long
  (xdoc::topstring
   (xdoc::p
    "Submit the event form generated by @(tsee schemalg-fn).")
   (xdoc::@def "schemalg"))
  (defmacro schemalg (&whole
                      call
                      old
                      &key
                      (schema ':no-default schema?)
                      (list-input ':auto list-input?)
                      (oset-input ':auto oset-input?)
                      (cdr-output ':auto cdr-output?)
                      (tail-output ':auto tail-output?)
                      (fvar-0-name ':auto fvar-0-name?)
                      (fvar-1-name ':auto fvar-1-name?)
                      (algo-name ':auto)
                      (algo-enable 'nil)
                      (spec-0-name ':auto spec-0-name?)
                      (spec-0-enable 'nil spec-0-enable?)
                      (spec-1-name ':auto spec-1-name?)
                      (spec-1-enable 'nil spec-1-enable?)
                      (equal-algo-name ':auto)
                      (equal-algo-enable 'nil)
                      (new-name ':auto)
                      (new-enable ':auto)
                      (old-if-new-name ':no-default old-if-new-name?)
                      (old-if-new-enable ':no-default old-if-new-enable?)
                      (verify-guards ':auto)
                      (print ':result)
                      (show-only 'nil))
    `(make-event-terse (schemalg-fn ',old
                                    ',schema ',schema?
                                    ',list-input ',list-input?
                                    ',oset-input ',oset-input?
                                    ',cdr-output ',cdr-output?
                                    ',tail-output ',tail-output?
                                    ',fvar-0-name ',fvar-0-name?
                                    ',fvar-1-name ',fvar-1-name?
                                    ',algo-name
                                    ',algo-enable
                                    ',spec-0-name ',spec-0-name?
                                    ',spec-0-enable ',spec-0-enable?
                                    ',spec-1-name ',spec-1-name?
                                    ',spec-1-enable ',spec-1-enable?
                                    ',equal-algo-name
                                    ',equal-algo-enable
                                    ',new-name
                                    ',new-enable
                                    ',old-if-new-name ',old-if-new-name?
                                    ',old-if-new-enable ',old-if-new-enable?
                                    ',verify-guards
                                    ',print
                                    ',show-only
                                    ',call
                                    (cons 'schemalg ',old)
                                    state)
                       :suppress-errors ,(not print))))
