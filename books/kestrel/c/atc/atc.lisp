; C Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2021 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "abstract-syntax")
(include-book "pretty-printer" :ttags ((:open-output-channel!)))
(include-book "static-semantics")
(include-book "dynamic-semantics")
(include-book "exec-limit-theorems")
(include-book "proof-support")

(include-book "kestrel/error-checking/ensure-function-is-defined" :dir :system)
(include-book "kestrel/error-checking/ensure-function-is-guard-verified" :dir :system)
(include-book "kestrel/error-checking/ensure-function-is-logic-mode" :dir :system)
(include-book "kestrel/error-checking/ensure-symbol-is-fresh-event-name" :dir :system)
(include-book "kestrel/error-checking/ensure-value-is-boolean" :dir :system)
(include-book "kestrel/error-checking/ensure-value-is-function-name" :dir :system)
(include-book "kestrel/error-checking/ensure-value-is-string" :dir :system)
(include-book "kestrel/error-checking/ensure-value-is-symbol" :dir :system)
(include-book "kestrel/event-macros/cw-event" :dir :system)
(include-book "kestrel/event-macros/event-generation" :dir :system)
(include-book "kestrel/event-macros/evmac-input-print-p" :dir :system)
(include-book "kestrel/event-macros/input-processing" :dir :system)
(include-book "kestrel/event-macros/make-event-terse" :dir :system)
(include-book "kestrel/event-macros/xdoc-constructors" :dir :system)
(include-book "kestrel/std/system/check-if-call" :dir :system)
(include-book "kestrel/std/system/check-lambda-call" :dir :system)
(include-book "kestrel/std/system/check-mbt-call" :dir :system)
(include-book "kestrel/std/system/check-mbt-dollar-call" :dir :system)
(include-book "kestrel/std/system/formals-plus" :dir :system)
(include-book "kestrel/std/system/fresh-logical-name-with-dollars-suffix" :dir :system)
(include-book "kestrel/std/system/maybe-pseudo-event-formp" :dir :system)
(include-book "kestrel/std/system/table-alist-plus" :dir :system)
(include-book "kestrel/std/system/ubody-plus" :dir :system)
(include-book "kestrel/std/system/uguard-plus" :dir :system)
(include-book "kestrel/std/util/tuple" :dir :system)
(include-book "oslib/dirname" :dir :system)
(include-book "oslib/file-types" :dir :system)
(include-book "tools/trivial-ancestors-check" :dir :system)

(local (include-book "kestrel/std/system/flatten-ands-in-lit" :dir :system))
(local (include-book "kestrel/std/system/pseudo-event-form-listp" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-implementation

 atc

 :items

 (xdoc::*evmac-topic-implementation-item-state*

  xdoc::*evmac-topic-implementation-item-wrld*

  xdoc::*evmac-topic-implementation-item-ctx*

  "@('fn1...fnp') is the list @('(fn1 ... fnp)') of inputs to @(tsee atc)."

  "@('fn') is one of the symbols in @('fn1...fnp')."

  "@('fns') is @('fn1...fnp') or a suffix of it."

  "@('vars') is a list of alists from ACL2 variable symbols to C types.
   These are the variables in scope
   for the ACL2 term whose code is being generated,
   organized in nested scopes from innermost to outermost.
   This is like a symbol table for ACL2's representation of the C code."

  "@('prec-fns') is an alist from ACL2 function symbols to function information.
   The function symbols are the ones in @('fn1...fnp') that precede,
   in the latter list,
   the symbol @('fn') in @('fn1...fnp') for which code is being generated;
   @('fn') is often also a parameter of
   the ATC function that has @('prec-fns') as parameter.
   According to the restrictions stated in the ATC user documentation,
   @('prec-fns') consists of (information about) the target function symbols
   that @('fn') is allowed to call."

  (xdoc::evmac-topic-implementation-item-input "const-name")

  (xdoc::evmac-topic-implementation-item-input "output-file")

  (xdoc::evmac-topic-implementation-item-input "proofs")

  (xdoc::evmac-topic-implementation-item-input "print")

  "@('print-info/all') is a boolean flag indicating whether
   @('print') is @(':info') or @(':all'), or not."

  xdoc::*evmac-topic-implementation-item-call*

  "@('prog-const') is the symbol specified by @('const-name')."

  "@('fenv-const') is the symbol used to name the local constant
   whose value is the function environment of the generated translation unit."

  xdoc::*evmac-topic-implementation-item-names-to-avoid*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-input-processing atc)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-process-function (fn ctx state)
  :returns (mv erp (nothing "Always @('nil').") state)
  :short "Process a target function @('fni') among @('fn1'), ..., @('fnp')."
  (b* ((desc (msg "The target ~x0 input" fn))
       ((er &) (acl2::ensure-value-is-function-name$ fn desc t nil))
       (desc (msg "The target function ~x0" fn))
       ((er &) (acl2::ensure-function-is-logic-mode$ fn desc t nil))
       ((er &) (acl2::ensure-function-is-guard-verified$ fn desc t nil))
       ((er &) (acl2::ensure-function-is-defined$ fn desc t nil)))
    (acl2::value nil))
  :guard-hints (("Goal" :in-theory (enable
                                    acl2::ensure-value-is-function-name
                                    acl2::ensure-function-is-guard-verified
                                    acl2::ensure-function-is-logic-mode))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-process-function-list ((fns true-listp) ctx state)
  :returns (mv erp (nothing "Always @('nil').") state)
  :short "Lift @(tsee atc-process-function) to lists."
  (b* (((when (endp fns)) (acl2::value nil))
       ((er &) (atc-process-function (car fns) ctx state)))
    (atc-process-function-list (cdr fns) ctx state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-process-fn1...fnp ((fn1...fnp true-listp) ctx state)
  :returns (mv erp (nothing "Always @('nil').") state)
  :verify-guards nil
  :short "Process the target functions @('fn1'), ..., @('fnp')."
  (b* (((er &) (atc-process-function-list fn1...fnp ctx state))
       ((unless (consp fn1...fnp))
        (er-soft+ ctx t nil
                  "At least one target function must be supplied.")))
    (acl2::value nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-process-const-name (const-name ctx state)
  :returns (mv erp (prog-const "A @(tsee symbolp).") state)
  :mode :program
  :short "Process the @(':const-name') input."
  (b* (((er &) (acl2::ensure-value-is-symbol$ const-name
                                              "The :CONST-NAME input"
                                              t
                                              nil))
       (name (if (eq const-name :auto)
                 'c::*program*
               const-name))
       ((er &) (acl2::ensure-symbol-is-fresh-event-name$
                name
                (msg "The constant name ~x0 ~
                      specified by the :CONST-NAME input"
                     name)
                'const
                nil
                t
                nil)))
    (acl2::value name)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-process-output-file (output-file
                                 (output-file? booleanp)
                                 ctx
                                 state)
  :returns (mv erp (nothing "Always @('nil').") state)
  :mode :program
  :short "Process the @(':output-file') input."
  (b* (((unless output-file?)
        (er-soft+ ctx t nil
                  "The :OUTPUT-FILE input must be present, ~
                   but it is absent instead."))
       ((er &) (acl2::ensure-value-is-string$ output-file
                                              "The :OUTPUT-FILE input"
                                              t
                                              nil))
       ((mv msg? dirname state) (oslib::dirname output-file))
       ((when msg?) (er-soft+ ctx t nil
                              "No directory path can be obtained ~
                               from the output file path ~x0. ~@1"
                              output-file msg?))
       ((er &)
        (if (equal dirname "")
            (acl2::value nil)
          (b* (((mv msg? kind state) (oslib::file-kind dirname))
               ((when msg?) (er-soft+ ctx t nil
                                      "The kind of ~
                                       the output directory path ~x0 ~
                                       cannot be tested. ~@1"
                                      dirname msg?))
               ((unless (eq kind :directory))
                (er-soft+ ctx t nil
                          "The output directory path ~x0 ~
                           is not a directory; it has kind ~x1 instead."
                          dirname kind)))
            (acl2::value nil))))
       ((mv msg? basename state) (oslib::basename output-file))
       ((when msg?) (er-soft+ ctx t nil
                              "No file name can be obtained ~
                               from the output file path ~x0. ~@1"
                              output-file msg?))
       ((unless (and (>= (length basename) 2)
                     (equal (subseq basename
                                    (- (length basename) 2)
                                    (length basename))
                            ".c")))
        (er-soft+ ctx t nil
                  "The file name ~x0 of the output path ~x1 ~
                   must have extension '.c', but it does not."
                  basename output-file))
       ((mv msg? existsp state) (oslib::path-exists-p output-file))
       ((when msg?) (er-soft+ ctx t nil
                              "The existence of the output path ~x0 ~
                               cannot be tested. ~@1"
                              output-file msg?))
       ((when (not existsp)) (acl2::value nil))
       ((mv msg? kind state) (oslib::file-kind output-file))
       ((when msg?) (er-soft+ ctx t nil
                              "The kind of output file path ~x0 ~
                               cannot be tested. ~@1"
                              output-file msg?))
       ((unless (eq kind :regular-file))
        (er-soft+ ctx t nil
                  "The output file path ~x0 ~
                   is not a regular file; it has kind ~x1 instead."
                  output-file kind)))
    (acl2::value nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *atc-allowed-options*
  :short "Keyword options accepted by @(tsee atc)."
  (list :const-name
        :output-file
        :proofs
        :print)
  ///
  (assert-event (symbol-listp *atc-allowed-options*))
  (assert-event (no-duplicatesp-eq *atc-allowed-options*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-process-inputs ((args true-listp) ctx state)
  :returns (mv erp
               (val "A @('(tuple (fn1...fnp symbol-listp)
                                 (prog-const symbolp)
                                 (output-file stringp)
                                 (proofs booleanp)
                                 (print evmac-input-print-p)
                                 (print-info/all booleanp)
                                 val)').")
               state)
  :mode :program
  :short "Process all the inputs."
  (b* (((mv erp fn1...fnp options)
        (partition-rest-and-keyword-args args *atc-allowed-options*))
       ((when erp) (er-soft+ ctx t nil
                             "The inputs must be the names of ~
                              one or more target functions ~
                              followed by the options ~&0."
                             *atc-allowed-options*))
       (const-name-option (assoc-eq :const-name options))
       (const-name (if const-name-option
                       (cdr const-name-option)
                     :auto))
       (output-file-option (assoc-eq :output-file options))
       ((mv output-file output-file?)
        (if output-file-option
            (mv (cdr output-file-option) t)
          (mv :irrelevant nil)))
       (proofs-option (assoc-eq :proofs options))
       (proofs (if proofs-option
                   (cdr proofs-option)
                 t))
       ((er &)
        (acl2::ensure-value-is-boolean$ proofs "The :PROOFS input" t nil))
       (print-option (assoc-eq :print options))
       (print (if print-option
                  (cdr print-option)
                :result))
       ((er &) (atc-process-fn1...fnp fn1...fnp ctx state))
       ((er prog-const) (atc-process-const-name const-name ctx state))
       ((er &) (atc-process-output-file output-file
                                        output-file?
                                        ctx
                                        state))
       ((er &) (acl2::evmac-process-input-print print ctx state))
       (print-info/all (or (eq print :info)
                           (eq print :all))))
    (acl2::value (list fn1...fnp
                       prog-const
                       output-file
                       proofs
                       print
                       print-info/all))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atc-table
  :parents (atc-implementation)
  :short "Table of @(tsee atc) calls."
  :long
  (xdoc::topstring
   (xdoc::p
    "Every successful call of @(tsee atc) is recorded in a table.
     This is used to support redundancy checking (see @(tsee atc-fn))."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *atc-table*
  :short "Name of the table of @(tsee atc) calls."
  'atc-table)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defaggregate atc-call-info
  :short "Information associated to an @(tsee atc) call
          in the table of @(tsee atc) calls."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now we only record the generated encapsulate.
     More information may be recorded in the future."))
  ((encapsulate pseudo-event-formp))
  :pred atc-call-infop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-maybe-call-infop (x)
  :short "Optional information associated to an @(tsee atc) call
          in the table of @(tsee atc) calls."
  (or (atc-call-infop x)
      (eq x nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-table-definition
  :short "Definition of the table of @(tsee atc) calls."
  :long
  (xdoc::topstring
   (xdoc::p
    "The keys of the table are calls of @(tsee atc).
     The values of the table are the associated information."))

  (make-event
   `(table ,*atc-table* nil nil
      :guard (and (pseudo-event-formp acl2::key)
                  (atc-call-infop acl2::val)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-table-lookup ((call pseudo-event-formp) (wrld plist-worldp))
  :returns (info? atc-maybe-call-infop)
  :short "Look up an @(tsee atc) call in the table."
  (b* ((table (acl2::table-alist+ *atc-table* wrld))
       (info? (cdr (assoc-equal call table))))
    (if (atc-maybe-call-infop info?)
        info?
      (raise "Internal error: value ~x0 of key ~x1 in the ATC table.")))
  :prepwork ((local (include-book "std/alists/top" :dir :system))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-table-record-event ((call pseudo-event-formp) (info atc-call-infop))
  :returns (event pseudo-event-formp)
  :short "Event to update the table of @(tsee atc) calls."
  `(table ,*atc-table* ',call ',info))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atc-event-and-code-generation
  :parents (atc-implementation)
  :short "Event generation and code generation performed by @(tsee atc)."
  :long
  (xdoc::topstring
   (xdoc::p
    "We generate C abstract syntax,
     which we pretty-print to a file
     and also assign to a named constant.")
   (xdoc::p
    "Given the restrictions on the target functions,
     the translation is fairly straightforward -- intentionally so.")
   (xdoc::p
    "Some events are generated in two slightly different variants:
     one that is local to the generated @(tsee encapsulate),
     and one that is exported from the  @(tsee encapsulate).
     Proof hints are in the former but not in the latter,
     thus keeping the ACL2 history ``clean'';
     some proof hints may refer to events
     that are generated only locally to the @(tsee encapsulate)."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defalist atc-symbol-type-alistp (x)
  :short "Recognize alists from symbols to types."
  :long
  (xdoc::topstring
   (xdoc::p
    "These represent scopes in the symbol tables for variables."))
  :key (symbolp x)
  :val (typep x)
  :true-listp t
  :keyp-of-nil t
  :valp-of-nil nil
  ///

  (defrule typep-of-cdr-of-assoc-equal
    (implies (and (atc-symbol-type-alistp x)
                  (assoc-equal k x))
             (typep (cdr (assoc-equal k x))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist atc-symbol-type-alist-listp (x)
  :short "Recognize lists of alists from symbols to types."
  :long
  (xdoc::topstring
   (xdoc::p
    "These represent symbol tables for variables.
     The @(tsee car) is the innermost scope."))
  (atc-symbol-type-alistp x)
  :true-listp t
  :elementp-of-nil t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-get-var ((var symbolp) (vars atc-symbol-type-alist-listp))
  :returns (type? type-optionp :hyp (atc-symbol-type-alist-listp vars))
  :short "Obtain the type of a variable from the symbol table."
  :long
  (xdoc::topstring
   (xdoc::p
    "We look through the scopes, from innermost to outermost.
     Actually, currently it is an invariant that the scopes are disjoint,
     so any lookup order would give the same result.")
   (xdoc::p
    "Return @('nil') if the variable is not in scope."))
  (if (endp vars)
      nil
    (or (cdr (assoc-eq var (car vars)))
        (atc-get-var var (cdr vars)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-get-var-innermost ((var symbolp)
                               (vars atc-symbol-type-alist-listp))
  :returns (type? type-optionp
                  :hyp (atc-symbol-type-alist-listp vars)
                  :hints (("Goal" :in-theory (enable type-optionp))))
  :short "Obtain the type of a variable
          from the innermost scope of the symbol table."
  :long
  (xdoc::topstring
   (xdoc::p
    "This only looks at the innermost scope; it ignores the others."))
  (cdr (assoc-eq var (car vars))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-add-var ((var symbolp)
                     (type typep)
                     (vars atc-symbol-type-alist-listp))
  :returns (new-vars atc-symbol-type-alist-listp :hyp :guard)
  :short "Add a variable with a type to the symbol table."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is added to the innermost scope.
     The symbol table has always at least one scope."))
  (cons (acons var type (car vars))
        (cdr vars)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-var-newp ((var-name stringp) (vars atc-symbol-type-alist-listp))
  :returns (yes/no booleanp)
  :short "Check if a variable name is not already in the symbol table."
  :long
  (xdoc::topstring
   (xdoc::p
    "We check that no variable in the table
     has the given string as @(tsee symbol-name).
     This is because the package name of ACL2 symbols
     is ignored for the purpose of representing C variables:
     only the symbol name is used,
     and thus all the symbol names must be distinct."))
  (or (endp vars)
      (and (not (member-equal var-name
                              (symbol-name-lst (strip-cars (car vars)))))
           (atc-var-newp var-name (cdr vars)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defaggregate atc-fn-info
  :short "Information associated to an ACL2 function translated to C."
  :long
  (xdoc::topstring
   (xdoc::p
    "This consists of
     the C output type of the function,
     the name of the locally generated theorem that asserts
     that the function returns a C value,
     the name of the locally generated theorem that asserts
     that the execution of the function (via @(tsee exec-fun))
     with a variable limit is functionally correct,
     and a limit that suffices for @(tsee exec-fun)
     to execute the function completely on any arguments.
     The latter is calculated when C code is generated for the function."))
  ((type typep)
   (returns-value-thm symbolp)
   (exec-var-limit-correct-thm symbolp)
   (limit natp))
  :pred atc-fn-infop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defalist atc-symbol-fninfo-alistp (x)
  :short "Recognize alists from symbols to function information."
  :long
  (xdoc::topstring
   (xdoc::p
    "These represent symbol tables for functions."))
  :key (symbolp x)
  :val (atc-fn-infop x)
  :true-listp t
  :keyp-of-nil t
  :valp-of-nil nil
  ///

  (defrule atc-fn-infop-of-cdr-of-assoc-equal
    (implies (and (atc-symbol-fninfo-alistp x)
                  (assoc-equal k x))
             (atc-fn-infop (cdr (assoc-equal k x))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-symbol-fninfo-alist-to-returns-value-thms
  ((prec-fns atc-symbol-fninfo-alistp))
  :returns (thms symbol-listp :hyp :guard)
  :short "Project all the returns-value theorems
          out of a function information alist."
  :long
  (xdoc::topstring
   (xdoc::p
    "The proof of each of these theorems for a function @('fn')
     makes use of the same theorems for
     the preceding functions in @('prec-fns').
     This function serves to collect those theorem names from the alist.")
   (xdoc::p
    "The alist has no duplicate keys.
     So this function is correct."))
  (cond ((endp prec-fns) nil)
        (t (cons (atc-fn-info->returns-value-thm (cdr (car prec-fns)))
                 (atc-symbol-fninfo-alist-to-returns-value-thms
                  (cdr prec-fns))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-symbol-fninfo-alist-to-exec-var-limit-correct-thms
  ((prec-fns atc-symbol-fninfo-alistp))
  :returns (thms symbol-listp :hyp :guard)
  :short "Project all the execution correctness theorems
          out of a function information alist."
  :long
  (xdoc::topstring
   (xdoc::p
    "The proof of each of these theorems for a function @('fn')
     makes use of the same theorems for
     the preceding functions in @('prec-fns').
     This function serves to collect those theorem names from the alist.")
   (xdoc::p
    "The alist has no duplicate keys.
     So this function is correct."))
  (cond ((endp prec-fns) nil)
        (t (cons (atc-fn-info->exec-var-limit-correct-thm (cdr (car prec-fns)))
                 (atc-symbol-fninfo-alist-to-exec-var-limit-correct-thms
                  (cdr prec-fns))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-check-sint-const ((term pseudo-termp))
  :returns (mv (yes/no booleanp)
               (val acl2::sbyte32p))
  :short "Check if a term represents an @('int') constant."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the term is a call of @(tsee sint-const) on a quoted integer constant
     whose value is non-negative and representable as an @('int'),
     we return the value.
     This way, the caller can generate the appropriate C integer constant."))
  (case-match term
    (('sint-const ('quote val))
     (if (and (natp val)
              (acl2::sbyte32p val))
         (mv t val)
       (mv nil 0)))
    (& (mv nil 0)))
  ///
  (defret natp-of-atc-check-sint-const
    (natp val)
    :rule-classes :type-prescription))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-check-unop ((term pseudo-termp))
  :returns (mv (yes/no booleanp)
               (op unopp)
               (arg pseudo-termp :hyp :guard)
               (type typep))
  :short "Check if a term represents a unary expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the term is a call of one of the ACL2 functions
     that represent C unary operators,
     we return the operator and the argument term.
     This way, the caller can translate the argument term to a C expression
     and apply the operator to the expression.")
   (xdoc::p
    "We also return the result C type of the operator.")
   (xdoc::p
    "If the term does not have that form, we return an indication of failure.
     The term may represent some other kind of C expression."))
  (case-match term
    ((fn arg)
     (case fn
       (sint-plus (mv t (unop-plus) arg (type-sint)))
       (sint-minus (mv t (unop-minus) arg (type-sint)))
       (sint-bitnot (mv t (unop-bitnot) arg (type-sint)))
       (sint-lognot (mv t (unop-lognot) arg (type-sint)))
       (t (mv nil (irr-unop) nil (irr-type)))))
    (& (mv nil (irr-unop) nil (irr-type))))
  ///

  (defret acl2-count-of-atc-check-unop-arg
    (implies yes/no
             (< (acl2-count arg)
                (acl2-count term)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-check-binop ((term pseudo-termp))
  :returns (mv (yes/no booleanp)
               (op binopp)
               (arg1 pseudo-termp :hyp :guard)
               (arg2 pseudo-termp :hyp :guard)
               (type typep))
  :short "Check if a term represents a non-side-effecting binary expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the term is a call of one of the ACL2 functions
     that represent C non-side-effecting binary operators,
     we return the operator and the argument terms.
     This way, the caller can translate the argument terms to C expressions
     and apply the operator to the expressions.")
   (xdoc::p
    "Note that when @('&&') and @('||') are represented this way,
     their ACL2 representation is strict,
     which may be acceptable in some cases.")
   (xdoc::p
    "We also return the result C type of the operator.")
   (xdoc::p
    "If the term does not have that form, we return an indication of failure.
     The term may represent some other kind of C expression."))
  (case-match term
    ((fn arg1 arg2)
     (case fn
       (sint-add (mv t (binop-add) arg1 arg2 (type-sint)))
       (sint-sub (mv t (binop-sub) arg1 arg2 (type-sint)))
       (sint-mul (mv t (binop-mul) arg1 arg2 (type-sint)))
       (sint-div (mv t (binop-div) arg1 arg2 (type-sint)))
       (sint-rem (mv t (binop-rem) arg1 arg2 (type-sint)))
       (sint-shl-sint (mv t (binop-shl) arg1 arg2 (type-sint)))
       (sint-shr-sint (mv t (binop-shr) arg1 arg2 (type-sint)))
       (sint-lt (mv t (binop-lt) arg1 arg2 (type-sint)))
       (sint-le (mv t (binop-le) arg1 arg2 (type-sint)))
       (sint-gt (mv t (binop-gt) arg1 arg2 (type-sint)))
       (sint-ge (mv t (binop-ge) arg1 arg2 (type-sint)))
       (sint-eq (mv t (binop-eq) arg1 arg2 (type-sint)))
       (sint-ne (mv t (binop-ne) arg1 arg2 (type-sint)))
       (sint-bitand (mv t (binop-bitand) arg1 arg2 (type-sint)))
       (sint-bitxor (mv t (binop-bitxor) arg1 arg2 (type-sint)))
       (sint-bitior (mv t (binop-bitior) arg1 arg2 (type-sint)))
       (sint-logand (mv t (binop-logand) arg1 arg2 (type-sint)))
       (sint-logor (mv t (binop-logor) arg1 arg2 (type-sint)))
       (t (mv nil (irr-binop) nil nil (irr-type)))))
    (& (mv nil (irr-binop) nil nil (irr-type))))
  ///

  (defret acl2-count-of-atc-check-binop-arg1
    (implies yes/no
             (< (acl2-count arg1)
                (acl2-count term)))
    :rule-classes :linear)

  (defret acl2-count-of-atc-check-binop-arg2
    (implies yes/no
             (< (acl2-count arg2)
                (acl2-count term)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-check-conv ((term pseudo-termp))
  :returns (mv (yes/no booleanp)
               (tyname tynamep)
               (arg pseudo-termp :hyp :guard))
  :short "Check if a term represents a conversion."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the term is a call of one of the ACL2 functions
     that represents C integer conversions,
     we return the C type name for the destination type
     and the argument term.
     This way, the caller can translate the argument term to a C expression
     and apply a cast with a type name to the expression.")
   (xdoc::p
    "For now we always generate explicit casts for conversions.
     Future versions of ATC will avoid generating casts
     when the conversions happen automatically
     due to where the argument expression occurs.")
   (xdoc::p
    "The C type of the conversion can be determined from the returned type name,
     so there is no need to also return a C type here.")
   (xdoc::p
    "If the term does not have the form explained above,
     we return an indication of failure."))
  (case-match term
    ((fn arg)
     (case fn
       (sint-from-uchar (mv t (tyname (tyspecseq-sint)) arg))
       (uchar-from-sint (mv t (tyname (tyspecseq-uchar)) arg))
       (t (mv nil (irr-tyname) nil))))
    (& (mv nil (irr-tyname) nil)))
  ///

  (defret acl2-count-of-atc-check-conv-arg
    (implies yes/no
             (< (acl2-count arg)
                (acl2-count term)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-check-callable-fn ((term pseudo-termp)
                               (prec-fns atc-symbol-fninfo-alistp))
  :returns (mv (yes/no booleanp)
               (fn symbolp :hyp (atc-symbol-fninfo-alistp prec-fns))
               (args pseudo-term-listp :hyp (pseudo-termp term))
               (type typep)
               (limit natp :rule-classes :type-prescription))
  :short "Check if a term represents a call to a callable target function."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the check is successful, we return
     the called function along with the arguments.
     We also return the result type of the function
     and the limit sufficient to execute the function."))
  (case-match term
    ((fn . args) (b* (((unless (symbolp fn))
                       (mv nil nil nil (irr-type) 0))
                      ((when (eq fn 'quote))
                       (mv nil nil nil (irr-type) 0))
                      (fn+info (assoc-eq fn prec-fns))
                      ((unless (consp fn+info))
                       (mv nil nil nil (irr-type) 0))
                      (info (cdr fn+info))
                      (type (type-fix (atc-fn-info->type info)))
                      (limit (lnfix (atc-fn-info->limit info))))
                   (mv t fn args type limit)))
    (& (mv nil nil nil (irr-type) 0)))
  ///

  (defret acl2-count-of-atc-check-callable-fn-args
    (implies yes/no
             (< (acl2-count args)
                (acl2-count term)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-check-let ((term pseudo-termp))
  :returns (mv (yes/no booleanp)
               (var symbolp :hyp :guard)
               (init pseudo-termp :hyp :guard)
               (body pseudo-termp :hyp :guard))
  :short "Check if a term represents
          a local variable declaration or an assignment
          followed by more code."
  :long
  (xdoc::topstring
   (xdoc::p
    "Here we recognize and decompose allowed outer terms
     that are @(tsee let)s.
     In translated form, these are terms @('((lambda (var) body) init)').
     However, if @('body') has other free variables in addition to @('var'),
     those appear as both formal paramaters and actual arguments, e.g.
     @('((lambda (var x y) body<var,x,y>) init x y)'):
     this is because ACL2 translated terms have all closed lambda expressions,
     so ACL2 adds formal parameters and actual arguments to make that happen.
     Here, we must remove them in order to get the ``true'' @(tsee let).
     This is easily done by going through
     formal parameters and actual arguments at the same time,
     and removing the ones that match."))
  (b* (((mv okp formals body actuals) (acl2::check-lambda-call term))
       ((when (not okp)) (mv nil nil nil nil))
       ((mv formals actuals) (atc-check-let-aux formals actuals))
       ((unless (and (= (len formals) 1)
                     (= (len actuals) 1)))
        (mv nil nil nil nil))
       (var (car formals))
       (init (car actuals)))
    (mv t var init body))
  :guard-hints (("Goal"
                 :in-theory
                 (enable acl2::len-of-check-lambda-calls.args-is-formals)))

  :prepwork

  ((local (include-book "std/typed-lists/pseudo-term-listp" :dir :system))

   (define atc-check-let-aux ((formals symbol-listp)
                              (actuals pseudo-term-listp))
     :guard (= (len formals) (len actuals))
     :returns (mv (new-formals symbol-listp
                               :hyp (symbol-listp formals))
                  (new-actuals pseudo-term-listp
                               :hyp (pseudo-term-listp actuals)))
     :parents nil
     (b* (((when (endp formals)) (mv nil nil))
          ((unless (mbt (consp actuals))) (mv nil nil))
          (formal (car formals))
          (actual (car actuals))
          ((when (eq formal actual))
           (atc-check-let-aux (cdr formals) (cdr actuals)))
          ((mv rest-formals rest-actuals)
           (atc-check-let-aux (cdr formals) (cdr actuals))))
       (mv (cons formal rest-formals)
           (cons actual rest-actuals)))
     ///

     (defret acl2-count-of-atc-check-let-aux.formals
       (<= (acl2-count new-formals)
           (acl2-count formals))
       :rule-classes :linear)

     (defret acl2-count-of-atc-check-let-aux.actuals
       (<= (acl2-count new-actuals)
           (acl2-count actuals))
       :rule-classes :linear)))

  ///

  (defret acl2-count-of-atc-check-let-init
    (implies yes/no
             (< (acl2-count init)
                (acl2-count term)))
    :rule-classes :linear)

  (defret acl2-count-of-atc-check-let-body
    (implies yes/no
             (< (acl2-count body)
                (acl2-count term)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines atc-gen-expr-pure
  :short "Mutually recursive ACL2 functions to
          generate pure C expressions from ACL2 terms."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are for allowed pure non-boolean terms
     and for allowed boolean terms (which are always pure)."))

  (define atc-gen-expr-pure-nonbool ((term pseudo-termp)
                                     (vars atc-symbol-type-alist-listp)
                                     (fn symbolp)
                                     ctx
                                     state)
    :returns (mv erp
                 (val (tuple (expr exprp)
                             (type typep)
                             val))
                 state)
    :parents (atc-event-and-code-generation atc-gen-expr-pure)
    :short "Generate a C expression from an ACL2 term
            that must be an allowed pure non-boolean term."
    :long
    (xdoc::topstring
     (xdoc::p
      "At the same time,
       we check that the term is an allowed pure non-boolean term,
       as described in the user documentation.")
     (xdoc::p
      "We also return the C type of the expression.")
     (xdoc::p
      "An ACL2 variable is translated to a C variable.
       Its type is looked up in the symbol table passed as input.")
     (xdoc::p
      "If the term fits the @(tsee sint-const) pattern,
       we translate it to a C integer constant.")
     (xdoc::p
      "If the term fits the pattern of a unary or binary operation,
       we translate it to the application of the operator
       to the recursively generated expressions.
       The type is the result type of the operator.")
     (xdoc::p
      "If the term fits the pattern of a conversion,
       we translate it to a cast of
       the recursively generated subexpression.
       The type is the one of the cast.
       (Future versions of ATC will avoid the cast
       when the conversion happens automatically in C.)")
     (xdoc::p
      "If the term is a call of @(tsee c::sint01),
       we call the mutually recursive ACL2 function
       that translates the argument (which must be an allowed boolean term)
       to an expression, which we return.
       The type of this expression is always @('int').")
     (xdoc::p
      "If the term is an @(tsee if) call,
       first we check if the test is @(tsee mbt) or @(tsee mbt$);
       in that case, we discard test and `else' branch
       and recursively process the `then' branch.
       Otherwise,
       we call the mutually recursive ACL2 function on the test,
       we call this ACL2 function on the branches,
       and we construct a conditional expression.
       We ensure that the two branches have the same type.")
     (xdoc::p
      "In all other cases, we fail with an error.
       The term is not an allowed pure non-boolean term.
       We could extend this code to provide
       more information to the user at some point."))
    (b* (((when (acl2::variablep term))
          (b* ((type (atc-get-var term vars))
               ((when (not type))
                (raise "Internal error: the variable ~x0 in function ~x1 ~
                        has no associated type." term fn)
                (acl2::value (list (irr-expr) (irr-type)))))
            (acl2::value
             (list (expr-ident (make-ident :name (symbol-name term)))
                   (type-fix type)))))
         ((mv okp val) (atc-check-sint-const term))
         ((when okp)
          (acl2::value
           (list
            (expr-const (const-int (make-iconst :value val
                                                :base (iconst-base-dec)
                                                :unsignedp nil
                                                :type (iconst-tysuffix-none))))
            (type-sint))))
         ((mv okp op arg type) (atc-check-unop term))
         ((when okp)
          (b* (((er (list arg-expr &)) (atc-gen-expr-pure-nonbool arg
                                                                  vars
                                                                  fn
                                                                  ctx
                                                                  state)))
            (acl2::value (list (make-expr-unary :op op :arg arg-expr)
                               type))))
         ((mv okp op arg1 arg2 type) (atc-check-binop term))
         ((when okp)
          (b* (((er (list arg1-expr &)) (atc-gen-expr-pure-nonbool arg1
                                                                   vars
                                                                   fn
                                                                   ctx
                                                                   state))
               ((er (list arg2-expr &)) (atc-gen-expr-pure-nonbool arg2
                                                                   vars
                                                                   fn
                                                                   ctx
                                                                   state)))
            (acl2::value (list (make-expr-binary :op op
                                                 :arg1 arg1-expr
                                                 :arg2 arg2-expr)
                               type))))
         ((mv okp tyname arg) (atc-check-conv term))
         ((when okp)
          (b* (((er (list arg-expr &)) (atc-gen-expr-pure-nonbool arg
                                                                  vars
                                                                  fn
                                                                  ctx
                                                                  state)))
            (acl2::value (list (make-expr-cast :type tyname
                                               :arg arg-expr)
                               (type-name-to-type tyname))))))
      (case-match term
        (('c::sint01 arg)
         (b* (((mv erp expr state)
               (atc-gen-expr-bool arg vars fn ctx state))
              ((when erp) (mv erp (list (irr-expr) (irr-type)) state)))
           (mv nil (list expr (type-sint)) state)))
        (('if test then else)
         (b* (((mv mbtp &) (acl2::check-mbt-call test))
              ((when mbtp) (atc-gen-expr-pure-nonbool then
                                                      vars
                                                      fn
                                                      ctx
                                                      state))
              ((mv mbt$p &) (acl2::check-mbt$-call test))
              ((when mbt$p) (atc-gen-expr-pure-nonbool then
                                                       vars
                                                       fn
                                                       ctx
                                                       state))
              ((mv erp test-expr state) (atc-gen-expr-bool test
                                                           vars
                                                           fn
                                                           ctx
                                                           state))
              ((when erp) (mv erp (list (irr-expr) (irr-type)) state))
              ((er (list then-expr then-type)) (atc-gen-expr-pure-nonbool
                                                then
                                                vars
                                                fn
                                                ctx
                                                state))
              ((er (list else-expr else-type)) (atc-gen-expr-pure-nonbool
                                                else
                                                vars
                                                fn
                                                ctx
                                                state))
              ((unless (equal then-type else-type))
               (er-soft+ ctx t (list (irr-expr) (irr-type))
                         "When generating C code for the function ~x0, ~
                          two branches ~x1 and ~x2 of a conditional term ~
                          have different types ~x3 and ~x4;
                          use conversion operations, if needed, ~
                          to make the branches of the same type."
                         fn then else then-type else-type)))
           (acl2::value
            (list
             (make-expr-cond :test test-expr :then then-expr :else else-expr)
             then-type))))
        (& (er-soft+ ctx t (list (irr-expr) (irr-type))
                     "When generating C code for the function ~x0, ~
                      at a point where ~
                      an allowed non-boolean ACL2 term is expected, ~
                      the term ~x1 is encountered instead."
                     fn term)))))

  (define atc-gen-expr-bool ((term pseudo-termp)
                             (vars atc-symbol-type-alist-listp)
                             (fn symbolp)
                             ctx
                             state)
    :returns (mv erp (expr exprp) state)
    :parents (atc-event-and-code-generation atc-gen-expr-pure)
    :short "Generate a C expression from an ACL2 term
            that must be an allowed boolean term."
    :long
    (xdoc::topstring
     (xdoc::p
      "At the same time, we check that the term is an allowed boolen term,
       as described in the user documentation.")
     (xdoc::p
      "If the term is a call of @(tsee not), @(tsee and), or @(tsee or),
       we recursively translate the arguments,
       which must be an allowed boolean terms,
       and we construct a logical expression
       with the corresponding C operators.")
     (xdoc::p
      "If the term is a call of @(tsee sint-nonzerop),
       we call the mutually recursive function
       that translates the argument, which must be an allowed non-boolean term,
       to an expression, which we return.")
     (xdoc::p
      "In all other cases, we fail with an error.
       The term is not an allowed non-boolean term.
       We could extend this code to provide
       more information to the user at some point."))
    (case-match term
      (('not arg)
       (b* (((er arg-expr) (atc-gen-expr-bool arg
                                              vars
                                              fn
                                              ctx
                                              state)))
         (acl2::value (make-expr-unary :op (unop-lognot) :arg arg-expr))))
      (('if arg1 arg2 ''nil)
       (b* (((er arg1-expr) (atc-gen-expr-bool arg1
                                               vars
                                               fn
                                               ctx
                                               state))
            ((er arg2-expr) (atc-gen-expr-bool arg2
                                               vars
                                               fn
                                               ctx
                                               state)))
         (acl2::value (make-expr-binary :op (binop-logand)
                                        :arg1 arg1-expr
                                        :arg2 arg2-expr))))
      (('if arg1 arg1 arg2)
       (b* (((er arg1-expr) (atc-gen-expr-bool arg1
                                               vars
                                               fn
                                               ctx
                                               state))
            ((er arg2-expr) (atc-gen-expr-bool arg2
                                               vars
                                               fn
                                               ctx
                                               state)))
         (acl2::value (make-expr-binary :op (binop-logor)
                                        :arg1 arg1-expr
                                        :arg2 arg2-expr))))
      (('c::sint-nonzerop arg)
       (b* (((mv erp (list expr &) state)
             (atc-gen-expr-pure-nonbool arg vars fn ctx state)))
         (mv erp expr state)))
      (& (er-soft+ ctx t (irr-expr)
                   "When generating C code for the function ~x0, ~
                    at a point where
                    an allowed boolean ACL2 term is expected, ~
                    the term ~x1 is encountered instead."
                   fn term))))

  :prepwork ((set-state-ok t))

  :verify-guards nil ; done below

  ///

  (defret-mutual consp-of-atc-gen-expr-pure
    (defret typeset-of-atc-gen-expr-pure-nonbool
      (and (consp val)
           (true-listp val))
      :rule-classes :type-prescription
      :fn atc-gen-expr-pure-nonbool)
    (defret true-of-atc-gen-expr-bool
      t
      :rule-classes nil
      :fn atc-gen-expr-bool))

  (verify-guards atc-gen-expr-pure-nonbool))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-expr-pure-nonbool-list ((terms pseudo-term-listp)
                                        (vars atc-symbol-type-alist-listp)
                                        (fn symbolp)
                                        ctx
                                        state)
  :returns (mv erp (exprs expr-listp) state)
  :short "Generate a list of C expressions from a list of ACL2 terms
          that must be allowed pure non-boolean terms."
  :long
  (xdoc::topstring
   (xdoc::p
    "This lifts @(tsee atc-gen-expr-pure-nonbool) to lists.
     However, we do not return the C types of the expressions."))
  (b* (((when (endp terms)) (acl2::value nil))
       ((mv erp (list expr &) state) (atc-gen-expr-pure-nonbool (car terms)
                                                                vars
                                                                fn
                                                                ctx
                                                                state))
       ((when erp) (mv erp nil state))
       ((er exprs) (atc-gen-expr-pure-nonbool-list (cdr terms)
                                                   vars
                                                   fn
                                                   ctx
                                                   state)))
    (acl2::value (cons expr exprs))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-expr-nonbool ((term pseudo-termp)
                              (vars atc-symbol-type-alist-listp)
                              (fn symbolp)
                              (prec-fns atc-symbol-fninfo-alistp)
                              ctx
                              state)
  :returns (mv erp
               (val (tuple (expr exprp)
                           (type typep)
                           (limit natp)
                           val))
               state)
  :short "Generate a C expression from an ACL2 term
          that must be an allowed non-boolean term."
  :long
  (xdoc::topstring
   (xdoc::p
    "At the same time,
     we check that the term is an allowed non-boolean term,
     as described in the user documentation.")
   (xdoc::p
    "We also return the C type of the expression.")
   (xdoc::p
    "We also return a limit that suffices for @(tsee exec-expr-call-or-pure)
     to execute the expression completely.
     This is the limit (associated to the function)
     sufficient to run @(tsee exec-fun),
     plus 1 to get there from @(tsee exec-expr-call-or-pure).")
   (xdoc::p
    "If the term is a call of a function that precedes @('fn')
     in the list of target functions @('fn1'), ..., @('fnp'),
     we translate it to a C function call on the translated arguments.
     The type of the expression is the result type of the function,
     which is looked up in the function alist passed as input.
     A sufficient limit for @(tsee exec-fun) to execute the called function
     is retrieved from the called function's information;
     we add 1 to it, to take into account the decrementing of the limit
     done by @(tsee exec-expr-call-or-pure) when it calls @(tsee exec-fun).")
   (xdoc::p
    "Otherwise, we attempt to translate the term
     as an allowed pure non-boolean terms.
     The type is the one returned by that translation.
     As limit we return 1, which suffices for @(tsee exec-expr-call-or-pure)
     to not stop right away due to the limit being 0."))
  (b* (((mv okp called-fn args type limit)
        (atc-check-callable-fn term prec-fns))
       ((when okp)
        (b* (((mv erp arg-exprs state) (atc-gen-expr-pure-nonbool-list args
                                                                       vars
                                                                       fn
                                                                       ctx
                                                                       state))
             ((when erp) (mv erp (list (irr-expr) (irr-type) 0) state)))
          (acl2::value (list
                        (make-expr-call :fun (make-ident
                                              :name (symbol-name called-fn))
                                        :args arg-exprs)
                        type
                        (1+ limit))))))
    (b* (((mv erp (list expr type) state)
          (atc-gen-expr-pure-nonbool term vars fn ctx state))
         ((when erp) (mv erp (list (irr-expr) (irr-type) 0) state)))
      (acl2::value (list expr type 1))))
  ///
  (more-returns
   (val (and (consp val)
             (true-listp val))
        :name typeset-of-atc-gen-expr-nonbool
        :rule-classes :type-prescription))
  (defret natp-of-atc-gen-expr-nonbool.limit
    (natp (caddr val))
    :rule-classes :type-prescription))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-tyspecseq ((type typep))
  :returns (tyspecseq tyspecseqp)
  :short "Generate a type specifier sequence for a type."
  :long
  (xdoc::topstring
   (xdoc::p
    "As discussed in @(see types),
     now types and type specifier sequences are isomorphic in our model,
     but they are not in C.
     When generating C code,
     in some cases it is necessary to generate
     type specifier sequences for types.
     This ACL2 function does that."))
  (type-case type
             :char (tyspecseq-char)
             :schar (tyspecseq-schar)
             :sshort (tyspecseq-sshort)
             :sint (tyspecseq-sint)
             :slong (tyspecseq-slong)
             :sllong (tyspecseq-sllong)
             :uchar (tyspecseq-uchar)
             :ushort (tyspecseq-ushort)
             :uint (tyspecseq-uint)
             :ulong (tyspecseq-ulong)
             :ullong (tyspecseq-ullong))
  :hooks (:fix)
  ///

  (defrule type-name-to-type-of-tyname-of-atc-gen-tyspecseq
    (equal (type-name-to-type (tyname (atc-gen-tyspecseq type)))
           (type-fix type))
    :enable type-name-to-type))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-stmt ((term pseudo-termp)
                      (vars atc-symbol-type-alist-listp)
                      (fn symbolp)
                      (prec-fns atc-symbol-fninfo-alistp)
                      ctx
                      state)
  :returns (mv erp
               (val (tuple (items block-item-listp)
                           (type typep)
                           (limit natp)
                           val))
               state)
  :short "Generate a C statement from an ACL2 term."
  :long
  (xdoc::topstring
   (xdoc::p
    "More precisely, we return a list of block items.
     These can be regarded as forming a compound statement,
     but lists of block items are compositional (via concatenation).")
   (xdoc::p
    "At the same time, we check that the term is an allowed outer term,
     as described in the user documentation.")
   (xdoc::p
    "Besides the generated block items list,
     we also return the C type of the value it returns.
     Even though C block item lists do not always return values,
     the ones generated by ATC always do;
     in fact, we are turning ACL2 terms (which return values)
     into block item lists that return values corresponding to the terms.")
   (xdoc::p
    "We also return a limit that suffices for @(tsee exec-block-item-list)
     to execute the returned block items completely.")
   (xdoc::p
    "If the term is a conditional, there are two cases.
     If the test is @(tsee mbt) or @(tsee mbt$),
     we discard test and `else' branch
     and recursively translate the `then' branch;
     the limit is the same as the `then' branch.
     Otherwise, we generate an @('if') statement
     (as a singleton block item list),
     with recursively generated compound statements as branches;
     the test expression is generated from the test term;
     we ensure that the two branches have the same type.
     When we process the branches,
     we extend the symbol table with a new empty scope for each branch.
     The calculation of the limit result is a bit more complicated in this case:
     we need 1 to go from @(tsee exec-block-item-list)
     to @(tsee exec-block-item),
     another 1 to go from that to @(tsee exec-stmt),
     and another one to go to the @(':ifelse') case there;
     the test is pure and so it needs no addition to the limit;
     since either branch may be taken,
     we return the maximum of the limits for the two branches.
     More precisely, the limit recursively returned for each branch
     pertains to the block item list in the branch,
     but those are put into a compound statement;
     thus, we need to increase the recursively calculated limit
     by 1 to go from @(tsee exec-block-item-list) to @(tsee exec-block-item),
     and another 1 to go from there to @(tsee exec-stmt).")
   (xdoc::p
    "If the term is a @(tsee let),
     we first check whether a variable with the same symbol name
     is not already in scope (i.e. in the symbol table):
     in that case, as explained in the user documentation,
     we generate a declaration for the variable,
     initialized with the expression obtained
     from the term that the variable is bound to,
     which also determines the type of the variable.
     Otherwise, we check whether a variable with the same symbol
     is in the innermost scope (only the innermost):
     in that case, we ensure that the type of the existing variable
     matches the one of the term bound to the inner variable,
     and we generate an assignment to the C variable,
     with the expression obtained
     from the term that the inner variable is bound to.
     In both cases, we recursively generate the block items for the body
     and we put those just after the variable declaration or assignment.
     If neither case applies,
     it means that a variable with the same symbol is in an outer scope:
     we stop with an error.")
   (xdoc::p
    "In the @(tsee let) case whose translation is explained above,
     the limit is calculated as follows.
     First, we need 1 to go from @(tsee exec-block-item-list)
     to @(tsee exec-block-item).
     Then we take the maximum of the limit for the first block item
     and the limit for the remaining block items.
     The first block item is either a declaration or an assignment.
     If it is a declaration, we need 1 to go from @(tsee exec-block-item)
     to the @(':decl') case and to @(tsee exec-expr-call-or-pure).
     If it is an assignment, we need 1 to go from @(tsee exec-block-item)
     to the @(':stmt') case and to @(tsee exec-stmt),
     another 1 to go from there to the @(':expr') case
     and to @(tsee exec-expr-asg),
     and another 1 to go from there to @(tsee exec-expr-call-or-pure),
     for which we recursively get the limit.
     For the remaining block items, we need to add another 1
     to go from @(tsee exec-block-item-list) to its recursive call.")
   (xdoc::p
    "If the term is neither an @(tsee if) nor a @(tsee let),
     we treat it as a non-boolean term.
     We translate it to an expression
     and we generate a @('return') statement with that expression.
     For the limit, we need 1 to go from @(tsee exec-block-item-list)
     to @(tsee exec-block-item),
     another 1 to go from there to the @(':stmt') case and @(tsee exec-stmt),
     another 1 to go from there to the @(':return') case
     and @(tsee exec-expr-call-or-pure),
     for which we use the recursively calculated limit."))
  (b* (((mv okp test then else) (acl2::check-if-call term))
       ((when okp)
        (b* (((mv mbtp &) (acl2::check-mbt-call test))
             ((when mbtp) (atc-gen-stmt then vars fn prec-fns ctx state))
             ((mv mbt$p &) (acl2::check-mbt$-call test))
             ((when mbt$p) (atc-gen-stmt then vars fn prec-fns ctx state))
             ((mv erp test-expr state) (atc-gen-expr-bool test
                                                          vars
                                                          fn
                                                          ctx
                                                          state))
             ((when erp) (mv erp (list nil (irr-type) 0) state))
             ((er (list then-items then-type then-limit))
              (atc-gen-stmt then (cons nil vars) fn prec-fns ctx state))
             ((er (list else-items else-type else-limit))
              (atc-gen-stmt else (cons nil vars) fn prec-fns ctx state))
             ((unless (equal then-type else-type))
              (er-soft+ ctx t (list nil (irr-type) 0)
                        "When generating C code for the function ~x0, ~
                         two branches ~x1 and ~x2 of a conditional term ~
                         have different types ~x3 and ~x4;
                         use conversion operations, if needed, ~
                         to make the branches of the same type."
                        fn then else then-type else-type))
             (type then-type)
             (limit (+ 1 1 1 (max (+ 1 then-limit)
                                  (+ 1 else-limit)))))
          (acl2::value
           (list
            (list
             (block-item-stmt
              (make-stmt-ifelse :test test-expr
                                :then (make-stmt-compound :items then-items)
                                :else (make-stmt-compound :items else-items))))
            type
            limit))))
       ((mv okp var val body) (atc-check-let term))
       ((when okp)
        (b* ((var-name (symbol-name var))
             ((unless (atc-ident-stringp var-name))
              (er-soft+ ctx t (list nil (irr-type) 0)
                        "The symbol name ~s0 of ~
                         the LET variable ~x1 of the function ~x2 ~
                         must be a portable ASCII C identifier, but it is not."
                        var-name var fn))
             ((when (atc-var-newp var-name vars))
              (b* (((mv erp (list init-expr init-type init-limit) state)
                    (atc-gen-expr-nonbool val vars fn prec-fns ctx state))
                   ((when erp) (mv erp (list nil (irr-type) 0) state))
                   (decl (make-decl :type (atc-gen-tyspecseq init-type)
                                    :name (make-ident :name (symbol-name var))
                                    :init init-expr))
                   (item (block-item-decl decl))
                   (vars (atc-add-var var init-type vars))
                   ((er (list body-items body-type body-limit))
                    (atc-gen-stmt body vars fn prec-fns ctx state))
                   (type body-type)
                   (limit (+ 1 (max (+ 1 init-limit)
                                    (+ 1 body-limit)))))
                (acl2::value (list (cons item body-items)
                                   type
                                   limit))))
             (prev-type (atc-get-var-innermost var vars))
             ((when (typep prev-type))
              (b* (((mv erp (list rhs-expr rhs-type rhs-limit) state)
                    (atc-gen-expr-nonbool val vars fn prec-fns ctx state))
                   ((when erp) (mv erp (list nil (irr-type) 0) state))
                   ((unless (equal prev-type rhs-type))
                    (er-soft+ ctx t (list nil (irr-type) 0)
                              "The type ~x0 of the term ~x1 ~
                               assigned to the LET variable ~x2 ~
                               of the function ~x3 ~
                               differs from the type ~x4 ~
                               of a variable with the same symbol ~
                               in the same innermost scope."
                              rhs-type val var fn prev-type))
                   (asg (make-expr-binary
                         :op (binop-asg)
                         :arg1 (expr-ident (make-ident :name var-name))
                         :arg2 rhs-expr))
                   (stmt (stmt-expr asg))
                   (item (block-item-stmt stmt))
                   ((er (list body-items body-type body-limit))
                    (atc-gen-stmt body vars fn prec-fns ctx state))
                   (type body-type)
                   (limit (+ 1 (max (+ 1 1 1 rhs-limit)
                                    body-limit))))
                (acl2::value (list (cons item body-items)
                                   type
                                   limit)))))
          (er-soft+ ctx t (list nil (irr-type) 0)
                    "When generating C code for the function ~x0, ~
                     the LET variable ~x1 has the same symbol name as ~
                     another variable (formal parameter or LET variable) ~
                     that is in an outer scope; ~
                     this is disallowed, even if the package names differ."
                    fn var)))
       ((mv erp (list expr type limit) state)
        (atc-gen-expr-nonbool term vars fn prec-fns ctx state))
       ((when erp) (mv erp (list nil (irr-type) 0) state))
       (limit (+ 1 1 1 limit)))
    (acl2::value (list (list (block-item-stmt (make-stmt-return :value expr)))
                       type
                       limit)))

  :verify-guards nil ; done below

  ///

  (more-returns
   (val (and (consp val)
             (true-listp val))
        :name cons-true-listp-of-atc-gen-stmt-val
        :rule-classes :type-prescription))
  (defret natp-of-atc-gen-stmt.limit
    (natp (caddr val))
    :rule-classes :type-prescription)

  (verify-guards atc-gen-stmt))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-find-param-type ((formal symbolp)
                             (fn symbolp)
                             (guard-conjuncts pseudo-term-listp)
                             (guard pseudo-termp)
                             ctx
                             state)
  :returns (mv erp (type typep) state)
  :short "Find the C type of a function's parameter from the guard."
  :long
  (xdoc::topstring
   (xdoc::p
    "We look for a term of the form @('(<type> <formal>)')
     among the conjuncts of the function's guard,
     where @('<type>') is a predicate corresponding to a C type
     and @('<formal>') is the formal argument in question.
     For now we only accept @(tsee sintp) and @(tsee ucharp) as @('<type>'),
     but this will be extended to more C types in the future."))
  (b* (((when (endp guard-conjuncts))
        (er-soft+ ctx t (irr-type)
                  "The guard ~x0 of the ~x1 function does not have ~
                   a recognizable conjunct that requires ~
                   the formal parameter ~x2 to be a C value ~
                   of some C type."
                  guard fn formal))
       (conjunct (car guard-conjuncts))
       ((unless (and (acl2::nvariablep conjunct)
                     (not (acl2::fquotep conjunct))
                     (not (acl2::flambda-applicationp conjunct))))
        (atc-find-param-type formal fn (cdr guard-conjuncts) guard ctx state))
       (type-fn (acl2::ffn-symb conjunct))
       (type (case type-fn
               (sintp (type-sint))
               (ucharp (type-uchar))
               (t nil)))
       ((when (not type))
        (atc-find-param-type formal fn (cdr guard-conjuncts) guard ctx state)))
    (acl2::value type)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-param-decl ((formal symbolp)
                            (fn symbolp)
                            (guard-conjuncts pseudo-term-listp)
                            (guard pseudo-termp)
                            ctx
                            state)
  :returns (mv erp
               (val (tuple (param param-declp)
                           (type typep)
                           val))
               state)
  :short "Generate a C parameter declaration from an ACL2 formal parameter."
  :long
  (xdoc::topstring
   (xdoc::p
    "Besides checking that the name of the parameter is adequate,
     we also (try and) retrieve its C type from the guard."))
  (b* ((name (symbol-name formal))
       ((unless (atc-ident-stringp name))
        (er-soft+ ctx t (list (irr-param-decl) (irr-type))
                  "The symbol name ~s0 of ~
                   the formal parameter ~x1 of the function ~x2 ~
                   must be a portable ASCII C identifier, but it is not."
                  name formal fn))
       ((mv erp type state)
        (atc-find-param-type formal fn guard-conjuncts guard ctx state))
       ((when erp) (mv erp (list (irr-param-decl) (irr-type)) state)))
    (acl2::value (list (make-param-decl :name (make-ident :name name)
                                        :type (atc-gen-tyspecseq type))
                       type)))
  ///
  (more-returns
   (val true-listp :rule-classes :type-prescription)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-param-decl-list ((formals symbol-listp)
                                 (fn symbolp)
                                 (guard-conjuncts pseudo-term-listp)
                                 (guard pseudo-termp)
                                 ctx
                                 state)
  :returns (mv erp
               (val (tuple (params param-decl-listp)
                           (vars atc-symbol-type-alist-listp)
                           val))
               state)
  :short "Generate a list of C parameter declarations
          from a list of ACL2 formal parameters."
  :long
  (xdoc::topstring
   (xdoc::p
    "Also generate an initial symbol table,
     consisting of a single scope
     that maps the formal parameters to their C types."))
  (b* (((when (endp formals)) (acl2::value (list nil (list nil))))
       (formal (mbe :logic (acl2::symbol-fix (car formals))
                    :exec (car formals)))
       ((when (member-equal (symbol-name formal)
                            (symbol-name-lst (cdr formals))))
        (er-soft+ ctx t (list nil nil)
                  "The formal parameter ~x0 of the function ~x1 ~
                      has the same symbol name as ~
                      another formal parameter among ~x2; ~
                      this is disallowed, even if the package names differ."
                  formal fn (cdr formals)))
       ((mv erp (list param type) state) (atc-gen-param-decl formal
                                                             fn
                                                             guard-conjuncts
                                                             guard
                                                             ctx
                                                             state))
       ((when erp) (mv erp (list nil nil) state))
       ((er (list params vars)) (atc-gen-param-decl-list (cdr formals)
                                                         fn
                                                         guard-conjuncts
                                                         guard
                                                         ctx
                                                         state)))
    (acl2::value (list (cons param params)
                       (atc-add-var formal type vars))))

  :verify-guards nil ; done below
  ///
  (verify-guards atc-gen-param-decl-list)

  (more-returns
   (val true-listp :rule-classes :type-prescription)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-fn-returns-value-thm ((fn symbolp)
                                      (prec-fns atc-symbol-fninfo-alistp)
                                      (names-to-avoid symbol-listp)
                                      (wrld plist-worldp))
  :returns (mv (event "A @(tsee pseudo-event-formp).")
               (name "A @(tsee symbolp).")
               (updated-names-to-avoid "A @(tsee symbol-listp)."))
  :mode :program
  :short "Generate the theorem saying that
          @('fn') returns a C value under the guard."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a local theorem for now.
     It will be used in upcoming proof generation extensions.")
   (xdoc::p
    "The restrictions on the form of the functions that ATC translated to C
     ensures that, under the guard, these functions always return C values.
     This is fairly easy to see,
     thinking of the different allowed forms of these functions' bodies:")
   (xdoc::ul
    (xdoc::li
     "A formal parameter is constrained to be a value by the guard.")
    (xdoc::li
     "Calls of @(tsee sint-const), @(tsee sint-add), etc.
      are known to return values.")
    (xdoc::li
     "A @(tsee let) variable is equal to a term that,
      recursively, always returns a value.")
    (xdoc::li
     "A call of a preceding function returns a value,
      as proved by the same theorems for the preceding functions.")
    (xdoc::li
     "An @(tsee if) reduces to the branches."))
   (xdoc::p
    "This suggests a coarse but adequate proof strategy:
     We use the theory consisting of
     the definition of @('fn'),
     the return type theorems of @(tsee sint-const) and related functions,
     and the theorems about the preceding functions;
     we also add a @(':use') hint fot the guard theorem of @('fn')."))
  (b* ((name (add-suffix fn "-RETURNS-VALUE"))
       ((mv name names-to-avoid)
        (acl2::fresh-logical-name-with-$s-suffix name nil names-to-avoid wrld))
       (formals (acl2::formals+ fn wrld))
       (guard (untranslate (acl2::uguard fn wrld) t wrld))
       (formula `(implies ,guard (valuep (,fn ,@formals))))
       (theory `(,fn
                 ,@(atc-symbol-fninfo-alist-to-returns-value-thms prec-fns)
                 sintp-of-sint-const
                 sintp-of-sint01
                 sintp-of-sint-plus
                 sintp-of-sint-minus
                 sintp-of-sint-bitnot
                 sintp-of-sint-lognot
                 sintp-of-sint-add
                 sintp-of-sint-sub
                 sintp-of-sint-mul
                 sintp-of-sint-div
                 sintp-of-sint-rem
                 sintp-of-sint-shl-sint
                 sintp-of-sint-shr-sint
                 sintp-of-sint-lt
                 sintp-of-sint-gt
                 sintp-of-sint-le
                 sintp-of-sint-ge
                 sintp-of-sint-eq
                 sintp-of-sint-ne
                 sintp-of-sint-bitand
                 sintp-of-sint-bitxor
                 sintp-of-sint-bitior
                 sintp-of-sint-logand
                 sintp-of-sint-logor
                 sintp-of-sint-from-uchar
                 ucharp-of-uchar-from-sint
                 valuep-when-ucharp
                 valuep-when-sintp))
       (hints `(("Goal"
                 :in-theory ',theory
                 :use (:guard-theorem ,fn))))
       ((mv event &) (acl2::evmac-generate-defthm name
                                                  :formula formula
                                                  :hints hints
                                                  :enable nil)))
    (mv event name names-to-avoid)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-fn-exec-const-limit-correct-thm
  ((fn symbolp)
   (prec-fns atc-symbol-fninfo-alistp)
   (fenv-const symbolp)
   (limit natp)
   (names-to-avoid symbol-listp)
   (wrld plist-worldp))
  :returns (mv (local-event "A @(tsee pseudo-event-formp).")
               (name "A @(tsee symbolp).")
               (updated-names-to-avoid "A @(tsee symbol-listp)."))
  :mode :program
  :short "Generate the theorem asserting
          the dynamic functional correctness of the C function
          generated from the specified ACL2 function,
          in any computation state,
          with a constant limit."
  :long
  (xdoc::topstring
   (xdoc::p
    "In a computation state @('compst'),
     the execution of the C function is expressed by calling @(tsee exec-fun)
     on the name of @('fn'),
     the formals of @('fn'),
     the computation state @('compst'),
     the function environment for the translation unit,
     and a suitably large limit (more on this below).
     In this generated theorem,
     the first result of @(tsee exec-fun) is equated to
     a call of @('fn') on its formals,
     while the second result of @(tsee exec-fun) is equated to @('compst').
     Currently function calls have no persistent effect on the state
     in the C code generated by ATC:
     this is why the final state is the same as the initial one.
     This will change in the future,
     and this theorem will be suitably generalized.
     The guard of @('fn') is used as hypothesis,
     along with the fact that @('compst') is a computation state.")
   (xdoc::p
    "The limit passed to @(tsee exec-fun) is a constant value,
     which is calculated by the code generation code
     as sufficient to run @(tsee exec-fun) to completion.")
   (xdoc::p
    "The proof is a symbolic execution of the generated translation unit,
     which is a constant: see @(see atc-proof-support).
     The proof is carried out in the theory that consists of
     exactly the general rules listed there,
     plus the definition of @('fn') (clearly),
     plus the theorems that the functions callable by @('fn') return values,
     plust the type prescriptions of the functions callable by @('fn'),
     plus the correctness theorems of the functions callable by @('fn').
     The latter are the correctness theorems
     with @(tsee exec-fun) and a variable limit:
     during symbolic execution, the initial constant limit for @('fn')
     is progressively decremented,
     so by the time we get to functions called by @('fn')
     it will have different values from the initial one;
     thus, we need to match that to the variable @('limit')
     in the correctness theorems for the callees,
     which are used as rewrite rules to turn calls of @(tsee exec-fun)
     into calls of the corresponding ACL2 functions.
     These will thus match the calls in the definition of @('fn'),
     and the called functions can stay disabled in the proof.
     The theorems about the callable functions returning values
     are needed to exclude, in the proof, the case that
     these functions return errors.
     The type prescriptions of the callable functions
     are needed to discharge some proof subgoal that arise.")
   (xdoc::p
    "Furthermore, we generate a @(':use') hint
     to augment the theorem's formula with the guard theorem of @('fn'):
     this is critical to ensure that the symbolic execution of the C operators
     does not split on the error cases:
     the fact that @('fn') is guard-verified
     ensures that @(tsee sint-add) and similar functions are always called
     on values such that the exact result fit into the type,
     which is the same condition under which the dynamic semantics
     does not error on the corresponding operators.")
   (xdoc::p
    "We also generate a hint to expand all lambdas (i.e. beta reduction).
     We found at least one instance in which ACL2's heuristics
     were preventing a lambda expansion that was preventing a proof.")
   (xdoc::p
    "Because @(tsee exec-fun) is disabled as explained above,
     but we still need to open its top-level call for @('fn'),
     we generate a hint to expand calls of @(tsee exec-fun) on @('fn')
     (more precisely, on the name of the C function generated from @('fn')).")
   (xdoc::p
    "This theorem is local for now.
     But we may want to export it at some point.")
   (xdoc::p
    "The name of the theorem is obtained by
     appending @('-exec-correct') to the name of @('fn'),
     and making it fresh by appending @('$')s as needed.")
   (xdoc::p
    "This theorem is not generated if @(':proofs') is @('nil')."))
  (b* ((name (add-suffix fn "-EXEC-CONST-LIMIT-CORRECT"))
       ((mv name names-to-avoid)
        (acl2::fresh-logical-name-with-$s-suffix name nil names-to-avoid wrld))
       (formals (acl2::formals+ fn wrld))
       (guard (untranslate (acl2::uguard fn wrld) t wrld))
       (equalities
        `(b* (((mv result compst1) (exec-fun ',(ident (symbol-name fn))
                                             (list ,@formals)
                                             compst
                                             ,fenv-const
                                             ,limit)))
           (and (equal compst1 compst)
                (equal result (,fn ,@formals)))))
       (returns-value-thms
        (atc-symbol-fninfo-alist-to-returns-value-thms prec-fns))
       (exec-var-limit-correct-thms
        (atc-symbol-fninfo-alist-to-exec-var-limit-correct-thms prec-fns))
       (type-prescriptions
        (loop$ for callable in (strip-cars prec-fns)
               collect `(:t ,callable)))
       (hints `(("Goal"
                 :in-theory (append *atc-all-rules*
                                    '(,fn)
                                    ',type-prescriptions
                                    ',returns-value-thms
                                    ',exec-var-limit-correct-thms)
                 :use (:guard-theorem ,fn)
                 :expand (:lambdas
                          (:free (args compst fenv limit)
                           (exec-fun '(:ident (name . ,(symbol-name fn)))
                                     args compst fenv limit))))))
       ((mv local-event &)
        (acl2::evmac-generate-defthm
         name
         :formula `(implies (and ,guard
                                 (compustatep compst))
                            ,equalities)
         :hints hints
         :enable nil)))
    (mv local-event name names-to-avoid)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-fn-exec-var-limit-correct-thm
  ((fn symbolp)
   (fenv-const symbolp)
   (limit natp)
   (fn-returns-value-thm symbolp)
   (fn-exec-const-limit-correct-thm symbolp)
   (names-to-avoid symbol-listp)
   (wrld plist-worldp))
  :returns (mv (local-event "A @(tsee pseudo-event-formp).")
               (name "A @(tsee symbolp).")
               (updated-names-to-avoid "A @(tsee symbol-listp)."))
  :mode :program
  :short "Generate the theorem asserting
          the dynamic functional correctness of the C function
          generated from the specified ACL2 function,
          in any computation state,
          with a variable limit."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is similar to the theorem generated by
     @(tsee atc-gen-fn-exec-const-limit-correct-thm),
     but here we use a variable for the limit,
     with hypotheses saying that it is an integer greater than or equal to
     the constant limit used in the theorem generated by
     @(tsee atc-gen-fn-exec-const-limit-correct-thm).
     That theorem is used to prove this theorem,
     via the general @('exec-fun-limit').")
   (xdoc::p
    "This theorem is not generated if @(':proofs') is @('nil')."))
  (b* ((name (add-suffix fn "-EXEC-VAR-LIMIT-CORRECT"))
       ((mv name names-to-avoid)
        (acl2::fresh-logical-name-with-$s-suffix name nil names-to-avoid wrld))
       (formals (acl2::formals+ fn wrld))
       (guard (untranslate (acl2::uguard fn wrld) t wrld))
       (equalities
        `(b* (((mv result compst1) (exec-fun ',(ident (symbol-name fn))
                                             (list ,@formals)
                                             compst
                                             ,fenv-const
                                             limit)))
           (and (equal compst1 compst)
                (equal result (,fn ,@formals)))))
       (hints `(("Goal"
                 :in-theory '((:executable-counterpart ident)
                              (:executable-counterpart natp)
                              (:executable-counterpart tau-system)
                              ,fn-exec-const-limit-correct-thm)
                 :use (,fn-returns-value-thm
                       (:instance errorp-of-error (info :limit))
                       (:instance exec-fun-limit
                        (limit ,limit)
                        (limit1 limit)
                        (fun (ident ,(symbol-name fn)))
                        (args (list ,@formals))
                        (fenv ,fenv-const))))))
       ((mv local-event &)
        (acl2::evmac-generate-defthm
         name
         :formula `(implies (and ,guard
                                 (compustatep compst)
                                 (integerp limit)
                                 (>= limit ,limit))
                            ,equalities)
         :hints hints
         :enable nil)))
    (mv local-event name names-to-avoid)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-fn-run-correct-thm ((fn symbolp)
                                    (prog-const symbolp)
                                    (fn-exec-var-limit-correct-thm symbolp)
                                    (names-to-avoid symbol-listp)
                                    ctx
                                    state)
  :returns (mv erp
               (val "A @('(tuple (local-event pseudo-event-formp)
                                 (exported-event pseudo-event-formp)
                                 (name symbolp)
                                 (updated-names-to-avoid symbol-listp)
                                 val)').")
               state)
  :mode :program
  :short "Generate the theorem asserting
          the dynamic functional correctness of the C function
          generated from the specified ACL2 function,
          in the initial computation state."
  :long
  (xdoc::topstring
   (xdoc::p
    "In the initial computation state,
     the execution of the C function according to the dynamic semantics
     is expressed by calling @(tsee run-fun) on
     the name of @('fn'), the formals of @('fn'), and @('*program*').
     This is equated to a call of @('fn') on its formals.
     The guard of @('fn') is used as hypothesis.")
   (xdoc::p
    "We prove this from the theorem generated by
     @(tsee atc-gen-fn-exec-var-limit-correct-thm),
     which is used as a rewrite rule here;
     the @('compustatep-of-compustate') theorem is used to
     discharge a hypothesis of the other theorem.
     We enable @(tsee run-fun) to expose @(tsee exec-fun),
     which is what the other theorem is about.
     We also need to enable some executable counterparts
     for the calculation of the function environment.")
   (xdoc::p
    "This theorem is not generated if @(':proofs') is @('nil')."))
  (b* ((name (acl2::packn (list prog-const "-" (symbol-name fn) "-CORRECT")))
       (names-to-avoid (cons name names-to-avoid))
       ((er &) (acl2::ensure-symbol-is-fresh-event-name$
                name
                (msg "The constant name ~x0 ~
                      specified by the :CONST-NAME input ~
                      must be such that ~x1 is a fresh theorem name, ~
                      but it is not."
                     prog-const name)
                nil
                nil
                t
                nil))
       (wrld (w state))
       (formals (acl2::formals+ fn wrld))
       (guard (untranslate (acl2::uguard fn wrld) t wrld))
       (lhs `(run-fun (ident ,(symbol-name fn))
                      (list ,@formals)
                      ,prog-const))
       (rhs `(,fn ,@formals))
       (hints `(("Goal"
                 :in-theory '(,fn-exec-var-limit-correct-thm
                              run-fun
                              compustatep-of-compustate
                              (:e ident)
                              (:e init-fun-env)
                              (:e fun-env-result-kind)
                              (:e fun-env-result-ok->get)))))
       ((mv local-event exported-event)
        (acl2::evmac-generate-defthm
         name
         :formula `(implies ,guard (equal ,lhs ,rhs))
         :hints hints
         :enable nil)))
    (acl2::value (list local-event
                       exported-event
                       names-to-avoid))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-fn-thms ((fn symbolp)
                         (prec-fns atc-symbol-fninfo-alistp)
                         (prog-const symbolp)
                         (proofs booleanp)
                         (print-info/all booleanp)
                         (fenv-const symbolp)
                         (limit natp)
                         (names-to-avoid symbol-listp)
                         ctx
                         state)
  :returns (mv erp
               (val "A @('(tuple (local-events pseudo-event-form-listp)
                                 (exported-events pseudo-event-form-listp)
                                 (fn-returns-value-thm symbolp)
                                 (fn-exec-var-limit-correct-thm symbolp)
                                 (updated-names-to-avoid symbol-listp)
                                 val)').")
               state)
  :mode :program
  :short "Generate the theorems associated to the specified ACL2 function."
  (b* (((when (not proofs)) (acl2::value (list nil nil names-to-avoid)))
       (wrld (w state))
       ((mv fn-returns-value-event fn-returns-value-thm names-to-avoid)
        (atc-gen-fn-returns-value-thm fn prec-fns names-to-avoid wrld))
       ((mv fn-exec-const-limit-correct-event
            fn-exec-const-limit-correct-thm
            names-to-avoid)
        (atc-gen-fn-exec-const-limit-correct-thm fn prec-fns fenv-const limit
                                                 names-to-avoid wrld))
       ((mv fn-exec-var-limit-correct-event
            fn-exec-var-limit-correct-thm
            names-to-avoid)
        (atc-gen-fn-exec-var-limit-correct-thm fn fenv-const limit
                                               fn-returns-value-thm
                                               fn-exec-const-limit-correct-thm
                                               names-to-avoid wrld))
       ((er (list fn-run-correct-local-event
                  fn-run-correct-exported-event
                  fn-run-correct-thm
                  names-to-avoid))
        (atc-gen-fn-run-correct-thm fn prog-const
                                    fn-exec-var-limit-correct-thm
                                    names-to-avoid ctx state))
       (progress-start?
        (and print-info/all
             `((cw-event "~%Generating the theorem ~x0..."
                         ',fn-run-correct-thm))))
       (progress-end? (and print-info/all `((cw-event " done.~%"))))
       (local-events (append progress-start?
                             (list fn-returns-value-event)
                             (list fn-exec-const-limit-correct-event)
                             (list fn-exec-var-limit-correct-event)
                             (list fn-run-correct-local-event)
                             progress-end?))
       (exported-events (list fn-run-correct-exported-event)))
    (acl2::value (list local-events
                       exported-events
                       fn-returns-value-thm
                       fn-exec-var-limit-correct-thm
                       names-to-avoid))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-ext-decl ((fn symbolp)
                          (prec-fns atc-symbol-fninfo-alistp)
                          (prog-const symbolp)
                          (proofs booleanp)
                          (print-info/all booleanp)
                          (fenv-const symbolp)
                          (names-to-avoid symbol-listp)
                          ctx
                          state)
  :returns (mv erp
               (val "A @('(tuple (ext ext-declp)
                                 (local-events pseudo-event-form-listp)
                                 (exported-events pseudo-event-form-listp)
                                 (updated-prec-fns atc-symbol-fninfo-alistp)
                                 (updated-names-to-avoid symbol-listp)
                                 val)').")
               state)
  :mode :program
  :short "Generate a C external declaration (a function definition)
          from an ACL2 function, with accompanying theorems."
  :long
  (xdoc::topstring
   (xdoc::p
    "We also return local and exported events for the theorems about
     the correctness of the C function definition.")
   (xdoc::p
    "We extend the alist @('prec-fns') with information about the function.")
   (xdoc::p
    "We use the type of the value returned by the statement for the body
     as the result type of the C function.")
   (xdoc::p
    "For the limit, we need 1 to go from @(tsee exec-fun) to @(tsee exec-stmt),
     another 1 from there to @(tsee exec-block-item-list)
     in the @(':compound') case,
     and then we use the recursively calculated limit for the block."))
  (b* ((name (symbol-name fn))
       ((unless (atc-ident-stringp name))
        (er-soft+ ctx t nil
                  "The symbol name ~s0 of the function ~x1 ~
                   must be a portable ASCII C identifier, but it is not."
                  name fn))
       (wrld (w state))
       (formals (acl2::formals+ fn wrld))
       (guard (acl2::uguard+ fn wrld))
       (guard-conjuncts (flatten-ands-in-lit guard))
       ((er (list params vars)) (atc-gen-param-decl-list formals
                                                         fn
                                                         guard-conjuncts
                                                         guard
                                                         ctx
                                                         state))
       (body (acl2::ubody+ fn wrld))
       ((er (list items type limit)) (atc-gen-stmt body
                                                   vars
                                                   fn
                                                   prec-fns
                                                   ctx
                                                   state))
       (ext (ext-decl-fundef
             (make-fundef :result (atc-gen-tyspecseq type)
                          :name (make-ident :name name)
                          :params params
                          :body (stmt-compound items))))
       (limit (+ 1 1 limit))
       ((er (list local-events
                  exported-events
                  fn-returns-value-thm
                  fn-exec-var-limit-correct-thm
                  names-to-avoid))
        (atc-gen-fn-thms fn prec-fns prog-const proofs print-info/all fenv-const
                         limit names-to-avoid ctx state))
       (info (make-atc-fn-info
              :type type
              :returns-value-thm fn-returns-value-thm
              :exec-var-limit-correct-thm fn-exec-var-limit-correct-thm
              :limit limit)))
    (acl2::value (list ext
                       local-events
                       exported-events
                       (acons fn info prec-fns)
                       names-to-avoid))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-ext-decl-list ((fns symbol-listp)
                               (prec-fns atc-symbol-fninfo-alistp)
                               (prog-const symbolp)
                               (proofs booleanp)
                               (print-info/all booleanp)
                               (fenv-const symbolp)
                               (names-to-avoid symbol-listp)
                               ctx
                               state)
  :returns (mv erp
               (val "A @('(tuple (exts ext-decl-listp)
                                 (local-events pseudo-event-form-listp)
                                 (exported-events pseudo-event-form-listp)
                                 (updated-names-to-avoid symbol-listp)
                                 val)').")
               state)
  :mode :program
  :short "Lift @(tsee atc-gen-ext-decl) to lists."
  :long
  (xdoc::topstring
   (xdoc::p
    "After we process the first function @('fn') in @('fns'),
     we use the extended @('prec-fns') for the subsequent functions."))
  (b* (((when (endp fns)) (acl2::value (list nil nil nil names-to-avoid)))
       ((cons fn rest-fns) fns)
       (dup? (member-eq fn rest-fns))
       ((when dup?)
        (er-soft+ ctx t nil
                  "The target functions must have distinct symbol names ~
                   (i.e. they may not differ only in the package names), ~
                   but the functions ~x0 and ~x1 ~
                   have the same symbol name."
                  fn (car dup?)))
       ((er (list ext local-events exported-events prec-fns names-to-avoid))
        (atc-gen-ext-decl fn prec-fns prog-const proofs print-info/all fenv-const
                          names-to-avoid ctx state))
       ((er (list exts more-local-events more-exported-events names-to-avoid))
        (atc-gen-ext-decl-list rest-fns prec-fns prog-const proofs print-info/all
                               fenv-const names-to-avoid ctx state)))
    (acl2::value (list (cons ext exts)
                       (append local-events more-local-events)
                       (append exported-events more-exported-events)
                       names-to-avoid))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-prog-const ((prog-const symbolp)
                            (tunit transunitp)
                            (print-info/all booleanp))
  :returns (mv (local-event pseudo-event-formp)
               (exported-event pseudo-event-formp))
  :short "Generate the named constant for the abstract syntax tree
          of the generated C code (i.e. translation unit)."
  (b* ((progress-start?
        (and print-info/all
             `((cw-event "~%Generating the named constant ~x0..." ',prog-const))))
       (progress-end? (and print-info/all `((cw-event " done.~%"))))
       (defconst-event `(defconst ,prog-const ',tunit))
       (local-event `(progn ,@progress-start?
                            (local ,defconst-event)
                            ,@progress-end?)))
    (mv local-event defconst-event)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-fenv-const ((prog-const symbolp)
                            (names-to-avoid symbol-listp)
                            (wrld plist-worldp))
  :returns (mv (local-event "A @(tsee pseudo-event-formp).")
               (fenv-const "A @(tsee symbolp).")
               (updated-names-to-avoid "A @(tsee symbol-listp)."))
  :mode :program
  :short "Generate a local event for a named constant whose value is
          the function environment for the generated translation unit."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a local-only named constant
     so the exact name does not need to be under user control.
     We use the name @('c::*environment*');
     if that constant happens to be in use,
     we add @('$') characters until we find an unused constant name
     @('c::*environment$...$*')."))
  (b* (((mv name names-to-avoid)
        (acl2::fresh-logical-name-with-$s-suffix 'c::*environment*
                                                 'acl2::const
                                                 names-to-avoid
                                                 wrld))
       (event `(local (defconst ,name (init-fun-env ,prog-const)))))
    (mv event name names-to-avoid)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-prog-wf-thm ((prog-const symbolp)
                             (proofs booleanp)
                             (print-info/all booleanp)
                             (names-to-avoid symbol-listp)
                             ctx
                             state)
  :returns (mv erp
               (val "A @('(tuple (local-events pseudo-event-form-listp)
                                 (exported-events pseudo-event-form-listp)
                                 (updated-names-to-avoid symbol-listp)
                                 val)').")
               state)
  :mode :program
  :short "Generate the theorem asserting
          the static well-formedness of the generated C code
          (referenced as the named constant)."
  :long
  (xdoc::topstring
   (xdoc::p
    "Since this is a ground theorem,
     we expect that it should be easily provable
     using just the executable counterpart of @(tsee check-transunit),
     which is an executable function.")
   (xdoc::p
    "We generate singleton lists of events if @(':proofs') is @('t'),
     empty lists otherwise."))
  (b* (((unless proofs) (acl2::value (list nil nil names-to-avoid)))
       (name (add-suffix prog-const "-WELL-FORMED"))
       ((er &) (acl2::ensure-symbol-is-fresh-event-name$
                name
                (msg "The constant name ~x0 ~
                      specified by the :CONST-NAME input ~
                      must be such that ~x1 is a fresh theorem name, ~
                      but it is not."
                     prog-const name)
                nil
                nil
                t
                nil))
       (names-to-avoid (cons name names-to-avoid))
       ((mv local-event exported-event)
        (acl2::evmac-generate-defthm
         name
         :formula `(check-transunit ,prog-const)
         :hints '(("Goal" :in-theory '((:e check-transunit))))
         :enable nil))
       (progress-start?
        (and print-info/all
             `((cw-event "~%Generating the theorem ~x0..." ',name))))
       (progress-end? (and print-info/all `((cw-event " done.~%"))))
       (local-event `(progn ,@progress-start?
                            ,local-event
                            ,@progress-end?)))
    (acl2::value (list (list local-event)
                       (list exported-event)
                       names-to-avoid))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-transunit ((fn1...fnp symbol-listp)
                           (prog-const symbolp)
                           (proofs booleanp)
                           (print-info/all booleanp)
                           (names-to-avoid symbol-listp)
                           ctx
                           state)
  :returns (mv erp
               (val "A @('(tuple (tunit transunitp)
                                 (local-events pseudo-event-form-listp)
                                 (exported-events pseudo-event-form-listp)
                                 (updated-names-to-avoid symbol-listp)
                                 val)').")
               state)
  :mode :program
  :short "Generate a C translation unit from the ACL2 target functions,
          and accompanying event."
  :long
  (xdoc::topstring
   (xdoc::p
    "We first generate the event for the named constant with the environment,
     because its name must be passed to the ACL2 functions
     that generate the external declarations that form the translation unit."))
  (b* (((mv fenv-const-event fenv-const names-to-avoid)
        (atc-gen-fenv-const prog-const names-to-avoid (w state)))
       ((er (list wf-thm-local-events wf-thm-exported-events names-to-avoid))
        (atc-gen-prog-wf-thm prog-const proofs print-info/all
                             names-to-avoid ctx state))
       ((er
         (list exts fn-thm-local-events fn-thm-exported-events names-to-avoid))
        (atc-gen-ext-decl-list fn1...fnp nil prog-const proofs print-info/all
                               fenv-const names-to-avoid ctx state))
       (tunit (make-transunit :decls exts))
       ((mv local-const-event exported-const-event)
        (atc-gen-prog-const prog-const tunit print-info/all))
       (local-events (append (list local-const-event)
                             (list fenv-const-event)
                             wf-thm-local-events
                             fn-thm-local-events))
       (exported-events (append (list exported-const-event)
                                wf-thm-exported-events
                                fn-thm-exported-events)))
    (acl2::value (list tunit
                       local-events
                       exported-events
                       names-to-avoid))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-file ((tunit transunitp) (output-file stringp) state)
  :returns (mv erp val state)
  :mode :program
  :short "Pretty-print the generated C code (i.e. translation unit)
          to the output file."
  (b* ((lines (pprint-transunit tunit)))
    (pprinted-lines-to-file lines output-file state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-file-event ((tunit transunitp)
                            (output-file stringp)
                            (print-info/all booleanp)
                            state)
  :returns (mv erp
               (event "A @(tsee pseudo-event-formp).")
               state)
  :mode :program
  :short "Event to pretty-print the generated C code to the output file."
  :long
  (xdoc::topstring
   (xdoc::p
    "This serves to run @(tsee atc-gen-file)
     after the constant and theorem events have been submitted.
     This function generates an event form
     that is put (by @(tsee atc-gen-everything))
     after the constant and theorem events.
     When the events are submitted to and processed by ACL2,
     we get to this file generation event
     only if the previous events are successful.
     This is a sort of safety/security constraint:
     do not even generate the file, unless it is correct.")
   (xdoc::p
    "If @(':print') is at @(':info') or @(':all'),
     we also generate events to print progress messages,
     as done with the constant and theorem events.")
   (xdoc::p
    "In order to generate an embedded event form for file generation,
     we generate a @(tsee make-event) whose argument generates the file.
     The argument must also return an embedded event form,
     so we use @(tsee value-triple) with @(':invisible'),
     so there is no extra screen output.
     This is a ``dummy'' event, it is not supposed to do anything:
     it is the execution of the @(tsee make-event) argument
     that matters, because it generates the file.
     In essence, we use @(tsee make-event) to turn a computation
     (the one that generates the file)
     into an event.
     But we cannot use just @(tsee value-triple)
     because our computation returns an error triple."))
  (b* ((progress-start?
        (and print-info/all
             `((cw-event "~%Generating the file ~s0..." ',output-file))))
       (progress-end? (and print-info/all `((cw-event " done.~%"))))
       (file-gen-event
        `(make-event
          (b* (((er &) (atc-gen-file ',tunit ,output-file state)))
            (acl2::value '(value-triple :invisible))))))
    (acl2::value `(progn ,@progress-start?
                         ,file-gen-event
                         ,@progress-end?))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-print-result ((events pseudo-event-form-listp)
                              (output-file stringp))
  :returns (events pseudo-event-form-listp)
  :short "Generate the events to print the results of ATC."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used only if @(':print') is at least @(':result')."))
  (append (atc-gen-print-result-aux events)
          (list `(cw-event "~%File ~s0.~%" ,output-file)))
  :prepwork
  ((define atc-gen-print-result-aux ((events pseudo-event-form-listp))
     :returns (events pseudo-event-form-listp)
     (cond ((endp events) nil)
           (t (cons `(cw-event "~%~x0~|" ',(car events))
                    (atc-gen-print-result-aux (cdr events))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-everything ((fn1...fnp symbol-listp)
                            (prog-const symbolp)
                            (output-file stringp)
                            (print evmac-input-print-p)
                            (proofs booleanp)
                            (print-info/all booleanp)
                            (call pseudo-event-formp)
                            ctx
                            state)
  :returns (mv erp (event "A @(tsee pseudo-event-formp).") state)
  :mode :program
  :short "Generate the file and the events."
  :long
  (xdoc::topstring
   (xdoc::p
    "We locally install the ``trivial ancestor check'' from the library.
     We found at least a case in which ACL2's default heuristic ancestor check
     prevented a valid functional correctness theorem from being proved.
     Since by construction the symbolic execution shoud always terminate,
     it does not seem like ACL2's heuristic ancestor check
     would ever be helpful (if this turns out to be wrong, we will re-evaluate).
     Thus, we locally install the simpler ancestor check."))
  (b* ((names-to-avoid (list prog-const))
       ((er (list tunit local-events exported-events &))
        (atc-gen-transunit fn1...fnp prog-const proofs print-info/all
                           names-to-avoid ctx state))
       ((er file-gen-event) (atc-gen-file-event tunit
                                                output-file
                                                print-info/all
                                                state))
       (print-events (and (member-eq print '(:result :info :all))
                          (atc-gen-print-result exported-events output-file)))
       (encapsulate
         `(encapsulate ()
            (evmac-prepare-proofs)
            (local (acl2::use-trivial-ancestors-check))
            ,@local-events
            ,@exported-events
            ,file-gen-event))
       (encapsulate+ (acl2::restore-output? (eq print :all) encapsulate))
       (info (make-atc-call-info :encapsulate encapsulate))
       (table-event (atc-table-record-event call info)))
    (acl2::value `(progn ,encapsulate+
                         ,table-event
                         ,@print-events
                         (value-triple :invisible)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-fn ((args true-listp) (call pseudo-event-formp) ctx state)
  :returns (mv erp
               (result "Always @('(value-triple :invisible)').")
               state)
  :mode :program
  :parents (atc-implementation)
  :short "Process the inputs and
          generate the constant definition and the C file."
  (b* (((when (atc-table-lookup call (w state)))
        (acl2::value '(value-triple :redundant)))
       ((er (list fn1...fnp prog-const output-file proofs print print-info/all))
        (atc-process-inputs args ctx state)))
    (atc-gen-everything fn1...fnp
                        prog-const
                        output-file
                        print
                        proofs
                        print-info/all
                        call
                        ctx
                        state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-macro-definition
  :parents (atc-implementation)
  :short "Definition of the @(tsee atc) macro."
  (defmacro atc (&whole call &rest args)
    (b* ((print-etc (member-eq :print args))
         (print-nil-p (and (consp print-etc)
                           (consp (cdr print-etc))
                           (eq (cadr print-etc) nil))))
      `(make-event-terse (atc-fn ',args ',call 'atc state)
                         :suppress-errors ,print-nil-p))))
