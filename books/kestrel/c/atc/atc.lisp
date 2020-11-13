; C Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "c-abstract-syntax")
(include-book "c-pretty-printer" :ttags ((:open-output-channel!)))
(include-book "c-static-semantics")
(include-book "c-dynamic-semantics")

(include-book "kestrel/error-checking/ensure-function-is-guard-verified" :dir :system)
(include-book "kestrel/error-checking/ensure-function-is-logic-mode" :dir :system)
(include-book "kestrel/error-checking/ensure-symbol-is-fresh-event-name" :dir :system)
(include-book "kestrel/error-checking/ensure-value-is-boolean" :dir :system)
(include-book "kestrel/error-checking/ensure-value-is-function-name" :dir :system)
(include-book "kestrel/error-checking/ensure-value-is-string" :dir :system)
(include-book "kestrel/error-checking/ensure-value-is-symbol" :dir :system)
(include-book "kestrel/event-macros/cw-event" :dir :system)
(include-book "kestrel/event-macros/event-generation" :dir :system)
(include-book "kestrel/event-macros/xdoc-constructors" :dir :system)
(include-book "kestrel/std/system/check-if-call" :dir :system)
(include-book "kestrel/std/util/tuple" :dir :system)
(include-book "kestrel/utilities/error-checking/top" :dir :system)
(include-book "oslib/dirname" :dir :system)
(include-book "oslib/file-types" :dir :system)

(local (include-book "kestrel/std/system/flatten-ands-in-lit" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-implementation

 atc

 :items

 (xdoc::*evmac-topic-implementation-item-state*

  xdoc::*evmac-topic-implementation-item-wrld*

  xdoc::*evmac-topic-implementation-item-ctx*

  "@('fn1...fnp') is the list @('(fn1 ... fnp)') of inputs to @(tsee atc)."

  (xdoc::evmac-topic-implementation-item-input "const-name")

  (xdoc::evmac-topic-implementation-item-input "output-file")

  "@('const') is the symbol specified by @('const-name')."))

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
       ((er &) (acl2::ensure-function-defined$ fn desc t nil)))
    (value nil))
  :guard-hints (("Goal" :in-theory (enable
                                    acl2::ensure-value-is-function-name
                                    acl2::ensure-function-is-guard-verified
                                    acl2::ensure-function-is-logic-mode))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-process-function-list ((fns true-listp) ctx state)
  :returns (mv erp (nothing "Always @('nil').") state)
  :short "Lift @(tsee atc-process-function) to lists."
  (b* (((when (endp fns)) (value nil))
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
    (value nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-process-const-name (const-name ctx state)
  :returns (mv erp (const "A @(tsee symbolp).") state)
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
    (value name)))

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
            (value nil)
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
            (value nil))))
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
       ((when (not existsp)) (value nil))
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
    (value nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *atc-allowed-options*
  :short "Keyword options accepted by @(tsee atc)."
  (list :const-name
        :output-file
        :verbose)
  ///
  (assert-event (symbol-listp *atc-allowed-options*))
  (assert-event (no-duplicatesp-eq *atc-allowed-options*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-process-inputs ((args true-listp) ctx state)
  :returns (mv erp
               (result "A @('(tuple (fn1...fnp symbol-listp)
                                    (const symbolp)
                                    (output-file stringp)
                                    (verbose booleanp))').")
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
       (verbose (cdr (assoc-eq :verbose options)))
       ((er &) (atc-process-fn1...fnp fn1...fnp ctx state))
       ((er const) (atc-process-const-name const-name ctx state))
       ((er &) (atc-process-output-file output-file
                                        output-file?
                                        ctx
                                        state))
       ((er &) (acl2::ensure-value-is-boolean$ verbose
                                               "The :VERBOSE input"
                                               t
                                               nil)))
    (value (list fn1...fnp
                 const
                 output-file
                 verbose))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atc-event-and-code-generation
  :parents (atc-implementation)
  :short "Event generation and code generation performed by @(tsee atc)."
  :long
  (xdoc::topstring
   (xdoc::p
    "We generate C abstract syntax,
     which we pretty-print to a file
     and also assign to a named constant..")
   (xdoc::p
    "Given the restrictions on the target functions,
     the translation is straightforward -- intentionally so.")
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

(define atc-check-sint-unop ((term pseudo-termp))
  :returns (mv (yes/no booleanp)
               (op unopp)
               (arg pseudo-termp :hyp :guard))
  :short "Check if a term represents
          an @('int') unary expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the term is a call of one of the ACL2 functions
     that represent C unary operators,
     we return the operator and the argument term.
     This way, the caller can translate the argument term to a C expression
     and apply the operator to the expression.")
   (xdoc::p
    "If the term does not have that form, we return an indication of failure.
     The term may represent some other kind of C expression."))
  (case-match term
    ((fn arg)
     (case fn
       (sint-plus (mv t (unop-plus) arg))
       (sint-minus (mv t (unop-minus) arg))
       (sint-bitnot (mv t (unop-bitnot) arg))
       (sint-lognot (mv t (unop-lognot) arg))
       (t (mv nil (irr-unop) nil))))
    (& (mv nil (irr-unop) nil)))
  ///

  (defret acl2-count-of-atc-check-sint-unop-arg
    (implies yes/no
             (< (acl2-count arg)
                (acl2-count term)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-check-sint-binop ((term pseudo-termp))
  :returns (mv (yes/no booleanp)
               (op binopp)
               (arg1 pseudo-termp :hyp :guard)
               (arg2 pseudo-termp :hyp :guard))
  :short "Check if a term represents
          an @('int') strict non-side-effecting binary expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the term is a call of one of the ACL2 functions
     that represent C strict non-side-effecting binary operators,
     we return the operator and the argument terms.
     This way, the caller can translate the argument terms to C expressions
     and apply the operator to the expressions.")
   (xdoc::p
    "If the term does not have that form, we return an indication of failure.
     The term may represent some other kind of C expression."))
  (case-match term
    ((fn arg1 arg2)
     (case fn
       (sint-add (mv t (binop-add) arg1 arg2))
       (sint-sub (mv t (binop-sub) arg1 arg2))
       (sint-mul (mv t (binop-mul) arg1 arg2))
       (sint-div (mv t (binop-div) arg1 arg2))
       (sint-rem (mv t (binop-rem) arg1 arg2))
       (sint-shl-sint (mv t (binop-shl) arg1 arg2))
       (sint-shr-sint (mv t (binop-shr) arg1 arg2))
       (sint-lt (mv t (binop-lt) arg1 arg2))
       (sint-le (mv t (binop-le) arg1 arg2))
       (sint-gt (mv t (binop-gt) arg1 arg2))
       (sint-ge (mv t (binop-ge) arg1 arg2))
       (sint-eq (mv t (binop-eq) arg1 arg2))
       (sint-ne (mv t (binop-ne) arg1 arg2))
       (sint-bitand (mv t (binop-bitand) arg1 arg2))
       (sint-bitxor (mv t (binop-bitxor) arg1 arg2))
       (sint-bitior (mv t (binop-bitior) arg1 arg2))
       (t (mv nil (irr-binop) nil nil))))
    (& (mv nil (irr-binop) nil nil)))
  ///

  (defret acl2-count-of-atc-check-sint-binop-arg1
    (implies yes/no
             (< (acl2-count arg1)
                (acl2-count term)))
    :rule-classes :linear)

  (defret acl2-count-of-atc-check-sint-binop-arg2
    (implies yes/no
             (< (acl2-count arg2)
                (acl2-count term)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; (define atc-check-sint-logand ((term pseudo-termp))
;;   :returns (mv  (yes/no booleanp)
;;                 (arg1 pseudo-termp :hyp :guard)
;;                 (arg2 pseudo-termp :hyp :guard))
;;   :short "Check if a term represents
;;           an @('int') logical conjunction expression."
;;   :long
;;   (xdoc::topstring
;;    (xdoc::p
;;     "As described in the user documentation,
;;      logical conjunction expressions, whch are non-strict,
;;      are represented as")
;;    (xdoc::codeblock
;;     "(sint01 (and (sint-nonzerop a) (sint-nonzerop b)))")
;;    (xdoc::p
;;     "In translated terms, this is")
;;    (xdoc::codeblock
;;     "(sint01 (if (sint-nonzerop a) (sint-nonzerop b) 'nil))")
;;    (xdoc::p
;;     "If the term has this form, we return @('a') and @('b').
;;      This way, the caller can translate them to C expressions
;;      and apply @('&&') to the expressions.")
;;    (xdoc::p
;;     "If the term does not have that form, we return an indication of failure.
;;      The term may represent some other kind of C expression."))
;;   (case-match term
;;     (('sint01 ('if ('sint-nonzerop arg1)
;;                   ('sint-nonzerop arg2)
;;                 ''nil))
;;      (mv t arg1 arg2))
;;     (& (mv nil nil nil)))
;;   ///

;;   (defret acl2-count-of-atc-check-sint-logand-arg1
;;     (implies yes/no
;;              (< (acl2-count arg1)
;;                 (acl2-count term)))
;;     :rule-classes :linear)

;;   (defret acl2-count-of-atc-check-sint-logand-arg2
;;     (implies yes/no
;;              (< (acl2-count arg2)
;;                 (acl2-count term)))
;;     :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; (define atc-check-sint-logor ((term pseudo-termp))
;;   :returns (mv  (yes/no booleanp)
;;                 (arg1 pseudo-termp :hyp :guard)
;;                 (arg2 pseudo-termp :hyp :guard))
;;   :short "Check if a term represents
;;           an @('int') logical disjunction expression."
;;   :long
;;   (xdoc::topstring
;;    (xdoc::p
;;     "As described in the user documentation,
;;      logical disjunction expressions, whch are non-strict,
;;      are represented as")
;;    (xdoc::codeblock
;;     "(sint01 (or (sint-nonzerop a) (sint-nonzerop b)))")
;;    (xdoc::p
;;     "In translated terms, this is")
;;    (xdoc::codeblock
;;     "(sint01 (if (sint-nonzerop a) (sint-nonzerop a) (sint-nonzerop b)))")
;;    (xdoc::p
;;     "If the term has this form, we return @('a') and @('b').
;;      This way, the caller can translate them to C expressions
;;      and apply @('||') to the expressions.")
;;    (xdoc::p
;;     "If the term does not have that form, we return an indication of failure.
;;      The term may represent some other kind of C expression."))
;;   (case-match term
;;     (('sint01 ('if ('sint-nonzerop arg1)
;;                   ('sint-nonzerop arg1)
;;                 ('sint-nonzerop arg2)))
;;      (mv t arg1 arg2))
;;     (& (mv nil nil nil)))
;;   ///

;;   (defret acl2-count-of-atc-check-sint-logor-arg1
;;     (implies yes/no
;;              (< (acl2-count arg1)
;;                 (acl2-count term)))
;;     :rule-classes :linear)

;;   (defret acl2-count-of-atc-check-sint-logor-arg2
;;     (implies yes/no
;;              (< (acl2-count arg2)
;;                 (acl2-count term)))
;;     :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; (define atc-check-conditional ((term pseudo-termp))
;;   :returns (mv (yes/no booleanp)
;;                (test pseudo-termp :hyp :guard)
;;                (then pseudo-termp :hyp :guard)
;;                (else pseudo-termp :hyp :guard))
;;   :short "Check if a term represents a conditional expression or statement."
;;   :long
;;   (xdoc::topstring
;;    (xdoc::p
;;     "If the term is a call of @(tsee if)
;;      whose test is a call of @(tsee sint-nonzerop),
;;      we return the argument of @(tsee sint-nonzerop) in the test
;;      and the two branch terms.
;;      This way, the caller can translate these terms to C expressions
;;      and construct a conditional expression or statement.")
;;    (xdoc::p
;;     "If the term does not have that form, we return an indication of failure.
;;      The term may represent some other kind of C expression."))
;;   (case-match term
;;     (('if ('sint-nonzerop test) then else)
;;      (mv t test then else))
;;     (& (mv nil nil nil nil)))
;;   ///

;;   (defret acl2-count-of-atc-check-conditional-test
;;     (implies yes/no
;;              (< (acl2-count test)
;;                 (acl2-count term)))
;;     :rule-classes :linear)

;;   (defret acl2-count-of-atc-check-conditional-then
;;     (implies yes/no
;;              (< (acl2-count then)
;;                 (acl2-count term)))
;;     :rule-classes :linear)

;;   (defret acl2-count-of-atc-check-conditional-else
;;     (implies yes/no
;;              (< (acl2-count else)
;;                 (acl2-count term)))
;;     :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines atc-gen-expr-fns
  :short "Mutually recursive functions to
          generate C expressions from ACL terms."

  (define atc-gen-expr-nonbool ((term pseudo-termp) (fn symbolp) ctx state)
    :returns (mv erp (expr exprp) state)
    :parents (atc-event-and-code-generation atc-gen-expr-fns)
    :short "Generate a C expression from a ACL2 term
            that must be an allowed non-boolean term."
    :long
    (xdoc::topstring
     (xdoc::p
      "At the same time, we check that the term is an allowed non-boolean term,
       as described in the user documentation.")
     (xdoc::p
      "An ACL2 variable is translated to a C variable.")
     (xdoc::p
      "If the term fits the @(tsee sint-const) pattern
       we translate it to a C integer constant.")
     (xdoc::p
      "If the term fits the pattern of a unary or binary operation,
       we translate it to the application of the operator
       to the recursively generated expressions.")
     (xdoc::p
      "If the term is a call of @(tsee c::sint01),
       we call the mutually recursive function
       that translates the argument, which must be an allowed boolean term,
       to an expression, which we return.")
     (xdoc::p
      "If the term is an @(tsee if) call,
       we call the mutually recursive function on the test,
       we call this function on the branches,
       and we construct a conditional expression.")
     (xdoc::p
      "In all other cases, we fail with an error.
       The term is not an allowed non-boolean term.
       We could extend this code to provide
       more information to the user at some point."))
    (b* (((when (acl2::variablep term))
          (value (expr-ident (make-ident :name (symbol-name term)))))
         ((mv okp val) (atc-check-sint-const term))
         ((when okp)
          (value
           (expr-const (const-int (make-iconst :value val
                                               :base (iconst-base-dec)
                                               :unsignedp nil
                                               :type (iconst-tysuffix-none))))))
         ((mv okp op arg) (atc-check-sint-unop term))
         ((when okp)
          (b* (((er arg-expr) (atc-gen-expr-nonbool arg fn ctx state)))
            (value (make-expr-unary :op op :arg arg-expr))))
         ((mv okp op arg1 arg2) (atc-check-sint-binop term))
         ((when okp)
          (b* (((er arg1-expr) (atc-gen-expr-nonbool arg1 fn ctx state))
               ((er arg2-expr) (atc-gen-expr-nonbool arg2 fn ctx state)))
            (value (make-expr-binary :op op :arg1 arg1-expr :arg2 arg2-expr)))))
      (case-match term
        (('c::sint01 arg)
         (atc-gen-expr-bool arg fn ctx state))
        (('if test then else)
         (b* (((er test-expr) (atc-gen-expr-bool test fn ctx state))
              ((er then-expr) (atc-gen-expr-nonbool then fn ctx state))
              ((er else-expr) (atc-gen-expr-nonbool else fn ctx state)))
           (value
            (make-expr-cond :test test-expr :then then-expr :else else-expr))))
        (& (er-soft+ ctx t (irr-expr)
                     "When generating C code for the function ~x0, ~
                      at a point where
                      an allowed non-boolean ACL2 term is expected, ~
                      the term ~x1 is encountered instead."
                     fn term)))))

  (define atc-gen-expr-bool ((term pseudo-termp) (fn symbolp) ctx state)
    :returns (mv erp (expr exprp) state)
    :parents (atc-event-and-code-generation atc-gen-expr-fns)
    :short "Generate a C expression from a ACL2 term
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
       (b* (((er arg-expr) (atc-gen-expr-bool arg fn ctx state)))
         (value (make-expr-unary :op (unop-lognot) :arg arg-expr))))
      (('if arg1 arg2 ''nil)
       (b* (((er arg1-expr) (atc-gen-expr-bool arg1 fn ctx state))
            ((er arg2-expr) (atc-gen-expr-bool arg2 fn ctx state)))
         (value (make-expr-binary :op (binop-logand)
                                  :arg1 arg1-expr
                                  :arg2 arg2-expr))))
      (('if arg1 arg1 arg2)
       (b* (((er arg1-expr) (atc-gen-expr-bool arg1 fn ctx state))
            ((er arg2-expr) (atc-gen-expr-bool arg2 fn ctx state)))
         (value (make-expr-binary :op (binop-logor)
                                  :arg1 arg1-expr
                                  :arg2 arg2-expr))))
      (('c::sint-nonzerop arg)
       (atc-gen-expr-nonbool arg fn ctx state))
      (& (er-soft+ ctx t (irr-expr)
                   "When generating C code for the function ~x0, ~
                    at a point where
                    an allowed boolean ACL2 term is expected, ~
                    the term ~x1 is encountered instead."
                   fn term))))

  :prepwork ((set-state-ok t))

  :verify-guards nil ; done below
  ///
  (verify-guards atc-gen-expr-nonbool))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-stmt ((term pseudo-termp) (fn symbolp) ctx state)
  :returns (mv erp (stmt stmtp) state)
  :verify-guards :after-returns
  :short "Generate a C statement from an ACL2 term."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is called on the body term of an ACL2 function.
     If the term is not a conditional,
     we generate a C expression for the term
     and generate a @('return') statement with that expression.
     Otherwise, we generate an @('if') statement,
     with recursively generated statements as branches;
     the test expression is generated from the test term."))
  (case-match term
    (('if test then else)
     (b* (((mv erp test-expr state) (atc-gen-expr-bool test fn ctx state))
          ((when erp) (mv erp (irr-stmt) state))
          ((er then-stmt) (atc-gen-stmt then fn ctx state))
          ((er else-stmt) (atc-gen-stmt else fn ctx state)))
       (value
        (make-stmt-ifelse :test test-expr :then then-stmt :else else-stmt))))
    (& (b* (((mv erp expr state) (atc-gen-expr-nonbool term fn ctx state))
            ((when erp) (mv erp (irr-stmt) state)))
         (value (make-stmt-return :value expr))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-param-decl ((formal symbolp) (fn symbolp) ctx state)
  :returns (mv erp (param param-declp) state)
  :short "Generate a C parameter declaration from an ACL2 formal parameter."
  (b* ((name (symbol-name formal))
       ((unless (atc-ident-stringp name))
        (er-soft+ ctx t (irr-param-decl)
                  "The symbol name ~s0 of ~
                   the formal parameter ~x1 of the function ~x2 ~
                   must be a portable ASCII C identifier, but it is not."
                  name formal fn)))
    (value (make-param-decl :name (make-ident :name name)
                            :type (tyspecseq-sint)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-param-decl-list ((formals symbol-listp) (fn symbolp) ctx state)
  :returns (mv erp (params param-decl-listp) state)
  :short "Generate a list of C parameter declarations
          from a list of ACL2 formal parameters."
  (b* (((when (endp formals)) (value nil))
       ((cons formal rest-formals) formals)
       ((mv erp param state) (atc-gen-param-decl formal fn ctx state))
       (dup? (member-eq formal rest-formals))
       ((when dup?)
        (er-soft+ ctx t nil
                  "The formal parameters of the ~x0 function ~
                   must have distinct symbol names ~
                   (i.e. they may not differ only in the package names), ~
                   but the formal parameters ~x1 and ~x2 ~
                   have the same symbol name."
                  fn formal (car dup?)))
       ((when erp) (mv erp nil state))
       ((er params) (atc-gen-param-decl-list rest-formals fn ctx state)))
    (value (cons param params))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-check-guard ((formals symbol-listp)
                         (fn symbolp)
                         (guard pseudo-termp)
                         (guard-conjuncts pseudo-term-listp)
                         ctx
                         state)
  :returns (mv erp (nothing null) state)
  :short "Check whether every formal parameter of a target function
          has an associated guard conjunct that requires the parameter
          to be (the ACL2 counterpart of) a C @('int') value."
  (b* (((when (endp formals)) (value nil))
       (formal (car formals))
       (conjunct (acl2::fcons-term* 'sintp formal))
       ((unless (member-equal conjunct guard-conjuncts))
        (er-soft+ ctx t nil
                  "The guard ~x0 of the ~x1 function does not have ~
                   a recognizable conjunct ~x2 that requires ~
                   the formal parameter ~x3 to be a C int value."
                  guard fn conjunct formal)))
    (atc-check-guard (cdr formals) fn guard guard-conjuncts ctx state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-ext-decl ((fn symbolp) ctx state)
  :returns (mv erp (ext ext-declp) state)
  :short "Generate a C external declaration (a function definition)
          from an ACL2 function."
  (b* ((name (symbol-name fn))
       ((unless (atc-ident-stringp name))
        (er-soft+ ctx t (irr-ext-decl)
                  "The symbol name ~s0 of the function ~x1 ~
                   must be a portable ASCII C identifier, but it is not."
                  name fn))
       (wrld (w state))
       (formals (acl2::formals+ fn wrld))
       (guard (acl2::uguard+ fn wrld))
       (guard-conjuncts (flatten-ands-in-lit guard))
       ((mv erp & state) (atc-check-guard formals
                                          fn
                                          guard
                                          guard-conjuncts
                                          ctx
                                          state))
       ((when erp) (mv erp (irr-ext-decl) state))
       ((mv erp params state) (atc-gen-param-decl-list formals
                                                       fn
                                                       ctx
                                                       state))
       ((when erp) (mv erp (irr-ext-decl) state))
       (body (acl2::ubody+ fn wrld))
       ((mv erp stmt state) (atc-gen-stmt body fn ctx state))
       ((when erp) (mv erp (irr-ext-decl) state)))
    (value
     (ext-decl-fundef
      (make-fundef :result (tyspecseq-sint)
                   :name (make-ident :name name)
                   :params params
                   :body (stmt-compound (list (block-item-stmt stmt))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-ext-decl-list ((fns symbol-listp) ctx state)
  :returns (mv erp (exts ext-decl-listp) state)
  :short "Lift @(tsee atc-gen-ext-decl) to lists."
  (b* (((when (endp fns)) (value nil))
       ((cons fn rest-fns) fns)
       ((mv erp ext state) (atc-gen-ext-decl fn ctx state))
       (dup? (member-eq fn rest-fns))
       ((when dup?)
        (er-soft+ ctx t nil
                  "The target functions must have distinct symbol names ~
                   (i.e. they may not differ only in the package names), ~
                   but the functions ~x0 and ~x1 ~
                   have the same symbol name."
                  fn (car dup?)))
       ((when erp) (mv erp nil state))
       ((er exts) (atc-gen-ext-decl-list rest-fns ctx state)))
    (value (cons ext exts))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-transunit ((fn1...fnp symbol-listp) ctx state)
  :returns (mv erp (tunit transunitp) state)
  :short "Generate a C translation unit from the ACL2 target functions."
  (b* (((mv erp exts state) (atc-gen-ext-decl-list fn1...fnp ctx state))
       ((when erp) (mv erp (irr-transunit) state)))
    (value (make-transunit :decls exts))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-const ((const symbolp) (tunit transunitp))
  :returns (event acl2::pseudo-event-formp)
  :short "Generate the named constant for the abstract syntax tree
          of the generated C code (i.e. translation unit)."
  `(defconst ,const ',tunit))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-wf-thm ((const symbolp) ctx state)
  :returns (mv erp
               (result
                "A @('(tuple (name symbolp)
                             (local-event acl2::pseudo-event-formp)
                             (exported-event acl2::pseudo-event-formp))').")
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
     using just the executable counterpart of @(tsee transunit-wfp),
     which is an executable function."))
  (b* ((name (add-suffix const "-WELL-FORMED"))
       ((er &) (acl2::ensure-symbol-is-fresh-event-name$
                name
                (msg "The constant name ~x0 ~
                      specified by the :CONST-NAME input ~
                      must be such that ~x1 is a fresh theorem name, ~
                      but it is not."
                     const name)
                nil
                nil
                t
                nil))
       ((mv local-event exported-event)
        (acl2::evmac-generate-defthm
         name
         :formula `(transunit-wfp ,const)
         :hints '(("Goal" :in-theory '((:e transunit-wfp))))
         :enable nil)))
    (value (list name local-event exported-event))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-fn-thm ((fn symbolp) (const symbolp) ctx state)
  :returns (mv erp
               (result
                "A @('(tuple (name symbolp)
                             (local-event acl2::pseudo-event-formp)
                             (exported-event acl2::pseudo-event-formp))').")
               state)
  :mode :program
  :short "Generate the theorem asserting
          the dynamic functional correctness of the C function
          generated from the specified ACL2 function."
  :long
  (xdoc::topstring
   (xdoc::p
    "The execution of the C function according to the dynamic semantics
     is expressed by calling @(tsee exec-fun) on
     the name of @('fn'), the formals of @('fn'), and @('*const*').
     This is equated to a call of @('fn') on its formals.
     The guard of @('fn') is used as hypothesis.")
   (xdoc::p
    "The currently generated proof hints are simple:
     we enable @(tsee exec-fun) and all the functions that it calls
     in the dynamic execution;
     we also use the guard theorem of @('fn').
     Given that the translation unit is a constant,
     this symbolically executes the C function.
     Since the generated C code currently has no loops,
     this strategy may be adequate,
     but eventually we will likely need more elaborate proof hints.
     The use of the guard theorem of @('fn') is critical
     to ensure that the symbolic execution of the C operators
     does not splits on the error case:
     the fact that @('fn') is guard-verified
     ensures that @(tsee sint-add) and similar functions are always called
     on values such that the exact result fit into the type,
     which is the same condition under which the dynamic semantics
     does not error on the corresponding operators."))
  (b* ((name (acl2::packn (list const "-" (symbol-name fn) "-CORRECT")))
       ((er &) (acl2::ensure-symbol-is-fresh-event-name$
                name
                (msg "The constant name ~x0 ~
                      specified by the :CONST-NAME input ~
                      must be such that ~x1 is a fresh theorem name, ~
                      but it is not."
                     const name)
                nil
                nil
                t
                nil))
       (wrld (w state))
       (formals (acl2::formals+ fn wrld))
       (guard (untranslate (acl2::uguard fn wrld) t wrld))
       (lhs `(exec-fun (ident ,(symbol-name fn))
                       (list ,@formals)
                       ,const))
       (rhs `(value-result-ok (,fn ,@formals)))
       (hints `(("Goal"
                 :in-theory (enable exec-fun
                                    init-store
                                    lookup-fun
                                    lookup-fun-aux
                                    exec-stmt
                                    exec-block-item
                                    exec-block-item-list
                                    exec-expr
                                    exec-binary
                                    exec-binary-strict
                                    exec-binary-logand
                                    exec-binary-logor
                                    exec-unary
                                    exec-ident
                                    exec-const
                                    exec-iconst
                                    store-result-kind
                                    store-result-ok->get
                                    value-result-kind
                                    value-result-ok->get
                                    maybe-value-result-kind
                                    maybe-value-result-ok->get)
                 :use (:guard-theorem ,fn))))
       ((mv local-event exported-event)
        (acl2::evmac-generate-defthm
         name
         :formula `(implies ,guard (equal ,lhs ,rhs))
         :hints hints
         :enable nil)))
    (value (list name local-event exported-event))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-fn-thm-list ((fns symbol-listp) (const symbolp) ctx state)
  :returns (mv erp
               (result
                "A @('(tuple
                       (names symbol-listp)
                       (local-events acl2::pseudo-event-form-listp)
                       (exported-events acl2::pseudo-event-form-listp))').")
               state)
  :mode :program
  :short "Lift @(tsee atc-gen-fn-thm) to lists."
  (b* (((when (endp fns)) (value (list nil nil nil)))
       ((er (list name local-event exported-event))
        (atc-gen-fn-thm (car fns) const ctx state))
       ((er (list names local-events exported-events))
        (atc-gen-fn-thm-list (cdr fns) const ctx state)))
    (value (list (cons name names)
                 (cons local-event local-events)
                 (cons exported-event exported-events)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-file ((tunit transunitp) (output-file stringp) state)
  :returns state
  :mode :program
  :short "Pretty-print the generated C code (i.e. translation unit)
          to the output file."
  (b* ((lines (pprint-transunit tunit)))
    (pprinted-lines-to-file lines output-file state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-fn ((args true-listp) ctx state)
  :returns (mv erp
               (result "Always @('(value-triple :invisible)').")
               state)
  :mode :program
  :parents (atc-implementation)
  :short "Process the inputs and
          generate the constant definition and the C file."
  (b* (((er (list fn1...fnp const output-file ?verbose))
        (atc-process-inputs args ctx state))
       ((er tunit) (atc-gen-transunit fn1...fnp ctx state))
       (const-event (atc-gen-const const tunit))
       ((er (list wf-thm-name wf-thm-local-event wf-thm-exported-event))
        (atc-gen-wf-thm const ctx state))
       ((er (list fn-thm-names fn-thm-local-events fn-thm-exported-events))
        (atc-gen-fn-thm-list fn1...fnp const ctx state))
       (state (atc-gen-file tunit output-file state))
       (- (cw "~%Generated C file:~% ~x0~%" output-file))
       (encapsulate
         `(encapsulate ()
            (evmac-prepare-proofs)
            ,const-event
            (cw-event "~%Generated named constant:~% ~x0~%" ',const)
            ,wf-thm-local-event
            ,wf-thm-exported-event
            ,@fn-thm-local-events
            ,@fn-thm-exported-events
            (cw-event "~%Generated theorems:~% ~x0~%" ',wf-thm-name)
            ,@(loop$ for name in fn-thm-names
                     collect `(cw-event " ~x0~%" ',name)))))
    (value `(progn ,encapsulate
                   (value-triple :invisible)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection atc-macro-definition
  :parents (atc-implementation)
  :short "Definition of the @(tsee atc) macro."
  :long
  (xdoc::topstring
   (xdoc::p
    "We suppress the extra output produced by @(tsee make-event)
     via @(tsee with-output) and @('(:on-behalf-of :quiet)').")
   (xdoc::@def "atc"))
  (defmacro atc (&rest args)
    `(with-output :off :all :on acl2::error
       (make-event
        (atc-fn ',args 'atc state)
        :on-behalf-of :quiet))))
