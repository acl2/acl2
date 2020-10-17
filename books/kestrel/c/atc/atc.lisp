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
(include-book "c-integers")
(include-book "portable-ascii-identifiers")

(include-book "kestrel/error-checking/ensure-value-is-boolean" :dir :system)
(include-book "kestrel/error-checking/ensure-value-is-string" :dir :system)
(include-book "kestrel/event-macros/xdoc-constructors" :dir :system)
(include-book "kestrel/utilities/error-checking/top" :dir :system)
(include-book "oslib/dirname" :dir :system)
(include-book "oslib/file-types" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; library extensions

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(include-book "kestrel/std/system/check-if-call" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-check-and-call ((term pseudo-termp))
  :returns (mv (yes/no booleanp)
               (left pseudo-termp :hyp :guard)
               (right pseudo-termp :hyp :guard))
  :short "Check if a term is a (translated) call of @(tsee and)."
  (b* (((mv ifp test then else) (acl2::check-if-call term))
       ((when (not ifp)) (mv nil nil nil)))
    (if (equal else acl2::*nil*)
        (mv t test then)
      (mv nil nil nil)))
  ///

  (defret acl2-count-of-atc-check-and-call.left
    (implies yes/no
             (< (acl2-count left)
                (acl2-count term)))
    :rule-classes :linear)

  (defret acl2-count-of-atc-check-and-call.right
    (implies yes/no
             (< (acl2-count right)
                (acl2-count term)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-flatten-conjuncts ((term pseudo-termp))
  :returns (conjuncts pseudo-term-listp :hyp :guard)
  :short "View a term as an @(tsee and) tree and return its leaves."
  (b* (((mv andp left right) (atc-check-and-call term))
       ((when (not andp)) (list term))
       (left-conjuncts (atc-flatten-conjuncts left))
       (right-conjuncts (atc-flatten-conjuncts right)))
    (append left-conjuncts right-conjuncts)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-implementation

 atc

 :items

 (xdoc::*evmac-topic-implementation-item-state*

  xdoc::*evmac-topic-implementation-item-wrld*

  xdoc::*evmac-topic-implementation-item-ctx*

  "@('fn1...fnp') is the list @('(fn1 ... fnp)') of inputs to @(tsee atc)."

  (xdoc::evmac-topic-implementation-item-input "output-file" "atc")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-input-processing atc)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-check-symbol-name ((sym symbolp) (desc msgp) ctx state)
  :returns (mv erp (nothing null) state)
  :short "Check whether the name of a symbol is a C identifier."
  (b* ((name (symbol-name sym)))
    (if (atc-ident-stringp name)
        (value nil)
      (er-soft+ ctx t nil
                "The name ~s0 of ~@1 must be a C identifier, but it is not."
                name desc))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-check-formals ((formals symbol-listp) (fn symbolp) ctx state)
  :returns (mv erp (nothing null) state)
  :short "Check whether the symbol names of the formal parameters of a function
          are C identifiers."
  (b*  (((when (endp formals)) (value nil))
        (formal (car formals))
        ((er &) (atc-check-symbol-name
                 formal
                 (msg "The formal parameter ~x0 of the function ~x1" formal fn)
                 ctx
                 state)))
    (atc-check-formals (cdr formals) fn ctx state))
  :prepwork ((local (in-theory (enable atc-check-symbol-name)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines atc-check-term
  :short "Check whether a term in the unnormalized body of a target function
          satisfies the conditions described in the documentation."
  :long
  (xdoc::topstring
   (xdoc::p
    "At the top-level, we disallow quoted constants.
     These are only allowed as arguments of @(tsee sint-const),
     so they are checked and accepted as part of a call of this function.")
   (xdoc::p
    "We allow any variables,
     because they must be formal parameters,
     given that we disallow lambda expressions.")
   (xdoc::p
    "We allow only calls of the functions listed in the user documentation.
     For calls of @(tsee sint-const), we check that the argument
     is an integer quoted constant.
     The fact that it is in the right range is guaranteed by guard verification,
     so we do not need to check that."))

  (define atc-check-term ((term pseudo-termp) (fn symbolp) ctx state)
    :returns (mv erp (nothing null) state)
    (b* (((when (acl2::variablep term)) (value nil))
         ((when (acl2::fquotep term))
          (er-soft+ ctx t nil
                    "The quoted constant ~x0 in the body of ~x1 ~
                     is disallowed. ~
                     Only quoted integer constants are allowed, ~
                     and only as arguments of SINT-CONST."
                    term fn))
         ((when (acl2::flambda-applicationp term))
          (er-soft+ ctx t nil
                    "Lambda expressions, such as ~x0 in the body of ~x1, ~
                     are disallowed.
                     Support for LET variables (i.e. lambda expressions) ~
                     will be added later."
                    (acl2::ffn-symb term) fn))
         (op (acl2::ffn-symb term)))
      (case op
        (sint-const
         (b* ((arg (acl2::fargn term 1)))
           (if (and (quotep arg)
                    (integerp (unquote arg)))
               (value nil)
             (er-soft+ ctx t nil
                       "The call ~x0 in the body of ~x1 is disallowed. ~
                        SINT-CONST may be called only on ~
                        quoted integer constants."
                       term fn))))
        ((sint-plus
          sint-minus
          sint-add
          sint-sub
          sint-mul
          sint-div
          sint-rem)
         (atc-check-term-list (acl2::fargs term) fn ctx state))
        (otherwise
         (er-soft+ ctx t nil
                   "The function ~x0 in the body of ~x1 is disallowed. ~
                    Support for calling more C operations, ~
                    and for calling the target functions, ~
                    will be added later."
                   op fn)))))

  (define atc-check-term-list ((terms pseudo-term-listp) (fn symbolp) ctx state)
    :returns (mv erp (nothing null) state)
    (b* (((when (endp terms)) (value nil))
         ((er &) (atc-check-term (car terms) fn ctx state)))
      (atc-check-term-list (cdr terms) fn ctx state)))

  :prepwork ((set-state-ok t)))

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

(define atc-process-function (fn ctx state)
  :returns (mv erp (nothing "Always @('nil').") state)
  :short "Process a target function @('fni') among @('fn1'), ..., @('fnp')."
  (b* ((wrld (w state))
       (desc (msg "The target ~x0 input" fn))
       ((er &) (acl2::ensure-function-name$ fn desc t nil))
       (desc (msg "The target function ~x0" fn))
       ((er &) (acl2::ensure-function-logic-mode$ fn desc t nil))
       ((er &) (acl2::ensure-function-guard-verified$ fn desc t nil))
       ((er &) (acl2::ensure-function-defined$ fn desc t nil))
       ((er &) (atc-check-symbol-name
                fn
                (msg "The symbol name of the function ~x0" fn)
                ctx
                state))
       (formals (acl2::formals+ fn wrld))
       ((er &) (atc-check-formals formals fn ctx state))
       (names (symbol-name-lst formals))
       ((er &) (acl2::ensure-list-no-duplicates$
                names
                (msg "The list ~x0 of symbol names of ~
                      the formal parameters of the function ~x1"
                     names fn)
                t
                nil))
       (guard (acl2::uguard+ fn wrld))
       (guard-conjuncts (atc-flatten-conjuncts guard))
       ((er &) (atc-check-guard formals fn guard guard-conjuncts ctx state)))
    (value nil))
  :guard-hints (("Goal" :in-theory (enable
                                    acl2::ensure-function-name
                                    acl2::ensure-function-guard-verified
                                    acl2::ensure-function-logic-mode))))

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
                  "At least one target function must be supplied."))
       (names (symbol-name-lst fn1...fnp))
       ((er &) (acl2::ensure-list-no-duplicates$
                names
                (msg "The list ~x0 of symbol names of ~
                      the target functions ~x1"
                     names fn1...fnp)
                t
                nil)))
    (value nil)))

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
  (list :output-file
        :verbose)
  ///
  (assert-event (symbol-listp *atc-allowed-options*))
  (assert-event (no-duplicatesp-eq *atc-allowed-options*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-process-inputs ((args true-listp) ctx state)
  :returns (mv erp
               (result "A @('(tuple (fn1...fnp symbol-listp)
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
       (output-file-option (assoc-eq :output-file options))
       ((mv output-file output-file?)
        (if output-file-option
            (mv (cdr output-file-option) t)
          (mv :irrelevant nil)))
       (verbose (cdr (assoc-eq :verbose options)))
       ((er &) (atc-process-fn1...fnp fn1...fnp ctx state))
       ((er &) (atc-process-output-file output-file
                                        output-file?
                                        ctx
                                        state))
       ((er &) (acl2::ensure-value-is-boolean$ verbose
                                               "The :VERBOSE input"
                                               t
                                               nil)))
    (value (list fn1...fnp
                 output-file
                 verbose))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atc-code-generation
  :parents (atc-implementation)
  :short "Code generation performed by @(tsee atc)."
  :long
  (xdoc::topstring
   (xdoc::p
    "We generate C abstract syntax, which we pretty-print to a file.")
   (xdoc::p
    "Given the restrictions on the target functions,
     the translation is straightforward -- intentionally so."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-expr ((term pseudo-termp) (fn symbolp) ctx state)
  :returns (mv erp (expr exprp) state)
  :verify-guards :after-returns
  :short "Generate a C expression from an ACL2 term."
  (b* (((when (acl2::variablep term))
        (value (expr-ident (ident (symbol-name term)))))
       ((when (acl2::fquotep term))
        (er-soft+ ctx t (irr-expr)
                  "The quoted constant ~x0 in the body of ~x1 ~
                   is disallowed. ~
                   Only quoted integer constants are allowed, ~
                   and only as arguments of SINT-CONST."
                  term fn))
       ((when (acl2::flambda-applicationp term))
        (er-soft+ ctx t (irr-expr)
                  "Lambda expressions, such as ~x0 in the body of ~x1, ~
                   are disallowed.
                   Support for LET variables (i.e. lambda expressions) ~
                   will be added later."
                  (acl2::ffn-symb term) fn))
       (op (acl2::ffn-symb term))
       ((when (eq op 'sint-const))
        (b* ((arg (acl2::fargn term 1))
             ((unless (quotep arg))
              (er-soft+ ctx t (irr-expr)
                        "The call x0 in the body of ~x1 is disallowed. ~
                         SINT-CONST may be called only on ~
                         quoted constants."
                        term fn))
             (val (unquote arg))
             ((unless (integerp val))
              (er-soft+ ctx t (irr-expr)
                        "The call x0 in the body of ~x1 is disallowed. ~
                         The quoted constant ~x2 argument of SINT-CONST ~
                         must be an integer."
                        term fn arg))
             ((unless (and (>= val 0)
                           (acl2::sbyte32p val)))
              (raise "Internal error: the value ~x0 of the quoted constant ~
                      in the argument of the call ~x1 in the body of ~x2 ~
                      is out of range.")
              (value (irr-expr))))
          (value (expr-const
                  (const-int
                   (make-iconst :value (unquote arg)
                                :base (iconst-base-dec)
                                :unsignedp nil
                                :type (iconst-tysuffix-none)))))))
       ((when (member-eq op '(sint-plus sint-minus)))
        (b* (((er arg) (atc-gen-expr (acl2::fargn term 1) fn ctx state))
             (unop (case op
                     (sint-plus (unop-plus))
                     (sint-minus (unop-minus))
                     (t (acl2::impossible)))))
          (value (make-expr-unary :op unop :arg arg))))
       ((when (member-eq op '(sint-add sint-sub sint-mul sint-div sint-rem)))
        (b* (((er arg1) (atc-gen-expr (acl2::fargn term 1) fn ctx state))
             ((er arg2) (atc-gen-expr (acl2::fargn term 2) fn ctx state))
             (binop (case op
                      (sint-add (binop-add))
                      (sint-sub (binop-sub))
                      (sint-mul (binop-mul))
                      (sint-div (binop-div))
                      (sint-rem (binop-rem))
                      (t (acl2::impossible)))))
          (value (make-expr-binary :op binop :arg1 arg1 :arg2 arg2)))))
    (er-soft+ ctx t (irr-expr)
              "The function ~x0 in the body of ~x1 is disallowed. ~
               Support for calling more C operations, ~
               and for calling the target functions, ~
               will be added later."
              op fn)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-param-decl ((formal symbolp) (fn symbolp) ctx state)
  :returns (mv erp (param param-declp) state)
  :short "Generate a C parameter declaration from an ACL2 formal parameter."
  (b* ((name (symbol-name formal))
       ((unless (atc-ident-stringp name))
        (er-soft+ ctx t (irr-param-decl)
                  "The name ~s0 of the formal parameter ~x1 ~
                   of the function ~x2 ~
                   must be a C identifier, but it is not."
                  name formal fn)))
    (value (make-param-decl :name (ident name)
                            :type (tyspecseq-sint)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-param-decl-list ((formals symbol-listp) (fn symbolp) ctx state)
  :returns (mv erp (params param-decl-listp) state)
  :short "Generate a list of C parameter declarations
          from a list of ACL2 formal parameters."
  (b* (((when (endp formals)) (value nil))
       ((mv erp param state) (atc-gen-param-decl (car formals) fn ctx state))
       ((when erp) (mv erp nil state))
       ((er params) (atc-gen-param-decl-list (cdr formals) fn ctx state)))
    (value (cons param params))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-ext-decl ((fn symbolp) ctx state)
  :returns (mv erp (ext ext-declp) state)
  :short "Generate a C external declaration (a function definition)
          from an ACL2 function."
  (b* ((wrld (w state))
       (body (acl2::ubody+ fn wrld))
       ((mv erp expr state) (atc-gen-expr body fn ctx state))
       ((when erp) (mv erp (irr-ext-decl) state))
       ((mv erp params state) (atc-gen-param-decl-list (acl2::formals+ fn wrld)
                                                       fn
                                                       ctx
                                                       state))
       ((when erp) (mv erp (irr-ext-decl) state)))
    (value
     (ext-decl-fundef
      (make-fundef :result (tyspecseq-sint)
                   :name (ident (symbol-name fn))
                   :params params
                   :body (stmt-compound
                          (list (block-item-stmt (stmt-return expr)))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-ext-decl-list ((fns symbol-listp) ctx state)
  :returns (mv erp (exts ext-decl-listp) state)
  :short "Lift @(tsee atc-gen-ext-decl) to lists."
  (b* (((when (endp fns)) (value nil))
       ((mv erp ext state) (atc-gen-ext-decl (car fns) ctx state))
       ((when erp) (mv erp nil state))
       ((er exts) (atc-gen-ext-decl-list (cdr fns) ctx state)))
    (value (cons ext exts))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-transunit ((fn1...fnp symbol-listp) ctx state)
  :returns (mv erp (tunit transunitp) state)
  :short "Generate a C translation unit from the ACL2 target functions."
  (b* (((mv erp exts state) (atc-gen-ext-decl-list fn1...fnp ctx state))
       ((when erp) (mv erp (irr-transunit) state)))
    (value (make-transunit :decls exts))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-file ((fn1...fnp symbol-listp) (output-file stringp) ctx state)
  :returns (mv erp (nothing "Always @('nil').") state)
  :mode :program
  :short "Generate the C file from the ACL2 target functions."
  (b* (((er tunit) (atc-gen-transunit fn1...fnp ctx state))
       (lines (pprint-transunit tunit))
       (state (pprinted-lines-to-file lines output-file state)))
    (mv nil nil state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-fn ((args true-listp) ctx state)
  :returns (mv erp
               (result "Always @('(value-triple :invisible)').")
               state)
  :mode :program
  :parents (atc-implementation)
  :short "Process the inputs and generate the C file."
  :long
  (xdoc::topstring
   (xdoc::p
    "Since the result of this function is passed to @(tsee make-event),
     this function must return an event form.
     By returning @('(value-triple :invisible)'),
     no return value is printed on the screen.
     A message of successful completion is printed,
     regardless of @(':verbose')."))
  (b* (((er (list fn1...fnp output-file ?verbose))
        (atc-process-inputs args ctx state))
       ((er &) (atc-gen-file fn1...fnp output-file ctx state))
       (- (cw "~%Generated C file:~% ~x0~%" output-file)))
    (value '(value-triple :invisible))))

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
    `(with-output :off :all :on error
       (make-event
        (atc-fn ',args 'atc state)
        :on-behalf-of :quiet))))
