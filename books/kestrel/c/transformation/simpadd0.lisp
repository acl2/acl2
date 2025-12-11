; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C2C")

(include-book "proof-generation")
(include-book "proof-generation-theorems")
(include-book "input-processing")

(include-book "../language/execution-limit-monotonicity")
(include-book "../representation/shallow-deep-relation")
(include-book "../atc/symbolic-execution-rules/top")

(include-book "std/system/constant-value" :dir :system)
(include-book "std/system/pseudo-event-form-listp" :dir :system)

(local (include-book "std/system/w" :dir :system))
(local (include-book "std/typed-lists/atom-listp" :dir :system))
(local (include-book "std/typed-lists/character-listp" :dir :system))
(local (include-book "std/typed-lists/symbol-listp" :dir :system))

(local (in-theory (enable* c$::abstract-syntax-aidentp-rules)))
(local (in-theory (enable* c$::abstract-syntax-unambp-rules)))
(local (in-theory (enable* c$::abstract-syntax-annop-rules)))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-implementation

 simpadd0

 :items

 ((xdoc::evmac-topic-implementation-item-input "const-old")

  (xdoc::evmac-topic-implementation-item-input "const-new"))

 :additional

 ("See @(see transformation-tools) for general information."))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-input-processing simpadd0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-process-inputs (const-old
                                 (const-old-present booleanp)
                                 const-new
                                 (const-new-present booleanp)
                                 (wrld plist-worldp))
  :returns (mv erp
               (code-old code-ensemblep)
               (const-new$ symbolp))
  :short "Process all the inputs."
  (b* (((reterr) (irr-code-ensemble) nil)
       ((erp code-old) (process-const-old const-old const-old-present wrld))
       ((erp const-new) (process-const-new const-new const-new-present)))
    (retok code-old const-new))

  ///

  (defret code-ensemble-unambp-of-simpadd0-process-inputs
    (implies (not erp)
             (code-ensemble-unambp code-old)))

  (defret code-ensemble-annop-of-simpadd0-process-inputs
    (implies (not erp)
             (code-ensemble-annop code-old))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::evmac-topic-event-generation simpadd0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-expr-binary ((op binopp)
                              (arg1 exprp)
                              (arg1-new exprp)
                              (arg1-thm-name symbolp)
                              (arg2 exprp)
                              (arg2-new exprp)
                              (arg2-thm-name symbolp)
                              (info expr-binary-infop)
                              (gin ginp))
  :guard (and (expr-unambp arg1)
              (expr-annop arg1)
              (expr-unambp arg1-new)
              (expr-annop arg1-new)
              (expr-unambp arg2)
              (expr-annop arg2)
              (expr-unambp arg2-new)
              (expr-annop arg2-new))
  :returns (mv (expr exprp) (gout goutp))
  :short "Transform a binary expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "First, we lift the equalities of the sub-expressions
     to an equality for the binary expression.
     Then we check whether the resulting binary expression
     has the form @('E + 0'),
     with @('E') of type @('int')
     and @('0') the @('int') octal 0 without leading zeros,
     in which case the resulting expression is just @('E');
     the theorem that lifts equality is used to prove
     the equality of the original expression to @('E').")
   (xdoc::p
    "The proof for the original-to-simplified theorem makes use of
     the supporting theorem @('simpadd0-expr+zero-to-expr'),
     which says that @('E + 0'), with @('E') of type @('int'),
     is semantically equivalent to @('E').
     The hypothesis that @('E') has type @('int')
     is discharged via the theorem @('arg1-thm-name');
     we only need the type part of it in the proof;
     to discharge that theorem's hypothesis that @('E') does not error,
     we also need an instance of @('expr-binary-pure-strict-errors')
     (of which we only really need the part for the first argument).
     To apply @('simpadd0-expr+zero-to-expr'),
     which includes the hypothesis that
     @('E') does not yield an error with @('limit'),
     we use @('c::exec-expr-limit-monotone') from @(tsee c::exec-monotone)
     to derive that hypothesis from
     the fact that @('E') does not yield an error with @('(1- limit)'),
     which in turn is obtained from the hypothesis that
     @('E + 0') does not yield an error with @('limit').
     We also need the theorem for the lifted equality,
     i.e. @('gout.thm-name').
     We enable the executable counterparts of various functions
     so that things match up in the proof;
     in particular, we need to reduce the @('(c::expr-const ...)')
     in the theorem @('simpadd0-expr+zero-to-expr') to a quoted constant."))
  (b* (((mv expr-new (gout gout))
        (xeq-expr-binary op
                         arg1 arg1-new arg1-thm-name
                         arg2 arg2-new arg2-thm-name
                         info
                         gin))
       (simpp (and (binop-case op :add)
                   (type-case (expr-type arg1-new) :sint)
                   (expr-zerop arg2-new)))
       ((when (not simpp)) (mv expr-new gout))
       (expr-new-simp (expr-fix arg1-new))
       ((unless gout.thm-name) (mv expr-new-simp gout))
       ((gin gin) (gin-update gin gout))
       (expr (make-expr-binary :op op :arg1 arg1 :arg2 arg2 :info info))
       ((mv & cexpr-new-simp) (ldm-expr expr-new-simp)) ; ERP must be NIL
       ((mv & czero) (ldm-expr arg2-new))
       (hints `(("Goal"
                 :in-theory '((:e c::iconst-length-none)
                              (:e c::iconst-base-oct)
                              (:e c::iconst)
                              (:e c::const-int)
                              (:e c::expr-const)
                              (:e c::binop-add)
                              (:e c::expr-binary)
                              (:e c::type-sint)
                              (:e c::binop-strictp)
                              (:e c::expr-purep)
                              (:e c::binop-purep)
                              expr-compustate-vars
                              nfix)
                 :use (,gout.thm-name
                       (:instance simpadd0-expr+zero-to-expr
                                  (expr ',cexpr-new-simp)
                                  (fenv old-fenv))
                       ,arg1-thm-name
                       (:instance expr-binary-pure-strict-errors
                                  (op ',(c::binop-add))
                                  (arg1 ',cexpr-new-simp)
                                  (arg2 ',czero)
                                  (fenv old-fenv))
                       (:instance c::exec-expr-limit-monotone
                                  (e ',cexpr-new-simp)
                                  (compst compst)
                                  (fenv old-fenv)
                                  (limit (1- limit))
                                  (limit1 limit))))))
       ((mv thm-event thm-name thm-index)
        (gen-expr-thm expr
                      expr-new-simp
                      gin.vartys
                      gin.const-new
                      gin.thm-index
                      hints)))
    (mv expr-new-simp
        (make-gout :events (cons thm-event gin.events)
                   :thm-index thm-index
                   :thm-name thm-name
                   :vartys gin.vartys)))

  ///

  (defret expr-unambp-of-simpadd0-expr-binary
    (expr-unambp expr)
    :hyp (and (expr-unambp arg1-new)
              (expr-unambp arg2-new)))

  (defret expr-annop-of-simpadd0-expr-binary
    (expr-annop expr)
    :hyp (and (expr-annop arg1-new)
              (expr-annop arg2-new)
              (expr-binary-infop info)))

  (defret expr-aidentp-of-simpadd0-expr-binary
    (expr-aidentp expr gcc)
    :hyp (and (expr-aidentp arg1-new gcc)
              (expr-aidentp arg2-new gcc)))

  (defruledl c::add-values-of-sint-and-sint0
    (implies (and (c::valuep val)
                  (c::value-case val :sint)
                  (equal sint0 (c::value-sint 0)))
             (equal (c::add-values val sint0)
                    val))
    :enable (c::add-values
             c::add-arithmetic-values
             c::add-integer-values
             c::value-arithmeticp-when-sintp
             c::value-integerp-when-sintp
             c::uaconvert-values-when-sintp-and-sintp
             c::sintp-alt-def
             c::type-of-value-when-sintp
             c::result-integer-value
             c::integer-type-rangep
             fix
             ifix))

  (defruled simpadd0-expr+zero-to-expr
    (b* ((zero (c::expr-const
                (c::const-int
                 (c::make-iconst
                  :value 0
                  :base (c::iconst-base-oct)
                  :unsignedp nil
                  :length (c::iconst-length-none)))))
         (expr+zero (c::expr-binary (c::binop-add) expr zero))
         ((mv expr-eval expr-compst)
          (c::exec-expr expr compst fenv (1- limit)))
         (expr-val (c::expr-value->value expr-eval))
         ((mv expr+zero-eval expr+zero-compst)
          (c::exec-expr expr+zero compst fenv limit))
         (expr+zero-val (c::expr-value->value expr+zero-eval)))
      (implies (and (c::expr-purep expr)
                    (not (c::errorp expr-eval))
                    expr-eval
                    (equal (c::type-of-value expr-val) (c::type-sint)))
               (and (not (c::errorp expr+zero-eval))
                    expr+zero-eval
                    (equal expr+zero-val expr-val)
                    (equal expr+zero-compst expr-compst))))
    :expand (c::exec-expr
             (c::expr-binary '(:add)
                             expr
                             '(:const (:int (:iconst (c::value . 0)
                                             (c::base :oct)
                                             (c::unsignedp)
                                             (length :none)))))
             compst fenv limit)
    :enable (c::exec-expr
             c::exec-binary-strict-pure
             c::eval-binary-strict-pure
             c::apconvert-expr-value-when-not-array
             c::add-values-of-sint-and-sint0
             c::type-of-value)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines simpadd0-exprs/decls/stmts
  :short "Transform expressions, declarations, statements,
          and related entities."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now we only generate theorems for certain kinds of expressions.
     We are in the process of extending the implementation to generate theorems
     for additional kinds of expressions and for other constructs."))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-expr ((expr exprp) (gin ginp))
    :guard (and (expr-unambp expr)
                (expr-annop expr))
    :returns (mv (new-expr exprp) (gout goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform an expression."
    (b* (((gin gin) gin))
      (expr-case
       expr
       :ident (xeq-expr-ident expr.ident expr.info gin)
       :const (xeq-expr-const expr.const expr.info gin)
       :string (mv (expr-fix expr) (gout-no-thm gin))
       :paren
       (b* (((mv new-inner gout) (simpadd0-expr expr.inner gin)))
         (mv (expr-paren new-inner) gout))
       :gensel
       (b* (((mv new-control (gout gout-control))
             (simpadd0-expr expr.control gin))
            (gin (gin-update gin gout-control))
            ((mv new-assocs (gout gout-assocs))
             (simpadd0-genassoc-list expr.assocs gin))
            (gin (gin-update gin gout-assocs)))
         (mv (make-expr-gensel :control new-control
                               :assocs new-assocs)
             (gout-no-thm gin)))
       :arrsub
       (b* (((mv new-arg1 (gout gout-arg1))
             (simpadd0-expr expr.arg1 gin))
            (gin (gin-update gin gout-arg1))
            ((mv new-arg2 (gout gout-arg2))
             (simpadd0-expr expr.arg2 gin))
            (gin (gin-update gin gout-arg2)))
         (mv (make-expr-arrsub :arg1 new-arg1
                               :arg2 new-arg2
                               :info expr.info)
             (gout-no-thm gin)))
       :funcall
       (b* (((mv new-fun (gout gout-fun))
             (simpadd0-expr expr.fun gin))
            (gin (gin-update gin gout-fun))
            ((mv new-args (gout gout-args))
             (simpadd0-expr-list expr.args gin))
            (gin (gin-update gin gout-args)))
         (mv (make-expr-funcall :fun new-fun
                                :args new-args
                                :info expr.info)
             (gout-no-thm gin)))
       :member
       (b* (((mv new-arg (gout gout-arg))
             (simpadd0-expr expr.arg gin))
            (gin (gin-update gin gout-arg)))
         (mv (make-expr-member :arg new-arg
                               :name expr.name)
             (gout-no-thm gin)))
       :memberp
       (b* (((mv new-arg (gout gout-arg))
             (simpadd0-expr expr.arg gin))
            (gin (gin-update gin gout-arg)))
         (mv (make-expr-memberp :arg new-arg
                                :name expr.name)
             (gout-no-thm gin)))
       :complit
       (b* (((mv new-type (gout gout-type))
             (simpadd0-tyname expr.type gin))
            (gin (gin-update gin gout-type))
            ((mv new-elems (gout gout-elems))
             (simpadd0-desiniter-list expr.elems gin))
            (gin (gin-update gin gout-elems)))
         (mv (make-expr-complit :type new-type
                                :elems new-elems
                                :final-comma expr.final-comma)
             (gout-no-thm gin)))
       :unary
       (b* (((mv new-arg (gout gout-arg))
             (simpadd0-expr expr.arg gin))
            (gin (gin-update gin gout-arg)))
         (xeq-expr-unary expr.op
                         expr.arg
                         new-arg
                         gout-arg.thm-name
                         expr.info
                         gin))
       :label-addr (mv (expr-fix expr) (gout-no-thm gin))
       :sizeof
       (b* (((mv new-type (gout gout-type))
             (simpadd0-tyname expr.type gin))
            (gin (gin-update gin gout-type)))
         (mv (expr-sizeof new-type)
             (gout-no-thm gin)))
       :alignof
       (b* (((mv new-type (gout gout-type))
             (simpadd0-tyname expr.type gin))
            (gin (gin-update gin gout-type)))
         (mv (make-expr-alignof :type new-type
                                :uscores expr.uscores)
             (gout-no-thm gin)))
       :cast
       (b* (((mv new-type (gout gout-type))
             (simpadd0-tyname expr.type gin))
            (gin (gin-update gin gout-type))
            ((mv new-arg (gout gout-arg))
             (simpadd0-expr expr.arg gin))
            (gin (gin-update gin gout-arg)))
         (xeq-expr-cast expr.type
                        new-type
                        gout-type.thm-name
                        expr.arg
                        new-arg
                        gout-arg.thm-name
                        (tyname->info expr.type)
                        gin))
       :binary
       (b* (((mv new-arg1 (gout gout-arg1))
             (simpadd0-expr expr.arg1 gin))
            (gin (gin-update gin gout-arg1))
            ((mv new-arg2 (gout gout-arg2))
             (simpadd0-expr expr.arg2 gin))
            (gin (gin-update gin gout-arg2)))
         (simpadd0-expr-binary expr.op
                               expr.arg1
                               new-arg1
                               gout-arg1.thm-name
                               expr.arg2
                               new-arg2
                               gout-arg2.thm-name
                               expr.info
                               gin))
       :cond
       (b* (((mv new-test (gout gout-test))
             (simpadd0-expr expr.test gin))
            (gin (gin-update gin gout-test))
            ((mv new-then (gout gout-then))
             (simpadd0-expr-option expr.then gin))
            (gin (gin-update gin gout-then))
            ((mv new-else (gout gout-else))
             (simpadd0-expr expr.else gin))
            (gin (gin-update gin gout-else)))
         (xeq-expr-cond expr.test
                        new-test
                        gout-test.thm-name
                        expr.then
                        new-then
                        gout-then.thm-name
                        expr.else
                        new-else
                        gout-else.thm-name
                        gin))
       :comma
       (b* (((mv new-first (gout gout-first))
             (simpadd0-expr expr.first gin))
            (gin (gin-update gin gout-first))
            ((mv new-next (gout gout-next))
             (simpadd0-expr expr.next gin))
            (gin (gin-update gin gout-next)))
         (mv (make-expr-comma :first new-first
                              :next new-next)
             (gout-no-thm gin)))
       :stmt
       (b* (((mv new-cstmt (gout gout-cstmt))
             (simpadd0-comp-stmt expr.stmt gin))
            (gin (gin-update gin gout-cstmt)))
         (mv (expr-stmt new-cstmt)
             (gout-no-thm gin)))
       :tycompat
       (b* (((mv new-type1 (gout gout-type1))
             (simpadd0-tyname expr.type1 gin))
            (gin (gin-update gin gout-type1))
            ((mv new-type2 (gout gout-type2))
             (simpadd0-tyname expr.type2 gin))
            (gin (gin-update gin gout-type2)))
         (mv (make-expr-tycompat :type1 new-type1
                                 :type2 new-type2)
             (gout-no-thm gin)))
       :offsetof
       (b* (((mv new-type (gout gout-type))
             (simpadd0-tyname expr.type gin))
            (gin (gin-update gin gout-type))
            ((mv new-member (gout gout-member))
             (simpadd0-member-designor expr.member gin))
            (gin (gin-update gin gout-member)))
         (mv (make-expr-offsetof :type new-type
                                 :member new-member)
             (gout-no-thm gin)))
       :va-arg
       (b* (((mv new-list (gout gout-list))
             (simpadd0-expr expr.list gin))
            (gin (gin-update gin gout-list))
            ((mv new-type (gout gout-type))
             (simpadd0-tyname expr.type gin))
            (gin (gin-update gin gout-type)))
         (mv (make-expr-va-arg :list new-list
                               :type new-type)
             (gout-no-thm gin)))
       :extension
       (b* (((mv new-expr (gout gout-expr))
             (simpadd0-expr expr.expr gin))
            (gin (gin-update gin gout-expr)))
         (mv (expr-extension new-expr)
             (gout-no-thm gin)))
       :otherwise (prog2$ (impossible) (mv (irr-expr) (irr-gout)))))
    :measure (expr-count expr))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-expr-list ((exprs expr-listp) (gin ginp))
    :guard (and (expr-list-unambp exprs)
                (expr-list-annop exprs))
    :returns (mv (new-exprs expr-listp)
                 (gout goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a list of expressions."
    (b* (((gin gin) gin)
         ((when (endp exprs))
          (mv nil (gout-no-thm gin)))
         ((mv new-expr (gout gout-expr))
          (simpadd0-expr (car exprs) gin))
         (gin (gin-update gin gout-expr))
         ((mv new-exprs (gout gout-exprs))
          (simpadd0-expr-list (cdr exprs) gin))
         (gin (gin-update gin gout-exprs)))
      (mv (cons new-expr new-exprs)
          (gout-no-thm gin)))
    :measure (expr-list-count exprs))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-expr-option ((expr? expr-optionp) (gin ginp))
    :guard (and (expr-option-unambp expr?)
                (expr-option-annop expr?))
    :returns (mv (new-expr? expr-optionp)
                 (gout goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform an optional expression."
    (b* (((gin gin) gin))
      (expr-option-case
       expr?
       :some (simpadd0-expr expr?.val gin)
       :none (mv nil (gout-no-thm gin))))
    :measure (expr-option-count expr?)

    ///

    (defret simpadd0-expr-option-iff-expr-option
      (iff new-expr? expr?)
      :hints (("Goal" :expand (simpadd0-expr-option expr? gin)))))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-const-expr ((cexpr const-exprp) (gin ginp))
    :guard (and (const-expr-unambp cexpr)
                (const-expr-annop cexpr))
    :returns (mv (new-cexpr const-exprp)
                 (gout goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a constant expression."
    (b* (((gin gin) gin)
         ((mv new-expr (gout gout-expr))
          (simpadd0-expr (const-expr->expr cexpr) gin))
         (gin (gin-update gin gout-expr)))
      (mv (const-expr new-expr)
          (gout-no-thm gin)))
    :measure (const-expr-count cexpr))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-const-expr-option ((cexpr? const-expr-optionp)
                                      (gin ginp))
    :guard (and (const-expr-option-unambp cexpr?)
                (const-expr-option-annop cexpr?))
    :returns (mv (new-cexpr? const-expr-optionp)
                 (gout goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform an optional constant expression."
    (b* (((gin gin) gin))
      (const-expr-option-case
       cexpr?
       :some (simpadd0-const-expr cexpr?.val gin)
       :none (mv nil (gout-no-thm gin))))
    :measure (const-expr-option-count cexpr?))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-genassoc ((genassoc genassocp) (gin ginp))
    :guard (and (genassoc-unambp genassoc)
                (genassoc-annop genassoc))
    :returns (mv (new-genassoc genassocp)
                 (gout goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a generic association."
    (b* (((gin gin) gin))
      (genassoc-case
       genassoc
       :type
       (b* (((mv new-type (gout gout-type))
             (simpadd0-tyname genassoc.type gin))
            (gin (gin-update gin gout-type))
            ((mv new-expr (gout gout-expr))
             (simpadd0-expr genassoc.expr gin))
            (gin (gin-update gin gout-expr)))
         (mv (make-genassoc-type :type new-type
                                 :expr new-expr)
             (gout-no-thm gin)))
       :default
       (b* (((mv new-expr (gout gout-expr))
             (simpadd0-expr genassoc.expr gin))
            (gin (gin-update gin gout-expr)))
         (mv (genassoc-default new-expr)
             (gout-no-thm gin)))))
    :measure (genassoc-count genassoc))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-genassoc-list ((genassocs genassoc-listp)
                                  (gin ginp))
    :guard (and (genassoc-list-unambp genassocs)
                (genassoc-list-annop genassocs))
    :returns (mv (new-genassocs genassoc-listp)
                 (gout goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a list of generic associations."
    (b* (((gin gin) gin)
         ((when (endp genassocs))
          (mv nil (gout-no-thm gin)))
         ((mv new-assoc (gout gout-assoc))
          (simpadd0-genassoc (car genassocs) gin))
         (gin (gin-update gin gout-assoc))
         ((mv new-assocs (gout gout-assocs))
          (simpadd0-genassoc-list (cdr genassocs) gin))
         (gin (gin-update gin gout-assocs)))
      (mv (cons new-assoc new-assocs)
          (gout-no-thm gin)))
    :measure (genassoc-list-count genassocs))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-member-designor ((memdes member-designorp)
                                    (gin ginp))
    :guard (and (member-designor-unambp memdes)
                (member-designor-annop memdes))
    :returns (mv (new-memdes member-designorp)
                 (gout goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a member designator."
    (b* (((gin gin) gin))
      (member-designor-case
       memdes
       :ident (mv (member-designor-fix memdes) (gout-no-thm gin))
       :dot
       (b* (((mv new-member (gout gout-member))
             (simpadd0-member-designor memdes.member gin))
            (gin (gin-update gin gout-member)))
         (mv (make-member-designor-dot :member new-member
                                       :name memdes.name)
             (gout-no-thm gin)))
       :sub
       (b* (((mv new-member (gout gout-member))
             (simpadd0-member-designor memdes.member gin))
            (gin (gin-update gin gout-member))
            ((mv new-index (gout gout-index))
             (simpadd0-expr memdes.index gin))
            (gin (gin-update gin gout-member)))
         (mv (make-member-designor-sub :member new-member
                                       :index new-index)
             (gout-no-thm gin)))))
    :measure (member-designor-count memdes))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-type-spec ((tyspec type-specp) (gin ginp))
    :guard (and (type-spec-unambp tyspec)
                (type-spec-annop tyspec))
    :returns (mv (new-tyspec type-specp)
                 (gout goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a type specifier."
    (b* (((gin gin) gin)
         (gout0 (gout-no-thm gin)))
      (type-spec-case
       tyspec
       :void (mv (type-spec-fix tyspec) gout0)
       :char (mv (type-spec-fix tyspec) gout0)
       :short (mv (type-spec-fix tyspec) gout0)
       :int (mv (type-spec-fix tyspec) gout0)
       :long (mv (type-spec-fix tyspec) gout0)
       :float (mv (type-spec-fix tyspec) gout0)
       :double (mv (type-spec-fix tyspec) gout0)
       :signed (mv (type-spec-fix tyspec) gout0)
       :unsigned (mv (type-spec-fix tyspec) gout0)
       :bool (mv (type-spec-fix tyspec) gout0)
       :complex (mv (type-spec-fix tyspec) gout0)
       :atomic (b* (((mv new-type (gout gout-type))
                     (simpadd0-tyname tyspec.type gin))
                    (gin (gin-update gin gout-type)))
                 (mv (type-spec-atomic new-type)
                     (gout-no-thm gin)))
       :struct (b* (((mv new-spec (gout gout-spec))
                     (simpadd0-struni-spec tyspec.spec gin))
                    (gin (gin-update gin gout-spec)))
                 (mv (type-spec-struct new-spec)
                     (gout-no-thm gin)))
       :union (b* (((mv new-spec (gout gout-spec))
                    (simpadd0-struni-spec tyspec.spec gin))
                   (gin (gin-update gin gout-spec)))
                (mv (type-spec-union new-spec)
                    (gout-no-thm gin)))
       :enum (b* (((mv new-spec (gout gout-spec))
                   (simpadd0-enum-spec tyspec.spec gin))
                  (gin (gin-update gin gout-spec)))
               (mv (type-spec-enum new-spec)
                   (gout-no-thm gin)))
       :typedef (mv (type-spec-fix tyspec) gout0)
       :int128 (mv (type-spec-fix tyspec) gout0)
       :locase-float80 (mv (type-spec-fix tyspec) gout0)
       :locase-float128 (mv (type-spec-fix tyspec) gout0)
       :float16 (mv (type-spec-fix tyspec) gout0)
       :float16x (mv (type-spec-fix tyspec) gout0)
       :float32 (mv (type-spec-fix tyspec) gout0)
       :float32x (mv (type-spec-fix tyspec) gout0)
       :float64 (mv (type-spec-fix tyspec) gout0)
       :float64x (mv (type-spec-fix tyspec) gout0)
       :float128 (mv (type-spec-fix tyspec) gout0)
       :float128x (mv (type-spec-fix tyspec) gout0)
       :builtin-va-list (mv (type-spec-fix tyspec) gout0)
       :struct-empty (mv (type-spec-fix tyspec) gout0)
       :typeof-expr (b* (((mv new-expr (gout gout-expr))
                          (simpadd0-expr tyspec.expr gin))
                         (gin (gin-update gin gout-expr)))
                      (mv (make-type-spec-typeof-expr :expr new-expr
                                                      :uscores tyspec.uscores)
                          (gout-no-thm gin)))
       :typeof-type (b* (((mv new-type (gout gout-type))
                          (simpadd0-tyname tyspec.type gin))
                         (gin (gin-update gin gout-type)))
                      (mv (make-type-spec-typeof-type :type new-type
                                                      :uscores tyspec.uscores)
                          (gout-no-thm gin)))
       :typeof-ambig (prog2$ (impossible)
                             (mv (irr-type-spec) (irr-gout)))
       :auto-type (mv (type-spec-fix tyspec) gout0)))
    :measure (type-spec-count tyspec))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-spec/qual ((specqual spec/qual-p)
                              (gin ginp))
    :guard (and (spec/qual-unambp specqual)
                (spec/qual-annop specqual))
    :returns (mv (new-specqual spec/qual-p)
                 (gout goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a type specifier or qualifier."
    (b* (((gin gin) gin))
      (spec/qual-case
       specqual
       :typespec (b* (((mv new-spec (gout gout-spec))
                       (simpadd0-type-spec specqual.spec gin))
                      (gin (gin-update gin gout-spec)))
                   (mv (spec/qual-typespec new-spec)
                       (gout-no-thm gin)))
       :typequal (mv (spec/qual-fix specqual) (gout-no-thm gin))
       :align (b* (((mv new-spec (gout gout-spec))
                    (simpadd0-align-spec specqual.spec gin))
                   (gin (gin-update gin gout-spec)))
                (mv (spec/qual-align new-spec)
                    (gout-no-thm gin)))
       :attrib (mv (spec/qual-fix specqual) (gout-no-thm gin))))
    :measure (spec/qual-count specqual))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-spec/qual-list ((specquals spec/qual-listp)
                                   (gin ginp))
    :guard (and (spec/qual-list-unambp specquals)
                (spec/qual-list-annop specquals))
    :returns (mv (new-specquals spec/qual-listp)
                 (gout goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a list of type specifiers and qualifiers."
    (b* (((gin gin) gin)
         ((when (endp specquals))
          (mv nil (gout-no-thm gin)))
         ((mv new-specqual (gout gout-specqual))
          (simpadd0-spec/qual (car specquals) gin))
         (gin (gin-update gin gout-specqual))
         ((mv new-specquals (gout gout-specquals))
          (simpadd0-spec/qual-list (cdr specquals) gin))
         (gin (gin-update gin gout-specquals)))
      (mv (cons new-specqual new-specquals)
          (gout-no-thm gin)))
    :measure (spec/qual-list-count specquals))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-align-spec ((alignspec align-specp)
                               (gin ginp))
    :guard (and (align-spec-unambp alignspec)
                (align-spec-annop alignspec))
    :returns (mv (new-alignspec align-specp)
                 (gout goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform an alignment specifier."
    (b* (((gin gin) gin))
      (align-spec-case
       alignspec
       :alignas-type (b* (((mv new-type (gout gout-type))
                           (simpadd0-tyname alignspec.type gin))
                          (gin (gin-update gin gout-type)))
                       (mv (align-spec-alignas-type new-type)
                           (gout-no-thm gin)))
       :alignas-expr (b* (((mv new-expr (gout gout-expr))
                           (simpadd0-const-expr alignspec.expr gin))
                          (gin (gin-update gin gout-expr)))
                       (mv (align-spec-alignas-expr new-expr)
                           (gout-no-thm gin)))
       :alignas-ambig (prog2$ (impossible)
                              (mv (irr-align-spec) (irr-gout)))))
    :measure (align-spec-count alignspec))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-decl-spec ((declspec decl-specp) (gin ginp))
    :guard (and (decl-spec-unambp declspec)
                (decl-spec-annop declspec))
    :returns (mv (new-declspec decl-specp)
                 (gout goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a declaration specifier."
    (b* (((gin gin) gin))
      (decl-spec-case
       declspec
       :stoclass (mv (decl-spec-fix declspec) (gout-no-thm gin))
       :typespec (b* (((mv new-spec (gout gout-spec))
                       (simpadd0-type-spec declspec.spec gin))
                      (gin (gin-update gin gout-spec)))
                   (mv (decl-spec-typespec new-spec)
                       (gout-no-thm gin)))
       :typequal (mv (decl-spec-fix declspec) (gout-no-thm gin))
       :function (mv (decl-spec-fix declspec) (gout-no-thm gin))
       :align (b* (((mv new-spec (gout gout-spec))
                    (simpadd0-align-spec declspec.spec gin))
                   (gin (gin-update gin gout-spec)))
                (mv (decl-spec-align new-spec)
                    (gout-no-thm gin)))
       :attrib (mv (decl-spec-fix declspec) (gout-no-thm gin))
       :stdcall (mv (decl-spec-fix declspec) (gout-no-thm gin))
       :declspec (mv (decl-spec-fix declspec) (gout-no-thm gin))))
    :measure (decl-spec-count declspec))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-decl-spec-list ((declspecs decl-spec-listp)
                                   (gin ginp))
    :guard (and (decl-spec-list-unambp declspecs)
                (decl-spec-list-annop declspecs))
    :returns (mv (new-declspecs decl-spec-listp)
                 (gout goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a list of declaration specifiers."
    (b* (((gin gin) gin)
         ((when (endp declspecs))
          (mv nil (gout-no-thm gin)))
         ((mv new-declspec (gout gout-declspec))
          (simpadd0-decl-spec (car declspecs) gin))
         (gin (gin-update gin gout-declspec))
         ((mv new-declspecs (gout gout-declspecs))
          (simpadd0-decl-spec-list (cdr declspecs) gin))
         (gin (gin-update gin gout-declspecs)))
      (mv (cons new-declspec new-declspecs)
          (gout-no-thm gin)))
    :measure (decl-spec-list-count declspecs))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-initer ((initer initerp) (gin ginp))
    :guard (and (initer-unambp initer)
                (initer-annop initer))
    :returns (mv (new-initer initerp)
                 (gout goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform an initializer."
    (b* (((gin gin) gin))
      (initer-case
       initer
       :single (b* (((mv new-expr (gout gout-expr))
                     (simpadd0-expr initer.expr gin))
                    (gin (gin-update gin gout-expr)))
                 (xeq-initer-single initer.expr
                                    new-expr
                                    gout-expr.thm-name
                                    gin))
       :list (b* (((mv new-elems (gout gout-elems))
                   (simpadd0-desiniter-list initer.elems gin))
                  (gin (gin-update gin gout-elems)))
               (mv (make-initer-list :elems new-elems
                                     :final-comma initer.final-comma)
                   (gout-no-thm gin)))))
    :measure (initer-count initer))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-initer-option ((initer? initer-optionp)
                                  (gin ginp))
    :guard (and (initer-option-unambp initer?)
                (initer-option-annop initer?))
    :returns (mv (new-initer? initer-optionp)
                 (gout goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform an optional initializer."
    (b* (((gin gin) gin))
      (initer-option-case
       initer?
       :some (simpadd0-initer initer?.val gin)
       :none (mv nil (gout-no-thm gin))))
    :measure (initer-option-count initer?))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-desiniter ((desiniter desiniterp)
                              (gin ginp))
    :guard (and (desiniter-unambp desiniter)
                (desiniter-annop desiniter))
    :returns (mv (new-desiniter desiniterp)
                 (gout goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform an initializer with optional designations."
    (b* (((desiniter desiniter) desiniter)
         ((mv new-designors (gout gout-designors))
          (simpadd0-designor-list desiniter.designors gin))
         ((mv new-initer (gout gout-initer))
          (simpadd0-initer desiniter.initer gin))
         (gin (gin-update gin gout-initer)))
      (mv (make-desiniter :designors new-designors
                          :initer new-initer)
          (gout-no-thm gin)))
    :measure (desiniter-count desiniter))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-desiniter-list ((desiniters desiniter-listp) (gin ginp))
    :guard (and (desiniter-list-unambp desiniters)
                (desiniter-list-annop desiniters))
    :returns (mv (new-desiniters desiniter-listp)
                 (gout goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a list of initializers with optional designations."
    (b* (((gin gin) gin)
         ((when (endp desiniters))
          (mv nil (gout-no-thm gin)))
         ((mv new-desiniter (gout gout-desiniter))
          (simpadd0-desiniter (car desiniters) gin))
         (gin (gin-update gin gout-desiniter))
         ((mv new-desiniters (gout gout-desiniters))
          (simpadd0-desiniter-list (cdr desiniters) gin))
         (gin (gin-update gin gout-desiniters)))
      (mv (cons new-desiniter new-desiniters)
          (gout-no-thm gin)))
    :measure (desiniter-list-count desiniters))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-designor ((designor designorp) (gin ginp))
    :guard (and (designor-unambp designor)
                (designor-annop designor))
    :returns (mv (new-designor designorp)
                 (gout goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a designator."
    (b* (((gin gin) gin))
      (designor-case
       designor
       :sub (b* (((mv new-index (gout gout-index))
                  (simpadd0-const-expr designor.index gin))
                 (gin (gin-update gin gout-index))
                 ((mv new-range? (gout gout-range?))
                  (simpadd0-const-expr-option designor.range? gin))
                 (gin (gin-update gin gout-range?)))
              (mv (make-designor-sub :index new-index :range? new-range?)
                  (gout-no-thm gin)))
       :dot (mv (designor-fix designor) (gout-no-thm gin))))
    :measure (designor-count designor))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-designor-list ((designors designor-listp) (gin ginp))
    :guard (and (designor-list-unambp designors)
                (designor-list-annop designors))
    :returns (mv (new-designors designor-listp)
                 (gout goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a list of designators."
    (b* (((gin gin) gin)
         ((when (endp designors))
          (mv nil (gout-no-thm gin)))
         ((mv new-designor (gout gout-designor))
          (simpadd0-designor (car designors) gin))
         (gin (gin-update gin gout-designor))
         ((mv new-designors (gout gout-designors))
          (simpadd0-designor-list (cdr designors) gin))
         (gin (gin-update gin gout-designors)))
      (mv (cons new-designor new-designors)
          (gout-no-thm gin)))
    :measure (designor-list-count designors))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-declor ((declor declorp) (fundefp booleanp) (gin ginp))
    :guard (and (declor-unambp declor)
                (declor-annop declor))
    :returns (mv (new-declor declorp)
                 (new-fundefp booleanp)
                 (gout goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a declarator."
    :long
    (xdoc::topstring
     (xdoc::p
      "The @('fundefp') flag is set iff
       the declarator is (part of) the one of a function definition
       whose parameters have not been transformed yet;
       see the callers of this function.
       A possibly changed flag is returned as output:
       see @(tsee simpadd0-dirdeclor) for its use and possile change."))
    (b* (((gin gin) gin)
         ((declor declor) declor)
         ((mv new-direct fundefp (gout gout-direct))
          (simpadd0-dirdeclor declor.direct fundefp gin))
         (gin (gin-update gin gout-direct)))
      (mv (make-declor :pointers declor.pointers
                       :direct new-direct)
          fundefp
          (change-gout (gout-no-thm gin)
                       :vartys gout-direct.vartys)))
    :measure (declor-count declor))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-declor-option ((declor? declor-optionp) (gin ginp))
    :guard (and (declor-option-unambp declor?)
                (declor-option-annop declor?))
    :returns (mv (new-declor? declor-optionp)
                 (gout goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform an optional declarator."
    (b* (((gin gin) gin))
      (declor-option-case
       declor?
       :some (b* (((mv new-declor & gout)
                   (simpadd0-declor declor?.val nil gin)))
               (mv new-declor gout))
       :none (mv nil (gout-no-thm gin))))
    :measure (declor-option-count declor?))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-dirdeclor ((dirdeclor dirdeclorp)
                              (fundefp booleanp)
                              (gin ginp))
    :guard (and (dirdeclor-unambp dirdeclor)
                (dirdeclor-annop dirdeclor))
    :returns (mv (new-dirdeclor dirdeclorp)
                 (new-fundefp booleanp)
                 (gout goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a direct declarator."
    :long
    (xdoc::topstring
     (xdoc::p
      "The @('fundefp') flag is set iff
       the direct declarator is (part of) the one of a function definition
       whose parameters have not been transformed yet;
       this function is only called by @(tsee simpadd0-declor)
       (see how the callers of @(tsee simpadd0-declor) set @('fundefp')),
       and recursively by itself.")
     (xdoc::p
      "The @('fundefp') flag is just threaded through most recursively calls.
       For the @(':function-params') kind of direct declarator,
       if @('fundefp') is @('t'),
       then the variable-type map resulting from
       transforming the parameter declarations
       is return as part of the @('gout') of this ACL2 function,
       so that the extended map is available for the function's body.
       Additionally, in this case the @('fundefp') result is @('nil'),
       because the parameters of the function definition have been
       transformed and the variable-type map has been extended for the body.
       If instead the input @('fundefp') is @('nil'),
       the variable-type map resulting from the parameters
       is discarded and not returned as part of the @('gout').")
     (xdoc::p
      "In the @(':function-names') case,
       there is no extension of the variable-type map,
       but we set the @('fundefp') output to @('nil')."))
    (b* (((gin gin) gin))
      (dirdeclor-case
       dirdeclor
       :ident (mv (dirdeclor-fix dirdeclor)
                  (acl2::bool-fix fundefp)
                  (gout-no-thm gin))
       :paren (b* (((mv new-declor fundefp (gout gout-declor))
                    (simpadd0-declor dirdeclor.inner fundefp gin))
                   (gin (gin-update gin gout-declor)))
                (mv (dirdeclor-paren new-declor)
                    fundefp
                    (gout-no-thm gin)))
       :array (b* (((mv new-decl fundefp (gout gout-decl))
                    (simpadd0-dirdeclor dirdeclor.declor fundefp gin))
                   (gin (gin-update gin gout-decl))
                   ((mv new-expr? (gout gout-expr?))
                    (simpadd0-expr-option dirdeclor.size? gin))
                   (gin (gin-update gin gout-expr?)))
                (mv (make-dirdeclor-array :declor new-decl
                                          :qualspecs dirdeclor.qualspecs
                                          :size? new-expr?)
                    fundefp
                    (gout-no-thm gin)))
       :array-static1 (b* (((mv new-decl fundefp (gout gout-decl))
                            (simpadd0-dirdeclor dirdeclor.declor fundefp gin))
                           (gin (gin-update gin gout-decl))
                           ((mv new-expr (gout gout-expr))
                            (simpadd0-expr dirdeclor.size gin))
                           (gin (gin-update gin gout-expr)))
                        (mv (make-dirdeclor-array-static1
                             :declor new-decl
                             :qualspecs dirdeclor.qualspecs
                             :size new-expr)
                            fundefp
                            (gout-no-thm gin)))
       :array-static2 (b* (((mv new-decl fundefp (gout gout-decl))
                            (simpadd0-dirdeclor dirdeclor.declor fundefp gin))
                           (gin (gin-update gin gout-decl))
                           ((mv new-expr (gout gout-expr))
                            (simpadd0-expr dirdeclor.size gin))
                           (gin (gin-update gin gout-expr)))
                        (mv (make-dirdeclor-array-static2
                             :declor new-decl
                             :qualspecs dirdeclor.qualspecs
                             :size new-expr)
                            fundefp
                            (gout-no-thm gin)))
       :array-star (b* (((mv new-decl fundefp (gout gout-decl))
                         (simpadd0-dirdeclor dirdeclor.declor fundefp gin))
                        (gin (gin-update gin gout-decl)))
                     (mv (make-dirdeclor-array-star
                          :declor new-decl
                          :qualspecs dirdeclor.qualspecs)
                         fundefp
                         (gout-no-thm gin)))
       :function-params (b* (((mv new-declor fundefp (gout gout-declor))
                              (simpadd0-dirdeclor dirdeclor.declor fundefp gin))
                             (gin (gin-update gin gout-declor))
                             ((mv new-params (gout gout-params))
                              (simpadd0-param-declon-list dirdeclor.params gin))
                             (gin (gin-update gin gout-params))
                             (gout (if fundefp
                                       (change-gout (gout-no-thm gin)
                                                    :vartys gout-params.vartys)
                                     (gout-no-thm gin))))
                          (mv (make-dirdeclor-function-params
                               :declor new-declor
                               :params new-params
                               :ellipsis dirdeclor.ellipsis)
                              nil
                              gout))
       :function-names (b* (((mv new-declor & (gout gout-declor))
                             (simpadd0-dirdeclor dirdeclor.declor fundefp gin))
                            (gin (gin-update gin gout-declor)))
                         (mv (make-dirdeclor-function-names
                              :declor new-declor
                              :names dirdeclor.names)
                             nil
                             (gout-no-thm gin)))))
    :measure (dirdeclor-count dirdeclor))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-absdeclor ((absdeclor absdeclorp) (gin ginp))
    :guard (and (absdeclor-unambp absdeclor)
                (absdeclor-annop absdeclor))
    :returns (mv (new-absdeclor absdeclorp)
                 (gout goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform an abstract declarator."
    (b* (((gin gin) gin)
         ((absdeclor absdeclor) absdeclor)
         ((mv new-direct? (gout gout-direct?))
          (simpadd0-dirabsdeclor-option absdeclor.direct? gin))
         (gin (gin-update gin gout-direct?)))
      (mv (make-absdeclor :pointers absdeclor.pointers
                          :direct? new-direct?)
          (gout-no-thm gin)))
    :measure (absdeclor-count absdeclor))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-absdeclor-option ((absdeclor? absdeclor-optionp)
                                     (gin ginp))
    :guard (and (absdeclor-option-unambp absdeclor?)
                (absdeclor-option-annop absdeclor?))
    :returns (mv (new-absdeclor? absdeclor-optionp)
                 (gout goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform an optional abstract declarator."
    (b* (((gin gin) gin))
      (absdeclor-option-case
       absdeclor?
       :some (simpadd0-absdeclor absdeclor?.val gin)
       :none (mv nil (gout-no-thm gin))))
    :measure (absdeclor-option-count absdeclor?))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-dirabsdeclor ((dirabsdeclor dirabsdeclorp)
                                 (gin ginp))
    :guard (and (dirabsdeclor-unambp dirabsdeclor)
                (dirabsdeclor-annop dirabsdeclor))
    :returns (mv (new-dirabsdeclor dirabsdeclorp)
                 (gout goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a direct abstract declarator."
    (b* (((gin gin) gin))
      (dirabsdeclor-case
       dirabsdeclor
       :dummy-base (prog2$
                    (raise "Misusage error: ~x0."
                           (dirabsdeclor-fix dirabsdeclor))
                    (mv (irr-dirabsdeclor) (irr-gout)))
       :paren (b* (((mv new-inner (gout gout-inner))
                    (simpadd0-absdeclor dirabsdeclor.inner gin))
                   (gin (gin-update gin gout-inner)))
                (mv (dirabsdeclor-paren new-inner)
                    (gout-no-thm gin)))
       :array (b* (((mv new-declor? (gout gout-declor?))
                    (simpadd0-dirabsdeclor-option
                     dirabsdeclor.declor? gin))
                   (gin (gin-update gin gout-declor?))
                   ((mv new-size? (gout gout-expr?))
                    (simpadd0-expr-option dirabsdeclor.size? gin))
                   (gin (gin-update gin gout-expr?)))
                (mv (make-dirabsdeclor-array
                     :declor? new-declor?
                     :qualspecs dirabsdeclor.qualspecs
                     :size? new-size?)
                    (gout-no-thm gin)))
       :array-static1 (b* (((mv new-declor? (gout gout-declor?))
                            (simpadd0-dirabsdeclor-option dirabsdeclor.declor?
                                                          gin))
                           (gin (gin-update gin gout-declor?))
                           ((mv new-size (gout gout-expr))
                            (simpadd0-expr dirabsdeclor.size gin))
                           (gin (gin-update gin gout-expr)))
                        (mv (make-dirabsdeclor-array-static1
                             :declor? new-declor?
                             :qualspecs dirabsdeclor.qualspecs
                             :size new-size)
                            (gout-no-thm gin)))
       :array-static2 (b* (((mv new-declor? (gout gout-declor?))
                            (simpadd0-dirabsdeclor-option dirabsdeclor.declor?
                                                          gin))
                           (gin (gin-update gin gout-declor?))
                           ((mv new-size (gout gout-expr))
                            (simpadd0-expr dirabsdeclor.size gin))
                           (gin (gin-update gin gout-expr)))
                        (mv (make-dirabsdeclor-array-static2
                             :declor? new-declor?
                             :qualspecs dirabsdeclor.qualspecs
                             :size new-size)
                            (gout-no-thm gin)))
       :array-star (b* (((mv new-declor? (gout gout-declor?))
                         (simpadd0-dirabsdeclor-option dirabsdeclor.declor?
                                                       gin))
                        (gin (gin-update gin gout-declor?)))
                     (mv (dirabsdeclor-array-star new-declor?)
                         (gout-no-thm gin)))
       :function (b* (((mv new-declor? (gout gout-declor?))
                       (simpadd0-dirabsdeclor-option dirabsdeclor.declor?
                                                     gin))
                      (gin (gin-update gin gout-declor?))
                      ((mv new-params (gout gout-params))
                       (simpadd0-param-declon-list dirabsdeclor.params gin))
                      (gin (gin-update gin gout-params)))
                   (mv (make-dirabsdeclor-function
                        :declor? new-declor?
                        :params new-params
                        :ellipsis dirabsdeclor.ellipsis)
                       (gout-no-thm gin)))))
    :measure (dirabsdeclor-count dirabsdeclor))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-dirabsdeclor-option ((dirabsdeclor? dirabsdeclor-optionp)
                                        (gin ginp))
    :guard (and (dirabsdeclor-option-unambp dirabsdeclor?)
                (dirabsdeclor-option-annop dirabsdeclor?))
    :returns (mv (new-dirabsdeclor? dirabsdeclor-optionp)
                 (gout goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform an optional direct abstract declarator."
    (b* (((gin gin) gin))
      (dirabsdeclor-option-case
       dirabsdeclor?
       :some (simpadd0-dirabsdeclor dirabsdeclor?.val gin)
       :none (mv nil (gout-no-thm gin))))
    :measure (dirabsdeclor-option-count dirabsdeclor?))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-param-declon ((paramdeclon param-declonp) (gin ginp))
    :guard (and (param-declon-unambp paramdeclon)
                (param-declon-annop paramdeclon))
    :returns (mv (new-paramdeclon param-declonp)
                 (gout goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a parameter declaration."
    :long
    (xdoc::topstring
     (xdoc::p
      "We extend the variable-type map
       according to the parameter declarators/declarations,
       one after the other."))
    (b* (((gin gin) gin)
         ((param-declon paramdeclon) paramdeclon)
         ((mv new-specs (gout gout-specs))
          (simpadd0-decl-spec-list paramdeclon.specs gin))
         (gin (gin-update gin gout-specs))
         ((mv new-declor (gout gout-declor))
          (simpadd0-param-declor paramdeclon.declor gin))
         (gin (gin-update gin gout-declor)))
      (mv (make-param-declon :specs new-specs
                             :declor new-declor
                             :attribs paramdeclon.attribs)
          (change-gout (gout-no-thm gin)
                       :vartys gout-declor.vartys)))
    :measure (param-declon-count paramdeclon))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-param-declon-list ((paramdeclons param-declon-listp)
                                      (gin ginp))
    :guard (and (param-declon-list-unambp paramdeclons)
                (param-declon-list-annop paramdeclons))
    :returns (mv (new-paramdeclons param-declon-listp)
                 (gout goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a list of parameter declarations."
    :long
    (xdoc::topstring
     (xdoc::p
      "We extend the variable-type map
       if it was extended by the parameter declarator."))
    (b* (((gin gin) gin)
         ((when (endp paramdeclons))
          (mv nil (gout-no-thm gin)))
         ((mv new-paramdeclon (gout gout-paramdeclon))
          (simpadd0-param-declon (car paramdeclons) gin))
         (gin (gin-update gin gout-paramdeclon))
         ((mv new-paramdeclons (gout gout-paramdeclons))
          (simpadd0-param-declon-list (cdr paramdeclons)
                                      (change-gin
                                       gin :vartys gout-paramdeclon.vartys)))
         (gin (gin-update gin gout-paramdeclons)))
      (mv (cons new-paramdeclon new-paramdeclons)
          (change-gout (gout-no-thm gin)
                       :vartys gout-paramdeclons.vartys)))
    :measure (param-declon-list-count paramdeclons))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-param-declor ((paramdeclor param-declorp) (gin ginp))
    :guard (and (param-declor-unambp paramdeclor)
                (param-declor-annop paramdeclor))
    :returns (mv (new-paramdeclor param-declorp)
                 (gout goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a parameter declarator."
    :long
    (xdoc::topstring
     (xdoc::p
      "If the type of the parameter declarator
       is in the subset supported by our formal semantics,
       we extend the variable-type map with the parameter and its type."))
    (b* (((gin gin) gin))
      (param-declor-case
       paramdeclor
       :nonabstract
       (b* (((mv new-declor & (gout gout-declor))
             (simpadd0-declor paramdeclor.declor nil gin))
            (gin (gin-update gin gout-declor))
            (type (param-declor-nonabstract-info->type paramdeclor.info))
            (ident (declor->ident paramdeclor.declor))
            (post-vartys
             (if (and (ident-formalp ident)
                      (type-formalp type)
                      (not (type-case type :void))
                      (not (type-case type :char)))
                 (b* (((mv & cvar) (ldm-ident ident))
                      ((mv & ctype) (ldm-type type)))
                   (omap::update cvar ctype gin.vartys))
               gin.vartys)))
         (mv (make-param-declor-nonabstract
              :declor new-declor
              :info paramdeclor.info)
             (change-gout (gout-no-thm gin)
                          :vartys post-vartys)))
       :abstract (b* (((mv new-absdeclor (gout gout-absdeclor))
                       (simpadd0-absdeclor paramdeclor.declor gin))
                      (gin (gin-update gin gout-absdeclor)))
                   (mv (param-declor-abstract new-absdeclor)
                       (gout-no-thm gin)))
       :none (mv (param-declor-none) (gout-no-thm gin))
       :ambig (prog2$ (impossible) (mv (irr-param-declor) (irr-gout)))))
    :measure (param-declor-count paramdeclor))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-tyname ((tyname tynamep) (gin ginp))
    :guard (and (tyname-unambp tyname)
                (tyname-annop tyname))
    :returns (mv (new-tyname tynamep)
                 (gout goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a type name."
    (b* (((gin gin) gin)
         ((tyname tyname) tyname)
         ((mv new-specquals (gout gout-specqual))
          (simpadd0-spec/qual-list tyname.specquals gin))
         (gin (gin-update gin gout-specqual))
         ((mv new-declor? (gout gout-declor?))
          (simpadd0-absdeclor-option tyname.declor? gin))
         (gin (gin-update gin gout-declor?)))
      (mv (make-tyname :specquals new-specquals
                       :declor? new-declor?
                       :info tyname.info)
          (gout-no-thm gin)))
    :measure (tyname-count tyname))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-struni-spec ((struni-spec struni-specp)
                                (gin ginp))
    :guard (and (struni-spec-unambp struni-spec)
                (struni-spec-annop struni-spec))
    :returns (mv (new-struni-spec struni-specp)
                 (gout goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a structure or union specifier."
    (b* (((gin gin) gin)
         ((struni-spec struni-spec) struni-spec)
         ((mv new-members (gout gout-members))
          (simpadd0-struct-declon-list struni-spec.members gin))
         (gin (gin-update gin gout-members)))
      (mv (make-struni-spec :attribs struni-spec.attribs
                            :name? struni-spec.name?
                            :members new-members)
          (gout-no-thm gin)))
    :measure (struni-spec-count struni-spec))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-struct-declon ((structdeclon struct-declonp)
                                  (gin ginp))
    :guard (and (struct-declon-unambp structdeclon)
                (struct-declon-annop structdeclon))
    :returns (mv (new-structdeclon struct-declonp)
                 (gout goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a structure declaration."
    (b* (((gin gin) gin))
      (struct-declon-case
       structdeclon
       :member (b* (((mv new-specquals (gout gout-specqual))
                     (simpadd0-spec/qual-list structdeclon.specquals gin))
                    (gin (gin-update gin gout-specqual))
                    ((mv new-declors (gout gout-declor))
                     (simpadd0-struct-declor-list structdeclon.declors gin))
                    (gin (gin-update gin gout-declor)))
                 (mv (make-struct-declon-member
                      :extension structdeclon.extension
                      :specquals new-specquals
                      :declors new-declors
                      :attribs structdeclon.attribs)
                     (gout-no-thm gin)))
       :statassert (b* (((mv new-structdeclon (gout gout-structdeclon))
                         (simpadd0-statassert structdeclon.statassert gin))
                        (gin (gin-update gin gout-structdeclon)))
                     (mv (struct-declon-statassert new-structdeclon)
                         (gout-no-thm gin)))
       :empty (mv (struct-declon-empty) (gout-no-thm gin))))
    :measure (struct-declon-count structdeclon))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-struct-declon-list ((structdeclons struct-declon-listp)
                                       (gin ginp))
    :guard (and (struct-declon-list-unambp structdeclons)
                (struct-declon-list-annop structdeclons))
    :returns (mv (new-structdeclons struct-declon-listp)
                 (gout goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a list of structure declarations."
    (b* (((gin gin) gin)
         ((when (endp structdeclons))
          (mv nil (gout-no-thm gin)))
         ((mv new-structdeclon (gout gout-structdeclon))
          (simpadd0-struct-declon (car structdeclons) gin))
         (gin (gin-update gin gout-structdeclon))
         ((mv new-structdeclons (gout gout-structdeclons))
          (simpadd0-struct-declon-list (cdr structdeclons) gin))
         (gin (gin-update gin gout-structdeclons)))
      (mv (cons new-structdeclon new-structdeclons)
          (gout-no-thm gin)))
    :measure (struct-declon-list-count structdeclons))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-struct-declor ((structdeclor struct-declorp)
                                  (gin ginp))
    :guard (and (struct-declor-unambp structdeclor)
                (struct-declor-annop structdeclor))
    :returns (mv (new-structdeclor struct-declorp)
                 (gout goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a structure declarator."
    (b* (((gin gin) gin)
         ((struct-declor structdeclor) structdeclor)
         ((mv new-declor? (gout gout-declor?))
          (simpadd0-declor-option structdeclor.declor? gin))
         (gin (gin-update gin gout-declor?))
         ((mv new-expr? (gout gout-expr?))
          (simpadd0-const-expr-option structdeclor.expr? gin))
         (gin (gin-update gin gout-expr?)))
      (mv (make-struct-declor :declor? new-declor?
                              :expr? new-expr?)
          (gout-no-thm gin)))
    :measure (struct-declor-count structdeclor))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-struct-declor-list ((structdeclors struct-declor-listp)
                                       (gin ginp))
    :guard (and (struct-declor-list-unambp structdeclors)
                (struct-declor-list-annop structdeclors))
    :returns (mv (new-structdeclors struct-declor-listp)
                 (gout goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a list of structure declarators."
    (b* (((gin gin) gin)
         ((when (endp structdeclors))
          (mv nil (gout-no-thm gin)))
         ((mv new-structdeclor (gout gout-structdeclor))
          (simpadd0-struct-declor (car structdeclors) gin))
         (gin (gin-update gin gout-structdeclor))
         ((mv new-structdeclors (gout gout-structdeclors))
          (simpadd0-struct-declor-list (cdr structdeclors) gin))
         (gin (gin-update gin gout-structdeclors)))
      (mv (cons new-structdeclor new-structdeclors)
          (gout-no-thm gin)))
    :measure (struct-declor-list-count structdeclors))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-enum-spec ((enumspec enum-specp) (gin ginp))
    :guard (and (enum-spec-unambp enumspec)
                (enum-spec-annop enumspec))
    :returns (mv (new-enumspec enum-specp)
                 (gout goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform an enumeration specifier."
    (b* (((gin gin) gin)
         ((enum-spec enumspec) enumspec)
         ((mv new-enumers (gout gout-list))
          (simpadd0-enumer-list enumspec.enumers gin))
         (gin (gin-update gin gout-list)))
      (mv (make-enum-spec :name? enumspec.name?
                          :enumers new-enumers
                          :final-comma enumspec.final-comma)
          (gout-no-thm gin)))
    :measure (enum-spec-count enumspec))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-enumer ((enumer enumerp) (gin ginp))
    :guard (and (enumer-unambp enumer)
                (enumer-annop enumer))
    :returns (mv (new-enumer enumerp)
                 (gout goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform an enumerator."
    (b* (((gin gin) gin)
         ((enumer enumer) enumer)
         ((mv new-value? (gout gout-value))
          (simpadd0-const-expr-option enumer.value? gin))
         (gin (gin-update gin gout-value)))
      (mv (make-enumer :name enumer.name
                       :value? new-value?)
          (gout-no-thm gin)))
    :measure (enumer-count enumer))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-enumer-list ((enumers enumer-listp) (gin ginp))
    :guard (and (enumer-list-unambp enumers)
                (enumer-list-annop enumers))
    :returns (mv (new-enumers enumer-listp)
                 (gout goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a list of enumerators."
    (b* (((gin gin) gin)
         ((when (endp enumers))
          (mv nil (gout-no-thm gin)))
         ((mv new-enumer (gout gout-enumer))
          (simpadd0-enumer (car enumers) gin))
         (gin (gin-update gin gout-enumer))
         ((mv new-enumers (gout gout-enumers))
          (simpadd0-enumer-list (cdr enumers) gin))
         (gin (gin-update gin gout-enumers)))
      (mv (cons new-enumer new-enumers)
          (gout-no-thm gin)))
    :measure (enumer-list-count enumers))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-statassert ((statassert statassertp) (gin ginp))
    :guard (and (statassert-unambp statassert)
                (statassert-annop statassert))
    :returns (mv (new-statassert statassertp)
                 (gout goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform an static assertion declaration."
    (b* (((gin gin) gin)
         ((statassert statassert) statassert)
         ((mv new-test (gout gout-test))
          (simpadd0-const-expr statassert.test gin))
         (gin (gin-update gin gout-test)))
      (mv (make-statassert :test new-test
                           :message statassert.message)
          (gout-no-thm gin)))
    :measure (statassert-count statassert))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-init-declor ((initdeclor init-declorp) (gin ginp))
    :guard (and (init-declor-unambp initdeclor)
                (init-declor-annop initdeclor))
    :returns (mv (new-initdeclor init-declorp)
                 (gout goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform an initializer declarator."
    :long
    (xdoc::topstring
     (xdoc::p
      "If a theorem was generated for the initializer,
       it is regarded as the theorem for the initializer declarator.
       This is so that the theorem can surface up to block item declarations.")
     (xdoc::p
      "If the type of the declared identifier is supported for proof generation,
       we update the variable-type map."))
    (b* (((init-declor initdeclor) initdeclor)
         ((mv new-declor & (gout gout-declor))
          (simpadd0-declor initdeclor.declor nil gin))
         (gin (gin-update gin gout-declor))
         ((mv new-initer? (gout gout-initer?))
          (simpadd0-initer-option initdeclor.initer?
                                  (change-gin
                                   gin :vartys gout-declor.vartys)))
         ((gin gin) (gin-update gin gout-initer?))
         (type (init-declor-info->type initdeclor.info))
         (ident (declor->ident initdeclor.declor))
         (post-vartys
          (if (and (not (init-declor-info->typedefp initdeclor.info))
                   (ident-formalp ident)
                   (type-formalp type)
                   (not (type-case type :void))
                   (not (type-case type :char)))
              (b* (((mv & cvar) (ldm-ident ident))
                   ((mv & ctype) (ldm-type type)))
                (omap::update cvar ctype gout-initer?.vartys))
            gout-initer?.vartys)))
      (mv (make-init-declor :declor new-declor
                            :asm? initdeclor.asm?
                            :attribs initdeclor.attribs
                            :initer? new-initer?
                            :info initdeclor.info)
          (if gout-initer?.thm-name
              (make-gout :events gin.events
                         :thm-index gin.thm-index
                         :thm-name gout-initer?.thm-name
                         :vartys post-vartys)
            (change-gout (gout-no-thm gin)
                         :vartys post-vartys))))
    :measure (init-declor-count initdeclor))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-init-declor-list ((initdeclors init-declor-listp) (gin ginp))
    :guard (and (init-declor-list-unambp initdeclors)
                (init-declor-list-annop initdeclors))
    :returns (mv (new-initdeclors init-declor-listp)
                 (gout goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a list of initializer declarators."
    :long
    (xdoc::topstring
     (xdoc::p
      "If the list is a singleton
       and a theorem was generated for that one element,
       it is regarded as the theorem for the list of initializer declarators.
       This is so that the theorem can surface up to block item declarations."))
    (b* (((when (endp initdeclors))
          (mv nil (gout-no-thm gin)))
         ((mv new-initdeclor (gout gout-initdeclor))
          (simpadd0-init-declor (car initdeclors) gin))
         (gin (gin-update gin gout-initdeclor))
         ((mv new-initdeclors (gout gout-initdeclors))
          (simpadd0-init-declor-list (cdr initdeclors)
                                    (change-gin
                                     gin :vartys gout-initdeclor.vartys)))
         ((gin gin) (gin-update gin gout-initdeclors)))
      (mv (cons new-initdeclor new-initdeclors)
          (if (and (not (consp new-initdeclors))
                   gout-initdeclor.thm-name)
              (make-gout :events gin.events
                         :thm-index gin.thm-index
                         :thm-name gout-initdeclor.thm-name
                         :vartys gout-initdeclor.vartys)
            (change-gout (gout-no-thm gin)
                         :vartys gout-initdeclors.vartys))))
    :measure (init-declor-list-count initdeclors))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-declon ((declon declonp) (gin ginp))
    :guard (and (declon-unambp declon)
                (declon-annop declon))
    :returns (mv (new-declon declonp)
                 (gout goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a declaration."
    :long
    (xdoc::topstring
     (xdoc::p
      "In the case of a non-static-assert declaration,
       if a theorem was generated for the list of initializer declarators,
       it is regarded as the theorem for the declaration.
       This is so that the theorem can surface up to block item declarations."))
    (declon-case
     declon
     :declon (b* (((mv new-specs (gout gout-specs))
                   (simpadd0-decl-spec-list declon.specs gin))
                  (gin (gin-update gin gout-specs))
                  ((mv new-declors (gout gout-declors))
                   (simpadd0-init-declor-list declon.declors gin))
                  ((gin gin) (gin-update gin gout-declors)))
               (xeq-declon-declon declon.extension
                                  declon.specs
                                  new-specs
                                  gout-specs.thm-name
                                  declon.declors
                                  new-declors
                                  gout-declors.thm-name
                                  gout-declors.vartys
                                  gin))
     :statassert (b* (((mv new-declon (gout gout-declon))
                       (simpadd0-statassert declon.statassert gin))
                      (gin (gin-update gin gout-declon)))
                   (mv (declon-statassert new-declon)
                       (gout-no-thm gin))))
    :measure (declon-count declon))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-declon-list ((declons declon-listp) (gin ginp))
    :guard (and (declon-list-unambp declons)
                (declon-list-annop declons))
    :returns (mv (new-declons declon-listp)
                 (gout goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a list of declarations."
    (b* (((gin gin) gin)
         ((when (endp declons))
          (mv nil (gout-no-thm gin)))
         ((mv new-declon (gout gout-declon))
          (simpadd0-declon (car declons) gin))
         (gin (gin-update gin gout-declon))
         ((mv new-declons (gout gout-declons))
          (simpadd0-declon-list (cdr declons)
                              (change-gin
                               gin :vartys gout-declon.vartys)))
         (gin (gin-update gin gout-declons)))
      (mv (cons new-declon new-declons)
          (change-gout (gout-no-thm gin)
                       :vartys gout-declons.vartys)))
    :measure (declon-list-count declons))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-label ((label labelp) (gin ginp))
    :guard (and (label-unambp label)
                (label-annop label))
    :returns (mv (new-label labelp)
                 (gout goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a label."
    (b* (((gin gin) gin))
      (label-case
       label
       :name (mv (label-fix label) (gout-no-thm gin))
       :casexpr (b* (((mv new-expr (gout gout-expr))
                      (simpadd0-const-expr label.expr gin))
                     (gin (gin-update gin gout-expr))
                     ((mv new-range? (gout gout-range?))
                      (simpadd0-const-expr-option label.range? gin))
                     (gin (gin-update gin gout-range?)))
                  (mv (make-label-casexpr :expr new-expr
                                          :range? new-range?)
                      (gout-no-thm gin)))
       :default (mv (label-fix label) (gout-no-thm gin))))
    :measure (label-count label))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-stmt ((stmt stmtp) (gin ginp))
    :guard (and (stmt-unambp stmt)
                (stmt-annop stmt))
    :returns (mv (new-stmt stmtp)
                 (gout goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a statement."
    (b* (((gin gin) gin))
      (stmt-case
       stmt
       :labeled (b* (((mv new-label (gout gout-label))
                      (simpadd0-label stmt.label gin))
                     (gin (gin-update gin gout-label))
                     ((mv new-stmt (gout gout-stmt))
                      (simpadd0-stmt stmt.stmt gin))
                     (gin (gin-update gin gout-stmt)))
                  (mv (make-stmt-labeled :label new-label
                                         :stmt new-stmt)
                      (gout-no-thm gin)))
       :compound (b* (((mv new-cstmt (gout gout-cstmt))
                       (simpadd0-comp-stmt stmt.stmt gin))
                      (gin (gin-update gin gout-cstmt)))
                   (xeq-stmt-compound stmt.stmt
                                      new-cstmt
                                      gout-cstmt.thm-name
                                      gin))
       :expr (b* (((mv new-expr? (gout gout-expr?))
                   (simpadd0-expr-option stmt.expr? gin))
                  (gin (gin-update gin gout-expr?)))
               (xeq-stmt-expr stmt.expr?
                              new-expr?
                              gout-expr?.thm-name
                              stmt.info
                              gin))
       :if (b* (((mv new-test (gout gout-test))
                 (simpadd0-expr stmt.test gin))
                (gin (gin-update gin gout-test))
                ((mv new-then (gout gout-then))
                 (simpadd0-stmt stmt.then gin))
                (gin (gin-update gin gout-then)))
             (xeq-stmt-if stmt.test
                          new-test
                          gout-test.thm-name
                          stmt.then
                          new-then
                          gout-then.thm-name
                          gin))
       :ifelse (b* (((mv new-test (gout gout-test))
                     (simpadd0-expr stmt.test gin))
                    (gin (gin-update gin gout-test))
                    ((mv new-then (gout gout-then))
                     (simpadd0-stmt stmt.then gin))
                    (gin (gin-update gin gout-then))
                    ((mv new-else (gout gout-else))
                     (simpadd0-stmt stmt.else gin))
                    (gin (gin-update gin gout-else)))
                 (xeq-stmt-ifelse stmt.test
                                  new-test
                                  gout-test.thm-name
                                  stmt.then
                                  new-then
                                  gout-then.thm-name
                                  stmt.else
                                  new-else
                                  gout-else.thm-name
                                  gin))
       :switch (b* (((mv new-target (gout gout-target))
                     (simpadd0-expr stmt.target gin))
                    (gin (gin-update gin gout-target))
                    ((mv new-body (gout gout-body))
                     (simpadd0-stmt stmt.body gin))
                    (gin (gin-update gin gout-body)))
                 (mv (make-stmt-switch :target new-target
                                       :body new-body)
                     (gout-no-thm gin)))
       :while (b* (((mv new-test (gout gout-test))
                    (simpadd0-expr stmt.test gin))
                   (gin (gin-update gin gout-test))
                   ((mv new-body (gout gout-body))
                    (simpadd0-stmt stmt.body gin))
                   (gin (gin-update gin gout-body)))
                (xeq-stmt-while stmt.test
                                new-test
                                gout-test.thm-name
                                stmt.body
                                new-body
                                gout-body.thm-name
                                gin))
       :dowhile (b* (((mv new-body (gout gout-body))
                      (simpadd0-stmt stmt.body gin))
                     (gin (gin-update gin gout-body))
                     ((mv new-test (gout gout-test))
                      (simpadd0-expr stmt.test gin))
                     (gin (gin-update gin gout-test)))
                  (xeq-stmt-dowhile stmt.body
                                    new-body
                                    gout-body.thm-name
                                    stmt.test
                                    new-test
                                    gout-test.thm-name
                                    gin))
       :for-expr (b* (((mv new-init (gout gout-init))
                       (simpadd0-expr-option stmt.init gin))
                      (gin (gin-update gin gout-init))
                      ((mv new-test (gout gout-test))
                       (simpadd0-expr-option stmt.test gin))
                      (gin (gin-update gin gout-test))
                      ((mv new-next (gout gout-next))
                       (simpadd0-expr-option stmt.next gin))
                      (gin (gin-update gin gout-next))
                      ((mv new-body (gout gout-body))
                       (simpadd0-stmt stmt.body gin))
                      (gin (gin-update gin gout-body)))
                   (mv (make-stmt-for-expr :init new-init
                                           :test new-test
                                           :next new-next
                                           :body new-body)
                       (gout-no-thm gin)))
       :for-declon (b* (((mv new-init (gout gout-init))
                         (simpadd0-declon stmt.init gin))
                        (gin (gin-update gin gout-init))
                        (gin1 (change-gin gin :vartys gout-init.vartys))
                        ((mv new-test (gout gout-test))
                         (simpadd0-expr-option stmt.test gin1))
                        (gin (gin-update gin gout-test))
                        ((mv new-next (gout gout-next))
                         (simpadd0-expr-option stmt.next gin1))
                        (gin (gin-update gin gout-next))
                        ((mv new-body (gout gout-body))
                         (simpadd0-stmt stmt.body gin1))
                        (gin (gin-update gin gout-body)))
                     (mv (make-stmt-for-declon :init new-init
                                               :test new-test
                                               :next new-next
                                               :body new-body)
                         (gout-no-thm gin)))
       :for-ambig (prog2$ (impossible) (mv (irr-stmt) (irr-gout)))
       :goto (mv (stmt-fix stmt) (gout-no-thm gin))
       :gotoe (b* (((mv new-label gout) (simpadd0-expr stmt.label gin)))
                (mv (stmt-gotoe new-label) gout))
       :continue (mv (stmt-fix stmt) (gout-no-thm gin))
       :break (mv (stmt-fix stmt) (gout-no-thm gin))
       :return (b* (((mv new-expr? (gout gout-expr?))
                     (simpadd0-expr-option stmt.expr? gin))
                    (gin (gin-update gin gout-expr?)))
                 (xeq-stmt-return stmt.expr?
                                  new-expr?
                                  gout-expr?.thm-name
                                  stmt.info
                                  gin))
       :asm (mv (stmt-fix stmt) (gout-no-thm gin))))
    :measure (stmt-count stmt))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-comp-stmt ((cstmt comp-stmtp) (gin ginp))
    :guard (and (comp-stmt-unambp cstmt)
                (comp-stmt-annop cstmt))
    :returns (mv (new-cstmt comp-stmtp) (gout goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a compound-statement."
    :long
    (xdoc::topstring
     (xdoc::p
      "Since a compound statement maps
       to the same thing as its list of block items,
       in the abstract syntax of the language formalization,
       we just use the @('gout') for the block items
       as the @('gout') for the block."))
    (b* (((comp-stmt cstmt) cstmt)
         ((mv items gout) (simpadd0-block-item-list cstmt.items gin)))
      (mv (make-comp-stmt :labels cstmt.labels :items items) gout))
    :measure (comp-stmt-count cstmt))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-block-item ((item block-itemp) (gin ginp))
    :guard (and (block-item-unambp item)
                (block-item-annop item))
    :returns (mv (new-item block-itemp)
                 (gout goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a block item."
    (b* (((gin gin) gin))
      (block-item-case
       item
       :declon (b* (((mv new-declon (gout gout-declon))
                     (simpadd0-declon item.declon gin))
                    (gin (gin-update gin gout-declon)))
                 (xeq-block-item-declon item.declon
                                        new-declon
                                        gout-declon.thm-name
                                        item.info
                                        gout-declon.vartys
                                        gin))
       :stmt (b* (((mv new-stmt (gout gout-stmt))
                   (simpadd0-stmt item.stmt gin))
                  (gin (gin-update gin gout-stmt)))
               (xeq-block-item-stmt item.stmt
                                    new-stmt
                                    gout-stmt.thm-name
                                    item.info
                                    gin))
       :ambig (prog2$ (impossible) (mv (irr-block-item) (irr-gout)))))
    :measure (block-item-count item))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (define simpadd0-block-item-list ((items block-item-listp)
                                    (gin ginp))
    :guard (and (block-item-list-unambp items)
                (block-item-list-annop items))
    :returns (mv (new-items block-item-listp)
                 (gout goutp))
    :parents (simpadd0 simpadd0-exprs/decls/stmts)
    :short "Transform a list of block items."
    (b* (((gin gin) gin)
         ((when (endp items))
          (mv nil (xeq-block-item-list-empty gin)))
         (item (car items))
         ((mv new-item (gout gout-item))
          (simpadd0-block-item item gin))
         (gin (gin-update gin gout-item))
         ((mv new-items (gout gout-items))
          (simpadd0-block-item-list (cdr items)
                                    (change-gin
                                     gin :vartys gout-item.vartys)))
         (gin (gin-update gin gout-items)))
      (xeq-block-item-list-cons (car items)
                                new-item
                                gout-item.thm-name
                                (cdr items)
                                new-items
                                gout-items.thm-name
                                gin))
    :measure (block-item-list-count items))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  :hints (("Goal" :in-theory (enable o< o-finp)))

  :verify-guards nil ; done after the unambiguity proofs

  ///

  (local (in-theory (enable irr-absdeclor
                            irr-dirabsdeclor
                            irr-comp-stmt)))

  (fty::deffixequiv-mutual simpadd0-exprs/decls/stmts)

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (defret-mutual exprs/decls-unambp-of-simpadd0-exprs/decls
    (defret expr-unambp-of-simpadd0-expr
      (expr-unambp new-expr)
      :fn simpadd0-expr)
    (defret expr-list-unambp-of-simpadd0-expr-list
      (expr-list-unambp new-exprs)
      :fn simpadd0-expr-list)
    (defret expr-option-unambp-of-simpadd0-expr-option
      (expr-option-unambp new-expr?)
      :fn simpadd0-expr-option)
    (defret const-expr-unambp-of-simpadd0-const-expr
      (const-expr-unambp new-cexpr)
      :fn simpadd0-const-expr)
    (defret const-expr-option-unambp-of-simpadd0-const-expr-option
      (const-expr-option-unambp new-cexpr?)
      :fn simpadd0-const-expr-option)
    (defret genassoc-unambp-of-simpadd0-genassoc
      (genassoc-unambp new-genassoc)
      :fn simpadd0-genassoc)
    (defret genassoc-list-unambp-of-simpadd0-genassoc-list
      (genassoc-list-unambp new-genassocs)
      :fn simpadd0-genassoc-list)
    (defret member-designor-unambp-of-simpadd0-member-designor
      (member-designor-unambp new-memdes)
      :fn simpadd0-member-designor)
    (defret type-spec-unambp-of-simpadd0-type-spec
      (type-spec-unambp new-tyspec)
      :fn simpadd0-type-spec)
    (defret spec/qual-unambp-of-simpadd0-spec/qual
      (spec/qual-unambp new-specqual)
      :fn simpadd0-spec/qual)
    (defret spec/qual-list-unambp-of-simpadd0-spec/qual-list
      (spec/qual-list-unambp new-specquals)
      :fn simpadd0-spec/qual-list)
    (defret align-spec-unambp-of-simpadd0-align-spec
      (align-spec-unambp new-alignspec)
      :fn simpadd0-align-spec)
    (defret decl-spec-unambp-of-simpadd0-decl-spec
      (decl-spec-unambp new-declspec)
      :fn simpadd0-decl-spec)
    (defret decl-spec-list-unambp-of-simpadd0-decl-spec-list
      (decl-spec-list-unambp new-declspecs)
      :fn simpadd0-decl-spec-list)
    (defret initer-unambp-of-simpadd0-initer
      (initer-unambp new-initer)
      :fn simpadd0-initer)
    (defret initer-option-unambp-of-simpadd0-initer-option
      (initer-option-unambp new-initer?)
      :fn simpadd0-initer-option)
    (defret desiniter-unambp-of-simpadd0-desiniter
      (desiniter-unambp new-desiniter)
      :fn simpadd0-desiniter)
    (defret desiniter-list-unambp-of-simpadd0-desiniter-list
      (desiniter-list-unambp new-desiniters)
      :fn simpadd0-desiniter-list)
    (defret designor-unambp-of-simpadd0-designor
      (designor-unambp new-designor)
      :fn simpadd0-designor)
    (defret designor-list-unambp-of-simpadd0-designor-list
      (designor-list-unambp new-designors)
      :fn simpadd0-designor-list)
    (defret declor-unambp-of-simpadd0-declor
      (declor-unambp new-declor)
      :fn simpadd0-declor)
    (defret declor-option-unambp-of-simpadd0-declor-option
      (declor-option-unambp new-declor?)
      :fn simpadd0-declor-option)
    (defret dirdeclor-unambp-of-simpadd0-dirdeclor
      (dirdeclor-unambp new-dirdeclor)
      :fn simpadd0-dirdeclor)
    (defret absdeclor-unambp-of-simpadd0-absdeclor
      (absdeclor-unambp new-absdeclor)
      :fn simpadd0-absdeclor)
    (defret absdeclor-option-unambp-of-simpadd0-absdeclor-option
      (absdeclor-option-unambp new-absdeclor?)
      :fn simpadd0-absdeclor-option)
    (defret dirabsdeclor-unambp-of-simpadd0-dirabsdeclor
      (dirabsdeclor-unambp new-dirabsdeclor)
      :fn simpadd0-dirabsdeclor)
    (defret dirabsdeclor-option-unambp-of-simpadd0-dirabsdeclor-option
      (dirabsdeclor-option-unambp new-dirabsdeclor?)
      :fn simpadd0-dirabsdeclor-option)
    (defret param-declon-unambp-of-simpadd0-param-declon
      (param-declon-unambp new-paramdeclon)
      :fn simpadd0-param-declon)
    (defret param-declon-list-unambp-of-simpadd0-param-declon-list
      (param-declon-list-unambp new-paramdeclons)
      :fn simpadd0-param-declon-list)
    (defret param-declor-unambp-of-simpadd0-param-declor
      (param-declor-unambp new-paramdeclor)
      :fn simpadd0-param-declor)
    (defret tyname-unambp-of-simpadd0-tyname
      (tyname-unambp new-tyname)
      :fn simpadd0-tyname)
    (defret struni-spec-unambp-of-simpadd0-struni-spec
      (struni-spec-unambp new-struni-spec)
      :fn simpadd0-struni-spec)
    (defret struct-declon-unambp-of-simpadd0-struct-declon
      (struct-declon-unambp new-structdeclon)
      :fn simpadd0-struct-declon)
    (defret struct-declon-list-unambp-of-simpadd0-struct-declon-list
      (struct-declon-list-unambp new-structdeclons)
      :fn simpadd0-struct-declon-list)
    (defret struct-declor-unambp-of-simpadd0-struct-declor
      (struct-declor-unambp new-structdeclor)
      :fn simpadd0-struct-declor)
    (defret struct-declor-list-unambp-of-simpadd0-struct-declor-list
      (struct-declor-list-unambp new-structdeclors)
      :fn simpadd0-struct-declor-list)
    (defret enum-spec-unambp-of-simpadd0-enum-spec
      (enum-spec-unambp new-enumspec)
      :fn simpadd0-enum-spec)
    (defret enumer-unambp-of-simpadd0-enumer
      (enumer-unambp new-enumer)
      :fn simpadd0-enumer)
    (defret enumer-list-unambp-of-simpadd0-enumer-list
      (enumer-list-unambp new-enumers)
      :fn simpadd0-enumer-list)
    (defret statassert-unambp-of-simpadd0-statassert
      (statassert-unambp new-statassert)
      :fn simpadd0-statassert)
    (defret init-declor-unambp-of-simpadd0-init-declor
      (init-declor-unambp new-initdeclor)
      :fn simpadd0-init-declor)
    (defret init-declor-list-unambp-of-simpadd0-init-declor-list
      (init-declor-list-unambp new-initdeclors)
      :fn simpadd0-init-declor-list)
    (defret declon-unambp-of-simpadd0-declon
      (declon-unambp new-declon)
      :fn simpadd0-declon)
    (defret declon-list-unambp-of-simpadd0-declon-list
      (declon-list-unambp new-declons)
      :fn simpadd0-declon-list)
    (defret label-unambp-of-simpadd0-label
      (label-unambp new-label)
      :fn simpadd0-label)
    (defret stmt-unambp-of-simpadd0-stmt
      (stmt-unambp new-stmt)
      :fn simpadd0-stmt)
    (defret comp-stmt-unambp-of-simpadd0-block
      (comp-stmt-unambp new-cstmt)
      :fn simpadd0-comp-stmt)
    (defret block-item-unambp-of-simpadd0-block-item
      (block-item-unambp new-item)
      :fn simpadd0-block-item)
    (defret block-item-list-unambp-of-simpadd0-block-item-list
      (block-item-list-unambp new-items)
      :fn simpadd0-block-item-list)
    :hints (("Goal" :in-theory (enable simpadd0-expr
                                       simpadd0-expr-list
                                       simpadd0-expr-option
                                       simpadd0-const-expr
                                       simpadd0-const-expr-option
                                       simpadd0-genassoc
                                       simpadd0-genassoc-list
                                       simpadd0-type-spec
                                       simpadd0-spec/qual
                                       simpadd0-spec/qual-list
                                       simpadd0-align-spec
                                       simpadd0-decl-spec
                                       simpadd0-decl-spec-list
                                       simpadd0-initer
                                       simpadd0-initer-option
                                       simpadd0-desiniter
                                       simpadd0-desiniter-list
                                       simpadd0-designor
                                       simpadd0-designor-list
                                       simpadd0-declor
                                       simpadd0-declor-option
                                       simpadd0-dirdeclor
                                       simpadd0-absdeclor
                                       simpadd0-absdeclor-option
                                       simpadd0-dirabsdeclor
                                       simpadd0-dirabsdeclor-option
                                       simpadd0-param-declon
                                       simpadd0-param-declon-list
                                       simpadd0-param-declor
                                       simpadd0-tyname
                                       simpadd0-struni-spec
                                       simpadd0-struct-declon
                                       simpadd0-struct-declon-list
                                       simpadd0-struct-declor
                                       simpadd0-struct-declor-list
                                       simpadd0-enum-spec
                                       simpadd0-enumer
                                       simpadd0-enumer-list
                                       simpadd0-statassert
                                       simpadd0-init-declor
                                       simpadd0-init-declor-list
                                       simpadd0-declon
                                       simpadd0-declon-list
                                       simpadd0-label
                                       simpadd0-stmt
                                       simpadd0-comp-stmt
                                       simpadd0-block-item
                                       simpadd0-block-item-list
                                       irr-expr
                                       irr-const-expr
                                       irr-align-spec
                                       irr-dirabsdeclor
                                       irr-param-declor
                                       irr-type-spec
                                       irr-stmt
                                       irr-block-item))))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (defret-mutual exprs/decls-annop-of-simpadd0-exprs/decls
    (defret expr-annop-of-simpadd0-expr
      (expr-annop new-expr)
      :hyp (and (expr-unambp expr)
                (expr-annop expr))
      :fn simpadd0-expr)
    (defret expr-list-annop-of-simpadd0-expr-list
      (expr-list-annop new-exprs)
      :hyp (and (expr-list-unambp exprs)
                (expr-list-annop exprs))
      :fn simpadd0-expr-list)
    (defret expr-option-annop-of-simpadd0-expr-option
      (expr-option-annop new-expr?)
      :hyp (and (expr-option-unambp expr?)
                (expr-option-annop expr?))
      :fn simpadd0-expr-option)
    (defret const-expr-annop-of-simpadd0-const-expr
      (const-expr-annop new-cexpr)
      :hyp (and (const-expr-unambp cexpr)
                (const-expr-annop cexpr))
      :fn simpadd0-const-expr)
    (defret const-expr-option-annop-of-simpadd0-const-expr-option
      (const-expr-option-annop new-cexpr?)
      :hyp (and (const-expr-option-unambp cexpr?)
                (const-expr-option-annop cexpr?))
      :fn simpadd0-const-expr-option)
    (defret genassoc-annop-of-simpadd0-genassoc
      (genassoc-annop new-genassoc)
      :hyp (and (genassoc-unambp genassoc)
                (genassoc-annop genassoc))
      :fn simpadd0-genassoc)
    (defret genassoc-list-annop-of-simpadd0-genassoc-list
      (genassoc-list-annop new-genassocs)
      :hyp (and (genassoc-list-unambp genassocs)
                (genassoc-list-annop genassocs))
      :fn simpadd0-genassoc-list)
    (defret member-designor-annop-of-simpadd0-member-designor
      (member-designor-annop new-memdes)
      :hyp (and (member-designor-unambp memdes)
                (member-designor-annop memdes))
      :fn simpadd0-member-designor)
    (defret type-spec-annop-of-simpadd0-type-spec
      (type-spec-annop new-tyspec)
      :hyp (and (type-spec-unambp tyspec)
                (type-spec-annop tyspec))
      :fn simpadd0-type-spec)
    (defret spec/qual-annop-of-simpadd0-spec/qual
      (spec/qual-annop new-specqual)
      :hyp (and (spec/qual-unambp specqual)
                (spec/qual-annop specqual))
      :fn simpadd0-spec/qual)
    (defret spec/qual-list-annop-of-simpadd0-spec/qual-list
      (spec/qual-list-annop new-specquals)
      :hyp (and (spec/qual-list-unambp specquals)
                (spec/qual-list-annop specquals))
      :fn simpadd0-spec/qual-list)
    (defret align-spec-annop-of-simpadd0-align-spec
      (align-spec-annop new-alignspec)
      :hyp (and (align-spec-unambp alignspec)
                (align-spec-annop alignspec))
      :fn simpadd0-align-spec)
    (defret decl-spec-annop-of-simpadd0-decl-spec
      (decl-spec-annop new-declspec)
      :hyp (and (decl-spec-unambp declspec)
                (decl-spec-annop declspec))
      :fn simpadd0-decl-spec)
    (defret decl-spec-list-annop-of-simpadd0-decl-spec-list
      (decl-spec-list-annop new-declspecs)
      :hyp (and (decl-spec-list-unambp declspecs)
                (decl-spec-list-annop declspecs))
      :fn simpadd0-decl-spec-list)
    (defret initer-annop-of-simpadd0-initer
      (initer-annop new-initer)
      :hyp (and (initer-unambp initer)
                (initer-annop initer))
      :fn simpadd0-initer)
    (defret initer-option-annop-of-simpadd0-initer-option
      (initer-option-annop new-initer?)
      :hyp (and (initer-option-unambp initer?)
                (initer-option-annop initer?))
      :fn simpadd0-initer-option)
    (defret desiniter-annop-of-simpadd0-desiniter
      (desiniter-annop new-desiniter)
      :hyp (and (desiniter-unambp desiniter)
                (desiniter-annop desiniter))
      :fn simpadd0-desiniter)
    (defret desiniter-list-annop-of-simpadd0-desiniter-list
      (desiniter-list-annop new-desiniters)
      :hyp (and (desiniter-list-unambp desiniters)
                (desiniter-list-annop desiniters))
      :fn simpadd0-desiniter-list)
    (defret designor-annop-of-simpadd0-designor
      (designor-annop new-designor)
      :hyp (and (designor-unambp designor)
                (designor-annop designor))
      :fn simpadd0-designor)
    (defret designor-list-annop-of-simpadd0-designor-list
      (designor-list-annop new-designors)
      :hyp (and (designor-list-unambp designors)
                (designor-list-annop designors))
      :fn simpadd0-designor-list)
    (defret declor-annop-of-simpadd0-declor
      (declor-annop new-declor)
      :hyp (and (declor-unambp declor)
                (declor-annop declor))
      :fn simpadd0-declor)
    (defret declor-option-annop-of-simpadd0-declor-option
      (declor-option-annop new-declor?)
      :hyp (and (declor-option-unambp declor?)
                (declor-option-annop declor?))
      :fn simpadd0-declor-option)
    (defret dirdeclor-annop-of-simpadd0-dirdeclor
      (dirdeclor-annop new-dirdeclor)
      :hyp (and (dirdeclor-unambp dirdeclor)
                (dirdeclor-annop dirdeclor))
      :fn simpadd0-dirdeclor)
    (defret absdeclor-annop-of-simpadd0-absdeclor
      (absdeclor-annop new-absdeclor)
      :hyp (and (absdeclor-unambp absdeclor)
                (absdeclor-annop absdeclor))
      :fn simpadd0-absdeclor)
    (defret absdeclor-option-annop-of-simpadd0-absdeclor-option
      (absdeclor-option-annop new-absdeclor?)
      :hyp (and (absdeclor-option-unambp absdeclor?)
                (absdeclor-option-annop absdeclor?))
      :fn simpadd0-absdeclor-option)
    (defret dirabsdeclor-annop-of-simpadd0-dirabsdeclor
      (dirabsdeclor-annop new-dirabsdeclor)
      :hyp (and (dirabsdeclor-unambp dirabsdeclor)
                (dirabsdeclor-annop dirabsdeclor))
      :fn simpadd0-dirabsdeclor)
    (defret dirabsdeclor-option-annop-of-simpadd0-dirabsdeclor-option
      (dirabsdeclor-option-annop new-dirabsdeclor?)
      :hyp (and (dirabsdeclor-option-unambp dirabsdeclor?)
                (dirabsdeclor-option-annop dirabsdeclor?))
      :fn simpadd0-dirabsdeclor-option)
    (defret param-declon-annop-of-simpadd0-param-declon
      (param-declon-annop new-paramdeclon)
      :hyp (and (param-declon-unambp paramdeclon)
                (param-declon-annop paramdeclon))
      :fn simpadd0-param-declon)
    (defret param-declon-list-annop-of-simpadd0-param-declon-list
      (param-declon-list-annop new-paramdeclons)
      :hyp (and (param-declon-list-unambp paramdeclons)
                (param-declon-list-annop paramdeclons))
      :fn simpadd0-param-declon-list)
    (defret param-declor-annop-of-simpadd0-param-declor
      (param-declor-annop new-paramdeclor)
      :hyp (and (param-declor-unambp paramdeclor)
                (param-declor-annop paramdeclor))
      :fn simpadd0-param-declor)
    (defret tyname-annop-of-simpadd0-tyname
      (tyname-annop new-tyname)
      :hyp (and (tyname-unambp tyname)
                (tyname-annop tyname))
      :fn simpadd0-tyname)
    (defret struni-spec-annop-of-simpadd0-struni-spec
      (struni-spec-annop new-struni-spec)
      :hyp (and (struni-spec-unambp struni-spec)
                (struni-spec-annop struni-spec))
      :fn simpadd0-struni-spec)
    (defret struct-declon-annop-of-simpadd0-struct-declon
      (struct-declon-annop new-structdeclon)
      :hyp (and (struct-declon-unambp structdeclon)
                (struct-declon-annop structdeclon))
      :fn simpadd0-struct-declon)
    (defret struct-declon-list-annop-of-simpadd0-struct-declon-list
      (struct-declon-list-annop new-structdeclons)
      :hyp (and (struct-declon-list-unambp structdeclons)
                (struct-declon-list-annop structdeclons))
      :fn simpadd0-struct-declon-list)
    (defret struct-declor-annop-of-simpadd0-struct-declor
      (struct-declor-annop new-structdeclor)
      :hyp (and (struct-declor-unambp structdeclor)
                (struct-declor-annop structdeclor))
      :fn simpadd0-struct-declor)
    (defret struct-declor-list-annop-of-simpadd0-struct-declor-list
      (struct-declor-list-annop new-structdeclors)
      :hyp (and (struct-declor-list-unambp structdeclors)
                (struct-declor-list-annop structdeclors))
      :fn simpadd0-struct-declor-list)
    (defret enum-spec-annop-of-simpadd0-enum-spec
      (enum-spec-annop new-enumspec)
      :hyp (and (enum-spec-unambp enumspec)
                (enum-spec-annop enumspec))
      :fn simpadd0-enum-spec)
    (defret enumer-annop-of-simpadd0-enumer
      (enumer-annop new-enumer)
      :hyp (and (enumer-unambp enumer)
                (enumer-annop enumer))
      :fn simpadd0-enumer)
    (defret enumer-list-annop-of-simpadd0-enumer-list
      (enumer-list-annop new-enumers)
      :hyp (and (enumer-list-unambp enumers)
                (enumer-list-annop enumers))
      :fn simpadd0-enumer-list)
    (defret statassert-annop-of-simpadd0-statassert
      (statassert-annop new-statassert)
      :hyp (and (statassert-unambp statassert)
                (statassert-annop statassert))
      :fn simpadd0-statassert)
    (defret init-declor-annop-of-simpadd0-init-declor
      (init-declor-annop new-initdeclor)
      :hyp (and (init-declor-unambp initdeclor)
                (init-declor-annop initdeclor))
      :fn simpadd0-init-declor)
    (defret init-declor-list-annop-of-simpadd0-init-declor-list
      (init-declor-list-annop new-initdeclors)
      :hyp (and (init-declor-list-unambp initdeclors)
                (init-declor-list-annop initdeclors))
      :fn simpadd0-init-declor-list)
    (defret declon-annop-of-simpadd0-declon
      (declon-annop new-declon)
      :hyp (and (declon-unambp declon)
                (declon-annop declon))
      :fn simpadd0-declon)
    (defret declon-list-annop-of-simpadd0-declon-list
      (declon-list-annop new-declons)
      :hyp (and (declon-list-unambp declons)
                (declon-list-annop declons))
      :fn simpadd0-declon-list)
    (defret label-annop-of-simpadd0-label
      (label-annop new-label)
      :hyp (and (label-unambp label)
                (label-annop label))
      :fn simpadd0-label)
    (defret stmt-annop-of-simpadd0-stmt
      (stmt-annop new-stmt)
      :hyp (and (stmt-unambp stmt)
                (stmt-annop stmt))
      :fn simpadd0-stmt)
    (defret comp-stmt-annop-of-simpadd0-comp-stmt
      (comp-stmt-annop new-cstmt)
      :hyp (and (comp-stmt-unambp cstmt)
                (comp-stmt-annop cstmt))
      :fn simpadd0-comp-stmt)
    (defret block-item-annop-of-simpadd0-block-item
      (block-item-annop new-item)
      :hyp (and (block-item-unambp item)
                (block-item-annop item))
      :fn simpadd0-block-item)
    (defret block-item-list-annop-of-simpadd0-block-item-list
      (block-item-list-annop new-items)
      :hyp (and (block-item-list-unambp items)
                (block-item-list-annop items))
      :fn simpadd0-block-item-list)
    :hints (("Goal" :in-theory (enable simpadd0-expr
                                       simpadd0-expr-list
                                       simpadd0-expr-option
                                       simpadd0-const-expr
                                       simpadd0-const-expr-option
                                       simpadd0-genassoc
                                       simpadd0-genassoc-list
                                       simpadd0-type-spec
                                       simpadd0-spec/qual
                                       simpadd0-spec/qual-list
                                       simpadd0-align-spec
                                       simpadd0-decl-spec
                                       simpadd0-decl-spec-list
                                       simpadd0-initer
                                       simpadd0-initer-option
                                       simpadd0-desiniter
                                       simpadd0-desiniter-list
                                       simpadd0-designor
                                       simpadd0-designor-list
                                       simpadd0-declor
                                       simpadd0-declor-option
                                       simpadd0-dirdeclor
                                       simpadd0-absdeclor
                                       simpadd0-absdeclor-option
                                       simpadd0-dirabsdeclor
                                       simpadd0-dirabsdeclor-option
                                       simpadd0-param-declon
                                       simpadd0-param-declon-list
                                       simpadd0-param-declor
                                       simpadd0-tyname
                                       simpadd0-struni-spec
                                       simpadd0-struct-declon
                                       simpadd0-struct-declon-list
                                       simpadd0-struct-declor
                                       simpadd0-struct-declor-list
                                       simpadd0-enum-spec
                                       simpadd0-enumer
                                       simpadd0-enumer-list
                                       simpadd0-statassert
                                       simpadd0-init-declor
                                       simpadd0-init-declor-list
                                       simpadd0-declon
                                       simpadd0-declon-list
                                       simpadd0-label
                                       simpadd0-stmt
                                       simpadd0-comp-stmt
                                       simpadd0-block-item
                                       simpadd0-block-item-list))))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (defret-mutual exprs/decls-aidentp-of-simpadd0-exprs/decls
    (defret expr-aidentp-of-simpadd0-expr
      (expr-aidentp new-expr gcc)
      :hyp (and (expr-unambp expr)
                (expr-aidentp expr gcc))
      :fn simpadd0-expr)
    (defret expr-list-aidentp-of-simpadd0-expr-list
      (expr-list-aidentp new-exprs gcc)
      :hyp (and (expr-list-unambp exprs)
                (expr-list-aidentp exprs gcc))
      :fn simpadd0-expr-list)
    (defret expr-option-aidentp-of-simpadd0-expr-option
      (expr-option-aidentp new-expr? gcc)
      :hyp (and (expr-option-unambp expr?)
                (expr-option-aidentp expr? gcc))
      :fn simpadd0-expr-option)
    (defret const-expr-aidentp-of-simpadd0-const-expr
      (const-expr-aidentp new-cexpr gcc)
      :hyp (and (const-expr-unambp cexpr)
                (const-expr-aidentp cexpr gcc))
      :fn simpadd0-const-expr)
    (defret const-expr-option-aidentp-of-simpadd0-const-expr-option
      (const-expr-option-aidentp new-cexpr? gcc)
      :hyp (and (const-expr-option-unambp cexpr?)
                (const-expr-option-aidentp cexpr? gcc))
      :fn simpadd0-const-expr-option)
    (defret genassoc-aidentp-of-simpadd0-genassoc
      (genassoc-aidentp new-genassoc gcc)
      :hyp (and (genassoc-unambp genassoc)
                (genassoc-aidentp genassoc gcc))
      :fn simpadd0-genassoc)
    (defret genassoc-list-aidentp-of-simpadd0-genassoc-list
      (genassoc-list-aidentp new-genassocs gcc)
      :hyp (and (genassoc-list-unambp genassocs)
                (genassoc-list-aidentp genassocs gcc))
      :fn simpadd0-genassoc-list)
    (defret member-designor-aidentp-of-simpadd0-member-designor
      (member-designor-aidentp new-memdes gcc)
      :hyp (and (member-designor-unambp memdes)
                (member-designor-aidentp memdes gcc))
      :fn simpadd0-member-designor)
    (defret type-spec-aidentp-of-simpadd0-type-spec
      (type-spec-aidentp new-tyspec gcc)
      :hyp (and (type-spec-unambp tyspec)
                (type-spec-aidentp tyspec gcc))
      :fn simpadd0-type-spec)
    (defret spec/qual-aidentp-of-simpadd0-spec/qual
      (spec/qual-aidentp new-specqual gcc)
      :hyp (and (spec/qual-unambp specqual)
                (spec/qual-aidentp specqual gcc))
      :fn simpadd0-spec/qual)
    (defret spec/qual-list-aidentp-of-simpadd0-spec/qual-list
      (spec/qual-list-aidentp new-specquals gcc)
      :hyp (and (spec/qual-list-unambp specquals)
                (spec/qual-list-aidentp specquals gcc))
      :fn simpadd0-spec/qual-list)
    (defret align-spec-aidentp-of-simpadd0-align-spec
      (align-spec-aidentp new-alignspec gcc)
      :hyp (and (align-spec-unambp alignspec)
                (align-spec-aidentp alignspec gcc))
      :fn simpadd0-align-spec)
    (defret decl-spec-aidentp-of-simpadd0-decl-spec
      (decl-spec-aidentp new-declspec gcc)
      :hyp (and (decl-spec-unambp declspec)
                (decl-spec-aidentp declspec gcc))
      :fn simpadd0-decl-spec)
    (defret decl-spec-list-aidentp-of-simpadd0-decl-spec-list
      (decl-spec-list-aidentp new-declspecs gcc)
      :hyp (and (decl-spec-list-unambp declspecs)
                (decl-spec-list-aidentp declspecs gcc))
      :fn simpadd0-decl-spec-list)
    (defret initer-aidentp-of-simpadd0-initer
      (initer-aidentp new-initer gcc)
      :hyp (and (initer-unambp initer)
                (initer-aidentp initer gcc))
      :fn simpadd0-initer)
    (defret initer-option-aidentp-of-simpadd0-initer-option
      (initer-option-aidentp new-initer? gcc)
      :hyp (and (initer-option-unambp initer?)
                (initer-option-aidentp initer? gcc))
      :fn simpadd0-initer-option)
    (defret desiniter-aidentp-of-simpadd0-desiniter
      (desiniter-aidentp new-desiniter gcc)
      :hyp (and (desiniter-unambp desiniter)
                (desiniter-aidentp desiniter gcc))
      :fn simpadd0-desiniter)
    (defret desiniter-list-aidentp-of-simpadd0-desiniter-list
      (desiniter-list-aidentp new-desiniters gcc)
      :hyp (and (desiniter-list-unambp desiniters)
                (desiniter-list-aidentp desiniters gcc))
      :fn simpadd0-desiniter-list)
    (defret designor-aidentp-of-simpadd0-designor
      (designor-aidentp new-designor gcc)
      :hyp (and (designor-unambp designor)
                (designor-aidentp designor gcc))
      :fn simpadd0-designor)
    (defret designor-list-aidentp-of-simpadd0-designor-list
      (designor-list-aidentp new-designors gcc)
      :hyp (and (designor-list-unambp designors)
                (designor-list-aidentp designors gcc))
      :fn simpadd0-designor-list)
    (defret declor-aidentp-of-simpadd0-declor
      (declor-aidentp new-declor gcc)
      :hyp (and (declor-unambp declor)
                (declor-aidentp declor gcc))
      :fn simpadd0-declor)
    (defret declor-option-aidentp-of-simpadd0-declor-option
      (declor-option-aidentp new-declor? gcc)
      :hyp (and (declor-option-unambp declor?)
                (declor-option-aidentp declor? gcc))
      :fn simpadd0-declor-option)
    (defret dirdeclor-aidentp-of-simpadd0-dirdeclor
      (dirdeclor-aidentp new-dirdeclor gcc)
      :hyp (and (dirdeclor-unambp dirdeclor)
                (dirdeclor-aidentp dirdeclor gcc))
      :fn simpadd0-dirdeclor)
    (defret absdeclor-aidentp-of-simpadd0-absdeclor
      (absdeclor-aidentp new-absdeclor gcc)
      :hyp (and (absdeclor-unambp absdeclor)
                (absdeclor-aidentp absdeclor gcc))
      :fn simpadd0-absdeclor)
    (defret absdeclor-option-aidentp-of-simpadd0-absdeclor-option
      (absdeclor-option-aidentp new-absdeclor? gcc)
      :hyp (and (absdeclor-option-unambp absdeclor?)
                (absdeclor-option-aidentp absdeclor? gcc))
      :fn simpadd0-absdeclor-option)
    (defret dirabsdeclor-aidentp-of-simpadd0-dirabsdeclor
      (dirabsdeclor-aidentp new-dirabsdeclor gcc)
      :hyp (and (dirabsdeclor-unambp dirabsdeclor)
                (dirabsdeclor-aidentp dirabsdeclor gcc))
      :fn simpadd0-dirabsdeclor)
    (defret dirabsdeclor-option-aidentp-of-simpadd0-dirabsdeclor-option
      (dirabsdeclor-option-aidentp new-dirabsdeclor? gcc)
      :hyp (and (dirabsdeclor-option-unambp dirabsdeclor?)
                (dirabsdeclor-option-aidentp dirabsdeclor? gcc))
      :fn simpadd0-dirabsdeclor-option)
    (defret param-declon-aidentp-of-simpadd0-param-declon
      (param-declon-aidentp new-paramdeclon gcc)
      :hyp (and (param-declon-unambp paramdeclon)
                (param-declon-aidentp paramdeclon gcc))
      :fn simpadd0-param-declon)
    (defret param-declon-list-aidentp-of-simpadd0-param-declon-list
      (param-declon-list-aidentp new-paramdeclons gcc)
      :hyp (and (param-declon-list-unambp paramdeclons)
                (param-declon-list-aidentp paramdeclons gcc))
      :fn simpadd0-param-declon-list)
    (defret param-declor-aidentp-of-simpadd0-param-declor
      (param-declor-aidentp new-paramdeclor gcc)
      :hyp (and (param-declor-unambp paramdeclor)
                (param-declor-aidentp paramdeclor gcc))
      :fn simpadd0-param-declor)
    (defret tyname-aidentp-of-simpadd0-tyname
      (tyname-aidentp new-tyname gcc)
      :hyp (and (tyname-unambp tyname)
                (tyname-aidentp tyname gcc))
      :fn simpadd0-tyname)
    (defret struni-spec-aidentp-of-simpadd0-struni-spec
      (struni-spec-aidentp new-struni-spec gcc)
      :hyp (and (struni-spec-unambp struni-spec)
                (struni-spec-aidentp struni-spec gcc))
      :fn simpadd0-struni-spec)
    (defret struct-declon-aidentp-of-simpadd0-struct-declon
      (struct-declon-aidentp new-structdeclon gcc)
      :hyp (and (struct-declon-unambp structdeclon)
                (struct-declon-aidentp structdeclon gcc))
      :fn simpadd0-struct-declon)
    (defret struct-declon-list-aidentp-of-simpadd0-struct-declon-list
      (struct-declon-list-aidentp new-structdeclons gcc)
      :hyp (and (struct-declon-list-unambp structdeclons)
                (struct-declon-list-aidentp structdeclons gcc))
      :fn simpadd0-struct-declon-list)
    (defret struct-declor-aidentp-of-simpadd0-struct-declor
      (struct-declor-aidentp new-structdeclor gcc)
      :hyp (and (struct-declor-unambp structdeclor)
                (struct-declor-aidentp structdeclor gcc))
      :fn simpadd0-struct-declor)
    (defret struct-declor-list-aidentp-of-simpadd0-struct-declor-list
      (struct-declor-list-aidentp new-structdeclors gcc)
      :hyp (and (struct-declor-list-unambp structdeclors)
                (struct-declor-list-aidentp structdeclors gcc))
      :fn simpadd0-struct-declor-list)
    (defret enum-spec-aidentp-of-simpadd0-enum-spec
      (enum-spec-aidentp new-enumspec gcc)
      :hyp (and (enum-spec-unambp enumspec)
                (enum-spec-aidentp enumspec gcc))
      :fn simpadd0-enum-spec)
    (defret enumer-aidentp-of-simpadd0-enumer
      (enumer-aidentp new-enumer gcc)
      :hyp (and (enumer-unambp enumer)
                (enumer-aidentp enumer gcc))
      :fn simpadd0-enumer)
    (defret enumer-list-aidentp-of-simpadd0-enumer-list
      (enumer-list-aidentp new-enumers gcc)
      :hyp (and (enumer-list-unambp enumers)
                (enumer-list-aidentp enumers gcc))
      :fn simpadd0-enumer-list)
    (defret statassert-aidentp-of-simpadd0-statassert
      (statassert-aidentp new-statassert gcc)
      :hyp (and (statassert-unambp statassert)
                (statassert-aidentp statassert gcc))
      :fn simpadd0-statassert)
    (defret init-declor-aidentp-of-simpadd0-init-declor
      (init-declor-aidentp new-initdeclor gcc)
      :hyp (and (init-declor-unambp initdeclor)
                (init-declor-aidentp initdeclor gcc))
      :fn simpadd0-init-declor)
    (defret init-declor-list-aidentp-of-simpadd0-init-declor-list
      (init-declor-list-aidentp new-initdeclors gcc)
      :hyp (and (init-declor-list-unambp initdeclors)
                (init-declor-list-aidentp initdeclors gcc))
      :fn simpadd0-init-declor-list)
    (defret declon-aidentp-of-simpadd0-declon
      (declon-aidentp new-declon gcc)
      :hyp (and (declon-unambp declon)
                (declon-aidentp declon gcc))
      :fn simpadd0-declon)
    (defret declon-list-aidentp-of-simpadd0-declon-list
      (declon-list-aidentp new-declons gcc)
      :hyp (and (declon-list-unambp declons)
                (declon-list-aidentp declons gcc))
      :fn simpadd0-declon-list)
    (defret label-aidentp-of-simpadd0-label
      (label-aidentp new-label gcc)
      :hyp (and (label-unambp label)
                (label-aidentp label gcc))
      :fn simpadd0-label)
    (defret stmt-aidentp-of-simpadd0-stmt
      (stmt-aidentp new-stmt gcc)
      :hyp (and (stmt-unambp stmt)
                (stmt-aidentp stmt gcc))
      :fn simpadd0-stmt)
    (defret comp-stmt-aidentp-of-simpadd0-comp-stmt
      (comp-stmt-aidentp new-cstmt gcc)
      :hyp (and (comp-stmt-unambp cstmt)
                (comp-stmt-aidentp cstmt gcc))
      :fn simpadd0-comp-stmt)
    (defret block-item-aidentp-of-simpadd0-block-item
      (block-item-aidentp new-item gcc)
      :hyp (and (block-item-unambp item)
                (block-item-aidentp item gcc))
      :fn simpadd0-block-item)
    (defret block-item-list-aidentp-of-simpadd0-block-item-list
      (block-item-list-aidentp new-items gcc)
      :hyp (and (block-item-list-unambp items)
                (block-item-list-aidentp items gcc))
      :fn simpadd0-block-item-list)
    :hints (("Goal" :in-theory (enable simpadd0-expr
                                       simpadd0-expr-list
                                       simpadd0-expr-option
                                       simpadd0-const-expr
                                       simpadd0-const-expr-option
                                       simpadd0-genassoc
                                       simpadd0-genassoc-list
                                       simpadd0-member-designor
                                       simpadd0-type-spec
                                       simpadd0-spec/qual
                                       simpadd0-spec/qual-list
                                       simpadd0-align-spec
                                       simpadd0-decl-spec
                                       simpadd0-decl-spec-list
                                       simpadd0-initer
                                       simpadd0-initer-option
                                       simpadd0-desiniter
                                       simpadd0-desiniter-list
                                       simpadd0-designor
                                       simpadd0-designor-list
                                       simpadd0-declor
                                       simpadd0-declor-option
                                       simpadd0-dirdeclor
                                       simpadd0-absdeclor
                                       simpadd0-absdeclor-option
                                       simpadd0-dirabsdeclor
                                       simpadd0-dirabsdeclor-option
                                       simpadd0-param-declon
                                       simpadd0-param-declon-list
                                       simpadd0-param-declor
                                       simpadd0-tyname
                                       simpadd0-struni-spec
                                       simpadd0-struct-declon
                                       simpadd0-struct-declon-list
                                       simpadd0-struct-declor
                                       simpadd0-struct-declor-list
                                       simpadd0-enum-spec
                                       simpadd0-enumer
                                       simpadd0-enumer-list
                                       simpadd0-statassert
                                       simpadd0-init-declor
                                       simpadd0-init-declor-list
                                       simpadd0-declon
                                       simpadd0-declon-list
                                       simpadd0-label
                                       simpadd0-stmt
                                       simpadd0-comp-stmt
                                       simpadd0-block-item
                                       simpadd0-block-item-list))))

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  (verify-guards simpadd0-expr))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-fundef ((fundef fundefp) (gin ginp))
  :guard (and (fundef-unambp fundef)
              (fundef-annop fundef))
  :returns (mv (new-fundef fundefp)
               (gout goutp))
  :short "Transform a function definition."
  :long
  (xdoc::topstring
   (xdoc::p
    "The variable-type map resulting from
     the transformation of the function declarator
     includes the applicable parameters of the function,
     if the function declarator has the @(':function-params') kind.
     We extend this variable-type map with the function itself,
     which is in scope just after the declarator;
     currently this extension is a no-op,
     because @(tsee type-formalp) does not hold on function types,
     but we want to have the more general code here.
     If declarations follow, which is the case only if
     the function declarator has the @(':function-names') kind,
     the declarations may further extend the variable-type map before the body,
     with entries for the parameters declared there.
     In any case, the body is transformed with the variable-type map
     after the declarator and any following declarations.")
   (xdoc::p
    "The variable-type map resulting from transforming the body is discarded.
     We call a separate function, @(tsee xeq-fundef),
     to complete the transformation and possibly generate a theorem.
     That function returns, among other things,
     a variable-type map that is
     like the one at the beginning of the function definition
     (before its declaration specifiers, declarator, etc.),
     with the addition of the function itself
     (no addition currently, as explained above,
     but the code is more general for future extensions)."))
  (b* (((fundef fundef) fundef)
       ((mv new-spec (gout gout-spec))
        (simpadd0-decl-spec-list fundef.spec gin))
       (gin (gin-update gin gout-spec))
       ((mv new-declor & (gout gout-declor))
        (simpadd0-declor fundef.declor t gin))
       (gin (gin-update gin gout-declor))
       (type (fundef-info->type fundef.info))
       (ident (declor->ident fundef.declor))
       (vartys-with-fun (if (and (ident-formalp ident)
                                 (type-formalp type)
                                 (not (type-case type :void))
                                 (not (type-case type :char)))
                            (b* (((mv & cvar) (ldm-ident ident))
                                 ((mv & ctype) (ldm-type type)))
                              (omap::update cvar ctype gout-declor.vartys))
                          gout-declor.vartys))
       ((mv new-declons (gout gout-declons))
        (simpadd0-declon-list fundef.decls
                              (change-gin gin :vartys vartys-with-fun)))
       (gin (gin-update gin gout-declons))
       (vartys-for-body gout-declons.vartys)
       ((mv new-body (gout gout-body))
        (simpadd0-comp-stmt fundef.body
                            (change-gin gin :vartys vartys-for-body)))
       ((gin gin) (gin-update gin gout-body)))
    (xeq-fundef fundef.extension
                fundef.spec
                new-spec
                fundef.declor
                new-declor
                fundef.asm?
                fundef.attribs
                fundef.decls
                new-declons
                fundef.body
                new-body
                gout-body.thm-name
                fundef.info
                gin))
  :hooks (:fix)

  ///

  (defret fundef-unambp-of-simpadd0-fundef
    (fundef-unambp new-fundef))

  (defret fundef-annop-of-simpadd0-fundef
    (fundef-annop new-fundef)
    :hyp (and (fundef-unambp fundef)
              (fundef-annop fundef)))

  (defret fundef-aidentp-of-simpadd0-fundef
    (fundef-aidentp new-fundef gcc)
    :hyp (and (fundef-unambp fundef)
              (fundef-aidentp fundef gcc))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-extdecl ((extdecl extdeclp) (gin ginp))
  :guard (and (extdecl-unambp extdecl)
              (extdecl-annop extdecl))
  :returns (mv (new-extdecl extdeclp)
               (gout goutp))
  :short "Transform an external declaration."
  (b* (((gin gin) gin))
    (extdecl-case
     extdecl
     :fundef (b* (((mv new-fundef (gout gout-fundef))
                   (simpadd0-fundef extdecl.fundef gin))
                  (gin (gin-update gin gout-fundef)))
               (mv (extdecl-fundef new-fundef)
                   (change-gout (gout-no-thm gin)
                                :vartys gout-fundef.vartys)))
     :decl (b* (((mv new-declon (gout gout-declon))
                 (simpadd0-declon extdecl.decl gin))
                (gin (gin-update gin gout-declon)))
             (mv (extdecl-decl new-declon)
                 (change-gout (gout-no-thm gin)
                              :vartys gout-declon.vartys)))
     :empty (mv (extdecl-empty) (gout-no-thm gin))
     :asm (mv (extdecl-fix extdecl) (gout-no-thm gin))))
  :hooks (:fix)

  ///

  (defret extdecl-unambp-of-simpadd0-extdecl
    (extdecl-unambp new-extdecl))

  (defret extdecl-annop-of-simpadd0-extdecl
    (extdecl-annop new-extdecl)
    :hyp (and (extdecl-unambp extdecl)
              (extdecl-annop extdecl)))

  (defret extdecl-aidentp-of-simpadd0-extdecl
    (extdecl-aidentp new-extdecl gcc)
    :hyp (and (extdecl-unambp extdecl)
              (extdecl-aidentp extdecl gcc))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-extdecl-list ((extdecls extdecl-listp) (gin ginp))
  :guard (and (extdecl-list-unambp extdecls)
              (extdecl-list-annop extdecls))
  :returns (mv (new-extdecls extdecl-listp)
               (gout goutp))
  :short "Transform a list of external declarations."
  (b* (((gin gin) gin)
       ((when (endp extdecls)) (mv nil (gout-no-thm gin)))
       ((mv new-edecl (gout gout-edecl)) (simpadd0-extdecl (car extdecls) gin))
       (gin (gin-update gin gout-edecl))
       ((mv new-edecls (gout gout-edecls))
        (simpadd0-extdecl-list (cdr extdecls)
                               (change-gin gin :vartys gout-edecl.vartys)))
       (gin (gin-update gin gout-edecls)))
    (mv (cons new-edecl new-edecls)
        (change-gout (gout-no-thm gin) :vartys gout-edecls.vartys)))
  :verify-guards :after-returns
  :hooks (:fix)

  ///

  (defret extdecl-list-unambp-of-simpadd0-extdecl-list
    (extdecl-list-unambp new-extdecls)
    :hints (("Goal" :induct t)))

  (defret extdecl-list-annop-of-simpadd0-extdecl-list
    (extdecl-list-annop new-extdecls)
    :hyp (and (extdecl-list-unambp extdecls)
              (extdecl-list-annop extdecls))
    :hints (("Goal" :induct t)))

  (defret extdecl-list-aidentp-of-simpadd0-extdecl-list
    (extdecl-list-aidentp new-extdecls gcc)
    :hyp (and (extdecl-list-unambp extdecls)
              (extdecl-list-aidentp extdecls gcc))
    :hints (("Goal" :induct t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-transunit ((tunit transunitp) (gin ginp))
  :guard (and (transunit-unambp tunit)
              (transunit-annop tunit))
  :returns (mv (new-tunit transunitp)
               (gout goutp))
  :short "Transform a translation unit."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('gin') passed as input has @('vartys') set to @('nil')
     (see @(tsee simpadd0-filepath-transunit-map)),
     but the theorem index and the list of events
     may be the result of transforming previous translation units."))
  (b* (((gin gin) gin)
       ((transunit tunit) tunit)
       ((mv new-decls (gout gout-decls))
        (simpadd0-extdecl-list tunit.decls gin))
       (gin (gin-update gin gout-decls)))
    (mv  (make-transunit :decls new-decls
                         :info tunit.info)
         (gout-no-thm gin)))
  :hooks (:fix)

  ///

  (defret transunit-unambp-of-simpadd0-transunit
    (transunit-unambp new-tunit))

  (defret transunit-annop-of-simpadd0-transunit
    (transunit-annop new-tunit)
    :hyp (and (transunit-unambp tunit)
              (transunit-annop tunit)))

  (defret transunit-aidentp-of-simpadd0-transunit
    (transunit-aidentp new-tunit gcc)
    :hyp (and (transunit-unambp tunit)
              (transunit-aidentp tunit gcc))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-filepath-transunit-map ((map filepath-transunit-mapp)
                                         (gin ginp))
  :guard (and (filepath-transunit-map-unambp map)
              (filepath-transunit-map-annop map))
  :returns (mv (new-map filepath-transunit-mapp
                        :hyp (filepath-transunit-mapp map))
               (gout goutp))
  :short "Transform a map from file paths to translation units."
  :long
  (xdoc::topstring
   (xdoc::p
    "We transform both the file paths and the translation units.")
   (xdoc::p
    "After each translation unit,
     we reset the @('vartys') component of @('gin') to @('nil'),
     because each translation unit starts with no variables in scope.
     This component is initialized to @('nil')
     in @(tsee simpadd0-code-ensemble),
     so the first translation unit also has the right @('vartys')."))
  (b* (((gin gin) gin)
       ((when (omap::emptyp map))
        (mv nil (gout-no-thm gin)))
       ((mv path tunit) (omap::head map))
       ((mv new-tunit (gout gout-tunit))
        (simpadd0-transunit tunit gin))
       (gin (gin-update gin gout-tunit))
       (gin (change-gin gin :vartys nil))
       ((mv new-map (gout gout-map))
        (simpadd0-filepath-transunit-map (omap::tail map) gin))
       (gin (gin-update gin gout-map)))
    (mv (omap::update path new-tunit new-map)
        (gout-no-thm gin)))
  :verify-guards :after-returns

  ///

  (fty::deffixequiv simpadd0-filepath-transunit-map
    :args ((gin ginp)))

  (defret filepath-transunit-map-unambp-of-simpadd0-filepath-transunit-map
    (filepath-transunit-map-unambp new-map)
    :hyp (filepath-transunit-mapp map)
    :hints (("Goal" :induct t)))

  (defret filepath-transunit-map-annop-of-simpadd0-filepath-transunit-map
    (filepath-transunit-map-annop new-map)
    :hyp (and (filepath-transunit-mapp map)
              (filepath-transunit-map-unambp map)
              (filepath-transunit-map-annop map))
    :hints (("Goal" :induct t)))

  (defret filepath-transunit-map-aidentp-of-simpadd0-filepath-transunit-map
    (filepath-transunit-map-aidentp new-map gcc)
    :hyp (and (filepath-transunit-mapp map)
              (filepath-transunit-map-unambp map)
              (filepath-transunit-map-aidentp map gcc))
    :hints (("Goal" :induct t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-transunit-ensemble ((tunits transunit-ensemblep)
                                     (gin ginp))
  :guard (and (transunit-ensemble-unambp tunits)
              (transunit-ensemble-annop tunits))
  :returns (mv (new-tunits transunit-ensemblep)
               (gout goutp))
  :short "Transform a translation unit ensemble."
  (b* (((transunit-ensemble tunits) tunits)
       ((mv new-map (gout gout-map))
        (simpadd0-filepath-transunit-map tunits.units gin))
       (gin (gin-update gin gout-map)))
    (mv (transunit-ensemble new-map)
        (gout-no-thm gin)))
  :hooks (:fix)

  ///

  (defret transunit-ensemble-unambp-of-simpadd0-transunit-ensemble
    (transunit-ensemble-unambp new-tunits))

  (defret transunit-ensemble-annop-of-simpadd0-transunit-ensemble
    (transunit-ensemble-annop new-tunits)
    :hyp (and (transunit-ensemble-unambp tunits)
              (transunit-ensemble-annop tunits)))

  (defret transunit-ensemble-aidentp-of-simpadd0-transunit-ensemble
    (transunit-ensemble-aidentp new-tunits gcc)
    :hyp (and (transunit-ensemble-unambp tunits)
              (transunit-ensemble-aidentp tunits gcc))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-code-ensemble ((code code-ensemblep)
                                (gin ginp))
  :guard (and (code-ensemble-unambp code)
              (code-ensemble-annop code))
  :returns (mv (new-code code-ensemblep)
               (gout goutp))
  :short "Transform a code ensemble."
  (b* (((code-ensemble code) code)
       ((mv tunits-new (gout gout))
        (simpadd0-transunit-ensemble code.transunits gin)))
    (mv (change-code-ensemble code :transunits tunits-new) gout))
  :hooks (:fix)

  ///

  (defret code-ensemble-unambp-of-simpadd0-code-ensemble
    (code-ensemble-unambp new-code))

  (defret code-ensemble-annop-of-simpadd0-code-ensemble
    (code-ensemble-annop new-code)
    :hyp (and (code-ensemble-unambp code)
              (code-ensemble-annop code)))

  (defret code-ensemble-aidentp-of-simpadd0-code-ensemble
    (code-ensemble-aidentp new-code)
    :hyp (and (code-ensemble-unambp code)
              (code-ensemble-aidentp code))
    :hints (("Goal" :in-theory (enable code-ensemble-aidentp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-gen-everything ((code-old code-ensemblep)
                                 (const-new symbolp))
  :guard (and (code-ensemble-unambp code-old)
              (code-ensemble-annop code-old))
  :returns (mv erp (event pseudo-event-formp))
  :short "Event expansion of the transformation."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('vartys') component of @(tsee gin)
     is initialized to @('nil') here,
     and it applies to the first translation unit (if any):
     see @(tsee simpadd0-filepath-transunit-map)."))
  (b* (((reterr) '(_))
       (gin (make-gin :ienv (code-ensemble->ienv code-old)
                      :const-new const-new
                      :vartys nil
                      :events nil
                      :thm-index 1))
       ((mv code-new (gout gout))
        (simpadd0-code-ensemble code-old gin))
       (const-event `(defconst ,const-new ',code-new)))
    (retok `(encapsulate () ,const-event ,@(rev gout.events)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-process-inputs-and-gen-everything (const-old
                                                    (const-old-present booleanp)
                                                    const-new
                                                    (const-new-present booleanp)
                                                    state)
  :returns (mv erp (event pseudo-event-formp))
  :parents (simpadd0-implementation)
  :short "Process the inputs and generate the events."
  (b* (((reterr) '(_))
       ((erp code-old const-new)
        (simpadd0-process-inputs const-old
                                 const-old-present
                                 const-new
                                 const-new-present
                                 (w state))))
    (simpadd0-gen-everything code-old const-new)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define simpadd0-fn (const-old
                     (const-old-present booleanp)
                     const-new
                     (const-new-present booleanp)
                     (ctx ctxp)
                     state)
  :returns (mv erp (event pseudo-event-formp) state)
  :parents (simpadd0-implementation)
  :short "Event expansion of @(tsee simpadd0)."
  (b* (((mv erp event)
        (simpadd0-process-inputs-and-gen-everything const-old
                                                    const-old-present
                                                    const-new
                                                    const-new-present
                                                    state))
       ((when erp) (er-soft+ ctx t '(_) "~@0" erp)))
    (value event)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection simpadd0-macro-definition
  :parents (simpadd0-implementation)
  :short "Definition of the @(tsee simpadd0) macro."
  (defmacro simpadd0 (&key (const-old 'irrelevant const-old-present)
                           (const-new 'irrelevant const-new-present))
    `(make-event
      (simpadd0-fn ',const-old
                   ',const-old-present
                   ',const-new
                   ',const-new-present
                   'simpadd0
                   state))))
