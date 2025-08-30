; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C2C")

(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(include-book "centaur/fty/deftypes" :dir :system)

(include-book "../language/dynamic-semantics")
(include-book "../language/values")
(include-book "../syntax/abstract-syntax-operations")
(include-book "../syntax/langdef-mapping")
(include-book "../syntax/code-ensembles")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ constant-propagation
  :parents (transformation-tools)
  :short "A C-to-C transformation to propagate constants."
  :long
  (xdoc::topstring
    (xdoc::p
      "This is a very preliminary transformation to propogate constants at the
       function level.")
    (xdoc::p
      "The transformation currently only folds integer constants."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defomap env-block
  :parents (env)
  :short "A scope block within an environment."
  :key-type ident
  :val-type c::value-option
  :pred env-blockp)

(defrule value-optionp-of-cdr-assoc-when-env-blockp
  (implies (env-blockp block)
           (c::value-optionp (cdr (omap::assoc ident block))))
  :induct t
  :enable omap::assoc)

(encapsulate ()
  (local (in-theory (enable nfix)))

  (fty::deflist env
    :short "A C environment mapping identifiers to values."
    :long
    (xdoc::topstring
      (xdoc::p
        "This is implemented as a stack of maps. Blocks within the stack
         correspond to nested scopes within C. Entries within higher blocks
         shadow those in the lower blocks."))
    :elt-type env-block
    :true-listp t
    :elementp-of-nil t
    :pred envp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define in-scope-env
  ((ident identp)
   (env envp))
  :parents (env)
  :short "Check whether a variable is in scope."
  :long
  (xdoc::topstring
   (xdoc::p
     "A variable in scope does not necessarily have a value. A variable which
      is declared (see @(tsee declare-var-env)) but not initialized, or whose
      value is unknown."))
  (declare (xargs :type-prescription (booleanp (in-scope-env ident env))))
  (and (consp env)
       (or (and (omap::assoc ident (first env))
                t)
           (in-scope-env ident (rest env)))))

(define read-env
  ((ident identp)
   (env envp))
  :parents (env)
  :short "Retrieve the value of a variable."
  :long
  (xdoc::topstring
   (xdoc::p
     "A result of @('nil') indicates that the variable is not in scope (see
      @(tsee in-scope-env)), or its value is unknown."))
  :returns (value? c::value-optionp)
  (b* (((when (endp env))
        nil)
       (lookup (omap::assoc ident (env-block-fix (first env)))))
    (if lookup
        (cdr lookup)
      (read-env ident (rest env)))))

(define write-env
  ((ident identp)
   (value? c::value-optionp)
   (env envp))
  :parents (env)
  :short "Overwrite the value of a variable."
  :long
  (xdoc::topstring
   (xdoc::p
     "This assumes that the variable is already declared (see @(tsee
      declare-var-env)). If the variable has been shadowed, only the unshadowed
      variable is overwritten."))
  :returns (new-env envp)
  (b* ((env (env-fix env))
       (value? (c::value-option-fix value?))
       ((when (endp env))
        ;; TODO: raise error?
        nil)
       (lookup (omap::assoc ident (first env))))
    (if lookup
        (cons (omap::update ident
                            value?
                            (first env))
              (rest env))
      (cons (first env)
            (write-env ident value? (rest env)))))
  :measure (acl2-count (env-fix env))
  :hints (("Goal" :in-theory (enable o< o-finp endp))))

(define push-scope-env
  ((env envp))
  :parents (env)
  :short "Push a new scope block to the top of the environment."
  :long
  (xdoc::topstring
   (xdoc::p
     "This mirrors entering a new scope block in the corresponding C
      program. Newly declared variables (see @(tsee declare-var-env)) shall be
      declared within the top scope block."))
  :returns (new-env envp)
  (cons nil (env-fix env)))

(define pop-scope-env
  ((env envp))
  :parents (env)
  :short "Pop a scope block from the top of the environment."
  :long
  (xdoc::topstring
   (xdoc::p
     "All variables declared in the top scope are removed from scope. Any
      variables shadowed by the top scope block are unshadowed."))
  :returns (new-env envp)
  (cdr (env-fix env)))

(define declare-var-env
  ((ident identp)
   (env envp))
  :parents (env)
  :short "Declare a new variables within the environment."
  :long
  (xdoc::topstring
   (xdoc::p
     "The newly declare variable is placed in the top scope block."))
   :returns (new-env envp)
  (b* ((env (env-fix env))
       ((when (endp env))
        ;; TODO: raise error?
        nil))
    (cons (omap::update (ident-fix ident)
                        nil
                        (first env))
          (rest env))))

(define merge-block-env
  ((block env-blockp)
   (env envp))
  :parents (env)
  :short "Update the top block of the environment with the specified scope block."
  :returns (new-env envp)
  (b* ((block (env-block-fix block))
       (env (env-fix env))
       ((when (endp env))
        ;; TODO: raise error
        nil))
    (cons (omap::update* block (first env))
          (rest env))))

(define union-env-block
  ((x env-blockp)
   (y env-blockp))
  :parents (union-env)
  :short "Unions two scope blocks."
  :long
  (xdoc::topstring
   (xdoc::p
     "See @(tsee union-env)."))
  :returns (block env-blockp)
  (if (omap::emptyp x)
      nil
    (b* ((ident (ident-fix (omap::head-key x)))
         (value? (c::value-option-fix (omap::head-val x)))
         (y-lookup (omap::assoc ident y)))
      (if (and y-lookup
               (equal value?
                      (cdr y-lookup)))
          ;; TODO: cons would be more efficient, but would need to prove its an omap
          (omap::update ident
                        value?
                        (union-env-block (omap::tail x)
                                         y))

        (union-env-block (omap::tail x)
                         y))))
  :verify-guards :after-returns)

(define union-env
  ((x envp)
   (y envp))
  :parents (env)
  :short "Take the conservative union of two environments."
  :long
  (xdoc::topstring
   (xdoc::p
     "It is assumed that the each scope block in the environment agrees on
      which variables have been declared. They may only disagree on the value
      of variables")
   (xdoc::p
     "For each scope block, the value of variables which are agreed upon by the
      two environment are retained. The values of all other variables are
      marked \"unknown\"."))
  :returns (env envp)
  (if (endp x)
      nil
    (cons (union-env-block (first x)
                           (first y))
          (union-env (rest x)
                     (rest y)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define value-result-to-option
  ((result c::value-resultp))
  :short "Convert a @(see c::value-result) to a @(see c::value-option)."
  :returns (value? c::value-optionp)
  (if (c::errorp result)
      nil
    (c::value-fix result)))

(define iconst-to-value
  ((iconst c$::iconstp))
  :short "Convert an @(see c$::iconst) to a @(see c::value-option)."
  :returns (value? c::value-optionp)
  (value-result-to-option
   (c::eval-iconst (c$::ldm-iconst iconst))))

(define const-to-value
  ((const constp))
  :short "Convert a @(see c$::const) to a @(see c::value-option)."
  :returns (value? c::value-optionp)
  (const-case
   const
   :int (iconst-to-value const.unwrap)
   ;; TODO: support other constants
   :otherwise nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define const-prop-eval-unop-expr
  ((unop c$::unopp)
   (arg c::valuep))
  :short "Propogate a constant through a @(see c$::unop)."
  :returns (value? c::value-optionp)
  (c$::unop-case
   unop
   :plus (value-result-to-option (c::eval-unary (c::unop-plus) arg))
   :minus (value-result-to-option (c::eval-unary (c::unop-minus) arg))
   :bitnot (value-result-to-option (c::eval-unary (c::unop-bitnot) arg))
   :lognot (value-result-to-option (c::eval-unary (c::unop-lognot) arg))
   :otherwise nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pure-binopp
  ((binop c$::binopp))
  :short "Recognizer pure @(see c$::binop)s."
  (declare (xargs :type-prescription (booleanp (pure-binopp binop))))
  (c$::binop-case
   binop
   :mul t
   :div t
   :rem t
   :add t
   :sub t
   :shl t
   :shr t
   :lt t
   :gt t
   :le t
   :ge t
   :eq t
   :ne t
   :bitand t
   :bitxor t
   :bitior t
   :logand t
   :logor t
   :otherwise nil))

(define const-prop-eval-pure-binop-expr
  ((binop c$::binopp)
   (left c::valuep)
   (right c::valuep))
  :short "Propogate a constant through a pure @(see c$::binop)."
  :guard (pure-binopp binop)
  :returns (value? c::value-optionp)
  (c$::binop-case
   binop
   :mul (value-result-to-option
          (c::eval-binary-strict-pure (c::binop-mul) left right))
   :div (value-result-to-option
          (c::eval-binary-strict-pure (c::binop-div) left right))
   :rem (value-result-to-option
          (c::eval-binary-strict-pure (c::binop-rem) left right))
   :add (value-result-to-option
          (c::eval-binary-strict-pure (c::binop-add) left right))
   :sub (value-result-to-option
          (c::eval-binary-strict-pure (c::binop-sub) left right))
   :shl (value-result-to-option
          (c::eval-binary-strict-pure (c::binop-shl) left right))
   :shr (value-result-to-option
          (c::eval-binary-strict-pure (c::binop-shr) left right))
   :lt (value-result-to-option
         (c::eval-binary-strict-pure (c::binop-lt) left right))
   :gt (value-result-to-option
         (c::eval-binary-strict-pure (c::binop-gt) left right))
   :le (value-result-to-option
         (c::eval-binary-strict-pure (c::binop-le) left right))
   :ge (value-result-to-option
         (c::eval-binary-strict-pure (c::binop-ge) left right))
   :eq (value-result-to-option
         (c::eval-binary-strict-pure (c::binop-eq) left right))
   :ne (value-result-to-option
         (c::eval-binary-strict-pure (c::binop-ne) left right))
   :bitand (value-result-to-option
             (c::eval-binary-strict-pure (c::binop-bitand) left right))
   :bitxor (value-result-to-option
             (c::eval-binary-strict-pure (c::binop-bitxor) left right))
   :bitior (value-result-to-option
             (c::eval-binary-strict-pure (c::binop-bitior) left right))
   ;; Raise hard error
   :otherwise nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expr-to-ident
  ((expr exprp))
  :short "Convert an @(see c$::expr) to an @(see c$::ident-option)."
  :returns (ident? ident-optionp)
  (expr-case
   expr
   :ident expr.ident
   :otherwise nil))

(define const-prop-eval-impure-binop-expr
  ((binop c$::binopp)
   (left exprp)
   (right c::valuep)
   (env envp))
  :short "Propogate a constant through an impure @(see c$::binop)."
  :long
  (xdoc::topstring
   (xdoc::p
     "If the lvalue cannot be resolved, the environment is nullified, as we
      cannot be sure what has been mutated.
      For instance, consider the following sequence of statements:")
   (xdoc::codeblock
     "int a = 1;"
     "int b = 4;"
     "*x = 0;"
     "int c = a + b;")
   (xdoc::p
     "Without knowing the value of @('x'), we cannot constant fold the
      initializer of @('c'). For instance, the constraints @('x == &a'),
      @('x == &b'), and @('x != &a && x != &b') would all produce different
      results."))
  :guard (not (pure-binopp binop))
  :returns (mv (value? c::value-optionp)
               (env envp))
  (b* ((env (env-fix env))
       (right (c::value-fix right)))
    (c$::binop-case
      binop
      :asg (b* ((ident? (expr-to-ident left)))
             (if ident?
                 (mv right (write-env ident? right env))
               (mv nil nil)))
      :otherwise (mv nil nil))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: cast down integer values less than int
;; TODO: check edge case that absolute value of negative number fits in same type
(define value-to-expr
  ((value c::valuep))
  :short "Convert a @(see c::value) to an @(see c$::expr)."
  :returns (expr exprp)
  (c::value-case
   value
   :uchar (expr-const
            (c$::const-int
              (c$::make-iconst :core (if (zp value.get)
                                         (dec/oct/hex-const-oct 1 0)
                                       (c$::dec/oct/hex-const-dec value.get))
                               :suffix? (c$::isuffix-u (c$::usuffix-locase-u)))))
   :schar (if (minusp value.get)
              (make-expr-unary
                :op (c::unop-minus)
                :arg (expr-const
                       (c$::const-int
                         (c$::make-iconst
                           :core (c$::dec/oct/hex-const-dec (- value.get)))))
                :info nil)
            (expr-const
              (c$::const-int
                (c$::make-iconst :core (if (zp value.get)
                                           (dec/oct/hex-const-oct 1 0)
                                         (c$::dec/oct/hex-const-dec value.get))))))
   :ushort (expr-const
             (c$::const-int
               (c$::make-iconst :core (if (zp value.get)
                                          (dec/oct/hex-const-oct 1 0)
                                        (c$::dec/oct/hex-const-dec value.get))
                                :suffix? (c$::isuffix-u (c$::usuffix-locase-u)))))
   :sshort (if (minusp value.get)
               (make-expr-unary
                 :op (c::unop-minus)
                 :arg (expr-const
                        (c$::const-int
                          (c$::make-iconst
                            :core (c$::dec/oct/hex-const-dec (- value.get)))))
                 :info nil)
             (expr-const
               (c$::const-int
                 (c$::make-iconst :core (if (zp value.get)
                                            (dec/oct/hex-const-oct 1 0)
                                          (c$::dec/oct/hex-const-dec value.get))))))
   :uint (expr-const
           (c$::const-int
             (c$::make-iconst :core (if (zp value.get)
                                        (dec/oct/hex-const-oct 1 0)
                                      (c$::dec/oct/hex-const-dec value.get))
                              :suffix? (c$::isuffix-u (c$::usuffix-locase-u)))))
   :sint (if (minusp value.get)
             (make-expr-unary
               :op (c::unop-minus)
               :arg (expr-const
                      (c$::const-int
                        (c$::make-iconst
                          :core (c$::dec/oct/hex-const-dec (- value.get)))))
               :info nil)
           (expr-const
             (c$::const-int
               (c$::make-iconst :core (if (zp value.get)
                                          (dec/oct/hex-const-oct 1 0)
                                        (c$::dec/oct/hex-const-dec value.get))))))
   :ulong (expr-const
            (c$::const-int
              (c$::make-iconst :core (if (zp value.get)
                                         (dec/oct/hex-const-oct 1 0)
                                       (c$::dec/oct/hex-const-dec value.get))
                               :suffix? (c$::isuffix-ul
                                          (c$::usuffix-locase-u)
                                          (c$::lsuffix-locase-l)))))
   :slong (if (minusp value.get)
              (make-expr-unary
                :op (c::unop-minus)
                :arg (expr-const
                       (c$::const-int
                         (c$::make-iconst
                           :core (c$::dec/oct/hex-const-dec (- value.get))
                           :suffix? (c$::isuffix-l (c$::lsuffix-locase-l)))))
                :info nil)
            (expr-const
              (c$::const-int
                (c$::make-iconst :core (if (zp value.get)
                                           (dec/oct/hex-const-oct 1 0)
                                         (c$::dec/oct/hex-const-dec value.get))
                                 :suffix? (c$::isuffix-l (c$::lsuffix-locase-l))))))
   :ullong (expr-const
             (c$::const-int
               (c$::make-iconst :core (if (zp value.get)
                                          (dec/oct/hex-const-oct 1 0)
                                        (c$::dec/oct/hex-const-dec value.get))
                                :suffix? (c$::isuffix-ul
                                           (c$::usuffix-locase-u)
                                           (c$::lsuffix-locase-ll)))))
   :sllong (if (minusp value.get)
               (make-expr-unary
                 :op (c::unop-minus)
                 :arg (expr-const
                        (c$::const-int
                          (c$::make-iconst
                            :core (c$::dec/oct/hex-const-dec (- value.get))
                            :suffix? (c$::isuffix-l (c$::lsuffix-locase-ll)))))
                 :info nil)
             (expr-const
               (c$::const-int
                 (c$::make-iconst :core (if (zp value.get)
                                            (dec/oct/hex-const-oct 1 0)
                                          (c$::dec/oct/hex-const-dec value.get))
                                  :suffix? (c$::isuffix-l (c$::lsuffix-locase-ll))))))
   ;; TODO
   :pointer (prog2$ (raise "TODO: pointer case not yet implemented")
                    (irr-expr))
   :array (prog2$ (raise "TODO: array case not yet implemented")
                  (irr-expr))
   :struct (prog2$ (raise "TODO: struct case not yet implemented")
                   (irr-expr))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zero-valuep
  ((value c::valuep))
  :short "Recognize @(see c::value)s which count as zero for the purpose of "
  (declare (xargs :type-prescription (booleanp (zero-valuep value))))
  (c::value-case
   value
   :uchar (int= value.get 0)
   :schar (int= value.get 0)
   :ushort (int= value.get 0)
   :sshort (int= value.get 0)
   :uint (int= value.get 0)
   :sint (int= value.get 0)
   :ulong (int= value.get 0)
   :slong (int= value.get 0)
   :ullong (int= value.get 0)
   :sllong (int= value.get 0)
   :pointer (c::pointer-case
              value.core
              :null t
              :dangling nil
              :valid nil)
   :array nil
   :struct nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: rewrite as a map?
(defines const-prop-exprs/decls/stmts
  (define const-prop-expr
    ((expr exprp)
     (env envp))
    :short "Propogate a constant through an impure @(see c$::expr)."
    :returns (mv (new-expr exprp)
                 (value? c::value-optionp)
                 (new-env envp))
    (b* ((env (env-fix env)))
      (expr-case
        expr
        :ident (b* ((value? (read-env expr.ident env)))
                 (if value?
                     (mv (value-to-expr value?) value? env)
                   (mv (expr-fix expr) nil env)))
        :const (b* ((value? (const-to-value expr.const)))
                 (mv (if value?
                         (value-to-expr value?)
                       (expr-fix expr))
                     value?
                     env))
        :string (mv (expr-fix expr)
                    ;; TODO
                    nil
                    env)
        :paren (b* (((mv expr value? env)
                     (const-prop-expr expr.inner env)))
                 (mv (expr-paren expr) value? env))
        :gensel
        (b* (((mv control - env)
              (const-prop-expr expr.control env))
             ((mv assocs env)
              (const-prop-genassoc-list expr.assocs env)))
          (mv (make-expr-gensel
                :control control
                :assocs assocs)
              ;; TODO
              nil
              env))
        ;; TODO: which of the two expressions is executed first?
        ;;   (for now, we just choose an arbitrary order. Needs to change.)
        ;;   I think it is undefined. To do this properly, we'd like to try
        ;;   both orders. If the result is different, we can maintain that set
        ;;   and proceed, or just give up.
        ;; For instance, consider the expression: `x++ + x++`. Should always
        ;; evaluate to 2*x + 1
        ;; Note: this applies to many of the below cases
        :arrsub (b* (((mv arg1 - env)
                      (const-prop-expr expr.arg1 env))
                     ((mv arg2 - env)
                      (const-prop-expr expr.arg2 env)))
                  (mv (make-expr-arrsub :arg1 arg1 :arg2 arg2)
                      ;; TODO
                      nil
                      env))
        :funcall
        (b* (((mv fun - env)
              (const-prop-expr expr.fun env))
             ((mv args env)
              (const-prop-expr-list expr.args env)))
          (mv (make-expr-funcall
                :fun fun
                ;; TODO
                :args args)
              ;; TODO: handle pure functions on constant arguments
              ;;   (perhaps this should be handled by first inlining the
              ;;   function)
              nil
              env))
        :member (b* (((mv arg - env)
                      (const-prop-expr expr.arg env)))
                  (mv (make-expr-member :arg arg :name expr.name)
                      ;; TODO
                      nil
                      env))
        :memberp (b* (((mv arg - env)
                       (const-prop-expr expr.arg env)))
                   (mv (make-expr-memberp :arg arg :name expr.name)
                       nil
                       env))
        :complit (b* (((mv type env)
                       (const-prop-tyname expr.type env))
                      ((mv elems env)
                       (const-prop-desiniter-list expr.elems env)))
                   (mv (make-expr-complit
                         :type type
                         :elems elems
                         :final-comma expr.final-comma)
                       ;; TODO
                       nil
                       env))
        :unary (b* (((mv arg arg-value? env)
                     (const-prop-expr expr.arg env))
                    ((unless arg-value?)
                     (mv (make-expr-unary :op expr.op :arg arg :info nil) nil env))
                    (value? (const-prop-eval-unop-expr expr.op arg-value?)))
                 (mv (if value?
                         (value-to-expr value?)
                       (make-expr-unary :op expr.op :arg arg :info nil))
                     value?
                     env))
        :sizeof (b* (((mv type env)
                      (const-prop-tyname expr.type env)))
                  (mv (expr-sizeof type)
                      ;; TODO
                      nil
                      env))
        :sizeof-ambig (mv (prog2$ (raise "Misusage error: ~x0." (expr-fix expr))
                                  (expr-fix expr))
                          nil
                          env)
        :alignof (b* (((mv type env)
                       (const-prop-tyname expr.type env)))
                   (mv (make-expr-alignof :type type
                                          :uscores expr.uscores)
                       ;; TODO
                       nil
                       env))
        :cast (b* (((mv arg - env)
                    (const-prop-expr expr.arg env))
                   ((mv type env)
                    (const-prop-tyname expr.type env)))
                (mv (make-expr-cast :type type
                                    :arg arg)
                    ;; TODO
                    nil
                    env))
        ;; NOTE: asgmt here
        :binary (b* (((mv arg2 arg2-value? env)
                      (const-prop-expr expr.arg2 env))
                     ((unless (pure-binopp expr.op))
                      (b* (((unless arg2-value?)
                            (mv (make-expr-binary :op expr.op
                                                  :arg1 expr.arg1
                                                  :arg2 arg2
                                                  :info expr.info)
                                nil
                                env))
                           ((mv value? env)
                            (const-prop-eval-impure-binop-expr expr.op
                                                               expr.arg1
                                                               arg2-value?
                                                               env)))
                        ;; (if value?
                        ;; Cannot necessarily remove assignments (consider an
                        ;; assignment in one of many branches. E.g. example 4.)
                        ;; Removing unused variables might be a different
                        ;; transform, or at least a different pass.
                        (if nil
                            (mv (value-to-expr value?) value? env)
                          (mv (make-expr-binary :op expr.op
                                                :arg1 expr.arg1
                                                :arg2 arg2
                                                :info expr.info)
                              nil
                              env))))
                     ((mv arg1 arg1-value? env)
                      (const-prop-expr expr.arg1 env))
                     ((unless (and arg1-value? arg2-value?))
                      (mv (make-expr-binary :op expr.op
                                            :arg1 arg1
                                            :arg2 arg2
                                            :info expr.info)
                          nil
                          env))
                     (value?
                       (const-prop-eval-pure-binop-expr expr.op
                                                        arg1-value?
                                                        arg2-value?)))
                  (mv (if value?
                          (value-to-expr value?)
                        (make-expr-binary :op expr.op
                                          :arg1 arg1
                                          :arg2 arg2
                                          :info expr.info))
                      value?
                      env))
        :cond (b* (((mv test - env)
                    (const-prop-expr expr.test env))
                   ((mv then - env)
                     (const-prop-expr-option expr.then env))
                   ((mv else - env)
                    (const-prop-expr expr.else env)))
                ;; TODO (easy)
                (mv (make-expr-cond :test test :then then :else else)
                    nil
                    env))
        :comma (b* (((mv first - env)
                     (const-prop-expr expr.first env))
                    ((mv next - env)
                     (const-prop-expr expr.next env)))
                 (mv (make-expr-comma :first first
                                      :next next)
                     ;; TODO
                     nil
                     env))
        :cast/call-ambig (mv (prog2$ (raise "Misusage error: ~x0." (expr-fix expr))
                                     (expr-fix expr))
                             nil
                             env)
        :cast/mul-ambig (mv (prog2$ (raise "Misusage error: ~x0." (expr-fix expr))
                                    (expr-fix expr))
                            nil
                            env)
        :cast/add-ambig (mv (prog2$ (raise "Misusage error: ~x0." (expr-fix expr))
                                    (expr-fix expr))
                            nil
                            env)
        :cast/sub-ambig (mv (prog2$ (raise "Misusage error: ~x0." (expr-fix expr))
                                    (expr-fix expr))
                            nil
                            env)
        :cast/and-ambig (mv (prog2$ (raise "Misusage error: ~x0." (expr-fix expr))
                                    (expr-fix expr))
                            nil
                            env)
        :stmt (b* (((mv items env)
                    (const-prop-block-item-list expr.items (push-scope-env env))))
                (mv (expr-stmt items)
                    ;; TODO
                    nil
                    (pop-scope-env env)))
        :tycompat (b* (((mv type1 env)
                        (const-prop-tyname expr.type1 env))
                       ((mv type2 env)
                        (const-prop-tyname expr.type2 env)))
                    (mv (make-expr-tycompat :type1 type1
                                            :type2 type2)
                        ;; TODO
                        nil
                        env))
        :offsetof (b* (((mv type env)
                        (const-prop-tyname expr.type env))
                       ((mv member env)
                        (const-prop-member-designor expr.member env)))
                    (mv (make-expr-offsetof
                          :type type
                          :member member)
                        ;; TODO
                        nil
                        env))
        :va-arg (mv (prog2$ (raise "Unhandled case: ~x0." (expr-fix expr))
                            (expr-fix expr))
                    nil
                    env)
        :extension (mv (prog2$ (raise "Unhandled case: ~x0." (expr-fix expr))
                               (expr-fix expr))
                       nil
                       env)))
    :measure (expr-count expr))

  (define const-prop-expr-list
    ((exprs expr-listp)
     (env envp))
    :short "Propagate a constant through a @(see c$::expr-list)."
    :returns (mv (new-exprs expr-listp)
                 (new-env envp))
    (b* ((env (env-fix env))
         ((when (endp exprs))
          (mv nil env))
         ((mv first - env)
          (const-prop-expr (first exprs) env))
         ((mv rest env)
          (const-prop-expr-list (rest exprs) env)))
      (mv (cons first rest)
          env))
    :measure (expr-list-count exprs))

  (define const-prop-expr-option
    ((expr? expr-optionp)
     (env envp))
    :short "Propagate a constant through a @(see c$::expr-option)."
    :returns (mv (new-expr? expr-optionp)
                 (value? c::value-optionp)
                 (new-env envp))
    (b* ((env (env-fix env)))
      (expr-option-case
        expr?
        :some (b* (((mv val value? env)
                    (const-prop-expr expr?.val env)))
                (mv val value? env))
        :none (mv nil nil env)))
    :measure (expr-option-count expr?))

  (define const-prop-const-expr
    ((cexpr const-exprp)
     (env envp))
    :short "Propagate a constant through a @(see c$::const-expr)."
    :returns (mv (new-cexpr const-exprp)
                 (new-env envp))
    (b* (((mv expr - env)
          (const-prop-expr (const-expr->expr cexpr) env)))
      (mv (const-expr expr) env))
    :measure (const-expr-count cexpr))

  (define const-prop-const-expr-option
    ((const-expr? const-expr-optionp)
     (env envp))
    :short "Propagate a constant through a @(see c$::const-expr-option)."
    :returns (mv (new-const-expr? const-expr-optionp)
                 (new-env envp))
    (b* ((env (env-fix env)))
      (const-expr-option-case
        const-expr?
        :some (const-prop-const-expr const-expr?.val env)
        :none (mv nil env)))
    :measure (const-expr-option-count const-expr?))

  (define const-prop-genassoc
    ((genassoc genassocp)
     (env envp))
    :short "Propagate a constant through a @(see c$::genassoc)."
    :returns (mv (new-genassoc genassocp)
                 (new-env envp))
    (b* ((env (env-fix env)))
      (genassoc-case
        genassoc
        :type
        (b* (((mv type env)
              (const-prop-tyname genassoc.type env))
             ((mv expr - env)
              (const-prop-expr genassoc.expr env)))
          (mv (make-genassoc-type :type type
                                  :expr expr)
              env))
        :default (b* (((mv expr - env)
                       (const-prop-expr genassoc.expr env)))
                   (mv (genassoc-default expr)
                       env))))
    :measure (genassoc-count genassoc))

  (define const-prop-genassoc-list
    ((genassocs genassoc-listp)
     (env envp))
    :short "Propagate a constant through a @(see c$::genassoc-list)."
    :returns (mv (new-genassocs genassoc-listp)
                 (new-env envp))
    (b* ((env (env-fix env))
         ((when (endp genassocs))
          (mv nil env))
         ((mv first env)
          (const-prop-genassoc (first genassocs) env))
         ((mv rest env)
          (const-prop-genassoc-list (rest genassocs) env)))
      (mv (cons first rest)
          env))
    :measure (genassoc-list-count genassocs))

  (define const-prop-member-designor
    ((memdes member-designorp)
     (env envp))
    :short "Propagate a constant through a @(see c$::member-designor)."
    :returns (mv (new-memdes member-designorp)
                 (new-env envp))
    (b* ((env (env-fix env)))
      (member-designor-case
        memdes
        :ident (mv (member-designor-fix memdes) env)
        :dot (b* (((mv member env)
                   (const-prop-member-designor memdes.member env)))
               (mv (make-member-designor-dot
                     :member member
                     :name memdes.name)
                   env))
        :sub (b* (((mv index - env)
                   (const-prop-expr memdes.index env))
                  ((mv member env)
                   (const-prop-member-designor memdes.member env)))
               (mv (make-member-designor-sub
                     :member member
                     :index index)
                   env))))
    :measure (member-designor-count memdes))

  (define const-prop-type-spec
    ((tyspec type-specp)
     (env envp))
    :short "Propagate a constant through a @(see c$::type-spec)."
    :returns (mv (new-tyspec type-specp)
                 (new-env envp))
    (b* ((env (env-fix env)))
      (type-spec-case
        tyspec
        :void (mv (type-spec-fix tyspec) env)
        :char (mv (type-spec-fix tyspec) env)
        :short (mv (type-spec-fix tyspec) env)
        :int (mv (type-spec-fix tyspec) env)
        :long (mv (type-spec-fix tyspec) env)
        :float (mv (type-spec-fix tyspec) env)
        :double (mv (type-spec-fix tyspec) env)
        :signed (mv (type-spec-fix tyspec) env)
        :unsigned (mv (type-spec-fix tyspec) env)
        :bool (mv (type-spec-fix tyspec) env)
        :complex (mv (type-spec-fix tyspec) env)
        :atomic (b* (((mv type env)
                      (const-prop-tyname tyspec.type env)))
                  (mv (type-spec-atomic type) env))
        :struct (b* (((mv spec env)
                      (const-prop-struni-spec tyspec.spec env)))
                  (mv (type-spec-struct spec) env))
        :union (b* (((mv spec env)
                     (const-prop-struni-spec tyspec.spec env)))
                 (mv (type-spec-union spec) env))
        :enum (b* (((mv spec env)
                    (const-prop-enumspec tyspec.spec env)))
                (mv (type-spec-enum spec) env))
        :typedef (mv (type-spec-fix tyspec) env)
        :int128 (mv (type-spec-fix tyspec) env)
        :float32 (mv (type-spec-fix tyspec) env)
        :float32x (mv (type-spec-fix tyspec) env)
        :float64 (mv (type-spec-fix tyspec) env)
        :float64x (mv (type-spec-fix tyspec) env)
        :float128 (mv (type-spec-fix tyspec) env)
        :float128x (mv (type-spec-fix tyspec) env)
        :builtin-va-list (mv (type-spec-fix tyspec) env)
        :struct-empty (mv (type-spec-fix tyspec) env)
        :typeof-expr (b* (((mv expr - env)
                           (const-prop-expr tyspec.expr env)))
                       (mv (make-type-spec-typeof-expr
                             :expr expr
                             :uscores tyspec.uscores)
                           env))
        :typeof-type (b* (((mv type env)
                           (const-prop-tyname tyspec.type env)))
                       (mv (make-type-spec-typeof-type
                             :type type
                             :uscores tyspec.uscores)
                           env))
        :typeof-ambig (prog2$ (raise "Misusage error: ~x0."
                                     (type-spec-fix tyspec))
                              (mv (type-spec-fix tyspec) env))
        :auto-type (mv (type-spec-fix tyspec) env)))
    :measure (type-spec-count tyspec))

  (define const-prop-spec/qual
    ((specqual spec/qual-p)
     (env envp))
    :short "Propagate a constant through a @(see c$::spec/qual)."
    :returns (mv (new-specqual spec/qual-p)
                 (new-env envp))
    (b* ((env (env-fix env)))
      (spec/qual-case
        specqual
        :typespec (b* (((mv spec env)
                        (const-prop-type-spec specqual.spec env)))
                    (mv (spec/qual-typespec spec) env))
        :typequal (mv (spec/qual-fix specqual) env)
        :align (b* (((mv spec env)
                     (const-prop-align-spec specqual.spec env)))
                 (mv (spec/qual-align spec) env))
        :attrib (mv (spec/qual-fix specqual) env)))
    :measure (spec/qual-count specqual))

  (define const-prop-spec/qual-list
    ((specquals spec/qual-listp)
     (env envp))
    :short "Propagate a constant through a @(see c$::spec/qual-list)."
    :returns (mv (new-specquals spec/qual-listp)
                 (new-env envp))
    (b* ((env (env-fix env))
         ((when (endp specquals))
          (mv nil env))
         ((mv first env)
          (const-prop-spec/qual (first specquals) env))
         ((mv rest env)
          (const-prop-spec/qual-list (rest specquals) env)))
      (mv (cons first rest)
          env))
    :measure (spec/qual-list-count specquals))

  (define const-prop-align-spec
    ((alignspec align-specp)
     (env envp))
    :short "Propagate a constant through a @(see c$::align-spec)."
    :returns (mv (new-alignspec align-specp)
                 (new-env envp))
    (b* ((env (env-fix env)))
      (align-spec-case
        alignspec
        :alignas-type (b* (((mv type env)
                            (const-prop-tyname alignspec.type env)))
                        (mv (align-spec-alignas-type type) env))
        :alignas-expr (b* (((mv expr env)
                            (const-prop-const-expr alignspec.expr env)))
                        (mv (align-spec-alignas-expr expr) env))
        :alignas-ambig (prog2$ (raise "Misusage error: ~x0."
                                      (align-spec-fix alignspec))
                               (mv (align-spec-fix alignspec) env))))
    :measure (align-spec-count alignspec))

  (define const-prop-decl-spec
    ((decl-spec decl-specp)
     (env envp))
    :short "Propagate a constant through a @(see c$::decl-spec)."
    :returns (mv (new-decl-spec decl-specp)
                 (new-env envp))
    (b* ((env (env-fix env)))
      (decl-spec-case
        decl-spec
        :stoclass (mv (decl-spec-fix decl-spec) env)
        :typespec (b* (((mv spec env)
                      (const-prop-type-spec decl-spec.spec env)))
                  (mv (decl-spec-typespec spec) env))
        :typequal (mv (decl-spec-fix decl-spec) env)
        :function (mv (decl-spec-fix decl-spec) env)
        :align (b* (((mv spec env)
                     (const-prop-align-spec decl-spec.spec env)))
                 (mv (decl-spec-align spec) env))
        :attrib (mv (decl-spec-fix decl-spec) env)
        :stdcall (mv (decl-spec-fix decl-spec) env)
        :declspec (mv (decl-spec-fix decl-spec) env)))
    :measure (decl-spec-count decl-spec))

  (define const-prop-decl-spec-list
    ((decl-specs decl-spec-listp)
     (env envp))
    :short "Propagate a constant through a @(see c$::decl-spec-list)."
    :returns (mv (new-decl-specs decl-spec-listp)
                 (new-env envp))
    (b* ((env (env-fix env))
         ((when (endp decl-specs))
          (mv nil env))
         ((mv first env)
          (const-prop-decl-spec (first decl-specs) env))
         ((mv rest env)
          (const-prop-decl-spec-list (rest decl-specs) env)))
      (mv (cons first rest) env))
    :measure (decl-spec-list-count decl-specs))

  (define const-prop-initer
    ((initer initerp)
     (env envp))
    :short "Propagate a constant through a @(see c$::initer)."
    :returns (mv (new-initer initerp)
                 (value? c::value-optionp)
                 (new-env envp))
    (b* ((env (env-fix env)))
      (initer-case
        initer
        :single (b* (((mv expr value? env)
                      (const-prop-expr initer.expr env)))
                  (mv (initer-single expr) value? env))
        :list (b* (((mv elems env)
                    (const-prop-desiniter-list initer.elems env)))
                (mv (make-initer-list
                      :elems elems
                      :final-comma initer.final-comma)
                    nil
                    env))))
    :measure (initer-count initer))

  (define const-prop-initer-option
    ((initer? initer-optionp)
     (env envp))
    :short "Propagate a constant through a @(see c$::initer-option)."
    :returns (mv (new-initer? initer-optionp)
                 (value? c::value-optionp)
                 (new-env envp))
    (b* ((env (env-fix env)))
      (initer-option-case initer?
                          :some (const-prop-initer initer?.val env)
                          :none (mv nil nil env)))
    :measure (initer-option-count initer?))

  (define const-prop-desiniter
    ((desiniter desiniterp)
     (env envp))
    :short "Propagate a constant through a @(see c$::desiniter)."
    :returns (mv (new-desiniter desiniterp)
                 (new-env envp))
    (b* ((env (env-fix env))
         ((desiniter desiniter) desiniter)
         ((mv designors env)
          (const-prop-designor-list desiniter.designors env))
         ((mv initer - env)
          (const-prop-initer desiniter.initer env)))
      (mv (make-desiniter
            :designors designors
            :initer initer)
          env))
    :measure (desiniter-count desiniter))

  (define const-prop-desiniter-list
    ((desiniters desiniter-listp)
     (env envp))
    :short "Propagate a constant through a @(see c$::desiniter-list)."
    :returns (mv (new-desiniters desiniter-listp)
                 (new-env envp))
    (b* ((env (env-fix env))
         ((when (endp desiniters))
          (mv nil env))
         ((mv first env)
          (const-prop-desiniter (first desiniters) env))
         ((mv rest env)
          (const-prop-desiniter-list (rest desiniters) env)))
      (mv (cons first rest)
          env))
    :measure (desiniter-list-count desiniters))

  (define const-prop-designor
    ((designor designorp)
     (env envp))
    :short "Propagate a constant through a @(see c$::designor)."
    :returns (mv (new-designor designorp)
                 (new-env envp))
    (b* ((env (env-fix env)))
      (designor-case
        designor
        :sub (b* (((mv index env)
                   (const-prop-const-expr designor.index env)))
               (mv (designor-sub index) env))
        :dot (mv (designor-fix designor) env)))
    :measure (designor-count designor))

  (define const-prop-designor-list
    ((designors designor-listp)
     (env envp))
    :short "Propagate a constant through a @(see c$::designor-list)."
    :returns (mv (new-designors designor-listp)
                 (new-env envp))
    (b* ((env (env-fix env))
         ((when (endp designors))
          (mv nil env))
         ((mv first env)
          (const-prop-designor (first designors) env))
         ((mv rest env)
          (const-prop-designor-list (rest designors) env)))
      (mv (cons first rest) env))
    :measure (designor-list-count designors))

  (define const-prop-declor
    ((declor declorp)
     (env envp))
    :short "Propagate a constant through a @(see c$::declor)."
    :returns (mv (new-declor declorp)
                 (new-env envp))
    (b* ((env (env-fix env))
         ((declor declor) declor)
         ((mv direct env)
          (const-prop-dirdeclor declor.direct env)))
      (mv (make-declor :pointers declor.pointers
                       :direct direct)
          env))
    :measure (declor-count declor))

  (define const-prop-declor-option
    ((declor? declor-optionp)
     (env envp))
    :short "Propagate a constant through a @(see c$::declor-option)."
    :returns (mv (new-declor? declor-optionp)
                 (new-env envp))
    (b* ((env (env-fix env)))
      (declor-option-case
        declor?
        :some (const-prop-declor declor?.val env)
        :none (mv nil env)))
    :measure (declor-option-count declor?))

  (define const-prop-dirdeclor
    ((dirdeclor dirdeclorp)
     (env envp))
    :short "Propagate a constant through a @(see c$::dirdeclor)."
    :returns (mv (new-dirdeclor dirdeclorp)
                 (new-env envp))
    (b* ((env (env-fix env)))
      (dirdeclor-case
        dirdeclor
        :ident (mv (dirdeclor-fix dirdeclor) env)
        :paren (b* (((mv unwrap env)
                     (const-prop-declor dirdeclor.inner env)))
                 (mv (dirdeclor-paren unwrap) env))
        :array (b* (((mv decl env)
                     (const-prop-dirdeclor dirdeclor.declor env))
                    ((mv expr? - env)
                     (const-prop-expr-option dirdeclor.size? env)))
                 (mv (make-dirdeclor-array
                       :declor decl
                       :qualspecs dirdeclor.qualspecs
                       :size? expr?)
                     env))
        :array-static1 (b* (((mv decl env)
                             (const-prop-dirdeclor dirdeclor.declor env))
                            ((mv expr - env)
                             (const-prop-expr dirdeclor.size env)))
                         (mv (make-dirdeclor-array-static1
                               :declor decl
                               :qualspecs dirdeclor.qualspecs
                               :size expr)
                             env))
        :array-static2 (b* (((mv decl env)
                             (const-prop-dirdeclor dirdeclor.declor env))
                            ((mv expr - env)
                             (const-prop-expr dirdeclor.size env)))
                         (mv (make-dirdeclor-array-static2
                               :declor decl
                               :qualspecs dirdeclor.qualspecs
                               :size expr)
                             env))
        :array-star (b* (((mv decl env)
                          (const-prop-dirdeclor dirdeclor.declor env)))
                      (mv (make-dirdeclor-array-star
                            :declor decl
                            :qualspecs dirdeclor.qualspecs)
                          env))
        :function-params
        (b* (((mv decl env)
              (const-prop-dirdeclor dirdeclor.declor env))
             ((mv params env)
              (const-prop-param-declon-list dirdeclor.params env)))
          (mv (make-dirdeclor-function-params
                :declor decl
                :params params
                :ellipsis dirdeclor.ellipsis)
              env))
        :function-names (b* (((mv decl env)
                              (const-prop-dirdeclor dirdeclor.declor env)))
                          (mv (make-dirdeclor-function-names
                                :declor decl
                                ;; TODO: deftrans added unneeded fixing function
                                :names dirdeclor.names)
                              env))))
    :measure (dirdeclor-count dirdeclor))

  (define const-prop-absdeclor
    ((absdeclor absdeclorp)
     (env envp))
    :short "Propagate a constant through a @(see c$::absdeclor)."
    :returns (mv (new-absdeclor absdeclorp)
                 (new-env envp))
    (b* ((env (env-fix env))
         ((absdeclor absdeclor) absdeclor)
         ((mv direct? env)
          (const-prop-dirabsdeclor-option absdeclor.direct? env)))
      (mv (make-absdeclor
            :pointers absdeclor.pointers
            :direct? direct?)
          env))
    :measure (absdeclor-count absdeclor))

  (define const-prop-absdeclor-option
    ((absdeclor? absdeclor-optionp)
     (env envp))
    :short "Propagate a constant through a @(see c$::absdeclor-option)."
    :returns (mv (new-absdeclor? absdeclor-optionp)
                 (new-env envp))
    (b* ((env (env-fix env)))
      (absdeclor-option-case
        absdeclor?
        :some (const-prop-absdeclor absdeclor?.val env)
        :none (mv nil env)))
    :measure (absdeclor-option-count absdeclor?))

  (define const-prop-dirabsdeclor
    ((dirabsdeclor dirabsdeclorp)
     (env envp))
    :short "Propagate a constant through a @(see c$::dirabsdeclor)."
    :returns (mv (new-dirabsdeclor dirabsdeclorp)
                 (new-env envp))
    (b* ((env (env-fix env)))
      (dirabsdeclor-case
        dirabsdeclor
        :dummy-base (prog2$ (raise "Misusage error: ~x0."
                                   (dirabsdeclor-fix dirabsdeclor))
                            (mv (dirabsdeclor-fix dirabsdeclor)
                                env))
        :paren (b* (((mv unwrap env)
                     (const-prop-absdeclor dirabsdeclor.inner env)))
                 (mv (dirabsdeclor-paren unwrap) env))
        :array
        (b* (((mv declor? env)
              (const-prop-dirabsdeclor-option dirabsdeclor.declor? env))
             ((mv expr? - env)
              (const-prop-expr-option dirabsdeclor.size? env)))
          (mv (make-dirabsdeclor-array
                :declor? declor?
                :qualspecs dirabsdeclor.qualspecs
                :size? expr?)
              env))
        :array-static1
        (b* (((mv declor? env)
              (const-prop-dirabsdeclor-option dirabsdeclor.declor? env))
             ((mv expr - env)
              (const-prop-expr dirabsdeclor.size env)))
          (mv (make-dirabsdeclor-array-static1
                :declor? declor?
                :qualspecs dirabsdeclor.qualspecs
                :size expr)
              env))
        :array-static2
        (b* (((mv declor? env)
              (const-prop-dirabsdeclor-option dirabsdeclor.declor? env))
             ((mv expr - env)
              (const-prop-expr dirabsdeclor.size env)))
          (mv (make-dirabsdeclor-array-static2
                :declor? declor?
                :qualspecs dirabsdeclor.qualspecs
                :size expr)
              env))
        :array-star
        (b* (((mv declor? env)
              (const-prop-dirabsdeclor-option dirabsdeclor.declor? env)))
          (mv (dirabsdeclor-array-star declor?)
              env))
        :function
        (b* (((mv declor? env)
              (const-prop-dirabsdeclor-option dirabsdeclor.declor? env))
             ((mv params env)
              (const-prop-param-declon-list dirabsdeclor.params env)))
          (mv (make-dirabsdeclor-function
                :declor? declor?
                :params params
                :ellipsis dirabsdeclor.ellipsis)
              env))))
    :measure (dirabsdeclor-count dirabsdeclor))

  (define const-prop-dirabsdeclor-option
    ((dirabsdeclor? dirabsdeclor-optionp)
     (env envp))
    :short "Propagate a constant through a @(see c$::dirabsdeclor-option)."
    :returns (mv (new-dirabsdeclor? dirabsdeclor-optionp)
                 (new-env envp))
    (b* ((env (env-fix env)))
      (dirabsdeclor-option-case
        dirabsdeclor?
        :some (const-prop-dirabsdeclor dirabsdeclor?.val env)
        :none (mv nil env)))
    :measure (dirabsdeclor-option-count dirabsdeclor?))

  (define const-prop-param-declon
    ((paramdecl param-declonp)
     (env envp))
    :short "Propagate a constant through a @(see c$::param-declon)."
    :returns (mv (new-paramdecl param-declonp)
                 (new-env envp))
    (b* ((env (env-fix env))
         ((param-declon paramdecl) paramdecl)
         ((mv spec env)
          (const-prop-decl-spec-list paramdecl.specs env))
         ((mv decl env)
          (const-prop-param-declor paramdecl.declor env)))
      (mv (make-param-declon
            :specs spec
            :declor decl)
          env))
    :measure (param-declon-count paramdecl))

  (define const-prop-param-declon-list
    ((paramdecls param-declon-listp)
     (env envp))
    :short "Propagate a constant through a @(see c$::param-declon-list)."
    :returns (mv (new-paramdecls param-declon-listp)
                 (new-env envp))
    (b* ((env (env-fix env))
         ((when (endp paramdecls))
          (mv nil env))
         ((mv first env)
          (const-prop-param-declon (first paramdecls) env))
         ((mv rest env)
          (const-prop-param-declon-list (rest paramdecls) env)))
      (mv (cons first rest)
          env))
    :measure (param-declon-list-count paramdecls))

  (define const-prop-param-declor
    ((paramdeclor param-declorp)
     (env envp))
    :short "Propagate a constant through a @(see c$::param-declor)."
    :returns (mv (new-paramdeclor param-declorp)
                 (new-env envp))
    (b* ((env (env-fix env)))
      (param-declor-case
        paramdeclor
        :nonabstract (b* (((mv declor env)
                           (const-prop-declor paramdeclor.declor env)))
                       (mv (c$::make-param-declor-nonabstract
                             :declor declor
                             :info paramdeclor.info)
                           env))
        :abstract (b* (((mv unwrap env)
                        (const-prop-absdeclor paramdeclor.declor env)))
                    (mv (param-declor-abstract unwrap) env))
        :none (mv (param-declor-none) env)
        :ambig (prog2$ (raise "Misusage error: ~x0."
                              (param-declor-fix paramdeclor))
                       (mv (param-declor-fix paramdeclor)
                           env))))
    :measure (param-declor-count paramdeclor))

  (define const-prop-tyname
    ((tyname tynamep)
     (env envp))
    :short "Propagate a constant through a @(see c$::tyname)."
    :returns (mv (new-tyname tynamep)
                 (new-env envp))
    (b* ((env (env-fix env))
         ((tyname tyname) tyname)
         ((mv specquals env)
          (const-prop-spec/qual-list tyname.specquals env))
         ((mv declor? env)
          (const-prop-absdeclor-option tyname.declor? env)))
      (mv (make-tyname
            :specquals specquals
            :declor? declor?
            :info tyname.info)
          env))
    :measure (tyname-count tyname))

  (define const-prop-struni-spec
    ((struni-spec struni-specp)
     (env envp))
    :short "Propagate a constant through a @(see c$::struni-spec)."
    :returns (mv (new-struni-spec struni-specp)
                 (new-env envp))
    (b* ((env (env-fix env))
         ((struni-spec struni-spec) struni-spec)
         ((mv members env)
          (const-prop-structdecl-list struni-spec.members env)))
      (mv (make-struni-spec
            :name? struni-spec.name?
            :members members)
          env))
    :measure (struni-spec-count struni-spec))

  (define const-prop-structdecl
    ((structdecl structdeclp)
     (env envp))
    :short "Propagate a constant through a @(see c$::structdecl)."
    :returns (mv (new-structdecl structdeclp)
                 (new-env envp))
    (b* ((env (env-fix env)))
      (structdecl-case
        structdecl
        :member (b* (((mv specqual env)
                      (const-prop-spec/qual-list structdecl.specqual env))
                     ((mv declor env)
                      (const-prop-structdeclor-list structdecl.declor env)))
                  (mv (make-structdecl-member
                        :extension structdecl.extension
                        :specqual specqual
                        :declor declor
                        :attrib structdecl.attrib)
                      env))
        :statassert (b* (((mv unwrap env)
                          (const-prop-statassert structdecl.unwrap env)))
                      (mv (structdecl-statassert unwrap)
                          env))
        :empty (mv (structdecl-empty) env)))
    :measure (structdecl-count structdecl))

  (define const-prop-structdecl-list
    ((structdecls structdecl-listp)
     (env envp))
    :short "Propagate a constant through a @(see c$::structdecl-list)."
    :returns (mv (new-structdecls structdecl-listp)
                 (new-env envp))
    (b* ((env (env-fix env))
         ((when (endp structdecls))
          (mv nil env))
         ((mv first env)
          (const-prop-structdecl (first structdecls) env))
         ((mv rest env)
          (const-prop-structdecl-list (rest structdecls) env)))
      (mv (cons first rest)
          env))
    :measure (structdecl-list-count structdecls))

  (define const-prop-structdeclor
    ((structdeclor structdeclorp)
     (env envp))
    :short "Propagate a constant through a @(see c$::structdeclor)."
    :returns (mv (new-structdeclor structdeclorp)
                 (new-env envp))
    (b* ((env (env-fix env))
         ((structdeclor structdeclor)
          structdeclor)
         ((mv declor? env)
          (const-prop-declor-option structdeclor.declor? env))
         ((mv expr? env)
          (const-prop-const-expr-option structdeclor.expr? env)))
      (mv (make-structdeclor
            :declor? declor?
            :expr? expr?)
          env))
    :measure (structdeclor-count structdeclor))

  (define const-prop-structdeclor-list
    ((structdeclors structdeclor-listp)
     (env envp))
    :short "Propagate a constant through a @(see c$::structdeclor-list)."
    :returns (mv (new-structdeclors structdeclor-listp)
                 (new-env envp))
    (b* ((env (env-fix env))
         ((when (endp structdeclors))
          (mv nil env))
         ((mv first env)
          (const-prop-structdeclor (first structdeclors) env))
         ((mv rest env)
          (const-prop-structdeclor-list (rest structdeclors) env)))
      (mv (cons first rest)
          env))
    :measure (structdeclor-list-count structdeclors))

  (define const-prop-enumspec
    ((enumspec enumspecp)
     (env envp))
    :short "Propagate a constant through a @(see c$::enumspec)."
    :returns (mv (new-enumspec enumspecp)
                 (new-env envp))
    (b* ((env (env-fix env))
         ((enumspec enumspec) enumspec)
         ((mv list env)
          (const-prop-enumer-list enumspec.list env)))
      (mv (make-enumspec :name enumspec.name
                         :list list
                         :final-comma enumspec.final-comma)
          env))
    :measure (enumspec-count enumspec))

  (define const-prop-enumer
    ((enumer enumerp)
     (env envp))
    :short "Propagate a constant through a @(see c$::enumer)."
    :returns (mv (new-enumer enumerp)
                 (new-env envp))
    (b* ((env (env-fix env))
         ((enumer enumer) enumer)
         ((mv value env)
          (const-prop-const-expr-option enumer.value env)))
      (mv (make-enumer
            :name enumer.name
            :value value)
          env))
    :measure (enumer-count enumer))

  (define const-prop-enumer-list
    ((enumers enumer-listp)
     (env envp))
    :short "Propagate a constant through a @(see c$::enumer-list)."
    :returns (mv (new-enumers enumer-listp)
                 (new-env envp))
    (b* ((env (env-fix env))
         ((when (endp enumers))
          (mv nil env))
         ((mv first env)
          (const-prop-enumer (first enumers) env))
         ((mv rest env)
          (const-prop-enumer-list (rest enumers) env)))
      (mv (cons first rest)
          env))
    :measure (enumer-list-count enumers))

  (define const-prop-statassert
    ((statassert statassertp)
     (env envp))
    :short "Propagate a constant through a @(see c$::statassert)."
    :returns (mv (new-statassert statassertp)
                 (new-env envp))
    (b* ((env (env-fix env))
         ((statassert statassert) statassert)
         ((mv test env)
          (const-prop-const-expr statassert.test env)))
      (mv (make-statassert
            :test test
            :message statassert.message)
          env))
    :measure (statassert-count statassert))

  ;; Needs to return identifier and optional value
  (define const-prop-initdeclor
    ((initdeclor initdeclorp)
     (env envp))
    :short "Propagate a constant through a @(see c$::initdeclor)."
    :returns (mv (new-initdeclor initdeclorp)
                 (ident identp)
                 (value? c::value-optionp)
                 (new-env envp))
    (b* ((env (env-fix env))
         ((initdeclor initdeclor) initdeclor)
         ((mv declor env)
          (const-prop-declor initdeclor.declor env))
         ((mv init? value? env)
          (const-prop-initer-option initdeclor.init? env)))
      (mv (make-initdeclor
            :declor declor
            :asm? initdeclor.asm?
            :init? init?)
          (declor->ident declor)
          value?
          env))
    :measure (initdeclor-count initdeclor))

  ;; Needs to return list of identifiers and optional values
  (define const-prop-initdeclor-list
    ((initdeclors initdeclor-listp)
     (env envp))
    :short "Propagate a constant through a @(see c$::initdeclor-list)."
    :returns (mv (new-initdeclors initdeclor-listp)
                 (idents env-blockp)
                 (new-env envp))
    (b* ((env (env-fix env))
         ((when (endp initdeclors))
          (mv nil nil env))
         ((mv first ident value? env)
          (const-prop-initdeclor (first initdeclors) env))
         ((mv rest idents env)
          (const-prop-initdeclor-list (cdr initdeclors) env)))
      (mv (cons first rest)
          (omap::update ident
                        value?
                        idents)
          env))
    :measure (initdeclor-list-count initdeclors))

  (define const-prop-decl
    ((decl declp)
     (env envp))
    :short "Propagate a constant through a @(see c$::decl)."
    :returns (mv (new-decl declp)
                 (new-env envp))
    (b* ((env (env-fix env)))
      (decl-case
        decl
        :decl (b* (((mv specs env)
                    (const-prop-decl-spec-list decl.specs env))
                   ((mv init idents env)
                    (const-prop-initdeclor-list decl.init env)))
                (mv (make-decl-decl :extension decl.extension
                                    :specs specs
                                    :init init)
                    (merge-block-env idents env)))
        :statassert (b* (((mv unwrap env)
                          (const-prop-statassert decl.unwrap env)))
                      (mv (decl-statassert unwrap) env))))
    :measure (decl-count decl))

  (define const-prop-decl-list
    ((decls decl-listp)
     (env envp))
    :short "Propagate a constant through a @(see c$::decl-list)."
    :returns (mv (new-decls decl-listp)
                 (new-env envp))
    (b* ((env (env-fix env))
         ((when (endp decls))
          (mv nil env))
         ((mv first env)
          (const-prop-decl (first decls) env))
         ((mv rest env)
          (const-prop-decl-list (rest decls) env)))
      (mv (cons first rest)
          env))
    :measure (decl-list-count decls))

  (define const-prop-label
    ((label labelp)
     (env envp))
    :short "Propagate a constant through a @(see c$::label)."
    :returns (mv (new-label labelp)
                 (new-env envp))
    (b* ((env (env-fix env)))
      (label-case
        label
        :name (mv (label-fix label) env)
        ;; Note: this expression should be constant already
        :casexpr (b* (((mv expr env)
                       (const-prop-const-expr label.expr env))
                      ((mv range? env)
                       (const-prop-const-expr-option label.range? env)))
                   (mv (make-label-casexpr
                         :expr expr
                         :range? range?)
                       env))
        :default (mv (label-fix label) env)))
    :measure (label-count label))

  (define const-prop-stmt
    ((stmt stmtp)
     (env envp))
    :short "Propagate a constant through a @(see c$::stmt)."
    ;; TODO: return optional stmt (for when it becomes nop)
    :returns (mv (new-stmt stmtp)
                 (new-env envp))
    (b* ((env (env-fix env)))
      (stmt-case
        stmt
        :labeled (b* (((mv label -)
                       (const-prop-label stmt.label nil))
                      ((mv stmt env)
                       ;; We assume nothing upon entering the labeled block. We
                       ;; could do better if we tried to establish a finite set
                       ;; goto in the function to this label.
                       (const-prop-stmt stmt.stmt nil)))
                   (mv (make-stmt-labeled :label label
                                          :stmt stmt)
                       env))
        :compound (b* (((mv items env)
                        (const-prop-block-item-list stmt.items env)))
                    (mv (stmt-compound items) env))
        :expr (b* (((mv expr? - env)
                    (const-prop-expr-option stmt.expr? env)))
                (mv (make-stmt-expr :expr? expr?
                                    :info stmt.info)
                    env))
        :if (b* (((mv test value? env)
                  (const-prop-expr stmt.test env))
                 ((mv then then-env)
                  (const-prop-stmt stmt.then (push-scope-env env)))
                 ((when value?)
                  (if (zero-valuep value?)
                      (mv (make-stmt-expr :expr? (value-to-expr value?)
                                          :info nil)
                          env)
                    (mv then
                        (pop-scope-env then-env)))))
              (mv (make-stmt-if :test test
                                :then then)
                  (union-env env
                             (pop-scope-env then-env))))
        :ifelse (b* (((mv test value? env)
                      (const-prop-expr stmt.test env))
                     ((mv then then-env)
                      (const-prop-stmt stmt.then (push-scope-env env)))
                     ((mv else else-env)
                      (const-prop-stmt stmt.else (push-scope-env env)))
                     ;; TODO: envs need to be conservatively combined (unioned)
                     ;;   That is, changes only kept if they agree. Otherwise,
                     ;;   var should be marked unknown.
                     ;; (env (union-env (pop-scope-env then-env)
                     ;;                 (pop-scope-env else-env)))
                     ((when value?)
                      (if (zero-valuep value?)
                          (mv else (pop-scope-env else-env))
                        (mv then (pop-scope-env then-env)))))
                  (mv (make-stmt-ifelse :test test
                                        :then then
                                        :else else)
                      (union-env (pop-scope-env then-env)
                                 (pop-scope-env else-env))))
        :switch
        (b* (((mv target - env)
              (const-prop-expr stmt.target env))
             ((mv body env)
              (const-prop-stmt stmt.body env)))
          (mv (make-stmt-switch :target target
                                :body body)
              env))
        ;; TODO: for now, we give up on loops
        :while (b* (((mv test - env)
                     (const-prop-expr stmt.test env))
                    ((mv body ?env)
                     (const-prop-stmt stmt.body env)))
                 (mv (make-stmt-while :test test
                                      :body body)
                     nil))
        :dowhile (b* (((mv body env)
                       (const-prop-stmt stmt.body env))
                      ((mv test - ?env)
                       (const-prop-expr stmt.test env)))
                   (mv (make-stmt-dowhile :body body
                                          :test test)
                       nil))
        :for-expr (b* (((mv init - env)
                        (const-prop-expr-option stmt.init env))
                       ((mv test - env)
                        (const-prop-expr-option stmt.test env))
                       ((mv next - env)
                        (const-prop-expr-option stmt.next env))
                       ((mv body ?env)
                        (const-prop-stmt stmt.body env)))
                    (mv (make-stmt-for-expr :init init
                                            :test test
                                            :next next
                                            :body body)
                        nil))
        :for-decl (b* (((mv init env)
                        (const-prop-decl stmt.init env))
                       ((mv test - env)
                        (const-prop-expr-option stmt.test env))
                       ((mv next - env)
                        (const-prop-expr-option stmt.next env))
                       ((mv body ?env)
                        (const-prop-stmt stmt.body env)))
                    (mv (make-stmt-for-decl :init init
                                            :test test
                                            :next next
                                            :body body)
                        nil))
        :for-ambig (prog2$ (raise "Misusage error: ~x0." (stmt-fix stmt))
                           (mv (stmt-fix stmt) env))
        :goto (mv (stmt-fix stmt) nil)
        :continue (mv (stmt-fix stmt) env)
        :break (mv (stmt-fix stmt) nil)
        :return (b* (((mv expr? - env)
                      (const-prop-expr-option stmt.expr? env)))
                  (mv (make-stmt-return :expr? expr? :info stmt.info) env))
        :asm (mv (stmt-fix stmt) nil)))
    :measure (stmt-count stmt))

  (define const-prop-block-item
    ((item block-itemp)
     (env envp))
    :short "Propagate a constant through a @(see c$::block-item)."
    :returns (mv (new-item block-itemp)
                 (new-env envp))
    (b* ((env (env-fix env)))
      (block-item-case
        item
        :decl (b* (((mv decl env)
                    (const-prop-decl item.decl env)))
                (mv (make-block-item-decl :decl decl :info item.info) env))
        :stmt (b* (((mv stmt env)
                    (const-prop-stmt item.stmt env)))
                (mv (make-block-item-stmt :stmt stmt :info item.info) env))
        :ambig (prog2$ (raise "Misusage error: ~x0."
                              (block-item-fix item))
                       (mv (block-item-fix item) env))))
    :measure (block-item-count item))

  (define const-prop-block-item-list
    ((items block-item-listp)
     (env envp))
    :short "Propagate a constant through a @(see c$::block-item-list)."
    :returns (mv (new-items block-item-listp)
                 (new-env envp))
    (b* ((env (env-fix env))
         ((when (endp items))
          (mv nil env))
         ((mv first env)
          (const-prop-block-item (first items) env))
         ((mv rest env)
          (const-prop-block-item-list (rest items) env)))
      (mv (cons first rest)
          env))
    :measure (block-item-list-count items))

  :hints (("Goal" :in-theory (enable o< o-finp)))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define const-prop-fundef
  ((fundef fundefp)
   (env envp))
  :returns (new-fundef fundefp)
  (b* (((fundef fundef) fundef)
       ((mv spec -)
        (const-prop-decl-spec-list fundef.spec env))
       ((mv declor -)
        (const-prop-declor fundef.declor env))
       ((mv decls -)
        (const-prop-decl-list fundef.decls env))
       ((mv body -)
        (const-prop-block-item-list fundef.body (push-scope-env env))))
    (make-fundef :extension fundef.extension
                 :spec spec
                 :declor declor
                 :asm? fundef.asm?
                 :decls decls
                 :body body
                 :info fundef.info)))

(define const-prop-extdecl
  ((extdecl extdeclp)
   (env envp))
  :returns (new-extdecl extdeclp)
  (extdecl-case
   extdecl
   :fundef (extdecl-fundef (const-prop-fundef extdecl.unwrap env))
   :decl (b* (((mv unwrap -)
               (const-prop-decl extdecl.unwrap env)))
           (extdecl-decl unwrap))
   :empty (extdecl-empty)
   :asm (extdecl-fix extdecl)))

(define const-prop-extdecl-list
  ((extdecls extdecl-listp)
   (env envp))
  :returns (new-extdecls extdecl-listp)
  (if (endp extdecls)
      nil
    (cons (const-prop-extdecl (first extdecls) env)
          (const-prop-extdecl-list (rest extdecls) env)))
  :measure (acl2-count extdecls)
  :hints (("Goal" :in-theory nil)))

(define const-prop-transunit
  ((tunit transunitp))
  :returns (new-tunit transunitp)
  (b* (((transunit tunit) tunit))
    (make-transunit :decls (const-prop-extdecl-list tunit.decls nil)
                    :info tunit.info)))

(define const-prop-filepath-transunit-map
  ((map filepath-transunit-mapp))
  :returns (new-map filepath-transunit-mapp
                    :hyp (filepath-transunit-mapp map))
  (b* (((when (omap::emptyp map)) nil)
       ((mv path tunit) (omap::head map))
       (new-tunit (const-prop-transunit tunit))
       (new-map
         (const-prop-filepath-transunit-map (omap::tail map))))
    (omap::update (c$::filepath-fix path)
                  new-tunit
                  new-map))
  :verify-guards :after-returns)

(define const-prop-transunit-ensemble
  ((tunits transunit-ensemblep))
  :returns (new-tunits transunit-ensemblep)
  :short "Transform a translation unit ensemble."
  (b* (((transunit-ensemble tunits) tunits))
    (transunit-ensemble
      (const-prop-filepath-transunit-map tunits.unwrap))))

(define const-prop-code-ensemble
  ((code code-ensemblep))
  :returns (new-code code-ensemblep)
  :short "Transform a code ensemble."
  (b* (((code-ensemble code) code))
    (make-code-ensemble
     :transunits (const-prop-transunit-ensemble code.transunits)
     :ienv code.ienv)))
