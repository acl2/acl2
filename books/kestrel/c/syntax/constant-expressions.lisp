; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "validation-annotations")

(include-book "kestrel/abstract-domains/many-valued-logics/3vl" :dir :system)

(local (in-theory (enable* abstract-syntax-unambp-rules)))
(acl2::controlled-configuration)

(local (include-book "kestrel/utilities/ordinals" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (in-theory (enable* abstract-syntax-annop-rules)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ constant-expressions
  :parents (validation)
  :short "Check for C constant expressions."
  :long
  (xdoc::topstring
   (xdoc::p
    "Currently, we only provide recognizer for
     integer constant expressions (ICEs).
     Eventually, we may wish to add support for
     arithmetic constant expressions,
     address constants,
     and constant expressions in general."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expr-integer-type-3p ((expr exprp))
  :guard (expr-unambp expr)
  :returns (3vl 3p)
  :short "Three-valued check of whether an expression has integer type."
  :long
  (xdoc::topstring-p
   "This typically checks the type returned by @(tsee expr-type).
    However, it handles @('sizeof') and @('alignof') separately
    because their implementation-specific result type
    is currently represented by the unknown arithmetic type,
    since we do not have a category for unknown integer types.")
  (b* ((definitely-integer
        (expr-case expr
                   :unary (and (unop-case expr.op '(:sizeof :alignof)) t)
                   :sizeof t
                   :alignof t
                   :otherwise nil))
       ((when definitely-integer)
        t)
       ((unless (expr-annop expr))
        :unknown)
       (type (expr-type expr)))
    (cond ((type-integerp type) t)
          ((type-some-unknownp type) :unknown)
          (t nil))))

(define expr-arithmetic-type-3p ((expr exprp))
  :guard (expr-unambp expr)
  :returns (3vl 3p)
  :short "Three-valued check of whether an expression has arithmetic type."
  (if (expr-annop expr)
      (b* ((type (expr-type expr)))
        (cond ((type-arithmeticp type) t)
              ((type-case type '(:unknown :unknown-builtin :unknown-scalar))
               :unknown)
              (t nil)))
    :unknown))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tyname-integer-type-3p ((tyname tynamep))
  :returns (3vl 3p)
  :short "Three-valued check of whether a type name denotes an integer type."
  (if (tyname-annop tyname)
      (b* ((type (type-vinfo->type (tyname->info tyname))))
        (cond ((type-integerp type) t)
              ((type-some-unknownp type) :unknown)
              (t nil)))
    :unknown))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-sizeof-result-const-3p ((type typep))
  :returns (3vl 3p)
  :short "Three-valued check of whether @('sizeof') of a type
          produces an integer constant."
  :long
  (xdoc::topstring-p
   "For a valid @('sizeof') operand, the standard distinguishes
    variable length array types from all other types:
    a VLA operand is evaluated, while any other operand is not evaluated
    and the result is an integer constant
    [C17:6.5.3.4/2] [C23:6.5.4.4/2].
    Thus @('sizeof') applied to a VLA is not an ICE under
    the standard ICE rules: its result is not the integer constant
    admitted for a @('sizeof') operand of an ICE
    [C17:6.6/6] [C23:6.6/8].
    For an array type with @(':const-len') kind,
    VLA status is inherited from its element type,
    so we recursively check that type.
    An array with @(':nonconst-len') kind is known to be a VLA.
    The @(':unknown-complete') kind produces @(':unknown').
    The @(':incomplete') kind also produces @(':unknown'),
    although an incomplete type is not a valid @('sizeof') operand.
    The general unknown types may conceal an array as well.")
  (type-case
    type
    :array (type-array-kind-case
             type.kind
             :const-len (type-sizeof-result-const-3p type.of)
             :nonconst-len nil
             :otherwise :unknown)
    :unknown :unknown
    :unknown-builtin :unknown
    :otherwise t)
  :measure (type-count type))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expr-sizeof-result-const-3p ((expr exprp))
  :guard (expr-unambp expr)
  :returns (3vl 3p)
  :short "Three-valued check of whether @('sizeof') of an expression
          produces an integer constant."
  (if (expr-annop expr)
      (type-sizeof-result-const-3p (expr-type expr))
    :unknown))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tyname-sizeof-result-const-3p ((tyname tynamep))
  :returns (3vl 3p)
  :short "Three-valued check of whether @('sizeof') of a type name
          produces an integer constant."
  (if (tyname-annop tyname)
      (type-sizeof-result-const-3p
       (type-vinfo->type (tyname->info tyname)))
    :unknown))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define typequal/attribspec-list-expr-free-p
  ((qualspecs typequal/attribspec-listp))
  :returns (yes/no booleanp)
  :short "Check that a list of type qualifiers and attribute specifiers
          contains no attribute specifiers."
  (or (endp qualspecs)
      (and (typequal/attribspec-case (car qualspecs) :type)
           (typequal/attribspec-list-expr-free-p (cdr qualspecs)))))

(define typequal/attribspec-list-list-expr-free-p
  ((qualspecss typequal/attribspec-list-listp))
  :returns (yes/no booleanp)
  :short "Lift @(tsee typequal/attribspec-list-expr-free-p) to lists."
  (or (endp qualspecss)
      (and (typequal/attribspec-list-expr-free-p (car qualspecss))
           (typequal/attribspec-list-list-expr-free-p (cdr qualspecss)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines expr-ice-core-3p
  (define expr-ice-core-3p
    ((expr exprp)
     (evaluatedp 3p)
     (cast-restrictionsp booleanp)
     (dialect c::dialectp))
    :guard (expr-unambp expr)
    :returns (3vl 3p)
    :short "Recursive core of the integer constant expression (ICE) check."
    :long
    (xdoc::topstring
     (xdoc::p
      "This is the recursive component of @(tsee expr-ice-p).
       It checks the ICE operand and cast restrictions [C17:6.6/6] [C23:6.6/8]
       together with the applicable general constant-expression constraints
       [C17:6.6/4] [C23:6.6/4].")
     (xdoc::p
      "The @('evaluatedp') argument is needed because assignment, increment,
       decrement, function-call, and comma operators
       are prohibited only in evaluated subexpressions.
       Its three values account conservatively for short-circuit,
       conditional, and generic-selection evaluation.
       ICE operand and cast restrictions are still checked
       in unevaluated subexpressions,
       consistently with the closed response to WG14 C11/C17 Issue 0489.")
     (xdoc::p
      "The @('cast-restrictionsp') argument is normally @('t').
       It is @('nil') while recursively checking
       the operand of @('sizeof') or @('alignof'),
       because casts within those operands
       are excepted from the ICE cast restriction [C17:6.6/6] [C23:6.6/8].
       C23 likewise excepts casts within a @('typeof') operand.
       ICE operand restrictions remain in force in each case.")
     (xdoc::p
      "C17 permits implementations to accept additional forms
       of constant expressions [C17:6.6/10],
       but this does not change the definition of an ICE [C17:6.6/6],
       as clarified in WG14's discussion of C99 Issue 0312.
       C23 explicitly makes it implementation-defined
       whether an additional form of constant expression is an ICE
       [C23:6.6/14].
       Thus a C17 ICE-specific violation produces @('nil'),
       while the corresponding unresolved C23 extension case
       normally produces @(':unknown').")
     (xdoc::p
      "The principal cases are as follows.")
     (xdoc::ul
      (xdoc::li
       "In C17 an @(':ident') expression is not an allowed ICE operand
        [C17:6.6/6].
        In C23 an identifier may instead be a named constant [C23:6.6/7-8].
        An identifier established to name a constant of integer type
        is an allowed ICE operand; an ordinary object or function is not.
        Because we don't track @('constexpr') information,
        an identifier has @(':unknown') ICE status under C23.")
      (xdoc::li
       "Integer constants, enumeration constants, and character constants
        are directly listed ICE operands [C17:6.6/6] [C23:6.6/8].
        A floating constant is permitted only
        as the immediate operand of a permitted cast.
        A string literal is not a standard ICE operand.
        Thus a floating constant outside the permitted cast context,
        or a string literal, produces @('nil') in C17;
        a possible implementation-defined extended ICE
        produces @(':unknown') in C23.")
      (xdoc::li
       "The controlling expression of a generic selection is not evaluated,
        and neither are the unselected branches [C17:6.5.1.1/3] [C23:6.5.2.1/3].
        If the selected association is not known,
        each association may be the selected one:
        Since we do not currently resolve generic associations,
        the evaluation status of each branch is @(':unknown')
        (unless we are already in an unevaluated context,
         in which case it is @('nil')).
        The controlling expression is checked under an unevaluated context,
        and each association under its possible evaluation context.")
      (xdoc::li
       "A C17 compound literal is not an allowed ICE operand [C17:6.6/6].
        C23 permits named constants and compound literal constants
        of integer type as ICE operands [C23:6.6/6-8].
        It also permits such constants of arithmetic type
        as immediate operands of casts.
        Recursive @('.') member access into a named or compound literal
        structure or union constant produces another such constant
        [C23:6.6/6-7,13,15].
        For a union constant,
        the accessed member must be the initialized member [C23:6.6/16].
        Because we don't track @('constexpr') information,
        a compound literal has @(':unknown') ICE status under C23.")
      (xdoc::li
       "The postfix operators are governed by the ICE operand restrictions.
        In C23, recursive @('.') access has the named-
        and compound-literal-constant behavior described above.")
      (xdoc::li
       "Parentheses and unary @('+'), @('~'), and @('!') recurse directly.
        Unary @('-') may overflow for a signed operand,
        so an evaluated occurrence produces @(':unknown').")
      (xdoc::li
       "An evaluated assignment, increment, decrement, function call,
        or comma operator produces @('nil') [C17:6.6/3] [C23:6.6/3].
        In an unevaluated subexpression the operator itself is permitted,
        but its component expressions must still be checked
        for the applicable ICE operand and cast restrictions.
        The GCC/Clang @('__builtin_va_arg') form
        is not one of the operators listed in those paragraphs,
        but is expected to behave similarly.
        An evaluated occurrence cannot yield a translation-time constant
        and modifies its list, so it produces @('nil').
        An unevaluated occurrence is checked conservatively
        as an extension form.")
      (xdoc::li
       "A @('sizeof') expression is an allowed ICE operand
        exactly when its result is an integer constant,
        which excludes an operand of variable length array type
        [C17:6.5.3.4/2] [C17:6.6/6] [C23:6.5.4.4/2] [C23:6.6/8].
        The type-directed result check produces @('t')
        for a known non-array operand and recursively classifies array kinds.
        A @(':nonconst-len') array produces @('nil'),
        a @(':const-len') array inherits the classification of its element,
        and the other array kinds produce @(':unknown').
        Other insufficient type information also produces @(':unknown').
        An expression operand is checked recursively,
        as required for unevaluated ICE operands
        by the closed response to WG14 C11/C17 Issue 0489.
        When the result is known to be constant, the operand is unevaluated;
        otherwise its evaluation status is unknown
        unless the containing @('sizeof') is itself unevaluated.")
      (xdoc::li
       "Within a type-name operand or cast target, the checker follows
        nested type names and array bounds.
        The evaluation status of an array bound is conservatively unknown
        when reached through @('sizeof'),
        unless that @('sizeof') is itself unevaluated:
        when changing the bound would not affect the @('sizeof') result,
        the standard leaves its evaluation unspecified
        [C17:6.7.6.2/5] [C23:6.7.7.3/5].
        An expression-bearing type-name construct not yet traversed,
        such as a type definition, parameter declaration, attribute,
        or alignment specifier, produces @(':unknown').
        The operand of a @('typeof') specifier is recursively checked.
        It is evaluated exactly when its type is variably modified
        [C23:6.7.3.6/4].
        Since this checker cannot currently establish that property,
        the operand's evaluation status is unknown
        unless its context is unevaluated.
        A @('typeof') form remains @(':unknown')
        even when its operand passes the recursive check.")
      (xdoc::li
       "A valid standard alignment expression has an integer-constant result,
        and its operand is not evaluated
        [C17:6.5.3.4/3] [C17:6.6/6] [C23:6.5.4.4/3] [C23:6.6/8].
        The checker nonetheless follows expressions within the operand
        type name under an unevaluated context,
        consistently with the closed response to WG14 C11/C17 Issue 0489.
        Cast restrictions are disabled
        during @('sizeof') and @('alignof') operand recursion,
        but ICE operand restrictions remain in force.
        The GCC/Clang expression-operand variant is checked in the same way,
        but its status as an extended ICE remains @(':unknown').")
      (xdoc::li
       "Outside the operand of @('sizeof') or @('alignof'),
        C17 permits a cast in an ICE only when it converts
        an arithmetic type to an integer type [C17:6.6/6].
        C23 has the same rule, also excepting casts within
        the operand of a @('typeof') operator [C23:6.6/8].
        The cast operand is checked recursively,
        with the special allowance for an immediate floating constant
        and, in C23, an immediate named or compound literal constant
        of arithmetic type.
        The target type name is checked recursively,
        because it may contain array bounds or other expressions.
        They have the cast expression's evaluation status;
        C23 explicitly specifies that size expressions and @('typeof')
        operators in the target type name are evaluated whenever
        the cast expression is evaluated [C23:6.5.5/5].
        If an evaluated conversion's representability cannot be established,
        the result is @(':unknown');
        an unevaluated conversion is still checked for the cast restriction
        unless it occurs within a specifically excepted operand.")
      (xdoc::li
       "The non-assignment binary operators recursively check both operands.
        The right operand of @('&&') or @('||') has unknown evaluation status
        unless the whole operator is itself unevaluated
        [C17:6.5.13/4] [C17:6.5.14/4] [C23:6.5.14/4] [C23:6.5.15/4].
        Bitwise, comparison, and logical results are representable once
        their operands are established.
        Arithmetic and shift results remain @(':unknown') when evaluated
        because overflow, division by zero, or an invalid shift
        may depend on values not available here.")
      (xdoc::li
       "A standard conditional expression recursively checks its test
        and both possible result expressions.
        Each result expression has unknown evaluation status
        unless the whole conditional expression
        is unevaluated [C17:6.5.15/4] [C23:6.5.16/5];
        the checker does not evaluate the test.
        The omitted-middle GCC form remains @(':unknown').")
      (xdoc::li
       "A statement expression, label address,
        @('__builtin_types_compatible_p'), @('__builtin_offsetof'),
        expression-operand @('__alignof__'), @('__real__'), @('__imag__'),
        or other extension form produces @(':unknown')
        when its ICE behavior is not established.
        A transparent @('__extension__') wrapper recurses on its operand.")))
    (b* (((c::dialect dialect) dialect)
         (extended-operand
          (c::standard-case dialect.std
            :c17 nil
            :c23 :unknown)))
      (expr-case
       expr
       :ident
       extended-operand
       :const
       (if (const-case expr.const '(:int :enum :char))
           t
         extended-operand)
       :string
       extended-operand
       :paren
       (expr-ice-core-3p
        expr.inner evaluatedp cast-restrictionsp dialect)
       :gensel
       (b* ((assoc-evaluatedp (3and evaluatedp :unknown)))
         (3and
           (expr-ice-core-3p
            expr.control nil cast-restrictionsp dialect)
           (genassoc-list-ice-core-3p
            expr.assocs assoc-evaluatedp cast-restrictionsp dialect)
           :unknown))
       :arrsub
       (3and
        (expr-ice-core-3p
         expr.arg1 evaluatedp cast-restrictionsp dialect)
        (expr-ice-core-3p
         expr.arg2 evaluatedp cast-restrictionsp dialect)
        extended-operand)
       :funcall
       (3and
        (3not evaluatedp)
        (expr-ice-core-3p
         expr.fun evaluatedp cast-restrictionsp dialect)
        (expr-list-ice-core-3p
         expr.args evaluatedp cast-restrictionsp dialect))
       :member
       (3and
        (expr-ice-core-3p
         expr.arg evaluatedp cast-restrictionsp dialect)
        extended-operand)
       :memberp
       (3and
        (expr-ice-core-3p
         expr.arg evaluatedp cast-restrictionsp dialect)
        extended-operand)
       :complit
       extended-operand
       :unary
       (unop-case
         expr.op
         :sizeof
         (b* ((result-constp
               (expr-sizeof-result-const-3p expr.arg))
              (arg-evaluatedp
               (3and evaluatedp (3not result-constp))))
           (3and
            result-constp
            (expr-ice-core-3p
             expr.arg arg-evaluatedp nil dialect)))
         :alignof
         (3and
          (expr-ice-core-3p expr.arg nil nil dialect)
          :unknown)
         :otherwise
         (b* ((arg (expr-ice-core-3p
                    expr.arg evaluatedp cast-restrictionsp dialect))
              (operator
               (cond
                ((unop-case expr.op '(:plus :bitnot :lognot))
                 t)
                ((unop-case expr.op '(:address :indir))
                 extended-operand)
                ((unop-case
                   expr.op
                   '(:preinc :predec :postinc :postdec))
                 (3not evaluatedp))
                ((unop-case expr.op :minus)
                 (if evaluatedp :unknown t))
                ((unop-case expr.op '(:real :imag))
                 :unknown)
                (t
                 (prog2$ (impossible) :unknown)))))
           (3and arg operator)))
       :label-addr
       :unknown
       :sizeof
       (b* ((result-constp
             (tyname-sizeof-result-const-3p expr.type))
            (type-evaluatedp
             (3and evaluatedp :unknown)))
         (3and
          result-constp
          (tyname-ice-core-3p
           expr.type type-evaluatedp nil dialect)))
       :sizeof-ambig
       (prog2$ (impossible) :unknown)
       :alignof
       (3and
        (tyname-ice-core-3p expr.type nil nil dialect)
        (keyword-uscores-case
         expr.uscores
         :none t
         :start :unknown
         :both :unknown))
       :alignof-ambig
       (prog2$ (impossible) :unknown)
       :cast
       (b* ((operand
             (cond
              ((and (expr-case expr.arg :const)
                    (const-case (expr-const->const expr.arg) :float))
               t)
              ((and (c::standard-case dialect.std :c17 nil :c23 t)
                    (expr-case expr.arg '(:ident :member :complit)))
               :unknown)
              (t
               (expr-ice-core-3p
                expr.arg evaluatedp cast-restrictionsp dialect))))
            (type-name
             (tyname-ice-core-3p
              expr.type evaluatedp cast-restrictionsp dialect))
            (types
             (if cast-restrictionsp
                 (3and
                  (expr-arithmetic-type-3p expr.arg)
                  (tyname-integer-type-3p expr.type))
               t))
            (representable
             (if (eq evaluatedp nil)
                 t
               :unknown)))
         (3and operand type-name types representable))
       :binary
       (if (binop-case
            expr.op
            '(:asg :asg-mul :asg-div :asg-rem :asg-add :asg-sub
              :asg-shl :asg-shr :asg-and :asg-xor :asg-ior))
           (3and
            (3not evaluatedp)
            (expr-ice-core-3p
             expr.arg1 evaluatedp cast-restrictionsp dialect)
            (expr-ice-core-3p
             expr.arg2 evaluatedp cast-restrictionsp dialect))
         (b* ((arg1
               (expr-ice-core-3p
                expr.arg1 evaluatedp cast-restrictionsp dialect))
              (arg2-evaluatedp
               (if (binop-case expr.op '(:logand :logor))
                   (3and evaluatedp :unknown)
                 evaluatedp))
              (arg2
               (expr-ice-core-3p
                expr.arg2
                arg2-evaluatedp
                cast-restrictionsp
                dialect))
              (args (3and arg1 arg2)))
           (cond
            ((binop-case
              expr.op
              '(:lt :gt :le :ge :eq :ne
                :bitand :bitxor :bitior :logand :logor))
             args)
            ((binop-case
              expr.op
              '(:mul :div :rem :add :sub :shl :shr))
             (if evaluatedp
                 (3and args :unknown)
               args))
            (t
             (3and args :unknown)))))
       :cond
       (b* ((test
             (expr-ice-core-3p
              expr.test evaluatedp cast-restrictionsp dialect))
            (branch-evaluatedp
             (3and evaluatedp :unknown))
            (then
             (expr-option-case
              expr.then
              :some
              (expr-ice-core-3p
               expr.then.val
               branch-evaluatedp
               cast-restrictionsp
               dialect)
              :none
              :unknown))
            (else
             (expr-ice-core-3p
              expr.else
              branch-evaluatedp
              cast-restrictionsp
              dialect)))
         (3and test then else))
       :comma
       (3and
        (3not evaluatedp)
        (expr-ice-core-3p
         expr.first evaluatedp cast-restrictionsp dialect)
        (expr-ice-core-3p
         expr.next evaluatedp cast-restrictionsp dialect))
       :cast/call-ambig
       (prog2$ (impossible) :unknown)
       :cast/mul-ambig
       (prog2$ (impossible) :unknown)
       :cast/add-ambig
       (prog2$ (impossible) :unknown)
       :cast/sub-ambig
       (prog2$ (impossible) :unknown)
       :cast/and-ambig
       (prog2$ (impossible) :unknown)
       :cast/logand-ambig
       (prog2$ (impossible) :unknown)
       :stmt
       :unknown
       :tycompat
       :unknown
       :offsetof
       :unknown
       :va-arg
       (3and
        (3not evaluatedp)
        (expr-ice-core-3p
         expr.list evaluatedp cast-restrictionsp dialect)
        :unknown)
       :extension
       (expr-ice-core-3p
        expr.expr evaluatedp cast-restrictionsp dialect)))
    :measure (expr-count expr))

  (define tyname-ice-core-3p
    ((tyname tynamep)
     (evaluatedp 3p)
     (cast-restrictionsp booleanp)
     (dialect c::dialectp))
    :guard (tyname-unambp tyname)
    :returns (3vl 3p)
    :short "Apply the recursive ICE check within a type name."
    (b* (((tyname tyname) tyname)
         (specquals
          (spec/qual-list-ice-core-3p
           tyname.specquals evaluatedp cast-restrictionsp dialect))
         (declor
          (absdeclor-option-case
           tyname.declor?
           :none t
           :some
           (absdeclor-ice-core-3p
            tyname.declor?.val
            evaluatedp
            cast-restrictionsp
            dialect))))
      (3and specquals declor))
    :measure (tyname-count tyname))

  (define spec/qual-list-ice-core-3p
    ((specquals spec/qual-listp)
     (evaluatedp 3p)
     (cast-restrictionsp booleanp)
     (dialect c::dialectp))
    :guard (spec/qual-list-unambp specquals)
    :returns (3vl 3p)
    :short "Apply the recursive ICE check within
            a specifier-qualifier list."
    (or (endp specquals)
        (3and
         (spec/qual-ice-core-3p
          (car specquals) evaluatedp cast-restrictionsp dialect)
         (spec/qual-list-ice-core-3p
          (cdr specquals) evaluatedp cast-restrictionsp dialect)))
    :measure (spec/qual-list-count specquals))

  (define spec/qual-ice-core-3p
    ((specqual spec/qual-p)
     (evaluatedp 3p)
     (cast-restrictionsp booleanp)
     (dialect c::dialectp))
    :guard (spec/qual-unambp specqual)
    :returns (3vl 3p)
    :short "Apply the recursive ICE check within
            a specifier or qualifier."
    (spec/qual-case
     specqual
     :typespec
     (type-spec-ice-core-3p
      specqual.spec evaluatedp cast-restrictionsp dialect)
     :typequal t
     :align :unknown
     :attrib :unknown)
    :measure (spec/qual-count specqual))

  (define type-spec-ice-core-3p
    ((typespec type-specp)
     (evaluatedp 3p)
     (cast-restrictionsp booleanp)
     (dialect c::dialectp))
    :guard (type-spec-unambp typespec)
    :returns (3vl 3p)
    :short "Apply the recursive ICE check within a type specifier."
    (type-spec-case
     typespec
     :atomic
     (tyname-ice-core-3p
      typespec.type evaluatedp cast-restrictionsp dialect)
     :struct
     (if (and (endp (struni-spec->attribs typespec.spec))
              (endp (struni-spec->members typespec.spec)))
         t
       :unknown)
     :union
     (if (and (endp (struni-spec->attribs typespec.spec))
              (endp (struni-spec->members typespec.spec)))
         t
       :unknown)
     :enum
     (if (endp (enum-spec->enumers typespec.spec))
         t
       :unknown)
     :struct-empty :unknown
     :typeof-expr
     (3and
      (expr-ice-core-3p
       typespec.expr (3and evaluatedp :unknown) nil dialect)
      :unknown)
     :typeof-type
     (3and
      (tyname-ice-core-3p
       typespec.type (3and evaluatedp :unknown) nil dialect)
      :unknown)
     :typeof-ambig (prog2$ (impossible) :unknown)
     :auto-type :unknown
     :otherwise t)
    :measure (type-spec-count typespec))

  (define absdeclor-ice-core-3p
    ((declor absdeclorp)
     (evaluatedp 3p)
     (cast-restrictionsp booleanp)
     (dialect c::dialectp))
    :guard (absdeclor-unambp declor)
    :returns (3vl 3p)
    :short "Apply the recursive ICE check within an abstract declarator."
    (b* (((absdeclor declor) declor)
         (pointers
          (if (typequal/attribspec-list-list-expr-free-p declor.pointers)
              t
            :unknown))
         (direct
          (dirabsdeclor-option-case
           declor.direct?
           :none t
           :some
           (dirabsdeclor-ice-core-3p
            declor.direct?.val
            evaluatedp
            cast-restrictionsp
            dialect))))
      (3and pointers direct))
    :measure (absdeclor-count declor))

  (define dirabsdeclor-ice-core-3p
    ((declor dirabsdeclorp)
     (evaluatedp 3p)
     (cast-restrictionsp booleanp)
     (dialect c::dialectp))
    :guard (dirabsdeclor-unambp declor)
    :returns (3vl 3p)
    :short "Apply the recursive ICE check within
            a direct abstract declarator."
    (dirabsdeclor-case
     declor
     :dummy-base
     (prog2$ (impossible) :unknown)
     :paren
     (absdeclor-ice-core-3p
      declor.inner evaluatedp cast-restrictionsp dialect)
     :array
     (3and
      (dirabsdeclor-option-case
       declor.declor?
       :none t
       :some
       (dirabsdeclor-ice-core-3p
        declor.declor?.val evaluatedp cast-restrictionsp dialect))
      (if (typequal/attribspec-list-expr-free-p declor.qualspecs)
          t
        :unknown)
      (expr-option-case
       declor.size?
       :none t
       :some
       (expr-ice-core-3p
        declor.size?.val evaluatedp cast-restrictionsp dialect)))
     :array-static1
     (3and
      (dirabsdeclor-option-case
       declor.declor?
       :none t
       :some
       (dirabsdeclor-ice-core-3p
        declor.declor?.val evaluatedp cast-restrictionsp dialect))
      (if (typequal/attribspec-list-expr-free-p declor.qualspecs)
          t
        :unknown)
      (expr-ice-core-3p
       declor.size evaluatedp cast-restrictionsp dialect))
     :array-static2
     (3and
      (dirabsdeclor-option-case
       declor.declor?
       :none t
       :some
       (dirabsdeclor-ice-core-3p
        declor.declor?.val evaluatedp cast-restrictionsp dialect))
      (if (typequal/attribspec-list-expr-free-p declor.qualspecs)
          t
        :unknown)
      (expr-ice-core-3p
       declor.size evaluatedp cast-restrictionsp dialect))
     :array-star
     (dirabsdeclor-option-case
      declor.declor?
      :none t
      :some
      (dirabsdeclor-ice-core-3p
       declor.declor?.val evaluatedp cast-restrictionsp dialect))
     :function
     (3and
      (dirabsdeclor-option-case
       declor.declor?
       :none t
       :some
       (dirabsdeclor-ice-core-3p
        declor.declor?.val evaluatedp cast-restrictionsp dialect))
      (if (endp declor.params)
          t
        :unknown)))
    :measure (dirabsdeclor-count declor))

  (define expr-list-ice-core-3p
    ((exprs expr-listp)
     (evaluatedp 3p)
     (cast-restrictionsp booleanp)
     (dialect c::dialectp))
    :guard (expr-list-unambp exprs)
    :returns (3vl 3p)
    :short "Apply the recursive ICE check to a list of expressions."
    (or (endp exprs)
        (3and
         (expr-ice-core-3p
          (car exprs) evaluatedp cast-restrictionsp dialect)
         (expr-list-ice-core-3p
          (cdr exprs) evaluatedp cast-restrictionsp dialect)))
    :measure (expr-list-count exprs))

  (define genassoc-list-ice-core-3p
    ((assocs genassoc-listp)
     (evaluatedp 3p)
     (cast-restrictionsp booleanp)
     (dialect c::dialectp))
    :guard (genassoc-list-unambp assocs)
    :returns (3vl 3p)
    :short "Apply the recursive ICE check to generic associations."
    (b* (((when (endp assocs)) t)
         (assoc (car assocs))
         (first
          (genassoc-case
           assoc
           :type
           (expr-ice-core-3p
            assoc.expr evaluatedp cast-restrictionsp dialect)
           :default
           (expr-ice-core-3p
            assoc.expr evaluatedp cast-restrictionsp dialect))))
      (3and
       first
       (genassoc-list-ice-core-3p
        (cdr assocs) evaluatedp cast-restrictionsp dialect)))
    :measure (genassoc-list-count assocs))

  :ruler-extenders :all
  :verify-guards :after-returns
  ///

  (fty::deffixequiv-mutual expr-ice-core-3p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expr-ice-p ((expr exprp) (evaluatedp 3p) (dialect c::dialectp))
  :guard (expr-unambp expr)
  :returns (3vl 3p)
  :short "Check whether an expression is an integer constant expression (ICE)."
  :long
  (xdoc::topstring
   (xdoc::p
    "Integer constant expressions are defined in [C17:6.6/6] and [C23:6.6/8].
     This predicate directly checks the required integer result type,
     the ICE-specific operand and cast restrictions,
     and the applicable general constant-expression constraints.")
   (xdoc::p
    "C17 permits additional forms of constant expressions [C17:6.6/10],
     but this does not change the ICE definition [C17:6.6/6],
     as clarified in WG14's discussion of C99 Issue 0312.
     C23 explicitly makes it implementation-defined
     whether an additional constant-expression form is an ICE [C23:6.6/14].
     We therefore use @(':unknown') for unresolved C23 extension cases,
     while returning @('nil') for an established violation
     of a C17 ICE requirement.")
   (xdoc::p
    "We assume that @('expr') is grammatically a @('constant-expression')
     [C17:6.6/1] [C23:6.6/1].
     Missing or insufficient validation annotations produce @(':unknown')
     when the result type, a variable length array type,
     or another required fact cannot be established.")
   (xdoc::p
    "The recursive checks are performed by @(tsee expr-ice-core-3p)."))
  (3and
   (expr-integer-type-3p expr)
   (expr-ice-core-3p expr evaluatedp t dialect)))
