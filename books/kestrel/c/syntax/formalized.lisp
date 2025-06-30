; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "unambiguity")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ formalized-subset
  :parents (syntax-for-tools)
  :short "Subset of the abstract syntax that has a formal semantics."
  :long
  (xdoc::topstring
   (xdoc::p
    "The "
    (xdoc::seetopic "c$::syntax-for-tools" "C syntax for tools")
    " is designed to cover all of C (currently after preprocessing),
     but the "
    (xdoc::seetopic "c::language" "formal language definition")
    " only covers a subset of C.
     More precisely:
     the abstract syntax of the formal language definition
     is a subset of the abstract syntax for tools;
     the static semantics of C is defined for
     a subset of the latter abstract syntax;
     and the dynamic semantics of C is defined for
     a subset of the subset for which the static semantics is defined.
     Note how these subsets are linearly ordered.")
   (xdoc::p
    "It is useful to characterize which subset of the abstract syntax for tools
     corresponds to the subset of C that has both static and dynamic semantics.
     This is the subset for which we can state and prove formal properties,
     e.g. of a "
    (xdoc::seetopic "c2c::transformation-tools" "C-to-C transformation")
    ". Here we provide such a characterization,
     in the form of predicates over the abstract syntax fixtypes.")
   (xdoc::p
    "Note that the subset of the abstract syntax for tools
     that corresponds to the abstract syntax of the language definition
     is implicitly defined by "
    (xdoc::seetopic "mapping-to-language-definition"
                    "mapping between the two abstract syntaxes")
    ": it is the subset for which the mapping does not return an error.
     We could also define separate predicates
     over the abstract syntax for tools
     that identify the subset with static semantics,
     which is between the one defined by
     the syntactic language definition mapping
     and the one that has dynamic semantics.
     However, for now we do not do that,
     because that intermediate subset is not particularly interesting:
     we are generally more interested in proofs about the dynamic semnantics.")
   (xdoc::p
    "Exactly characterizing the subset with formal dynamic semantics
     is not that straightforward, due to the complexity of the constructs.
     An exact characterization may also need some type information,
     resulting from a static semantic analysis of the code.
     The current characterization is a good starting point,
     but it needs to be improved."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ident-formalp ((ident identp))
  :returns (yes/no booleanp)
  :short "Check if an identifier has formal dynamic semantics."
  :long
  (xdoc::topstring
   (xdoc::p
    "Identifiers are supported, via @(tsee c::exec-ident),
     when they denote variables.
     Based on the identifier alone,
     we cannot determine whether it denotes a variable,
     so we must accept it here,
     delegating the test to whether it denotes a variable elsewhere.")
   (xdoc::p
    "However, we impose a restriction here,
     to ensure that the C subset defined by these predicates
     is a subset of the one defined by the syntactic language mapping,
     whose @(tsee ldm-ident) function requires
     the identifier to be an ACL2 string.
     So here we require the identifier to be an ACL2 string as well.")
   (xdoc::p
    "This may turn out to be too restrictive,
     e.g. if we want to support the verification of transformations
     that take advantage of the flexibility mentioned in @(tsee ident).
     So we may revisit this in the future."))
  (stringp (ident->unwrap ident))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define const-formalp ((const constp))
  :returns (yes/no booleanp)
  :short "Check if a constant has formal dynamic semantics."
  :long
  (xdoc::topstring
   (xdoc::p
    "Based on @(tsee c::eval-const) and @(tsee c::exec-const),
     only integer constants pass the test."))
  (const-case const :int)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-integer-formalp ((tyspecs type-spec-listp))
  :guard (type-spec-list-unambp tyspecs)
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has formal dynamic semantics,
          when used to denote an integer type."
  :long
  (xdoc::topstring
   (xdoc::p
    "Cast expressions are supported only if
     the destination type name denotes an integer type
     that is not the plain @('char') type:
     see @(tsee c::eval-cast).
     In the abstract syntax of the formal language definition,
     type names, which contain type specifier sequences,
     are only used in cast expressions;
     so we use this ACL2 function to check whether
     the type specifier sequence of a type name is supported
     (see @(tsee tyname-formalp))."))
  (b* ((tyspecs (type-spec-list-fix tyspecs)))
    (or (equal tyspecs (list (type-spec-signed (keyword-uscores-none))
                             (type-spec-char)))
        (equal tyspecs (list (type-spec-unsigned)
                             (type-spec-char)))
        (equal tyspecs (list (type-spec-short)))
        (equal tyspecs (list (type-spec-signed (keyword-uscores-none))
                             (type-spec-short)))
        (equal tyspecs (list (type-spec-short)
                             (type-spec-int)))
        (equal tyspecs (list (type-spec-signed (keyword-uscores-none))
                             (type-spec-short)
                             (type-spec-int)))
        (equal tyspecs (list (type-spec-unsigned)
                             (type-spec-short)))
        (equal tyspecs (list (type-spec-unsigned)
                             (type-spec-short)
                             (type-spec-int)))
        (equal tyspecs (list (type-spec-int)))
        (equal tyspecs (list (type-spec-signed (keyword-uscores-none))))
        (equal tyspecs (list (type-spec-signed (keyword-uscores-none))
                             (type-spec-int)))
        (equal tyspecs (list (type-spec-unsigned)))
        (equal tyspecs (list (type-spec-unsigned)
                             (type-spec-int)))
        (equal tyspecs (list (type-spec-long)))
        (equal tyspecs (list (type-spec-long)
                             (type-spec-int)))
        (equal tyspecs (list (type-spec-signed (keyword-uscores-none))
                             (type-spec-long)))
        (equal tyspecs (list (type-spec-signed (keyword-uscores-none))
                             (type-spec-long)
                             (type-spec-int)))
        (equal tyspecs (list (type-spec-unsigned)
                             (type-spec-long)))
        (equal tyspecs (list (type-spec-unsigned)
                             (type-spec-long)
                             (type-spec-int)))
        (equal tyspecs (list (type-spec-long)
                             (type-spec-long)))
        (equal tyspecs (list (type-spec-long)
                             (type-spec-long)
                             (type-spec-int)))
        (equal tyspecs (list (type-spec-signed (keyword-uscores-none))
                             (type-spec-long)
                             (type-spec-long)))
        (equal tyspecs (list (type-spec-signed (keyword-uscores-none))
                             (type-spec-long)
                             (type-spec-long)
                             (type-spec-int)))
        (equal tyspecs (list (type-spec-unsigned)
                             (type-spec-long)
                             (type-spec-long)))
        (equal tyspecs (list (type-spec-unsigned)
                             (type-spec-long)
                             (type-spec-long)
                             (type-spec-int)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-formalp ((tyspecs type-spec-listp))
  :guard (type-spec-list-unambp tyspecs)
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has formal dynamic semantics."
  :long
  (xdoc::topstring
   (xdoc::p
    "In the abstract syntax of the formal language definition,
     type specifier sequences may occur in
     type names,
     structure declarations,
     parameter declarations,
     function declarations,
     object declarations,
     and function definitions.
     For type names, as discussed in @(tsee type-spec-list-integer-formalp),
     there is only support for type specifier sequences
     that denote integer types except plain @('char').
     For the other uses, we also allow
     type specifier sequences that denote structure types,
     of the form supported by @(tsee ldm-type-spec-list)."))
  (or (type-spec-list-integer-formalp tyspecs)
      (and (consp tyspecs)
           (endp (cdr tyspecs))
           (type-spec-case (car tyspecs) :struct)
           (b* ((struni-spec (type-spec-struct->spec (car tyspecs))))
             (and (check-struni-spec-no-members struni-spec)
                  (ident-formalp (struni-spec->name struni-spec))))))
  :guard-hints (("Goal" :in-theory (enable check-struni-spec-no-members)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stor-spec-list-formalp ((storspecs stor-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of storage class specifiers
          has formal dynamic semantics."
  :long
  (xdoc::topstring
   (xdoc::p
    "We only allow a single @('extern'),
     in file-scope object declarations."))
  (b* ((storspecs (stor-spec-list-fix storspecs)))
    (or (equal storspecs nil)
        (equal storspecs (list (stor-spec-extern)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tyname-formalp ((tyname tynamep))
  :guard (tyname-unambp tyname)
  :returns (yes/no booleanp)
  :short "Check if a type name has formal dynamic semantics."
  :long
  (xdoc::topstring
   (xdoc::p
    "In the abstract syntax of the formal language definition,
     type names are only used in cast expressions,
     which are required by @(tsee c::eval-cast) to denote integer types
     (except the plain @('char') type) in order to be supported.
     Thus we need to ensure that the list of type specifiers and qualifiers
     only contains supported type specifier sequences
     corresponding to those types,
     and that there is no abstract declarator.
     We must also ensure that there are no type qualifiers,
     which are not supported in the formal semantics."))
  (b* (((tyname tyname) tyname)
       ((mv okp tyspecs) (check-spec/qual-list-all-typespec tyname.specquals)))
    (and okp
         (type-spec-list-integer-formalp tyspecs)
         (not tyname.declor?)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expr-pure-formalp ((expr exprp))
  :guard (expr-unambp expr)
  :returns (yes/no booleanp)
  :short "Check if an expression has formal dynamic semantics,
          as a pure expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "Our formal semantics of C characterizes certain expressions as pure,
     and restricts certain expressions in the syntax to be pure.
     Thus, here we define a predicate that says whether an expression
     has formal semantics as a pure expression.
     Later we define other predicates for other kinds of expressions.")
   (xdoc::p
    "The expressions not supported by @(tsee ldm-expr)
     are not supported here either.
     The remaining expressions are supported or not
     according to @(tsee c::exec-expr-pure)
     and the specialized functions it calls (e.g. @(tsee c::exec-arrsub)).
     In order for an expression to be supported,
     it is necessary that its sub-expressions are supported.")
   (xdoc::p
    "The tests for identifiers and constants
     reduce to the ones defined in predicates defined earlier.")
   (xdoc::p
    "Parenthesized expressions lose the parentheses through @(tsee ldm-expr),
     so they are supported if and only if the unparenthesized versions are.")
   (xdoc::p
    "The check we perform here on cast expressions is
     an over-approximation of what we should check.
     It is not enough for the destination type to be integer;
     we should also check that the source value is an integer.
     But this cannot be done purely syntactically:
     we need type information, about the type of the argument expression.
     After we have a @(see validator),
     if the validator annotates the abstract syntax with type information,
     then we could make this check more precise."))
  (expr-case
   expr
   :ident (ident-formalp expr.ident)
   :const (const-formalp expr.const)
   :string nil
   :paren (expr-pure-formalp expr.inner)
   :gensel nil
   :arrsub (and (expr-pure-formalp expr.arg1)
                (expr-pure-formalp expr.arg2))
   :funcall nil
   :member (and (expr-pure-formalp expr.arg)
                (ident-formalp expr.name))
   :memberp (and (expr-pure-formalp expr.arg)
                 (ident-formalp expr.name))
   :complit nil
   :unary (unop-case
           expr.op
           :address (expr-pure-formalp expr.arg)
           :indir (expr-pure-formalp expr.arg)
           :plus (expr-pure-formalp expr.arg)
           :minus (expr-pure-formalp expr.arg)
           :bitnot (expr-pure-formalp expr.arg)
           :lognot (expr-pure-formalp expr.arg)
           :preinc nil
           :predec nil
           :postinc nil
           :postdec nil
           :sizeof nil)
   :sizeof nil
   :sizeof-ambig (impossible)
   :alignof nil
   :cast (and (tyname-formalp expr.type)
              (expr-pure-formalp expr.arg))
   :binary (and (member-eq (binop-kind expr.op)
                           '(:mul :div :rem :add :sub :shl :shr
                             :lt :gt :le :ge :eq :ne
                             :bitand :bitxor :bitior :logand :logor))
                (expr-pure-formalp expr.arg1)
                (expr-pure-formalp expr.arg2))
   :cond (and (expr-pure-formalp expr.test)
              (expr-option-case expr.then
                                :some (expr-pure-formalp expr.then.val)
                                :none nil)
              (expr-pure-formalp expr.else))
   :comma nil
   :cast/call-ambig (impossible)
   :cast/mul-ambig (impossible)
   :cast/add-ambig (impossible)
   :cast/sub-ambig (impossible)
   :cast/and-ambig (impossible)
   :stmt nil
   :tycompat nil
   :offsetof nil
   :va-arg nil
   :extension nil)
  :measure (expr-count expr)
  :hints (("Goal" :in-theory (enable o< o-finp)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expr-list-pure-formalp ((exprs expr-listp))
  :guard (expr-list-unambp exprs)
  :returns (yes/no booleanp)
  :short "Check if all the expressions in a list have formal dynamic semantics,
          as pure expressions."
  (or (endp exprs)
      (and (expr-pure-formalp (car exprs))
           (expr-list-pure-formalp (cdr exprs))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expr-call-formalp ((expr exprp))
  :guard (expr-unambp expr)
  :returns (yes/no booleanp)
  :short "Check if an expression has formal dynamic semantics,
          as a call expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the expressions supported by @(tsee c::exec-expr-call).
     The expression must be a function call,
     the function sub-expression must be an identifier,
     and the arguments must be supported pure expressions."))
  (and (expr-case expr :funcall)
       (expr-case (expr-funcall->fun expr) :ident)
       (ident-formalp (expr-ident->ident (expr-funcall->fun expr)))
       (expr-list-pure-formalp (expr-funcall->args expr)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define expr-asg-formalp ((expr exprp))
  :guard (expr-unambp expr)
  :returns (yes/no booleanp)
  :short "Check if an expression has formal dynamic semantics,
          as an assignment expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the expressions supported by @(tsee c::exec-expr-asg).
     The expression must be a simple assignment expression.
     The sub-expressions must have formal dynamic semantics.
     The left expression must be pure.
     The right expression must be pure
     unless the left expression is an identifier,
     in which case the right expression may be a function call."))
  (and (expr-case expr :binary)
       (binop-case (expr-binary->op expr) :asg)
       (if (expr-case (expr-binary->arg1 expr) :ident)
           (and (ident-formalp (expr-ident->ident (expr-binary->arg1 expr)))
                (or (expr-pure-formalp (expr-binary->arg2 expr))
                    (expr-call-formalp (expr-binary->arg2 expr))))
         (and (expr-pure-formalp (expr-binary->arg1 expr))
              (expr-pure-formalp (expr-binary->arg2 expr)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define desiniter-formalp ((desiniter desiniterp))
  :guard (desiniter-unambp desiniter)
  :returns (yes/no booleanp)
  :short "Check if an initializer with optional designations
          has formal dynamic semantics."
  :long
  (xdoc::topstring
   (xdoc::p
    "Since compound literals are not supported currently,
     the only place where initializers with optional designations occur
     is as elements of list initializers
     (i.e. the @(':list') case of @(tsee initer)).
     The supported initializers are the ones in @(tsee c::exec-initer),
     which only supports list initializers
     that consist of supported pure expressions.
     So each element of the list must
     have no designations
     and be a single supported pure expression."))
  (b* (((desiniter desiniter) desiniter))
    (and (endp desiniter.designors)
         (initer-case desiniter.initer :single)
         (expr-pure-formalp (initer-single->expr desiniter.initer))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define desiniter-list-formalp ((desiniters desiniter-listp))
  :guard (desiniter-list-unambp desiniters)
  :returns (yes/no booleanp)
  :short "Check if all the initializers with optional designations in a list
          have formal dynamic semantics."
  (or (endp desiniters)
      (and (desiniter-formalp (car desiniters))
           (desiniter-list-formalp (cdr desiniters))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define initer-formalp ((initer initerp))
  :guard (initer-unambp initer)
  :returns (yes/no booleanp)
  :short "Check if an initializer has formal dynamic semantics."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is based on @(tsee c::exec-initer).
     If the initializer is a single expression,
     the expression must be a supported call or pure expression.
     If the initializer is a list,
     each element of the list must be a supported pure expressions."))
  (initer-case
   initer
   :single (or (expr-pure-formalp initer.expr)
               (expr-call-formalp initer.expr))
   :list (desiniter-list-formalp initer.elems))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pointers-formalp ((pointers typequal/attribspec-list-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of pointers has formal dynamic semantics."
  :long
  (xdoc::topstring
   (xdoc::p
    "Here `pointers' refers to the constructs
     that may precede a direct declarator to form a declarator,
     or a direct abstract declarator to form an abstract declarator.
     Currently only (non-abstract) declarators are supported,
     so for now we are only interested in the pointers in them.
     We support any number of pointers,
     but without type qualifiers or attribute specifiers.
     So we just check that each inner list is empty.
     Refer @(tsee declor) for an explanation of how pointers are modeled."))
  (or (endp pointers)
      (and (endp (car pointers))
           (pointers-formalp (cdr pointers))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define dirdeclor-block-formalp ((dirdeclor dirdeclorp))
  :guard (dirdeclor-unambp dirdeclor)
  :returns (yes/no booleanp)
  :short "Check if a direct declarator has formal dynamic semantics,
          as part of a block item declaration."
  :long
  (xdoc::topstring
   (xdoc::p
    "In @(tsee c::exec-block-item),
     the declaration case requires an object (not function) declarator
     that is not an array declarator.
     So we can only have an identifier."))
  (and (dirdeclor-case dirdeclor :ident)
       (ident-formalp (dirdeclor-ident->ident dirdeclor)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define declor-block-formalp ((declor declorp))
  :guard (declor-unambp declor)
  :returns (yes/no booleanp)
  :short "Check if a declarator has formal dynamic semantics,
          as part of a block item declaration."
  :long
  (xdoc::topstring
   (xdoc::p
    "The direct declarator part must be supported,
     and we can have any number of supported pointers."))
  (and (pointers-formalp (declor->pointers declor))
       (dirdeclor-block-formalp (declor->direct declor)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define initdeclor-block-formalp ((initdeclor initdeclorp))
  :guard (initdeclor-unambp initdeclor)
  :returns (yes/no booleanp)
  :short "Check if an initializer declarator has formal dynamic semantics,
          as part of a block item declaration."
  :long
  (xdoc::topstring
   (xdoc::p
    "In @(tsee c::exec-block-item),
     the initializer must be present and supported.
     The declarator must be supported too.
     There must be no assembler name specifier and no attribute specifiers."))
  (b* (((initdeclor initdeclor) initdeclor))
    (and (declor-block-formalp initdeclor.declor)
         (not initdeclor.asm?)
         (endp initdeclor.attribs)
         initdeclor.init?
         (initer-formalp initdeclor.init?)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define decl-block-formalp ((decl declp))
  :guard (decl-unambp decl)
  :returns (yes/no booleanp)
  :short "Check if a declaration has formal dynamic semantics,
          as a block item."
  :long
  (xdoc::topstring
   (xdoc::p
    "The declaration must not be a static assertion declaration.
     The GCC extensions must be absent,
     since they are not covered by our formal semantics.
     All the declaration specifiers must be type specifiers,
     because @(tsee c::exec-block-item)
     does not support storage class specifiers;
     the type specifier sequence must be a supported one.
     There must be exactly one supported initializer declarator."))
  (decl-case
   decl
   :decl (and (not decl.extension)
              (b* (((mv okp tyspecs)
                    (check-decl-spec-list-all-typespec decl.specs)))
                (and okp
                     (type-spec-list-formalp tyspecs)))
              (consp decl.init)
              (endp (cdr decl.init))
              (initdeclor-block-formalp (car decl.init)))
   :statassert nil)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines stmts/blocks-formalp
  :short "Chek if statements and blocks have formal dynamic semantics."

  (define stmt-formalp ((stmt stmtp))
    :guard (stmt-unambp stmt)
    :returns (yes/no booleanp)
    :parents nil
    :short "Check if a statement has formal dynamic semantics."
    :long
    (xdoc::topstring
     (xdoc::p
      "Statements not supported by @(tsee ldm-stmt)
       are not supported here either.
       In addition, we look at @(tsee c::exec-stmt) to determine
       which of those statements have formal dynamic semantics,
       and what restrictions there are on the kinds of expressions
       that can occur in the statements."))
    (stmt-case
     stmt
     :labeled nil
     :compound (block-item-list-formalp stmt.items)
     :expr (and stmt.expr?
                (or (expr-call-formalp stmt.expr?)
                    (expr-asg-formalp stmt.expr?)))
     :if (and (expr-pure-formalp stmt.test)
              (stmt-formalp stmt.then))
     :ifelse (and (expr-pure-formalp stmt.test)
                  (stmt-formalp stmt.then)
                  (stmt-formalp stmt.else))
     :switch nil
     :while (and (expr-pure-formalp stmt.test)
                 (stmt-formalp stmt.body))
     :dowhile nil
     :for-expr nil
     :for-decl nil
     :for-ambig (impossible)
     :goto nil
     :continue nil
     :break nil
     :return (or (not stmt.expr?)
                 (expr-call-formalp stmt.expr?)
                 (expr-pure-formalp stmt.expr?))
     :asm nil)
    :measure (stmt-count stmt))

  (define block-item-formalp ((item block-itemp))
    :guard (block-item-unambp item)
    :returns (yes/no booleanp)
    :parents nil
    :short "Check if a block item has formal dynamic semantics."
    :long
    (xdoc::topstring
     (xdoc::p
      "TODO"))
    (block-item-case
     item
     :decl (decl-block-formalp item.unwrap)
     :stmt (stmt-formalp item.unwrap)
     :ambig (impossible))
    :measure (block-item-count item))

  (define block-item-list-formalp ((items block-item-listp))
    :guard (block-item-list-unambp items)
    :returns (yes/no booleanp)
    :parents nil
    :short "Check if a list of block items have formal dynamic semantics."
    :long
    (xdoc::topstring
     (xdoc::p
      "Every block item must be supported."))
    (or (endp items)
        (and (block-item-formalp (car items))
             (block-item-list-formalp (cdr items))))
    :measure (block-item-list-count items))

  :hints (("Goal" :in-theory (enable o< o-finp)))

  ///

  (fty::deffixequiv-mutual stmts/blocks-formalp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define dirdeclor-obj-formalp ((dirdeclor dirdeclorp))
  :guard (dirdeclor-unambp dirdeclor)
  :returns (yes/no booleanp)
  :short "Check if a direct declarator has formal dynamic semantics,
          as part of an object declaration (not in a block)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is for direct declarators not used as part of block items;
     for those, we have @(tsee dirdeclor-block-formalp) instead.")
   (xdoc::p
    "For all other uses of direct declarators (not as part of block items),
     we allow identifier declarators and array declarators,
     the latter without size or with an integer constant as size;
     also see @(tsee ldm-dirdeclor-obj)."))
  (dirdeclor-case
   dirdeclor
   :ident (ident-formalp dirdeclor.ident)
   :paren nil
   :array (and (dirdeclor-obj-formalp dirdeclor.declor)
               (endp dirdeclor.qualspecs)
               (or (not dirdeclor.size?)
                   (and (check-expr-iconst dirdeclor.size?) t)))
   :array-static1 nil
   :array-static2 nil
   :array-star nil
   :function-params nil
   :function-names nil)
  :measure (dirdeclor-count dirdeclor)
  :hints (("Goal" :in-theory (enable o< o-finp)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define declor-obj-formalp ((declor declorp))
  :guard (declor-unambp declor)
  :returns (yes/no booleanp)
  :short "Check if a declarator has formal dynamic semantics,
          as part of an object declaration (not in a block)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This complements @(tsee dirdeclor-obj-formalp):
     see the documentation of that function.
     We support any number of pointers, but without type qualifiers."))
  (b* (((declor declor) declor))
    (and (pointers-formalp declor.pointers)
         (dirdeclor-obj-formalp declor.direct)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define initdeclor-obj-formalp ((initdeclor initdeclorp))
  :guard (initdeclor-unambp initdeclor)
  :returns (yes/no booleanp)
  :short "Check if an initializer declarator has formal dynamic semantics,
          as part of an object declaration (not in a block)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This complements @(tsee declor-obj-formalp);
     see the documentation of that function.
     The initializer is optional, but if present it must be supported.
     There must be no assembler name specifier and no attribute specifiers."))
  (b* (((initdeclor initdeclor) initdeclor))
    (and (declor-obj-formalp initdeclor.declor)
         (not initdeclor.asm?)
         (endp initdeclor.attribs)
         (or (not initdeclor.init?)
             (initer-formalp initdeclor.init?))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define decl-obj-formalp ((decl declp))
  :guard (decl-unambp decl)
  :returns (yes/no booleanp)
  :short "Check if a declaration has formal dynamic semantics,
          as an object declaration (not in a block)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This complements @(tsee initdeclor-obj-formalp);
     see the documentation of that function.
     The declaration must not be a static assertion declaration.
     We require a single supported initializer declarator.
     The declaration specifiers must be
     all type specifiers and storage class specifiers:
     the former must form a supported sequence,
     and the latter must be either absent or a single @('extern').
     We do not support GCC extensions."))
  (decl-case
   decl
   :decl (and (not decl.extension)
              (b* (((mv okp tyspecs storspecs)
                    (check-decl-spec-list-all-typespec/stoclass decl.specs)))
                (and okp
                     (type-spec-list-formalp tyspecs)
                     (stor-spec-list-formalp storspecs)))
              (consp decl.init)
              (endp (cdr decl.init))
              (initdeclor-obj-formalp (car decl.init)))
   :statassert nil)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define structdeclor-formalp ((structdeclor structdeclorp))
  :guard (structdeclor-unambp structdeclor)
  :returns (yes/no booleanp)
  :short "Check if a structure declarator has formal dynamic semantics."
  :long
  (xdoc::topstring
   (xdoc::p
    "The declarator must be present and supported.
     The optional expression must be absent."))
  (b* (((structdeclor structdeclor) structdeclor))
    (and structdeclor.declor?
         (declor-obj-formalp structdeclor.declor?)
         (not structdeclor.expr?)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define structdecl-formalp ((structdecl structdeclp))
  :guard (structdecl-unambp structdecl)
  :returns (yes/no booleanp)
  :short "Check if a structure declaration has formal dynamic semantics."
  :long
  (xdoc::topstring
   (xdoc::p
    "This must be a declaration for a member, not a static assertion.
     There must be no GCC extension.
     There must be only type specifiers, not type qualifiers,
     and they must form a supported type.
     There must be a single supported structure declarator."))
  (structdecl-case
   structdecl
   :member (and (not structdecl.extension)
                (b* (((mv okp tyspecs)
                      (check-spec/qual-list-all-typespec structdecl.specqual)))
                  (and okp
                       (type-spec-list-formalp tyspecs)))
                (consp structdecl.declor)
                (endp (cdr structdecl.declor))
                (structdeclor-formalp (car structdecl.declor))
                (endp structdecl.attrib))
   :statassert nil
   :empty nil)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define structdecl-list-formalp ((structdecls structdecl-listp))
  :guard (structdecl-list-unambp structdecls)
  :returns (yes/no booleanp)
  :short "Check if all the structure declarations in a list
          have formal dynamic semantics."
  (or (endp structdecls)
      (and (structdecl-formalp (car structdecls))
           (structdecl-list-formalp (cdr structdecls))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define struni-spec-formalp ((struni-spec struni-specp))
  :guard (struni-spec-unambp struni-spec)
  :returns (yes/no booleanp)
  :short "Check if a structure declaration has formal dynamic semantics."
  :long
  (xdoc::topstring
   (xdoc::p
    "The name must be present,
     and each structure declaration must be supported."))
  (b* (((struni-spec struni-spec) struni-spec))
    (and struni-spec.name
         (ident-formalp struni-spec.name)
         (structdecl-list-formalp struni-spec.members)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define decl-struct-formalp ((decl declp))
  :guard (decl-unambp decl)
  :returns (yes/no booleanp)
  :short "Check if a declaration has formal dynamic semantics,
          as a declaration for a structure type."
  :long
  (xdoc::topstring
   (xdoc::p
    "This must not be a static assertion declaration.
     It must consists of a single type specifier without declarators.
     The type specifier must be for a structure type,
     and have a supported structure or union specifier.
     There must be no GCC extensions."))
  (decl-case
   decl
   :decl (and (not decl.extension)
              (consp decl.specs)
              (endp (cdr decl.specs))
              (decl-spec-case (car decl.specs) :typespec)
              (b* ((tyspec (decl-spec-typespec->spec (car decl.specs))))
                (and (type-spec-case tyspec :struct)
                     (b* ((struni-spec (type-spec-struct->spec tyspec)))
                       (and (struni-spec-formalp struni-spec)
                            (endp decl.init))))))
   :statassert nil)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define param-declor-formalp ((paramdeclor param-declorp))
  :guard (param-declor-unambp paramdeclor)
  :returns (yes/no booleanp)
  :short "Check if a parameter declarator has formal dynamic semantics."
  :long
  (xdoc::topstring
   (xdoc::p
    "Based on @(tsee ldm-param-declor),
     the parameter declarator must be present and not abstract.
     The underlying declarator must be supported, for an object."))
  (param-declor-case
   paramdeclor
   :nonabstract (declor-obj-formalp paramdeclor.declor)
   :abstract nil
   :none nil
   :ambig (impossible))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define param-declon-formalp ((param param-declonp))
  :guard (param-declon-unambp param)
  :returns (yes/no booleanp)
  :short "Check if a parameter declaration has formal dynamic semantics."
  :long
  (xdoc::topstring
   (xdoc::p
    "The declaration specifiers must be all type specifiers,
     and must form a supported type.
     The parameter declarator must be a supported one."))
  (b* (((param-declon param) param)
       ((mv okp tyspecs) (check-decl-spec-list-all-typespec param.specs)))
    (and okp
         (type-spec-list-formalp tyspecs)
         (param-declor-formalp param.declor)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define param-declon-list-formalp ((params param-declon-listp))
  :guard (param-declon-list-unambp params)
  :returns (yes/no booleanp)
  :short "Check if all the parameter declarations in a list
          have formal dynamic semantics."
  (or (endp params)
      (and (param-declon-formalp (car params))
           (param-declon-list-formalp (cdr params))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define dirdeclor-fun-formalp ((dirdeclor dirdeclorp))
  :guard (dirdeclor-unambp dirdeclor)
  :returns (yes/no booleanp)
  :short "Check if a direct declarator has formal dynamic semantics,
          as part of a function declaration."
  :long
  (xdoc::topstring
   (xdoc::p
    "It must be a function declarator with parameters,
     where the inner declarator is just a name;
     see @(tsee ldm-dirdeclor-fun).
     The parameter declarations must be supported."))
  (dirdeclor-case
   dirdeclor
   :function-params
   (and (dirdeclor-case dirdeclor.declor :ident)
        (ident-formalp (dirdeclor-ident->ident dirdeclor.declor))
        (param-declon-list-formalp dirdeclor.params))
   :function-names
   (and (dirdeclor-case dirdeclor.declor :ident)
        (ident-formalp (dirdeclor-ident->ident dirdeclor.declor))
        (endp dirdeclor.names))
   :otherwise nil)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define declor-fun-formalp ((declor declorp))
  :guard (declor-unambp declor)
  :returns (yes/no booleanp)
  :short "Check if a declarator has formal dynamic semantics,
          as part of a function declaration."
  :long
  (xdoc::topstring
   (xdoc::p
    "There may be any number of pointers, but without type qualifiers.
     And the direct declarator must be supported."))
  (b* (((declor declor) declor))
    (and (pointers-formalp declor.pointers)
         (dirdeclor-fun-formalp declor.direct)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define initdeclor-fun-formalp ((initdeclor initdeclorp))
  :guard (initdeclor-unambp initdeclor)
  :returns (yes/no booleanp)
  :short "Check if an initializer declarator has formal dynamic semantics,
          as part of a function declaration."
  :long
  (xdoc::topstring
   (xdoc::p
    "There must be no initializer,
     and the declarator must be supported.
     There must be no assembler name specifier and no attribute specifiers."))
  (b* (((initdeclor initdeclor) initdeclor))
    (and (declor-fun-formalp initdeclor.declor)
         (not initdeclor.asm?)
         (endp initdeclor.attribs)
         (not initdeclor.init?)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define decl-fun-formalp ((decl declp))
  :guard (decl-unambp decl)
  :returns (yes/no booleanp)
  :short "Check if a declaration has dynamic formal semantics,
          as a function declaration."
  :long
  (xdoc::topstring
   (xdoc::p
    "It must not be a static assertion declaration,
     and there must be no GCC extensions.
     There may be only type specifiers, for a supported type.
     There must a single supported initializer declarator."))
  (decl-case
   decl
   :decl (and (not decl.extension)
              (b* (((mv okp tyspecs)
                    (check-decl-spec-list-all-typespec decl.specs)))
                (and okp
                     (type-spec-list-formalp tyspecs)))
              (consp decl.init)
              (endp (cdr decl.init))
              (initdeclor-fun-formalp (car decl.init)))
   :statassert nil)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fundef-formalp ((fundef fundefp))
  :guard (fundef-unambp fundef)
  :returns (yes/no booleanp)
  :short "Check if a function definition has dynamic formal semantics."
  :long
  (xdoc::topstring
   (xdoc::p
    "There must be no GCC extensions.
     The declaration specifiers must be all type specifiers,
     and they must form a supported type specifier sequence.
     The declarator must be one supported for a function.
     There must be no assembler name specifier or attribute specifiers.
     There must be no declarations between the declarators and the body.
     The body must be a compound statement (see @(tsee ldm-fundef)),
     whose block items are all supported."))
  (b* (((fundef fundef) fundef))
    (and (not fundef.extension)
         (b* (((mv okp tyspecs) (check-decl-spec-list-all-typespec fundef.spec)))
           (and okp
                (type-spec-list-formalp tyspecs)))
         (declor-fun-formalp fundef.declor)
         (not fundef.asm?)
         (endp fundef.attribs)
         (endp fundef.decls)
         (stmt-case fundef.body :compound)
         (block-item-list-formalp (stmt-compound->items fundef.body))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define extdecl-formalp ((edecl extdeclp))
  :guard (extdecl-unambp edecl)
  :returns (yes/no booleanp)
  :short "Check if an external declaration has dynamic formal semantics."
  :long
  (xdoc::topstring
   (xdoc::p
    "We support
     function definitions,
     function declarations,
     object declarations,
     and structure declarations.")
   (xdoc::p
    "Strictly speaking, our current formal dynamic semantics
     actually ignores all the above except for function definitions:
     it uses function definitions to build the function environment,
     but there is no similar function to process
     the other kinds of external declarations.
     In theorems generated by ATC,
     external object and structure types are handled in hypotheses,
     and function declarations are not used.
     However, ATC generates the kind of external declarations supported here,
     so our formal dynamic semantics can (and will) be extended
     to handle those explicitly.
     This is why we include them in this predicate."))
  (extdecl-case
   edecl
   :fundef (fundef-formalp edecl.unwrap)
   :decl (or (decl-obj-formalp edecl.unwrap)
             (decl-struct-formalp edecl.unwrap)
             (decl-fun-formalp edecl.unwrap))
   :empty nil
   :asm nil)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define extdecl-list-formalp ((edecls extdecl-listp))
  :guard (extdecl-list-unambp edecls)
  :returns (yes/no booleanp)
  :short "Check if all the external declarations in a list
          have formal dynamic semantics."
  (or (endp edecls)
      (and (extdecl-formalp (car edecls))
           (extdecl-list-formalp (cdr edecls))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define transunit-formalp ((tunit transunitp))
  :guard (transunit-unambp tunit)
  :returns (yes/no booleanp)
  :short "Check if a translation unit has formal dynamic semantics."
  :long
  (xdoc::topstring
   (xdoc::p
    "All its external declarations must be supported."))
  (extdecl-list-formalp (transunit->decls tunit))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define transunit-ensemble-formalp ((tunits transunit-ensemblep))
  :guard (transunit-ensemble-unambp tunits)
  :returns (yes/no booleanp)
  :short "Check if a translation unit ensemble has formal dynamic semantics."
  :long
  (xdoc::topstring
   (xdoc::p
    "As in @(tsee ldm-transunit-ensemble),
     there must be a single translation unit,
     and in addition it must have formal dynamic semantics."))
  (b* ((map (transunit-ensemble->unwrap tunits)))
    (and (= (omap::size map) 1)
         (transunit-formalp (omap::head-val map))))
  :guard-hints (("Goal" :in-theory (enable omap::unfold-equal-size-const)))
  :hooks (:fix))
