; C++ Syntax Extension for ACL2 Kestrel C Library
;
; This book defines abstract syntax trees (ASTs) for C++ constructs:
; - Access specifiers (public, private, protected)
; - Constant expressions (minimal, for noexcept)
; - Noexcept specifiers
; - Type specifiers (recursive: name, qualified, template-inst, pointer, ref, const)
; - Typed parameters and parameter lists
; - Template parameters (type, non-type, and template-template)
; - Class keys (class/struct) and class specifiers
; - Namespace definitions
; - Operator function identifiers
; - Exception handlers
; - Module and import declarations
; - Coroutine keyword kinds

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "CPP")

(include-book "kestrel/c/syntax/abstract-syntax-trees" :dir :system)
(include-book "kestrel/c/syntax/abstract-syntax-irrelevants" :dir :system)

(include-book "centaur/fty/deftypes" :dir :system)
(include-book "std/basic/two-nats-measure" :dir :system)
(include-book "std/util/defirrelevant" :dir :system)

(local (include-book "std/lists/len" :dir :system))

(in-theory (disable mv-nth))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ cpp-abstract-syntax
  :parents (cpp-syntax)
  :short "Abstract syntax trees for C++ constructs."
  :long
  (xdoc::topstring
   (xdoc::p
    "We define fixtypes for the C++ constructs that our extension supports:
     access specifiers, type specifiers, typed parameters,
     template parameters, class specifiers,
     namespace definitions, operator function identifiers,
     lambda capture lists, exception handlers,
     module/import declarations, coroutine constructs,
     member declarations (fields, methods, using-aliases, enums, access labels),
     method name identifiers (@('cpp-member-name') with destructor
     and conversion-function variants), top-level declarations
     (including @('static_assert')), and translation units.")
   (xdoc::p
    "These fixtypes use the existing C$ abstract syntax types
     (such as @(tsee c$::ident)) as building blocks.")
   (xdoc::p
    "Type specifiers are represented structurally via @(tsee cpp-type-spec),
     which supports simple names, qualified names, template instantiations,
     pointers, references, and cv-qualifiers.
     Nested template arguments using @('>>') as two closing angles
     are a known parsing limitation (not an AST limitation)."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Access Specifiers
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum cpp-access-spec
  :short "Fixtype of C++ access specifiers."
  :long
  (xdoc::topstring
   (xdoc::p
    "The three C++ access specifiers:
     @('public'), @('private'), and @('protected').
     These control member accessibility in class bodies and base class
     specifications [C++23:11.8]."))
  (:public ())
  (:private ())
  (:protected ())
  :pred cpp-access-spec-p
  :layout :fulltree)

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-cpp-access-spec
  :short "An irrelevant C++ access specifier."
  :type cpp-access-spec-p
  :body (cpp-access-spec-public))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Constant Expressions (minimal, for noexcept)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum cpp-const-expr
  :short "Fixtype of minimal C++ constant expressions."
  :long
  (xdoc::topstring
   (xdoc::p
    "A minimal constant expression type used in @('noexcept(expr)')
     specifications [C++23:7.7].
     We support boolean literals and named constants (identifiers).")
   (xdoc::p
    "The @(':bool') variant represents @('true') or @('false').")
   (xdoc::p
    "The @(':ident') variant represents a named constant or
     constexpr variable reference."))
  (:bool  ((value bool)))
  (:ident ((name ident)))
  (:int   ((iconst c$::iconst)))
  :pred cpp-const-expr-p
  :layout :fulltree)

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-cpp-const-expr
  :short "An irrelevant C++ constant expression."
  :type cpp-const-expr-p
  :body (make-cpp-const-expr-bool :value nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Noexcept Specifiers
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum cpp-noexcept-spec
  :short "Fixtype of C++ noexcept specifiers [C++23:14.5]."
  :long
  (xdoc::topstring
   (xdoc::p
    "A @('noexcept') specifier on a function declaration.
     The bare form @('noexcept') is equivalent to @('noexcept(true)').
     The @(':expr') variant represents @('noexcept(expr)') where the
     expression is a @(tsee cpp-const-expr)."))
  (:bare ())
  (:expr ((value cpp-const-expr)))
  :pred cpp-noexcept-spec-p
  :layout :fulltree)

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-cpp-noexcept-spec
  :short "An irrelevant C++ noexcept specifier."
  :type cpp-noexcept-spec-p
  :body (cpp-noexcept-spec-bare))

;;;;;;;;;;;;;;;;;;;;

(fty::defoption cpp-noexcept-spec-option
  cpp-noexcept-spec
  :short "Fixtype of optional C++ noexcept specifiers."
  :pred cpp-noexcept-spec-option-p)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Type Specifiers (defined inside cpp-expr-stmt-types for mutual recursion
;;                  with cpp-expr via the :decltype variant)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Class Specifiers
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum cpp-class-key
  :short "Fixtype of C++ class keys."
  :long
  (xdoc::topstring
   (xdoc::p
    "The C++ class keys: @('class') and @('struct') [C++23:11.2].
     (We omit @('union') for now; it is already a C keyword.)"))
  (:class ())
  (:struct ())
  :pred cpp-class-key-p
  :layout :fulltree)

;;;;;;;;;;;;;;;;;;;;
;; cpp-member-decl, cpp-member-decl-list, and cpp-class-specifier
;; are defined AFTER the cpp-expr-stmt-types deftypes block below,
;; because the :method variant of cpp-member-decl carries an optional
;; cpp-block-item-list as the inline method body.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Namespace Kinds
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum cpp-namespace-kind
  :short "Fixtype of C++ namespace kinds (named, anonymous, or nested)."
  :long
  (xdoc::topstring
   (xdoc::p
    "The kind of a namespace definition header [C++23:9.8]:
     named (@('namespace Foo')),
     anonymous (@('namespace')),
     or nested (C++17: @('namespace A::B::C')).
     This is the header-only component; the body is in @(tsee cpp-namespace-def)."))
  (:named
   ((name ident)))               ; e.g., Foo
  (:anonymous ())                ; namespace { ... }
  (:nested
   ((names c$::ident-list)))          ; e.g., (A B C) for 'namespace A::B::C'
  :pred cpp-namespace-kind-p
  :layout :fulltree)

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-cpp-namespace-kind
  :short "An irrelevant C++ namespace kind."
  :type cpp-namespace-kind-p
  :body (cpp-namespace-kind-anonymous))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Namespace Alias
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod cpp-namespace-alias
  :short "Fixtype of C++ namespace alias definitions [C++23:9.8.2]."
  :long
  (xdoc::topstring
   (xdoc::p
    "A namespace alias definition: @('namespace NAME = QUALIFIED-NAME ;').
     The target is a qualified namespace specifier represented as a list
     of identifiers (e.g., @('(std filesystem)') for @('std::filesystem'))."))
  ((name    ident)           ; the alias identifier
   (target  c$::ident-list)) ; qualified target (e.g. (std filesystem))
  :pred cpp-namespace-alias-p
  :layout :fulltree)

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-cpp-namespace-alias
  :short "An irrelevant C++ namespace alias."
  :type cpp-namespace-alias-p
  :body (make-cpp-namespace-alias :name (c$::irr-ident) :target nil))

;; Note: cpp-namespace-def (the full namespace definition with body) is
;; defined later in the fty::deftypes cpp-top-level-types block at the
;; end of this file, because it is mutually recursive with
;; cpp-top-level-decl and cpp-top-level-decl-list.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Operator Function Identifiers
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum cpp-operator-kind
  :short "Fixtype of overloadable C++ operator kinds [C++23:12.5]."
  :long
  (xdoc::topstring
   (xdoc::p
    "Every overloadable operator has a corresponding variant here.
     The call operator @('()') and subscript operator @('[]') are included.
     The @('new'), @('delete'), @('new[]'), and @('delete[]') operators
     are also included; they arrive as identifier tokens."))
  ;; Arithmetic
  (:plus ())         ; +
  (:minus ())        ; -
  (:star ())         ; * (multiply or dereference)
  (:slash ())        ; /
  (:percent ())      ; %
  ;; Bitwise
  (:caret ())        ; ^
  (:amp ())          ; & (bitand or address-of)
  (:pipe ())         ; |
  (:tilde ())        ; ~ (complement)
  ;; Logical
  (:bang ())         ; ! (not)
  (:amp-amp ())      ; &&
  (:pipe-pipe ())    ; ||
  ;; Shift
  (:lshift ())       ; <<
  (:rshift ())       ; >>
  ;; Comparison
  (:eq ())           ; ==
  (:ne ())           ; !=
  (:lt ())           ; <
  (:gt ())           ; >
  (:le ())           ; <=
  (:ge ())           ; >=
  (:spaceship ())    ; <=> (C++20)
  ;; Assignment
  (:asg ())          ; =
  (:plus-asg ())     ; +=
  (:minus-asg ())    ; -=
  (:star-asg ())     ; *=
  (:slash-asg ())    ; /=
  (:percent-asg ())  ; %=
  (:caret-asg ())    ; ^=
  (:amp-asg ())      ; &=
  (:pipe-asg ())     ; |=
  (:lshift-asg ())   ; <<=
  (:rshift-asg ())   ; >>=
  ;; Increment / decrement
  (:inc ())          ; ++
  (:dec ())          ; --
  ;; Pointer-to-member
  (:arrow ())        ; ->
  (:arrow-star ())   ; ->*
  ;; Special
  (:call ())         ; ()
  (:subscript ())    ; []
  (:comma ())        ; ,
  ;; Memory management
  (:new ())          ; new
  (:delete ())       ; delete
  (:new-array ())    ; new[]
  (:delete-array ()) ; delete[]
  ;; Coroutines (C++20)
  (:co-await ())     ; co_await
  :pred cpp-operator-kind-p
  :layout :fulltree)

;;;;;;;;;;;;;;;;;;;;

(fty::defprod cpp-operator-function-id
  :short "Fixtype of C++ operator function identifiers."
  :long
  (xdoc::topstring
   (xdoc::p
    "An operator function identifier is of the form @('operator op')
     where @('op') is one of the overloadable operators [C++23:12.5].
     It names a function that overloads that operator."))
  ((op cpp-operator-kind))
  :pred cpp-operator-function-id-p
  :layout :fulltree)

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-cpp-operator-function-id
  :short "An irrelevant C++ operator function identifier."
  :type cpp-operator-function-id-p
  :body (make-cpp-operator-function-id :op (cpp-operator-kind-plus)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Exception Handlers
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Module Declarations
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum cpp-module-decl
  :short "Fixtype of C++ module declaration headers (simplified) [C++23:10.2]."
  :long
  (xdoc::topstring
   (xdoc::p
    "A module declaration: @('[export] module name ;') or
     the private module fragment @('module : private ;').
     We represent the header only (without the body/fragment)."))
  (:named
   ((name    c$::ident-list)   ; dotted module name, e.g. (std core) for std.core
    (exportp bool)))            ; 'export module name' ?
  (:private ())
  :pred cpp-module-decl-p
  :layout :fulltree)

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-cpp-module-decl
  :short "An irrelevant C++ module declaration."
  :type cpp-module-decl-p
  :body (cpp-module-decl-private))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Import Declarations
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod cpp-import-decl
  :short "Fixtype of C++ import declaration headers (simplified) [C++23:10.3]."
  :long
  (xdoc::topstring
   (xdoc::p
    "An import declaration: @('[export] import name ;').
     We represent the header only."))
  ((name    c$::ident-list)  ; dotted module name to import, e.g. (std core) for std.core
   (exportp bool))          ; 'export import name' ?
  :pred cpp-import-decl-p
  :layout :fulltree)

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-cpp-import-decl
  :short "An irrelevant C++ import declaration."
  :type cpp-import-decl-p
  :body (make-cpp-import-decl :name nil :exportp nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Coroutine Keyword Kinds
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum cpp-coroutine-kw-kind
  :short "Fixtype of C++ coroutine keyword kinds [C++23:9.5]."
  :long
  (xdoc::topstring
   (xdoc::p
    "The three C++ coroutine keywords:
     @('co_return'), @('co_yield'), and @('co_await').
     We represent only the keyword kind; the expression operand is not captured."))
  (:return ())
  (:yield ())
  (:await ())
  :pred cpp-coroutine-kw-kind-p
  :layout :fulltree)

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-cpp-coroutine-kw-kind
  :short "An irrelevant C++ coroutine keyword kind."
  :type cpp-coroutine-kw-kind-p
  :body (cpp-coroutine-kw-kind-return))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Assignment Operators
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum cpp-assign-op
  :short "Fixtype of C++ assignment operators [C++23:7.6.19]."
  :long
  (xdoc::topstring
   (xdoc::p
    "The 11 assignment operators in C++ (simple and compound).
     We keep them separate from @(tsee c$::binop) to avoid conflating
     the assignment operator @('=') with the @('=') token used elsewhere."))
  (:simple ())   ; =
  (:add ())      ; +=
  (:sub ())      ; -=
  (:mul ())      ; *=
  (:div ())      ; /=
  (:rem ())      ; %=
  (:bitand ())   ; &=
  (:bitor ())    ; |=
  (:bitxor ())   ; ^=
  (:lshift ())   ; <<=
  (:rshift ())   ; >>=
  :pred cpp-assign-op-p
  :layout :fulltree)

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-cpp-assign-op
  :short "An irrelevant C++ assignment operator."
  :type cpp-assign-op-p
  :body (cpp-assign-op-simple))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Expressions, Statements, Block Items, Catch Clauses, and Captures (mutually recursive)
;; Note: cpp-capture is inside the deftypes block because init-captures
;; ([x = expr] and [&x = expr]) reference cpp-expr, creating a mutual
;; dependency with cpp-expr's lambda variant which references cpp-capture-list.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftypes cpp-expr-stmt-types
  :short "Mutually recursive fixtypes for C++ type specifiers, parameters,
          captures, expressions, statements, block items, and catch clauses."
  :long
  (xdoc::topstring
   (xdoc::p
    "These types are mutually recursive because:
     a @(tsee cpp-type-spec) @(':decltype') variant contains a @(tsee cpp-expr);
     a @(tsee cpp-expr) cast variant contains a @(tsee cpp-type-spec);
     a @(tsee cpp-expr) lambda has a @(tsee cpp-capture-list),
     a @(tsee cpp-param-list), and a @(tsee cpp-block-item-list) body;
     a @(tsee cpp-capture) @(':init') and @(':ref-init') variants contain
     a @(tsee cpp-expr) (for C++14 init-captures such as @('[x = expr]'));
     a @(tsee cpp-stmt) compound has a @(tsee cpp-block-item-list);
     a @(tsee cpp-block-item) carries either a @(tsee cpp-stmt) or a
     declaration with an optional @(tsee cpp-expr) initializer;
     a @(tsee cpp-stmt) try has a @(tsee cpp-catch-clause-list);
     a @(tsee cpp-catch-clause) has a @(tsee cpp-block-item-list) body.")
   (xdoc::p
    "Optional sub-components are represented with a @('-p bool') flag
     and a value field (rather than option types), since option types
     defined inside a @('deftypes') block introduce complications.
     For optional sub-statements we use distinct tagsum variants
     (e.g., @(':if-then') vs @(':if-else'), @(':return-void') vs
     @(':return-expr'))."))

  ;;;;;;;;;;;;;;;;;;;;
  ;; Type Specifiers
  ;;;;;;;;;;;;;;;;;;;;

  (fty::deftagsum cpp-type-spec
    :short "Fixtype of C++ type specifiers."
    :long
    (xdoc::topstring
     (xdoc::p
      "Represents all forms of C++ type specifiers.
       The @(':name') variant is a simple named type (e.g., @('int'), @('T')).
       The @(':qualified') variant handles @('scope::T').
       The @(':template-inst') variant handles @('T<Args>').
       The @(':pointer') variant handles @('T*') and @('const T*').
       The @(':lref') and @(':rref') variants handle @('T&') and @('T&&').
       The @(':const-qual') and @(':volatile-qual') variants handle
       @('const T') and @('volatile T').
       The @(':decltype') variant handles @('decltype(expr)') where
       @('expr') is a full C++ expression (e.g., @('decltype(a+b)')).
       The @(':array') variant handles @('T[N]') and @('T[]')."))
    (:name          ((id       ident)))
    (:qualified     ((scope    ident) (inner cpp-type-spec)))
    (:template-inst ((template cpp-type-spec) (args cpp-type-spec-list)))
    (:pointer       ((pointee  cpp-type-spec) (constp bool)))
    (:lref          ((base     cpp-type-spec)))
    (:rref          ((base     cpp-type-spec)))
    (:const-qual    ((base     cpp-type-spec)))
    (:volatile-qual ((base     cpp-type-spec)))
    (:decltype      ((arg      cpp-expr)))
    (:array         ((element  cpp-type-spec) (size-p bool) (size cpp-const-expr)))
    :pred cpp-type-spec-p
    :layout :fulltree
    :measure (two-nats-measure (acl2-count x) 1))

  (fty::deflist cpp-type-spec-list
    :short "Fixtype of lists of C++ type specifiers."
    :elt-type cpp-type-spec
    :true-listp t
    :elementp-of-nil nil
    :pred cpp-type-spec-listp
    :measure (two-nats-measure (acl2-count x) 0))

  ;;;;;;;;;;;;;;;;;;;;
  ;; Parameters
  ;;;;;;;;;;;;;;;;;;;;

  (fty::defprod cpp-param
    :short "Fixtype of C++ typed parameters."
    :long
    (xdoc::topstring
     (xdoc::p
      "A function or lambda parameter: a type specifier and
       an optional parameter name [C++23:9.3.4.6]."))
    ((type cpp-type-spec)
     (name ident-option))
    :pred cpp-param-p
    :layout :fulltree
    :measure (two-nats-measure (acl2-count x) 2))

  (fty::deflist cpp-param-list
    :short "Fixtype of lists of C++ typed parameters."
    :elt-type cpp-param
    :true-listp t
    :elementp-of-nil nil
    :pred cpp-param-listp
    :measure (two-nats-measure (acl2-count x) 1))

  ;;;;;;;;;;;;;;;;;;;;
  ;; Lambda Captures
  ;;;;;;;;;;;;;;;;;;;;

  (fty::deftagsum cpp-capture
    :short "Fixtype of C++ lambda capture clauses [C++23:7.5.5]."
    :long
    (xdoc::topstring
     (xdoc::p
      "A single capture in a lambda capture list.
       We support the eight syntactic forms:
       @('[=]') (default by-value), @('[&]') (default by-reference),
       @('[x]') (named by-value), @('[&x]') (named by-reference),
       @('[this]'), @('[*this]') (C++17),
       @('[x = expr]') (init-capture by value, C++14), and
       @('[&x = expr]') (init-capture by reference, C++14)."))
    (:default-val ())                              ; [=]
    (:default-ref ())                              ; [&]
    (:by-value    ((name ident)))                  ; [x]
    (:by-ref      ((name ident)))                  ; [&x]
    (:this        ())                              ; [this]
    (:star-this   ())                              ; [*this]
    (:init        ((name ident) (expr cpp-expr)))  ; [x = expr]   C++14
    (:ref-init    ((name ident) (expr cpp-expr)))  ; [&x = expr]  C++14
    :pred cpp-capture-p
    :layout :fulltree
    :measure (two-nats-measure (acl2-count x) 2))

  (fty::deflist cpp-capture-list
    :short "Fixtype of lists of C++ lambda captures."
    :elt-type cpp-capture
    :true-listp t
    :elementp-of-nil nil
    :pred cpp-capture-listp
    :measure (two-nats-measure (acl2-count x) 1))

  ;;;;;;;;;;;;;;;;;;;;
  ;; Expressions
  ;;;;;;;;;;;;;;;;;;;;

  (fty::deftagsum cpp-expr
    :short "Fixtype of C++ expressions."
    :long
    (xdoc::topstring
     (xdoc::p
      "Covers C++ expressions across all 14 precedence levels."))
    ;; Primary
    (:ident ((name ident)))
    (:const ((value c$::const)))
    (:string ((value c$::stringlit-list)))
    (:this ())
    (:paren ((inner cpp-expr)))
    (:scoped ((scope ident) (inner cpp-expr)))
    ;; Postfix
    (:arrsub    ((array cpp-expr) (index cpp-expr)))
    (:call      ((fun cpp-expr) (args cpp-expr-list)))
    (:member    ((object cpp-expr) (name ident)))
    (:memberp   ((object cpp-expr) (name ident)))
    (:dot-star  ((lhs cpp-expr) (rhs cpp-expr)))   ; lhs .* rhs  C++98
    (:arrow-star ((lhs cpp-expr) (rhs cpp-expr)))  ; lhs ->* rhs C++98
    (:postinc   ((arg cpp-expr)))
    (:postdec   ((arg cpp-expr)))
    ;; C++ casts
    (:static-cast ((type cpp-type-spec) (arg cpp-expr)))
    (:dynamic-cast ((type cpp-type-spec) (arg cpp-expr)))
    (:reinterpret-cast ((type cpp-type-spec) (arg cpp-expr)))
    (:const-cast ((type cpp-type-spec) (arg cpp-expr)))
    (:typeid-expr ((arg cpp-expr)))
    (:typeid-type ((type cpp-type-spec)))
    ;; Unary
    (:preinc ((arg cpp-expr)))
    (:predec ((arg cpp-expr)))
    (:unary ((op c$::unop) (arg cpp-expr)))
    (:sizeof-expr ((arg cpp-expr)))
    (:sizeof-type ((type cpp-type-spec)))
    (:alignof-type ((type cpp-type-spec)))
    (:new ((type cpp-type-spec) (args cpp-expr-list)))
    (:delete ((arg cpp-expr) (arrayp bool)))
    (:rethrow ())
    (:throw-expr ((arg cpp-expr)))
    (:co-await ((arg cpp-expr)))
    (:c-cast ((type cpp-type-spec) (arg cpp-expr)))
    ;; Binary
    (:binary ((op c$::binop) (lhs cpp-expr) (rhs cpp-expr)))
    (:assign ((op cpp-assign-op) (lhs cpp-expr) (rhs cpp-expr)))
    ;; Ternary
    (:cond ((test cpp-expr) (then cpp-expr) (else cpp-expr)))
    ;; Comma
    (:comma ((lhs cpp-expr) (rhs cpp-expr)))
    ;; Lambda
    (:lambda ((captures cpp-capture-list)
              (params   cpp-param-list)
              (body     cpp-block-item-list)))
    :pred cpp-expr-p
    :layout :fulltree
    :measure (two-nats-measure (acl2-count x) 1))

  (fty::deflist cpp-expr-list
    :short "Fixtype of lists of C++ expressions."
    :elt-type cpp-expr
    :true-listp t
    :elementp-of-nil nil
    :pred cpp-expr-listp
    :measure (two-nats-measure (acl2-count x) 0))

  ;;;;;;;;;;;;;;;;;;;;
  ;; Block items
  ;;;;;;;;;;;;;;;;;;;;

  (fty::deftagsum cpp-block-item
    :short "Fixtype of C++ block items (statements or local declarations)."
    :long
    (xdoc::topstring
     (xdoc::p
      "For the @(':decl') variant, @('init-p') is @('t') iff an initializer
       is present.  When @('init-p') is @('nil') the @('init') field is
       still well-typed but is ignored.")
     (xdoc::p
      "The @(':empty') variant is a structural base case for the
       mutually recursive deftypes block; it is not produced by the parser."))
    (:empty ())
    (:stmt ((stmt cpp-stmt)))
    (:decl ((type cpp-type-spec)
            (name ident)
            (init-p bool)
            (init cpp-expr)))
    :pred cpp-block-item-p
    :layout :fulltree
    :measure (two-nats-measure (acl2-count x) 1))

  (fty::deflist cpp-block-item-list
    :short "Fixtype of lists of C++ block items."
    :elt-type cpp-block-item
    :true-listp t
    :elementp-of-nil nil
    :pred cpp-block-item-listp
    :measure (two-nats-measure (acl2-count x) 0))

  ;;;;;;;;;;;;;;;;;;;;
  ;; Statements
  ;;;;;;;;;;;;;;;;;;;;

  (fty::deftagsum cpp-stmt
    :short "Fixtype of C++ statements."
    :long
    (xdoc::topstring
     (xdoc::p
      "We use distinct variants for optional sub-statements/expressions
       (e.g., @(':if-then') vs @(':if-else'), @(':return-void') vs
       @(':return-expr')) instead of option types inside a deftypes block.
       For the @('for') family, we use boolean presence flags for the
       three optional sub-clauses."))
    (:compound ((body cpp-block-item-list)))
    (:expr-void ())
    (:expr-stmt ((e cpp-expr)))
    (:if-then ((constexprp bool) (test cpp-expr) (then cpp-stmt)))
    (:if-else ((constexprp bool) (test cpp-expr) (then cpp-stmt) (else cpp-stmt)))
    (:switch ((target cpp-expr) (body cpp-stmt)))
    (:while ((test cpp-expr) (body cpp-stmt)))
    (:dowhile ((body cpp-stmt) (test cpp-expr)))
    (:for-expr ((init-e-p bool) (init-e cpp-expr)
                (test-e-p bool) (test-e cpp-expr)
                (next-e-p bool) (next-e cpp-expr)
                (body cpp-stmt)))
    (:for-decl ((type cpp-type-spec) (name ident)
                (init-p bool) (init cpp-expr)
                (test-p bool) (test cpp-expr)
                (next-p bool) (next cpp-expr)
                (body cpp-stmt)))
    (:for-range ((type cpp-type-spec) (name ident)
                 (range cpp-expr) (body cpp-stmt)))
    (:goto ((label ident)))
    (:continue ())
    (:break ())
    (:return-void ())
    (:return-expr ((e cpp-expr)))
    (:rethrow ())
    (:throw-stmt ((e cpp-expr)))
    (:try ((body cpp-block-item-list)
           (handlers cpp-catch-clause-list)))
    (:labeled ((label ident) (s cpp-stmt)))
    (:caselbl ((e cpp-expr) (s cpp-stmt)))
    (:default ((s cpp-stmt)))
    (:co-yield ((e cpp-expr)))
    (:co-return-void ())
    (:co-return-expr ((e cpp-expr)))
    :pred cpp-stmt-p
    :layout :fulltree
    :measure (two-nats-measure (acl2-count x) 1))

  ;;;;;;;;;;;;;;;;;;;;
  ;; Exception Handler Headers
  ;;;;;;;;;;;;;;;;;;;;

  (fty::defprod cpp-exception-handler
    :short "Fixtype of C++ exception handler headers [C++23:14.4]."
    :long
    (xdoc::topstring
     (xdoc::p
      "The header of a @('catch') clause: @('catch ( SomeType e )').
       We capture the exception type as a @(tsee cpp-type-spec)
       and the optional parameter name.
       The body of the catch clause is not captured here."))
    ((type-name  cpp-type-spec)
     (param-name ident-option))
    :pred cpp-exception-handler-p
    :layout :fulltree
    :measure (two-nats-measure (acl2-count x) 2))

  (fty::deflist cpp-exception-handler-list
    :short "Fixtype of lists of C++ exception handler headers."
    :elt-type cpp-exception-handler
    :true-listp t
    :elementp-of-nil nil
    :pred cpp-exception-handler-listp
    :measure (two-nats-measure (acl2-count x) 2))

  ;;;;;;;;;;;;;;;;;;;;
  ;; Catch clauses
  ;;;;;;;;;;;;;;;;;;;;

  (fty::defprod cpp-catch-clause
    :short "Fixtype of C++ catch clauses (with bodies)."
    :long
    (xdoc::topstring
     (xdoc::p
      "Combines the header (@(tsee cpp-exception-handler)) with a body."))
    ((handler cpp-exception-handler)
     (body cpp-block-item-list))
    :pred cpp-catch-clause-p
    :layout :fulltree
    :measure (two-nats-measure (acl2-count x) 3))

  (fty::deflist cpp-catch-clause-list
    :short "Fixtype of lists of C++ catch clauses."
    :elt-type cpp-catch-clause
    :true-listp t
    :elementp-of-nil nil
    :pred cpp-catch-clause-listp
    :measure (two-nats-measure (acl2-count x) 0)))

;;;;;;;;;;;;;;;;;;;;
;; Irrelevant values for the mutually recursive types
;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-cpp-capture
  :short "An irrelevant C++ lambda capture."
  :type cpp-capture-p
  :body (cpp-capture-default-val))

(defirrelevant irr-cpp-type-spec
  :short "An irrelevant C++ type specifier."
  :type cpp-type-spec-p
  :body (make-cpp-type-spec-name :id (c$::irr-ident)))

(defirrelevant irr-cpp-param
  :short "An irrelevant C++ typed parameter."
  :type cpp-param-p
  :body (make-cpp-param :type (irr-cpp-type-spec) :name nil))

(defirrelevant irr-cpp-exception-handler
  :short "An irrelevant C++ exception handler header."
  :type cpp-exception-handler-p
  :body (make-cpp-exception-handler
         :type-name  (irr-cpp-type-spec)
         :param-name nil))

(defirrelevant irr-cpp-expr
  :short "An irrelevant C++ expression."
  :type cpp-expr-p
  :body (cpp-expr-this))

(defirrelevant irr-cpp-stmt
  :short "An irrelevant C++ statement."
  :type cpp-stmt-p
  :body (cpp-stmt-expr-void))

(defirrelevant irr-cpp-block-item
  :short "An irrelevant C++ block item."
  :type cpp-block-item-p
  :body (make-cpp-block-item-stmt :stmt (cpp-stmt-expr-void)))

(defirrelevant irr-cpp-catch-clause
  :short "An irrelevant C++ catch clause."
  :type cpp-catch-clause-p
  :body (make-cpp-catch-clause
         :handler (irr-cpp-exception-handler)
         :body nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Template Parameters
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftypes cpp-template-param-types
  :short "Mutually recursive fixtypes for C++ template parameters."

  (fty::deftagsum cpp-template-param
    :short "Fixtype of C++ template parameters."
    :long
    (xdoc::topstring
     (xdoc::p
      "A C++ template parameter is a type parameter, a non-type parameter,
       or a template template parameter [C++23:13.2].")
     (xdoc::p
      "A @(':type') parameter is introduced by @('typename') or @('class'),
       with an optional name.")
     (xdoc::p
      "A @(':nontype') parameter has a type specifier and a parameter name,
       e.g., @('int N') or @('const T* ptr').")
     (xdoc::p
      "A @(':template-template') parameter is itself a template,
       e.g., @('template<typename> class Container')."))
    (:type
     ((typenamep bool)
      (name      ident-option)))
    (:nontype
     ((type      cpp-type-spec)
      (param-name ident)))
    (:template-template
     ((params cpp-template-param-list)
      (name   ident-option)))
    :pred cpp-template-param-p
    :measure (two-nats-measure (acl2-count x) 1))

  (fty::deflist cpp-template-param-list
    :short "Fixtype of lists of C++ template parameters."
    :long
    (xdoc::topstring
     (xdoc::p
      "A list of @(tsee cpp-template-param) values,
       representing the parameter list in @('template < ... >')."))
    :elt-type cpp-template-param
    :true-listp t
    :elementp-of-nil nil
    :pred cpp-template-param-listp
    :measure (two-nats-measure (acl2-count x) 0)))

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-cpp-template-param
  :short "An irrelevant C++ template parameter."
  :type cpp-template-param-p
  :body (make-cpp-template-param-type :typenamep t :name nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Member Names
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum cpp-member-name
  :short "Fixtype of C++ member names."
  :long
  (xdoc::topstring
   (xdoc::p
    "A member name can be a simple identifier, a destructor name (@('~T')),
     a conversion function id, or an operator function id."))
  (:simple     ((id         c$::ident)))
  (:destructor ((class-name c$::ident)))
  (:conversion ((target-type cpp-type-spec)))
  (:operator   ((op cpp-operator-function-id)))
  :pred cpp-member-name-p)

(defirrelevant irr-cpp-member-name
  :short "An irrelevant C++ member name."
  :type cpp-member-name-p
  :body (make-cpp-member-name-simple :id (c$::irr-ident)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Constructor Initializer Lists
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod cpp-ctor-init-item
  :short "Fixtype of a single constructor initializer item."
  :long
  (xdoc::topstring
   (xdoc::p
    "One member-initializer in a constructor initializer list:
     @('name(args)') or @('name{args}') [C++23:11.10.2]."))
  ((name   c$::ident)
   (bracep bool)
   (args   cpp-expr-list))
  :pred cpp-ctor-init-item-p
  :layout :fulltree)

(fty::deflist cpp-ctor-init-list
  :short "Fixtype of lists of constructor initializer items."
  :elt-type cpp-ctor-init-item
  :true-listp t
  :elementp-of-nil nil
  :pred cpp-ctor-init-listp)

(defirrelevant irr-cpp-ctor-init-item
  :short "An irrelevant constructor initializer item."
  :type cpp-ctor-init-item-p
  :body (make-cpp-ctor-init-item :name (c$::irr-ident) :bracep nil :args nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Class Member Declarations (moved here to reference cpp-block-item-list)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;
;; Enumerators and Enum Declarations
;;;;;;;;;;;;;;;;;;;;

(fty::defprod cpp-enumerator
  :short "Fixtype of a single C++ enumerator [C++23:9.7.1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "A single enumerator in an enum body.  If @('value-p') is @('t'),
     @('value') holds the explicitly specified constant expression."))
  ((name    ident)
   (value-p bool)
   (value   cpp-const-expr))
  :pred cpp-enumerator-p
  :layout :fulltree)

(fty::deflist cpp-enumerator-list
  :short "Fixtype of lists of C++ enumerators."
  :elt-type cpp-enumerator
  :true-listp t
  :elementp-of-nil nil
  :pred cpp-enumerator-listp)

(defirrelevant irr-cpp-enumerator
  :short "An irrelevant C++ enumerator."
  :type cpp-enumerator-p
  :body (make-cpp-enumerator
         :name    (c$::irr-ident)
         :value-p nil
         :value   (irr-cpp-const-expr)))

(fty::defprod cpp-enum-decl
  :short "Fixtype of C++ enum declarations [C++23:9.7.1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "An enum declaration: @('enum [class|struct] [name] [: base-type] { body }').
     @('classp') is @('t') for @('enum class') or @('enum struct').
     @('name') is @('nil') for anonymous enums.
     @('base-p') is @('t') iff an explicit base type is given."))
  ((classp  bool)
   (name    ident-option)
   (base-p  bool)
   (base    cpp-type-spec)
   (body    cpp-enumerator-list))
  :pred cpp-enum-decl-p
  :layout :fulltree)

(defirrelevant irr-cpp-enum-decl
  :short "An irrelevant C++ enum declaration."
  :type cpp-enum-decl-p
  :body (make-cpp-enum-decl
         :classp nil
         :name   nil
         :base-p nil
         :base   (irr-cpp-type-spec)
         :body   nil))

;;;;;;;;;;;;;;;;;;;;
;; Using Declarations
;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum cpp-using-decl
  :short "Fixtype of C++ using declarations [C++23:9.9]."
  :long
  (xdoc::topstring
   (xdoc::p
    "A @('using') declaration at class or namespace scope.
     The @(':alias') variant is a type alias: @('using Name = TypeSpec;').
     The @(':name') variant imports a name: @('using ns::Foo;'),
     represented as a @(tsee cpp-type-spec)."))
  (:alias ((alias ident)
           (type  cpp-type-spec)))   ; using Alias = Type;
  (:name  ((name  cpp-type-spec)))   ; using ns::Foo;
  :pred cpp-using-decl-p
  :layout :fulltree)

(defirrelevant irr-cpp-using-decl
  :short "An irrelevant C++ using declaration."
  :type cpp-using-decl-p
  :body (make-cpp-using-decl-name :name (irr-cpp-type-spec)))

(fty::deftagsum cpp-member-decl
  :short "Fixtype of C++ class member declarations."
  :long
  (xdoc::topstring
   (xdoc::p
    "A member declaration in a class body is one of:
     an access specifier label (@('public:')),
     a field declaration (@('int x;')),
     or a method declaration (@('void foo(int a, double b) const noexcept;')
     possibly with an inline body).
     [C++23:11.4].")
   (xdoc::p
    "For the @(':method') variant, @('body-p') is @('t') iff the method has
     an inline body @('{ ... }').  When @('body-p') is @('nil') the
     @('body') field is the empty list."))
  (:access
   ((spec cpp-access-spec)))
  (:field
   ((type-name  cpp-type-spec)
    (field-name ident)
    (staticp    bool)
    (mutablep   bool)
    (constexprp bool)))
  (:method
   ((return-type     cpp-type-spec)
    (method-id       cpp-member-name)
    (params          cpp-param-list)
    (virtualp        bool)
    (const-qualp     bool)
    (noexcept-spec   cpp-noexcept-spec-option)
    (pure-virtualp   bool)
    (staticp         bool)
    (body-p          bool)
    (body            cpp-block-item-list)
    (destructorp     bool)
    (explicitp       bool)
    (constexprp      bool)
    (inlinep         bool)
    (ctor-init-p     bool)
    (ctor-init-list  cpp-ctor-init-list)))
  (:using-decl
   ((decl cpp-using-decl)))
  (:enum-decl
   ((def cpp-enum-decl)))
  (:friend
   ((subject cpp-type-spec)))
  (:typedef
   ((type cpp-type-spec)
    (name c$::ident)))
  (:static-assert
   ((cond cpp-expr)
    (msg-p bool)
    (msg   c$::ident)))
  (:attribute
   ((name  c$::ident)
    (arg-p bool)
    (arg   c$::ident)))
  :pred cpp-member-decl-p
  :layout :fulltree)

;;;;;;;;;;;;;;;;;;;;

(fty::deflist cpp-member-decl-list
  :short "Fixtype of lists of C++ class member declarations."
  :elt-type cpp-member-decl
  :true-listp t
  :elementp-of-nil nil
  :pred cpp-member-decl-listp)

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-cpp-member-decl
  :short "An irrelevant C++ member declaration."
  :type cpp-member-decl-p
  :body (cpp-member-decl-access (cpp-access-spec-public)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Base Class Specifiers
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod cpp-base-specifier
  :short "Fixtype of C++ base class specifiers."
  :long
  (xdoc::topstring
   (xdoc::p
    "A base class specifier appears in the @(':') clause after the class name:
     @('class D : public B').
     We capture the access specifier and the base class type [C++23:11.7].")
   (xdoc::p
    "The base class is represented as a @(tsee cpp-type-spec),
     supporting qualified names (@('public ns::Base'))
     and template instantiations (@('public Base<int>'))."))
  ((access     cpp-access-spec)
   (class-name cpp-type-spec))
  :pred cpp-base-specifier-p
  :layout :fulltree)

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-cpp-base-specifier
  :short "An irrelevant C++ base class specifier."
  :type cpp-base-specifier-p
  :body (make-cpp-base-specifier
         :access (cpp-access-spec-public)
         :class-name (irr-cpp-type-spec)))

;;;;;;;;;;;;;;;;;;;;

(fty::defoption cpp-base-specifier-option
  cpp-base-specifier
  :short "Fixtype of optional C++ base class specifiers."
  :long
  (xdoc::topstring
   (xdoc::p
    "A class may or may not have a base class specifier."))
  :pred cpp-base-specifier-option-p)

;;;;;;;;;;;;;;;;;;;;;

(fty::deflist cpp-base-specifier-list
  :short "Fixtype of lists of C++ base class specifiers."
  :long
  (xdoc::topstring
   (xdoc::p
    "A list of @(tsee cpp-base-specifier) values,
     representing the comma-separated list in a base clause
     @(': public B, private C') [C++23:11.7].
     An empty list means no base classes."))
  :elt-type cpp-base-specifier
  :true-listp t
  :elementp-of-nil nil
  :pred cpp-base-specifier-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod cpp-class-specifier
  :short "Fixtype of C++ class specifiers."
  :long
  (xdoc::topstring
   (xdoc::p
    "A class specifier introduces a class type [C++23:11.2]:
     @('class Foo : public Bar { public: int x; void foo(); }')."))
  ((key             cpp-class-key)
   (name            ident-option)
   (template-params cpp-template-param-list)
   (base            cpp-base-specifier-list)
   (members         cpp-member-decl-list))
  :pred cpp-class-specifier-p
  :layout :fulltree)

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-cpp-class-specifier
  :short "An irrelevant C++ class specifier."
  :type cpp-class-specifier-p
  :body (make-cpp-class-specifier
         :key (cpp-class-key-class)
         :name nil
         :template-params nil
         :base nil
         :members nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Top-Level Declarations, Namespace Definitions, and Translation Units
;; (mutually recursive: namespace-def contains top-level-decl-list, and
;;  top-level-decl can be a namespace-def)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftypes cpp-top-level-types
  :short "Mutually recursive fixtypes for C++ top-level declarations
          and namespace definitions."
  :long
  (xdoc::topstring
   (xdoc::p
    "These types are mutually recursive because a @(tsee cpp-namespace-def)
     has a @(tsee cpp-top-level-decl-list) body, and a
     @(tsee cpp-top-level-decl) may be a @(tsee cpp-namespace-def)."))

  (fty::defprod cpp-namespace-def
    :short "Fixtype of C++ namespace definitions (with body) [C++23:9.8]."
    :long
    (xdoc::topstring
     (xdoc::p
      "A complete namespace definition: kind, optional @('inline') qualifier,
       and the body as a list of top-level declarations."))
    ((kind    cpp-namespace-kind)
     (inlinep bool)
     (body    cpp-top-level-decl-list))
    :pred cpp-namespace-def-p
    :layout :fulltree
    :measure (two-nats-measure (acl2-count x) 1))

  (fty::deftagsum cpp-top-level-decl
    :short "Fixtype of C++ top-level declarations."
    :long
    (xdoc::topstring
     (xdoc::p
      "A top-level declaration that can appear in a namespace or translation
       unit: a namespace definition, class definition, using declaration,
       enum definition, an empty declaration (@(';')),
       a function/variable declaration, an extern linkage block,
       a namespace alias, a module declaration, an import declaration,
       or an explicit template specialization."))
    (:namespace-def  ((def  cpp-namespace-def)))
    (:class-def      ((def  cpp-class-specifier)))
    (:using-decl     ((decl cpp-using-decl)))
    (:enum-def       ((def  cpp-enum-decl)))
    (:static-assert  ((cond cpp-expr)
                      (msg-p bool)
                      (msg   c$::ident)))
    (:empty          ())
    (:func-or-var-decl ((decl cpp-member-decl)))
    (:extern-linkage ((linkage c$::stringlit)
                      (body    cpp-top-level-decl-list)))
    (:module-decl    ((decl cpp-module-decl)))
    (:import-decl    ((decl cpp-import-decl)))
    (:namespace-alias        ((decl cpp-namespace-alias)))
    (:template-specialization ((decl cpp-top-level-decl)))
    (:template-decl ((params cpp-template-param-list) (decl cpp-top-level-decl)))
    :pred cpp-top-level-decl-p
    :layout :fulltree
    :measure (two-nats-measure (acl2-count x) 1))

  (fty::deflist cpp-top-level-decl-list
    :short "Fixtype of lists of C++ top-level declarations."
    :elt-type cpp-top-level-decl
    :true-listp t
    :elementp-of-nil nil
    :pred cpp-top-level-decl-listp
    :measure (two-nats-measure (acl2-count x) 0)))

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-cpp-namespace-def
  :short "An irrelevant C++ namespace definition."
  :type cpp-namespace-def-p
  :body (make-cpp-namespace-def
         :kind    (cpp-namespace-kind-anonymous)
         :inlinep nil
         :body    nil))

(defirrelevant irr-cpp-top-level-decl
  :short "An irrelevant C++ top-level declaration."
  :type cpp-top-level-decl-p
  :body (cpp-top-level-decl-empty))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Translation Units
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod cpp-translation-unit
  :short "Fixtype of C++ translation units."
  :long
  (xdoc::topstring
   (xdoc::p
    "A translation unit is the top-level compilation unit [C++23:5].
     It is represented as a list of top-level declarations."))
  ((decls cpp-top-level-decl-list))
  :pred cpp-translation-unit-p
  :layout :fulltree)

(defirrelevant irr-cpp-translation-unit
  :short "An irrelevant C++ translation unit."
  :type cpp-translation-unit-p
  :body (make-cpp-translation-unit :decls nil))
