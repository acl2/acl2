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
     exception handlers, module/import declarations, and coroutine keywords.")
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
  (:bool ((value bool)))
  (:ident ((name ident)))
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
;; Type Specifiers
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftypes cpp-type-spec-types
  :short "Mutually recursive fixtypes for C++ type specifiers."
  :long
  (xdoc::topstring
   (xdoc::p
    "A C++ type specifier represents the structure of a type expression.
     Types can be simple names, qualified names (@('A::B')),
     template instantiations (@('vector<int>')),
     pointers, references, and cv-qualified types [C++23:9.2]."))

  (fty::deftagsum cpp-type-spec
    :short "Fixtype of C++ type specifiers."
    (:name ((id ident)))
    (:qualified ((scope ident) (inner cpp-type-spec)))
    (:template-inst ((template cpp-type-spec)
                     (args cpp-type-spec-list)))
    (:pointer ((pointee cpp-type-spec) (constp bool)))
    (:lref ((base cpp-type-spec)))
    (:rref ((base cpp-type-spec)))
    (:const-qual ((base cpp-type-spec)))
    (:volatile-qual ((base cpp-type-spec)))
    :pred cpp-type-spec-p
    :measure (two-nats-measure (acl2-count x) 1))

  (fty::deflist cpp-type-spec-list
    :short "Fixtype of lists of C++ type specifiers."
    :elt-type cpp-type-spec
    :true-listp t
    :elementp-of-nil nil
    :pred cpp-type-spec-listp
    :measure (two-nats-measure (acl2-count x) 0)))

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-cpp-type-spec
  :short "An irrelevant C++ type specifier."
  :type cpp-type-spec-p
  :body (make-cpp-type-spec-name :id (c$::irr-ident)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Typed Parameters
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod cpp-param
  :short "Fixtype of C++ typed parameters."
  :long
  (xdoc::topstring
   (xdoc::p
    "A function parameter consisting of a type specifier
     and an optional parameter name [C++23:9.3.4.6]."))
  ((type cpp-type-spec)
   (name ident-option))
  :pred cpp-param-p
  :layout :fulltree)

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-cpp-param
  :short "An irrelevant C++ parameter."
  :type cpp-param-p
  :body (make-cpp-param :type (irr-cpp-type-spec) :name nil))

;;;;;;;;;;;;;;;;;;;;

(fty::deflist cpp-param-list
  :short "Fixtype of lists of C++ typed parameters."
  :long
  (xdoc::topstring
   (xdoc::p
    "A list of @(tsee cpp-param) values representing
     a function parameter list."))
  :elt-type cpp-param
  :true-listp t
  :elementp-of-nil nil
  :pred cpp-param-listp)

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

(fty::deftagsum cpp-member-decl
  :short "Fixtype of C++ class member declarations."
  :long
  (xdoc::topstring
   (xdoc::p
    "A member declaration in a class body is one of:
     an access specifier label (@('public:')),
     a field declaration (@('int x;')),
     or a method declaration (@('void foo(int a, double b) const noexcept;')).
     [C++23:11.4].")
   (xdoc::p
    "Type specifiers are represented as @(tsee cpp-type-spec) values.
     Parameter lists are represented as @(tsee cpp-param-list) values.
     Initializers and default arguments are omitted."))
  (:access
   ((spec cpp-access-spec)))
  (:field
   ((type-name  cpp-type-spec)
    (field-name ident)
    (staticp    bool)
    (mutablep   bool)))
  (:method
   ((return-type   cpp-type-spec)
    (method-name   ident)
    (params        cpp-param-list)
    (virtualp      bool)
    (const-qualp   bool)
    (noexcept-spec cpp-noexcept-spec-option)
    (pure-virtualp bool)
    (staticp       bool)))
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

(fty::defprod cpp-class-specifier
  :short "Fixtype of C++ class specifiers."
  :long
  (xdoc::topstring
   (xdoc::p
    "A class specifier introduces a class type [C++23:11.2]:
     @('class Foo : public Bar { public: int x; void foo(); }').")
   (xdoc::p
    "The @(':key') field is @('class') or @('struct').")
   (xdoc::p
    "The @(':name') field is the optional class name
     (@('nil') for anonymous classes).")
   (xdoc::p
    "The @(':template-params') field holds the template parameter list
     if this class is a class template
     (@('template < ... > class Foo');
     empty list if not a template).")
   (xdoc::p
    "The @(':base') field is the list of base class specifiers
     (empty list means no base classes).
     Multiple inheritance is supported by having multiple entries.")
   (xdoc::p
    "The @(':members') field is the list of member declarations."))
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
         :base nil          ; empty base-specifier-list
         :members nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Namespace Definitions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum cpp-namespace-def
  :short "Fixtype of C++ namespace definition headers (simplified)."
  :long
  (xdoc::topstring
   (xdoc::p
    "A namespace definition begins with the @('namespace') keyword
     followed by an optional name [C++23:9.8].")
   (xdoc::p
    "We capture the header (the kind and name) separately from the body,
     since the body is a sequence of declarations that may recursively
     contain further C++ constructs.
     The body itself is not captured here.")
   (xdoc::p
    "Three kinds are supported:
     named (@('namespace Foo { ... }')),
     anonymous (@('namespace { ... }')),
     and nested (C++17: @('namespace A::B::C { ... }'))."))
  (:named
   ((name ident)))               ; e.g., Foo
  (:anonymous ())                ; namespace { ... }
  (:nested
   ((names ident-listp)))         ; e.g., (A B C) for 'namespace A::B::C'
  :pred cpp-namespace-def-p
  :layout :fulltree)

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-cpp-namespace-def
  :short "An irrelevant C++ namespace definition."
  :type cpp-namespace-def-p
  :body (cpp-namespace-def-anonymous))

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
  :layout :fulltree)

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-cpp-exception-handler
  :short "An irrelevant C++ exception handler."
  :type cpp-exception-handler-p
  :body (make-cpp-exception-handler
         :type-name (irr-cpp-type-spec)
         :param-name nil))

;;;;;;;;;;;;;;;;;;;;

(fty::deflist cpp-exception-handler-list
  :short "Fixtype of lists of C++ exception handler headers."
  :elt-type cpp-exception-handler
  :true-listp t
  :elementp-of-nil nil
  :pred cpp-exception-handler-listp)

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
   ((name    ident)   ; module name
    (exportp bool)))  ; 'export module name' ?
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
  ((name    ident)  ; module name to import
   (exportp bool)) ; 'export import name' ?
  :pred cpp-import-decl-p
  :layout :fulltree)

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-cpp-import-decl
  :short "An irrelevant C++ import declaration."
  :type cpp-import-decl-p
  :body (make-cpp-import-decl :name (c$::irr-ident) :exportp nil))

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
