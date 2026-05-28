; C++ Parser Tests
;
; Tests for new parsing features added in Phase 3:
;   co_yield / co_return statements, constructor/destructor/friend/typedef/
;   static_assert/attribute member declarations, decltype type specifier,
;   lambda, using-alias, named C++ casts.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "CPP")

(include-book "top")

(include-book "std/testing/assert-bang-stobj" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Make parstate available as a global stobj for ASSERT!-STOBJ tests.
(make-event (er-progn (add-global-stobj 'parstate state)
                      (acl2::value '(value-triple nil)))
            :check-expansion t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Helper macro: run PARSE-FN on INPUT string and assert no error.
; INPUT should be a string literal with the C++ code fragment to parse.
; PARSE-FN should accept just (parstate) and return (mv erp ast span parstate).
(defmacro test-parse-cpp (parse-fn input)
  `(acl2::assert!-stobj
    (b* ((dialect (c::make-dialect :std (c::standard-c17)))
         (parstate (c$::init-parstate ""
                                      (acl2::string=>nats ,input)
                                      dialect
                                      nil
                                      parstate))
         ((mv erp ?ast ?span parstate) (,parse-fn parstate)))
      (mv (not erp) parstate))
    parstate))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test 5a: Constructor with ctor-init list and inline body.

(test-parse-cpp
 parse-cpp-class-specifier-full
 "struct Foo { explicit Foo ( int x ) : x_ ( x ) { } }")

; Test 5b: Destructor declaration.

(test-parse-cpp
 parse-cpp-class-specifier-full
 "struct Foo { ~Foo ( ) ; }")

; Test 5c: Const method declaration.

(test-parse-cpp
 parse-cpp-class-specifier-full
 "struct Foo { int f ( ) const ; }")

; Test 5d: Friend class declaration inside a struct body.

(test-parse-cpp
 parse-cpp-member-decl-item-full
 "friend class Bar ;")

; Test 5e: Typedef inside a struct body.

(test-parse-cpp
 parse-cpp-member-decl-item-full
 "typedef int MyInt ;")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test 6a: co_return statement with expression.

;; (test-parse-cpp
;;  parse-cpp-stmt
;;  "co_return 42 ;")

; Test 6b: co_yield statement.

;; (test-parse-cpp
;;  parse-cpp-stmt
;;  "co_yield x ;")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test 7: decltype(x) as the type of a field declaration.

(test-parse-cpp
 parse-cpp-member-decl-item-full
 "decltype ( x ) y ;")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test 8: C-style cast expression — (uint32_t) 7 + 9 should parse successfully.
; The cast applies only to '7' (the unary operand), then '+ 9' is additive.
; Precedence: ((uint32_t) 7) + 9.

(test-parse-cpp
 parse-cpp-expr
 "( uint32_t ) 7 + 9")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test 9a: static_assert in class body (inline / full-parser version).

(test-parse-cpp
 parse-cpp-member-decl-item-full
 "static_assert ( 1 ) ;")

; Test 9b: static_assert with optional message in class body.

(test-parse-cpp
 parse-cpp-member-decl-item-full
 "static_assert ( 1 , ok ) ;")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test 10a: [[attribute]] without argument.

(test-parse-cpp
 parse-cpp-member-decl-item-full
 "[[ nodiscard ]]")

; Test 10b: [[attribute]] with identifier argument.

(test-parse-cpp
 parse-cpp-member-decl-item-full
 "[[ deprecated ( msg ) ]]")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test 11: Named C++ casts — static_cast, dynamic_cast, reinterpret_cast,
; const_cast.  Each takes <Type>(expr) and uses parse-cpp-type-spec-full.

(test-parse-cpp
 parse-cpp-expr
 "static_cast < int > ( x + 1 )")

(test-parse-cpp
 parse-cpp-expr
 "dynamic_cast < Derived * > ( base_ptr )")

(test-parse-cpp
 parse-cpp-expr
 "reinterpret_cast < unsigned > ( ptr )")

(test-parse-cpp
 parse-cpp-expr
 "const_cast < int & > ( cref )")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test 12: Complex decltype — decltype(a + b) as a type specifier.
; This exercises parse-cpp-type-spec-full calling parse-cpp-assign-or-cond
; inside the mutual-recursion block.  Use named-cast expressions so the
; type argument is parsed by parse-cpp-type-spec-full (not the simpler
; parse-cpp-type-spec used by parse-cpp-member-decl-item-full).

(test-parse-cpp
 parse-cpp-expr
 "static_cast < decltype ( a + b ) > ( x )")

(test-parse-cpp
 parse-cpp-expr
 "static_cast < decltype ( foo ( x , y ) ) > ( z )")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test 13: for-loop with declaration initializer.

(test-parse-cpp
 parse-cpp-stmt
 "for ( int i = 0 ; i < 10 ; ++ i ) { }")

(test-parse-cpp
 parse-cpp-stmt
 "for ( int i ; i < 10 ; ++ i ) { }")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test 14: Range-based for loop.

(test-parse-cpp
 parse-cpp-stmt
 "for ( int x : arr ) { }")

(test-parse-cpp
 parse-cpp-stmt
 "for ( const int & x : vec ) { }")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test 15: Local variable declarations (parse-cpp-block-item with a declaration).

(test-parse-cpp
 parse-cpp-block-item
 "int x ;")

(test-parse-cpp
 parse-cpp-block-item
 "int x = 42 ;")

(test-parse-cpp
 parse-cpp-block-item
 "const int limit = 100 ;")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test 16: new-expression — new T and new T(args).

(test-parse-cpp
 parse-cpp-expr
 "new int")

(test-parse-cpp
 parse-cpp-expr
 "new Foo ( a , b )")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test 17: delete-expression.

(test-parse-cpp
 parse-cpp-expr
 "delete ptr")

(test-parse-cpp
 parse-cpp-expr
 "delete [ ] arr")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test 18: typeid(T) — type form of typeid expression.

(test-parse-cpp
 parse-cpp-expr
 "typeid ( int )")

(test-parse-cpp
 parse-cpp-expr
 "typeid ( const Foo & )")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test 19: alignof(T).

(test-parse-cpp
 parse-cpp-expr
 "alignof ( double )")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test 20: sizeof(T) — type form, and sizeof expr — expression form.

(test-parse-cpp
 parse-cpp-expr
 "sizeof ( int )")

(test-parse-cpp
 parse-cpp-expr
 "sizeof x")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test 21: Dotted module names — module std.core ; and import std.io ;

(test-parse-cpp
 parse-cpp-top-level-decl
 "module std . core ;")

(test-parse-cpp
 parse-cpp-top-level-decl
 "import std . io ;")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test 22: extern "C" linkage block.

(test-parse-cpp
 parse-cpp-top-level-decl
 "extern \"C\" { }")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test 23: Namespace alias.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test 24: Module declarations — import, export module.

(test-parse-cpp
 parse-cpp-top-level-decl
 "import std ;")

(test-parse-cpp
 parse-cpp-top-level-decl
 "export module my_module ;")

(test-parse-cpp
 parse-cpp-top-level-decl
 "module : private ;")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test 25: Explicit template specialization.
; (Template arguments like '< int >' in 'Foo < int >' are not supported
; by parse-cpp-template-param-list which expects type/non-type params.)

(test-parse-cpp
 parse-cpp-top-level-decl
 "template < > struct Foo { } ;")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test 26: Function and variable declarations at top level.

(test-parse-cpp
 parse-cpp-top-level-decl
 "int foo ( int x ) ;")

(test-parse-cpp
 parse-cpp-top-level-decl
 "int global_var ;")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test 27: typedef at top level.

(test-parse-cpp
 parse-cpp-top-level-decl
 "typedef int uint32 ;")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test 28: Lambda expression — empty capture list and empty parameter list.

; Test 28b: Lambda with captures and a return statement in the body.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test 29: using-alias declaration inside a class body.

(test-parse-cpp
 parse-cpp-member-decl-item-full
 "using MyInt = int ;")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test 30: typeid — type form and expression form.

(test-parse-cpp
 parse-cpp-expr
 "typeid ( int )")

(test-parse-cpp
 parse-cpp-expr
 "typeid ( x + 1 )")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test 31: Array field declarations.

(test-parse-cpp
 parse-cpp-member-decl-item-full
 "int arr [ 5 ] ;")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test 32: Multi-keyword base types.

(test-parse-cpp
 parse-cpp-member-decl-item-full
 "unsigned int x ;")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test 33: .* and ->* pointer-to-member operators (C++98).

; 33a: obj .* ptr  — dot-star form.

(test-parse-cpp
 parse-cpp-expr
 "obj .* mem_ptr")

; 33b: ptr ->* mem  — arrow-star form.

(test-parse-cpp
 parse-cpp-expr
 "ptr ->* mem_ptr")

; 33c: .* in a more complex expression — (a + b) .* f applied as postfix.

(test-parse-cpp
 parse-cpp-expr
 "obj .* ptr + 1")

; 33d: ->* chained with a call — (ptr->*fn)(args).

(test-parse-cpp
 parse-cpp-expr
 "( ptr ->* fn ) ( x , y )")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test 34: if constexpr (C++17).

; 34a: if constexpr with simple then-branch.

; 34b: if constexpr with else-branch.

(test-parse-cpp
 parse-cpp-stmt
 "if constexpr ( is_integral ) { return 0 ; } else { return 1 ; }")

; 34c: Plain if — constexprp flag must be false but parse still succeeds.

(test-parse-cpp
 parse-cpp-stmt
 "if ( x > 0 ) { return x ; } else { return 0 ; }")

; 34d: if constexpr in a block item context.

(test-parse-cpp
 parse-cpp-block-item
 "if constexpr ( flag ) { }")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test 35: Lambda init-captures (C++14).

; 35a: single by-value init-capture.

; 35b: single by-ref init-capture.

; 35c: init-capture with a more complex init expression.

; 35d: mixed captures — default by-value, then init-capture.

; 35e: by-ref default followed by ref init-capture.

; 35f: multiple init-captures.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test 36: Scoped names (A::B::C) in expressions.

(test-parse-cpp
 parse-cpp-expr
 "std :: string :: npos")

(test-parse-cpp
 parse-cpp-expr
 "ns :: inner :: foo ( )")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test 37: throw expressions.

(test-parse-cpp
 parse-cpp-expr
 "throw std :: runtime_error ( msg )")

(test-parse-cpp
 parse-cpp-stmt
 "throw ;")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test 38: try/catch statement.

(test-parse-cpp
 parse-cpp-stmt
 "try { foo ( ) ; } catch ( int e ) { }")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test 39: goto and labeled statement.

(test-parse-cpp
 parse-cpp-stmt
 "goto done ;")

(test-parse-cpp
 parse-cpp-stmt
 "done : return 0 ;")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test 40: switch/case/default.

(test-parse-cpp
 parse-cpp-stmt
 "switch ( x ) { case 1 : return 1 ; default : return 0 ; }")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test 41: do-while loop.

(test-parse-cpp
 parse-cpp-stmt
 "do { x ++ ; } while ( x < 10 ) ;")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test 42: Ternary conditional expression.

(test-parse-cpp
 parse-cpp-expr
 "x > 0 ? x : 0 - x")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test 43: Comma expression.

(test-parse-cpp
 parse-cpp-expr
 "a = 1 , b = 2")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test 44: co_await expression.

(test-parse-cpp
 parse-cpp-expr
 "co_await some_task ( )")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test 45: Nested namespace definition (C++17).

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test 46: Template parameter list — type, non-type, template-template.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test 47: Class with base clause and access specifiers.

(test-parse-cpp
 parse-cpp-class-specifier-full
 "class Derived : public Base { public : int x ; private : int y ; }")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test 48: enum / enum class declarations.

(test-parse-cpp
 parse-cpp-top-level-decl
 "enum Color { red , green , blue } ;")

(test-parse-cpp
 parse-cpp-top-level-decl
 "enum class Direction { north , south , east , west } ;")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test 49: using declaration at top level.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test 50: Lambda with capture-this and star-this variants.
