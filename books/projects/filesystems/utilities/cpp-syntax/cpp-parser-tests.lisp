; C++ Parser Tests
;
; Tests for new parsing features added in Phase 3:
;   co_yield / co_return statements, constructor/destructor/friend/typedef/
;   static_assert/attribute member declarations, decltype type specifier.

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

; Test 5: parse a struct with constructor (with ctor-init list and inline body),
; destructor, constexpr method, friend class, typedef, static_assert, attribute,
; and array field.

(test-parse-cpp
 parse-cpp-class-specifier-full
 "struct Foo { \
explicit Foo ( int x ) : x_ ( x ) { } \
~Foo ( ) ; \
constexpr int f ( ) const ; \
friend class Bar ; \
typedef int MyInt ; \
static_assert ( 1 ) ; \
[[ nodiscard ]] int g ( ) ; \
int a [ 10 ] ; \
}")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test 6a: co_return statement with expression.

(test-parse-cpp
 parse-cpp-stmt
 "co_return 42 ;")

; Test 6b: co_yield statement.

(test-parse-cpp
 parse-cpp-stmt
 "co_yield x ;")

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
