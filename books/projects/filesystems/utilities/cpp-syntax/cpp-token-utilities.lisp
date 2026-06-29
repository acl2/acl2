; C++ Syntax Extension for ACL2 Kestrel C Library
;
; This book defines utilities for checking C++ token types.
; Because C++ keywords arrive as identifier tokens (the C$ lexer does not
; know about C++ keywords), we need special predicates that check the
; unwrapped identifier string rather than using token-keywordp.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "CPP")

(include-book "cpp-keywords")
(include-book "cpp-abstract-syntax")

(include-book "kestrel/c/syntax/parser-states" :dir :system)

;; Globally disable the forward-chaining token-kind splitter so that
;; downstream parsers use the targeted one-way lemmas instead.
(in-theory (disable c$::token-kind-possibilities))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ cpp-token-utilities
  :parents (cpp-syntax)
  :short "Utilities for checking C++ tokens."
  :long
  (xdoc::topstring
   (xdoc::p
    "The C$ lexer tokenizes C++ keywords as @(see c$::token-ident) tokens,
     not @(see c$::token-keyword) tokens,
     because the C$ lexer only knows about C (not C++) keywords.
     We provide predicates that check for C++ keywords by
     inspecting the unwrapped identifier string."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define token-cpp-kw-p ((token? token-optionp) kw)
  :guard (stringp kw)
  :returns (yes/no booleanp)
  :short "Check whether an optional token is a given C++ keyword."
  :long
  (xdoc::topstring
   (xdoc::p
    "C++ keywords arrive as @(see c$::token-ident) tokens
     since the C$ lexer does not know about C++ keywords.
     This predicate checks whether @('token?') is an identifier token
     whose unwrapped value equals the string @('kw')."))
  (and token?
       (token-case token? :ident)
       (equal (ident->unwrap (token-ident->ident token?))
              kw))
  :hooks nil

  ///

  (defrule non-nil-when-token-cpp-kw-p
    (implies (token-cpp-kw-p token? kw)
             token?)
    :rule-classes :forward-chaining))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define token-cpp-access-spec-p ((token? token-optionp))
  :returns (yes/no booleanp)
  :short "Check whether an optional token is a C++ access specifier."
  :long
  (xdoc::topstring
   (xdoc::p
    "Returns true if the token is one of
     @('public'), @('private'), or @('protected')."))
  (or (token-cpp-kw-p token? "public")
      (token-cpp-kw-p token? "private")
      (token-cpp-kw-p token? "protected"))
  ///
  (defrule non-nil-when-token-cpp-access-spec-p
    (implies (token-cpp-access-spec-p token?)
             token?)
    :rule-classes :forward-chaining))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define token-cpp-class-key-p ((token? token-optionp))
  :returns (yes/no booleanp)
  :short "Check whether an optional token is a C++ class key."
  :long
  (xdoc::topstring
   (xdoc::p
    "Returns true if the token is @('class') or @('struct').
     Note that @('struct') is a C keyword so it arrives as
     a @(see c$::token-keyword) token,
     while @('class') is a C++-only keyword that arrives as
     a @(see c$::token-ident) token."))
  (or (token-cpp-kw-p token? "class")
      (token-keywordp token? "struct"))
  ///
  (defrule non-nil-when-token-cpp-class-key-p
    (implies (token-cpp-class-key-p token?)
             token?)
    :rule-classes :forward-chaining))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define token-cpp-template-type-kw-p ((token? token-optionp))
  :returns (yes/no booleanp)
  :short "Check whether a token is @('typename') or @('class')
          (used as a type parameter introducer in a template parameter list)."
  (or (token-cpp-kw-p token? "typename")
      (token-cpp-kw-p token? "class"))
  ///
  (defrule non-nil-when-token-cpp-template-type-kw-p
    (implies (token-cpp-template-type-kw-p token?)
             token?)
    :rule-classes :forward-chaining))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define token-cpp-overloadable-op-p ((token? token-optionp))
  :returns (yes/no booleanp)
  :short "Check whether a token can be an overloadable operator symbol."
  :long
  (xdoc::topstring
   (xdoc::p
    "Returns true if the token is a punctuator or keyword that can follow
     the @('operator') keyword in an operator-function-id.
     This covers all overloadable operators listed in [C++23:12.5]."))
  (or ;; Arithmetic operators
      (token-punctuatorp token? "+")
      (token-punctuatorp token? "-")
      (token-punctuatorp token? "*")
      (token-punctuatorp token? "/")
      (token-punctuatorp token? "%")
      ;; Bitwise operators
      (token-punctuatorp token? "^")
      (token-punctuatorp token? "&")
      (token-punctuatorp token? "|")
      (token-punctuatorp token? "~")
      ;; Logical operators
      (token-punctuatorp token? "!")
      (token-punctuatorp token? "&&")
      (token-punctuatorp token? "||")
      ;; Shift operators
      (token-punctuatorp token? "<<")
      (token-punctuatorp token? ">>")
      ;; Comparison operators
      (token-punctuatorp token? "==")
      (token-punctuatorp token? "!=")
      (token-punctuatorp token? "<")
      (token-punctuatorp token? ">")
      (token-punctuatorp token? "<=")
      (token-punctuatorp token? ">=")
      ;; Spaceship operator (C++20)
      (token-punctuatorp token? "<=>")
      ;; Assignment operators
      (token-punctuatorp token? "=")
      (token-punctuatorp token? "+=")
      (token-punctuatorp token? "-=")
      (token-punctuatorp token? "*=")
      (token-punctuatorp token? "/=")
      (token-punctuatorp token? "%=")
      (token-punctuatorp token? "^=")
      (token-punctuatorp token? "&=")
      (token-punctuatorp token? "|=")
      (token-punctuatorp token? "<<=")
      (token-punctuatorp token? ">>=")
      ;; Increment and decrement
      (token-punctuatorp token? "++")
      (token-punctuatorp token? "--")
      ;; Access operators
      (token-punctuatorp token? "->")
      (token-punctuatorp token? "->*")
      ;; Comma
      (token-punctuatorp token? ",")
      ;; new and delete (arrive as identifiers)
      (token-cpp-kw-p token? "new")
      (token-cpp-kw-p token? "delete")
      ;; co_await (C++20)
      (token-cpp-kw-p token? "co_await"))
  ///
  (defrule non-nil-when-token-cpp-overloadable-op-p
    (implies (token-cpp-overloadable-op-p token?)
             token?)
    :rule-classes :forward-chaining))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define token-cpp-kw-string ((token? token-optionp))
  :guard (and token? (token-case token? :ident))
  :verify-guards nil
  :returns (kw stringp)
  :short "Extract the identifier string from a token that is a C++ keyword."
  :long
  (xdoc::topstring
   (xdoc::p
    "Given a token that is an @(see c$::token-ident),
     returns the unwrapped string.
     This is used to extract the keyword string from C++ keyword tokens
     (which arrive as identifiers)."))
  (b* ((ident (token-ident->ident (token-option-some->val token?)))
       (unwrap (ident->unwrap ident)))
    (if (stringp unwrap)
        unwrap
      ""))
  :hooks nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define token-cpp-noexcept-p ((token? token-optionp))
  :returns (yes/no booleanp)
  :short "Check whether an optional token is the @('noexcept') keyword."
  (token-cpp-kw-p token? "noexcept")
  ///
  (defrule non-nil-when-token-cpp-noexcept-p
    (implies (token-cpp-noexcept-p token?)
             token?)
    :rule-classes :forward-chaining))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define token-cpp-coroutine-kw-p ((token? token-optionp))
  :returns (yes/no booleanp)
  :short "Check whether an optional token is a C++ coroutine keyword."
  :long
  (xdoc::topstring
   (xdoc::p
    "Returns true if the token is one of
     @('co_return'), @('co_yield'), or @('co_await')."))
  (or (token-cpp-kw-p token? "co_return")
      (token-cpp-kw-p token? "co_yield")
      (token-cpp-kw-p token? "co_await"))
  ///
  (defrule non-nil-when-token-cpp-coroutine-kw-p
    (implies (token-cpp-coroutine-kw-p token?)
             token?)
    :rule-classes :forward-chaining))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; C++ Expression Operator Tables
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define token-to-cpp-infix-prec ((token? token-optionp))
  :returns (prec natp :rule-classes (:rewrite :type-prescription))
  :short "Pratt precedence level for a C++ infix operator token."
  :long
  (xdoc::topstring
   (xdoc::p
    "Returns @('0') if the token is not a recognized infix operator.
     Otherwise, returns a precedence level (higher = binds tighter):
     2 = assignment (right-assoc), 3 = conditional @('?:'),
     4 = @('||'), 5 = @('&&'), 6 = @('|'), 7 = @('^'), 8 = @('&'),
     9 = equality @('==') @('!='), 10 = relational, 11 = shift,
     12 = additive, 13 = multiplicative.")
   (xdoc::p
    "We treat @('=') and the compound assignments as level 2 right-assoc.
     We treat @('?') as level 3 (handled specially as a ternary)."))
  (cond
   ;; Assignment (level 2, right-assoc)
   ((or (token-punctuatorp token? "=")
        (token-punctuatorp token? "+=")
        (token-punctuatorp token? "-=")
        (token-punctuatorp token? "*=")
        (token-punctuatorp token? "/=")
        (token-punctuatorp token? "%=")
        (token-punctuatorp token? "&=")
        (token-punctuatorp token? "|=")
        (token-punctuatorp token? "^=")
        (token-punctuatorp token? "<<=")
        (token-punctuatorp token? ">>="))
    2)
   ;; Ternary (level 3)
   ((token-punctuatorp token? "?") 3)
   ;; Logical or
   ((token-punctuatorp token? "||") 4)
   ;; Logical and
   ((token-punctuatorp token? "&&") 5)
   ;; Bit or
   ((token-punctuatorp token? "|") 6)
   ;; Bit xor
   ((token-punctuatorp token? "^") 7)
   ;; Bit and
   ((token-punctuatorp token? "&") 8)
   ;; Equality
   ((or (token-punctuatorp token? "==")
        (token-punctuatorp token? "!="))
    9)
   ;; Relational
   ((or (token-punctuatorp token? "<")
        (token-punctuatorp token? ">")
        (token-punctuatorp token? "<=")
        (token-punctuatorp token? ">=")
        (token-punctuatorp token? "<=>"))
    10)
   ;; Shift
   ((or (token-punctuatorp token? "<<")
        (token-punctuatorp token? ">>"))
    11)
   ;; Additive
   ((or (token-punctuatorp token? "+")
        (token-punctuatorp token? "-"))
    12)
   ;; Multiplicative
   ((or (token-punctuatorp token? "*")
        (token-punctuatorp token? "/")
        (token-punctuatorp token? "%"))
    13)
   (t 0))
  :hooks nil
  ///
  (defthm token-to-cpp-infix-prec-positive-implies-token
    (implies (not (equal (token-to-cpp-infix-prec token?) 0))
             token?)
    :rule-classes :forward-chaining))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define token-is-cpp-right-assoc ((token? token-optionp))
  :returns (yes/no booleanp)
  :short "Whether an infix operator token is right-associative."
  :long
  (xdoc::topstring
   (xdoc::p
    "In C++, only the assignment operators (level 2) and the ternary
     @('?:') (level 3) are right-associative.  All other infix operators
     are left-associative."))
  (or (token-punctuatorp token? "=")
      (token-punctuatorp token? "+=")
      (token-punctuatorp token? "-=")
      (token-punctuatorp token? "*=")
      (token-punctuatorp token? "/=")
      (token-punctuatorp token? "%=")
      (token-punctuatorp token? "&=")
      (token-punctuatorp token? "|=")
      (token-punctuatorp token? "^=")
      (token-punctuatorp token? "<<=")
      (token-punctuatorp token? ">>=")
      (token-punctuatorp token? "?"))
  :hooks nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define token-to-cpp-infix-binop ((token? token-optionp))
  :guard (let ((p (token-to-cpp-infix-prec token?)))
           (and (>= p 4) (<= p 13)))
  :returns (op c$::binopp)
  :short "Map a non-assignment infix operator token to a @(tsee c$::binop)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This function handles infix operators at precedence levels 4-13.
     Assignment operators (level 2) and the ternary @('?') (level 3) are
     handled separately."))
  (cond
   ((token-punctuatorp token? "||")  (c$::binop-logor))
   ((token-punctuatorp token? "&&")  (c$::binop-logand))
   ((token-punctuatorp token? "|")   (c$::binop-bitior))
   ((token-punctuatorp token? "^")   (c$::binop-bitxor))
   ((token-punctuatorp token? "&")   (c$::binop-bitand))
   ((token-punctuatorp token? "==")  (c$::binop-eq))
   ((token-punctuatorp token? "!=")  (c$::binop-ne))
   ((token-punctuatorp token? "<")   (c$::binop-lt))
   ((token-punctuatorp token? ">")   (c$::binop-gt))
   ((token-punctuatorp token? "<=")  (c$::binop-le))
   ((token-punctuatorp token? ">=")  (c$::binop-ge))
   ((token-punctuatorp token? "<=>") (c$::binop-ge)) ; no spaceship in C; fold to ge
   ((token-punctuatorp token? "<<")  (c$::binop-shl))
   ((token-punctuatorp token? ">>")  (c$::binop-shr))
   ((token-punctuatorp token? "+")   (c$::binop-add))
   ((token-punctuatorp token? "-")   (c$::binop-sub))
   ((token-punctuatorp token? "*")   (c$::binop-mul))
   ((token-punctuatorp token? "/")   (c$::binop-div))
   ((token-punctuatorp token? "%")   (c$::binop-rem))
   (t (prog2$ (impossible) (c$::binop-add))))
  :guard-hints (("Goal" :in-theory (enable token-to-cpp-infix-prec)))
  :hooks nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define token-to-cpp-assign-op ((token? token-optionp))
  :guard (equal (token-to-cpp-infix-prec token?) 2)
  :returns (op cpp-assign-op-p)
  :short "Map an assignment operator token to a @(tsee cpp-assign-op)."
  (cond
   ((token-punctuatorp token? "=")   (cpp-assign-op-simple))
   ((token-punctuatorp token? "+=")  (cpp-assign-op-add))
   ((token-punctuatorp token? "-=")  (cpp-assign-op-sub))
   ((token-punctuatorp token? "*=")  (cpp-assign-op-mul))
   ((token-punctuatorp token? "/=")  (cpp-assign-op-div))
   ((token-punctuatorp token? "%=")  (cpp-assign-op-rem))
   ((token-punctuatorp token? "&=")  (cpp-assign-op-bitand))
   ((token-punctuatorp token? "|=")  (cpp-assign-op-bitor))
   ((token-punctuatorp token? "^=")  (cpp-assign-op-bitxor))
   ((token-punctuatorp token? "<<=") (cpp-assign-op-lshift))
   ((token-punctuatorp token? ">>=") (cpp-assign-op-rshift))
   (t (prog2$ (impossible) (cpp-assign-op-simple))))
  :guard-hints (("Goal" :in-theory (enable token-to-cpp-infix-prec)))
  :hooks nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define token-cpp-prefix-unop-p ((token? token-optionp))
  :returns (yes/no booleanp)
  :short "Whether the token is a C++ prefix unary operator."
  (or (token-punctuatorp token? "+")
      (token-punctuatorp token? "-")
      (token-punctuatorp token? "!")
      (token-punctuatorp token? "~")
      (token-punctuatorp token? "*")
      (token-punctuatorp token? "&"))
  ///
  (defrule non-nil-when-token-cpp-prefix-unop-p
    (implies (token-cpp-prefix-unop-p token?)
             token?)
    :rule-classes :forward-chaining))

(define token-to-cpp-prefix-unop ((token? token-optionp))
  :guard (token-cpp-prefix-unop-p token?)
  :returns (op c$::unopp)
  :short "Map a prefix unary operator token to a @(tsee c$::unop)."
  (cond
   ((token-punctuatorp token? "+") (c$::unop-plus))
   ((token-punctuatorp token? "-") (c$::unop-minus))
   ((token-punctuatorp token? "!") (c$::unop-lognot))
   ((token-punctuatorp token? "~") (c$::unop-bitnot))
   ((token-punctuatorp token? "*") (c$::unop-indir))
   ((token-punctuatorp token? "&") (c$::unop-address))
   (t (prog2$ (impossible) (c$::unop-plus))))
  :prepwork ((local (in-theory (enable token-cpp-prefix-unop-p))))
  :hooks nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define token-cpp-cast-kw-p ((token? token-optionp))
  :returns (yes/no booleanp)
  :short "Whether the token is one of the C++ @('xxx_cast') keywords or @('typeid')."
  (or (token-cpp-kw-p token? "static_cast")
      (token-cpp-kw-p token? "dynamic_cast")
      (token-cpp-kw-p token? "reinterpret_cast")
      (token-cpp-kw-p token? "const_cast")
      (token-cpp-kw-p token? "typeid"))
  ///
  (defrule non-nil-when-token-cpp-cast-kw-p
    (implies (token-cpp-cast-kw-p token?)
             token?)
    :rule-classes :forward-chaining))
