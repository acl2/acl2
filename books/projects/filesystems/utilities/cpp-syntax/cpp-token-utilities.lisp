; C++ Syntax Extension for ACL2 Kestrel C Library
;
; This book defines utilities for checking C++ token types.
; Because C++ keywords arrive as identifier tokens (the C$ lexer does not
; know about C++ keywords), we need special predicates that check the
; unwrapped identifier string rather than using token-keywordp.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "CPP")

(include-book "cpp-keywords")

(include-book "kestrel/c/syntax/parser-states" :dir :system)

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
