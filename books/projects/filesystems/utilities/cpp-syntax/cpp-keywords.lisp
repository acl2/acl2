; C++ Syntax Extension for ACL2 Kestrel C Library
;
; This book defines the C++ keywords:
; the additional keywords that C++ introduces beyond C23.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "CPP")

(include-book "kestrel/c/language/keywords" :dir :system)

(include-book "std/util/defval" :dir :system)

(in-theory (disable mv-nth))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ cpp-keywords
  :parents (cpp-syntax)
  :short "C++ keywords."
  :long
  (xdoc::topstring
   (xdoc::p
    "We define the C++ keywords — the keywords that C++ introduces
     beyond those already in C23.
     Note that many C++ keywords overlap with C23 keywords
     (e.g., @('bool'), @('true'), @('false'), @('nullptr'),
     @('static_assert'), @('alignas'), @('alignof')),
     so those are not included here.")
   (xdoc::p
    "Because the C lexer in @(see c$::lexer) only knows about C keywords,
     C++ keywords arrive at the parser as @(see c$::token-ident) tokens,
     not @(see c$::token-keyword) tokens.
     Our C++ parser helpers therefore check identifiers by name
     rather than using @(tsee c$::token-keywordp)."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *cpp-only-keywords*
  :short "C++ keywords not present in C23 [C++23:5.11]."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the C++ keywords that are not already C23 keywords.
     Keywords shared with C23 (such as @('bool'), @('true'), @('nullptr'),
     @('alignas'), @('static_assert'), @('thread_local'), @('typeof'))
     are excluded because the C$ lexer already handles them.")
   (xdoc::p
    "Organized by category for clarity:
     OOP, memory management, exceptions, types, casts, coroutines,
     modules, concepts, alternative tokens."))
  '(;; Object-oriented programming
    "class"
    "namespace"
    "template"
    "typename"
    "operator"
    "public"
    "private"
    "protected"
    "virtual"
    "explicit"
    "friend"
    "mutable"
    "this"
    "using"
    ;; Memory management
    "new"
    "delete"
    ;; Exceptions
    "catch"
    "throw"
    "try"
    "noexcept"
    ;; Types
    "wchar_t"
    "char8_t"
    "char16_t"
    "char32_t"
    "decltype"
    ;; Casts
    "const_cast"
    "dynamic_cast"
    "static_cast"
    "reinterpret_cast"
    ;; Modern C++ (C++11 onwards)
    "typeid"
    "override"
    ;; C++20 coroutines
    "co_await"
    "co_return"
    "co_yield"
    ;; C++20 concepts
    "concept"
    "requires"
    ;; C++20 consteval/constinit
    "consteval"
    "constinit"
    ;; C++20 modules
    "export"
    "module"
    "import"
    ;; Alternative token representations [C++23:5.5]
    "and"
    "and_eq"
    "bitand"
    "bitor"
    "compl"
    "not"
    "not_eq"
    "or"
    "or_eq"
    "xor"
    "xor_eq")

  ///

  (assert-event (string-listp *cpp-only-keywords*))
  (assert-event (no-duplicatesp-equal *cpp-only-keywords*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *cpp-keywords*
  :short "All keywords for a C++ parser: union of C23 and C++-only keywords."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the complete list of keywords for parsing C++,
     combining the C23 standard keywords with the C++-only keywords."))
  (union-equal c::*keywords-c23* *cpp-only-keywords*)
  ///
  (assert-event (string-listp *cpp-keywords*))
  (assert-event (no-duplicatesp-equal *cpp-keywords*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define cpp-only-keyword-p (s)
  :guard (stringp s)
  :returns (yes/no booleanp)
  :short "Check whether a string is a C++-only keyword."
  :long
  (xdoc::topstring
   (xdoc::p
    "Returns @('t') iff the string is in @(tsee *cpp-only-keywords*),
     i.e., it is a keyword in C++ but not in C23."))
  (if (member-equal s *cpp-only-keywords*) t nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define cpp-keyword-p (s)
  :guard (stringp s)
  :returns (yes/no booleanp)
  :short "Check whether a string is a C++ keyword (C23 or C++-only)."
  :long
  (xdoc::topstring
   (xdoc::p
    "Returns @('t') iff the string is in @(tsee *cpp-keywords*),
     i.e., it is a keyword in C++ (whether or not it is also a C23 keyword)."))
  (if (member-equal s *cpp-keywords*) t nil))
