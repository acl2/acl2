; C++ Syntax Extension for ACL2 Kestrel C Library
;
; Top-level book: includes all books in the cpp-syntax extension.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "CPP")

(include-book "cpp-keywords")
(include-book "cpp-abstract-syntax")
(include-book "cpp-token-utilities")
(include-book "cpp-parser")
(include-book "cpp-expr-parser")
(include-book "cpp-member-full")
(include-book "cpp-top-level-parser")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc cpp-syntax
  :parents (c$::syntax-for-tools)
  :short "C++ syntax extension for the Kestrel C library."
  :long
  (xdoc::topstring
   (xdoc::p
    "This library extends the Kestrel C library's syntax infrastructure
     (@(see c$::syntax-for-tools)) to support C++ constructs.
     It is organized as certifiable ACL2 books in the @('CPP') package,
     mirroring the pattern used by the @('C2C') transformation package.")
   (xdoc::p
    "The library consists of the following books, in dependency order:")
   (xdoc::ul
    (xdoc::li "@(see cpp-keywords): the list of C++-only keyword strings
               and the predicate @('cpp-only-keyword-p')")
    (xdoc::li "@(see cpp-abstract-syntax): fixtypes for C++ AST nodes —
               access specifiers, type specifiers, typed parameters,
               template parameters, class specifiers, namespace definitions,
               operator function identifiers, lambda captures,
               coroutine/exception/module constructs,
               member declarations (fields, methods, using-aliases, enums,
               access labels), top-level declarations, and translation units")
    (xdoc::li "@(see cpp-token-utilities): predicates for classifying
               C++ keyword tokens (@('token-cpp-kw-p')) and
               access-specifier tokens")
    (xdoc::li "@(see cpp-parser): recursive-descent parsers for
               type specifiers, template parameters, parameter lists,
               operator function ids, class/namespace/enum/using headers,
               and noexcept specifiers")
    (xdoc::li "cpp-expr-parser: recursive-descent parsers for
               all C++ expressions, all statement forms
               (including @('try')/@('catch'), coroutine @('co_yield')/@('co_return'),
               and range-based @('for')), lambda expressions with capture lists,
               constructor initializer lists, and class bodies with inline
               member definitions (@('parse-cpp-class-specifier-full'))")
    (xdoc::li "@(see cpp-top-level-parser): the top-level dispatch loop —
               @('parse-cpp-translation-unit') iterates over top-level
               declarations including namespace definitions (with full bodies),
               class definitions (with inline method bodies),
               @('using') declarations and type aliases,
               @('enum')/@('enum class') declarations,
               @('static_assert'), and empty declarations"))
   (xdoc::p
    "Known remaining gaps (constructs not yet parsed):
     @('friend') declarations,
     @('decltype') in type specifiers,
     @('concept')/@('requires'),
     explicit template specializations,
     namespace aliases,
     and module/import/export declarations.")))