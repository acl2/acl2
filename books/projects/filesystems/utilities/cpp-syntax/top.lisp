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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc cpp-syntax
  :parents (c$::syntax-for-tools)
  :short "C++ syntax extension for the Kestrel C library."
  :long
  (xdoc::topstring
   (xdoc::p
    "This library extends the Kestrel C library's syntax infrastructure
     (@(see c$::syntax-for-tools)) to support C++ constructs.")
   (xdoc::p
    "The extension covers the following C++ features (Phase 1):")
   (xdoc::ul
    (xdoc::li "C++ keywords (@(see cpp-keywords))")
    (xdoc::li "C++ abstract syntax trees (@(see cpp-abstract-syntax)):
               access specifiers, template parameters, class specifiers,
               namespace definitions, operator function identifiers")
    (xdoc::li "C++ token utilities (@(see cpp-token-utilities)):
               predicates for identifying C++ keyword tokens")
    (xdoc::li "C++ parser (@(see cpp-parser)):
               recursive-descent parse functions for the above constructs"))
   (xdoc::p
    "The code is organized as certifiable ACL2 books in the CPP package.
     The package is defined in @('package.lsp') and mirrors the pattern
     used by the @('C2C') transformation package in the Kestrel C library.")
   (xdoc::p
    "Future phases will extend coverage to:
     inheritance and virtual dispatch,
     exceptions (@('try')/@('catch')/@('throw')),
     concepts (@('concept')/@('requires')),
     coroutines (@('co_await')/@('co_return')/@('co_yield')),
     and modules (@('module')/@('export')).")))
