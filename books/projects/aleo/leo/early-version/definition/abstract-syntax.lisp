; Leo Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "LEO-EARLY")

(include-book "abstract-syntax-trees")
(include-book "programs")
(include-book "input-files")
(include-book "output-files")
(include-book "syntax-abstraction")
(include-book "input-syntax-abstraction")
(include-book "output-syntax-abstraction")
(include-book "parser-abstractor-interface")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ abstract-syntax
  :parents (language)
  :short "Abstract syntax of Leo."
  :long
  (xdoc::topstring
   (xdoc::p
    "The abstract syntax of Leo is
     a representation of the Leo constructs
     obtained by abstracting away some information from the "
    (xdoc::seetopic "concrete-syntax" "concrete syntax")
    ".")
   (xdoc::p
    "The definition of the abstract syntax consists of
     fixtypes that represent the constructs
     and an abstraction mapping from concrete to abstract syntax.")
   (xdoc::p
    "While the concrete syntax of Leo is prescribed by
     the ABNF grammar and visible to the user,
     the abstract syntax is internal to the ACL2 formalization:
     its purpose is to formalize
     static semantics and dynamic semantics
     more conveniently on abstract syntax than on concrete syntax;
     the chosen form of the abstract syntax, among many possible,
     is motivated by this purpose.")
   (xdoc::p
    "This ACL2 abstract syntax of Leo is similar to
     the Rust abstract syntax of Leo in the Leo compiler.
     However, the two serve slightly different purposes,
     and therefore they do not have to be necessarily in strict alignment.")))
