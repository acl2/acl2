; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "abstract-syntax-trees")
(include-book "abstract-syntax-constructors")
(include-book "abstract-syntax-derived-fixtypes")
(include-book "abstract-syntax-structurals")
(include-book "abstract-syntax-matching-operations")
(include-book "abstract-syntax-variable-operations")
(include-book "abstract-syntax-core")
(include-book "abstract-syntax-well-formed")
(include-book "character-literal-codes")
(include-book "desugaring")
(include-book "frame-flattening")
(include-book "fresh-variables")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ abstract-syntax
  :parents (remora)
  :short "Abstract syntax of Remora."
  :long
  (xdoc::topstring
   (xdoc::p
    "We define an abstract syntax for core typed Remora,
     consisting of algebraic data types for abstract syntax trees (ASTs),
     accompanied by some fixtypes derived from the AST fixtypes,
     and by operations organized into various groups.")
   (xdoc::p
    "We may generalize this abstract syntax
     to encompass untyped and type-erased Remora,
     or we might define alternative abstract syntax for those,
     with suitable mappings."))
  :order-subtopics (abstract-syntax-trees
                    abstract-syntax-constructors
                    abstract-syntax-derived-fixtypes
                    abstract-syntax-structurals
                    abstract-syntax-matching-operations
                    abstract-syntax-variable-operations
                    abstract-syntax-core
                    abstract-syntax-well-formed
                    character-literal-codes
                    desugaring
                    frame-flattening
                    fresh-variables))
