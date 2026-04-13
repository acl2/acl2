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
(include-book "abstract-syntax-derived-fixtypes")
(include-book "abstract-syntax-structural-operations")
(include-book "abstract-syntax-constructors")
(include-book "abstract-syntax-matching-operations")

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
     and by some structural operations on ASTs.")
   (xdoc::p
    "We may generalize this abstract syntax
     to encompass untyped and type-erased Remora,
     or we might define alternative abstract syntax for those,
     with suitable mappings."))
  :order-subtopics (abstract-syntax-trees
                    abstract-syntax-derived-fixtypes
                    abstract-syntax-structural-operations
                    abstract-syntax-constructors
                    abstract-syntax-matching-operations))
