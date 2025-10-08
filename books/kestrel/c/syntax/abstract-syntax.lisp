; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "abstract-syntax-trees")
(include-book "abstract-syntax-irrelevants")
(include-book "code-ensembles")
(include-book "abstract-syntax-make-self")
(include-book "abstract-syntax-operations")
(include-book "purity")
(include-book "standard")
(include-book "ascii-identifiers")
(include-book "type-specifier-lists")
(include-book "storage-specifier-lists")
(include-book "abstraction-mapping")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ abstract-syntax
  :parents (syntax-for-tools)
  :short "An abstract syntax of C for use by tools."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(see syntax-for-tools) for background.")
   (xdoc::p
    "We define abstract syntax trees (ASTs),
     and operations on them.")
   (xdoc::p
    "We have also started defining a syntax abstraction mapping
     from the "
    (xdoc::seetopic "concrete-syntax" "concrete syntax")
    " to this abstract syntax.
     This is work in progress.")
   (xdoc::p
    "We define code ensembles as consisting of
     top-level ASTs and "
    (xdoc::seetopic "implementation-environments" "implementation environments")
    ", which are the entities manipulated by some of our tools.")
   (xdoc::p
    "We also provide make-self functions (via @(tsee fty::defmake-self))
     for code ensembles and contained ASTs."))
  :order-subtopics (abstract-syntax-trees
                    abstract-syntax-irrelevants
                    code-ensembles
                    make-self-code-ensemble
                    abstract-syntax-operations
                    purity
                    standard
                    ascii-identifiers
                    type-specifier-lists
                    storage-specifier-lists
                    abstraction-mapping))
