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
(include-book "abstract-syntax-operations")
(include-book "abstraction-mapping")
(include-book "code-ensembles")

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
    ", which are the entities manipulated by some of our tools."))
  :order-subtopics (abstract-syntax-trees
                    abstract-syntax-irrelevants
                    abstract-syntax-operations
                    abstraction-mapping
                    code-ensembles))
