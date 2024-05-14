; C Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "grammar")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc concrete-syntax-for-tools
  :parents (syntax-for-tools)
  :short "A formulation of the concrete syntax of C for use by tools."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(see syntax-for-tools) for background.")
   (xdoc::p
    "The concrete syntax of C is one, and it is defined in [C].
     Here we provide a particular formulation of the concrete syntax of C
     that is tailored to tools that manipulate C code,
     and in particular that matches the abstract syntax
     defined in @(see abstract-syntax-for-tools).")
   (xdoc::p
    "We start with an ABNF grammar that is based on the grammar in [C],
     but differs from that grammar because its purpose is
     to capture constructs both before and after preprocessing at the same time.
     Initially it actually only captures preprocessed code,
     but we plan to add a growing collection of preprocessing constructs.
     See @(see grammar).")
   (xdoc::p
    "We will complement the ABNF grammar with extra-grammatical predicates
     that specify additional constraints on the grammar,
     leading to a precise definition of the concrete syntax.")
   (xdoc::p
    "Note that this and [C] are just two different formulations
     (each formulation consisting of a grammar
     and of extra-grammatical requirements)
     of the same unique concrete syntax of C.
     We are not defining a different concrete syntax of C here.")
   (xdoc::p
    "We plan to add a parser and a pretty-printer.")))
