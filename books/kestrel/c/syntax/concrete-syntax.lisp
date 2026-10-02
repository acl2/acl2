; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "file-paths")
(include-book "files")
(include-book "unicode-characters")
(include-book "grammar")
(include-book "grammar-operations")
(include-book "grammar-characters")
(include-book "positions")
(include-book "spans")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ concrete-syntax
  :parents (syntax-for-tools)
  :short "A formulation of the concrete syntax of C for use by tools."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(see syntax-for-tools) for background.")
   (xdoc::p
    "The concrete syntax of C is defined in [C17] and [C23].
     Here we provide a formulation of the concrete syntax of C
     that is tailored to tools that manipulate C code,
     and in particular that matches the abstract syntax
     defined in @(see abstract-syntax).")
   (xdoc::p
    "We start with file paths and files, as well as Unicode characters
     (which are actually more general notions than this C library).
     We formulate an ABNF grammar based on the grammar in [C17] and [C23],
     but is not identical to that grammar because
     it captures constructs both before and after preprocessing.")
   (xdoc::p
    "We will complement the ABNF grammar with extra-grammatical predicates
     that specify additional constraints on the grammar,
     leading to a precise definition of the concrete syntax.")
   (xdoc::p
    "Note that this and the one in the standard [C17] [C23]
     are just two different formulations
     (each formulation consisting of a grammar
     and of extra-grammatical requirements)
     of the same unique concrete syntax of C.
     We are not defining a different concrete syntax of C here.
     However, we are instantiating certain aspects of the concrete syntax
     which [C17] and [C23] leave open, such as the exact character set used."))
  :order-subtopics (file-paths
                    files
                    unicode-characters
                    grammar
                    grammar-operations
                    grammar-characters
                    positions
                    spans))
