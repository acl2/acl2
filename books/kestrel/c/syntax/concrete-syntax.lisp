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
(include-book "files")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc concrete-syntax
  :parents (syntax-for-tools)
  :short "A formulation of the concrete syntax of C for use by tools."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(see syntax-for-tools) for background.")
   (xdoc::p
    "The concrete syntax of C is defined in [C].
     Here we provide a formulation of the concrete syntax of C
     that is tailored to tools that manipulate C code,
     and in particular that matches the abstract syntax
     defined in @(see abstract-syntax).")
   (xdoc::p
    "We start with an ABNF grammar that is based on the grammar in [C],
     but is not identical to that grammar because its purpose is
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
     We are not defining a different concrete syntax of C here.
     However, we are instantiating certain aspects of the concrete syntax
     which [C] leaves open, such as the exact character set used.")
   (xdoc::p
    "We plan to add a parser and a pretty-printer.")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define grammar-character-p ((char natp))
  :returns (yes/no booleanp)
  :short "Check if a character (code) is valid according to the ABNF grammar."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is based on the definition of @('character') in the ABNF grammar.
     At some point we should prove that
     this definition is consistent with that ABNF grammar rule."))
  (or (and (<= 9 char) (<= char 13))
      (and (<= 32 char) (<= char 126))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist grammar-character-listp (x)
  :guard (nat-listp x)
  :short "Check if all the characters (codes) in a list
          are valid according to the ABNF grammar."
  :long
  (xdoc::topstring
   (xdoc::p
    "This lifts @(tsee grammar-character-p) to lists of natural numbers."))
  (grammar-character-p x))
