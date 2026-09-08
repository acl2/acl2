; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "abstract-syntax-formal-subset")
(include-book "abstract-syntax-formal-mapping-direct")
(include-book "abstract-syntax-formal-mapping-inverse")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ abstract-syntax-formal-subset-and-mapping
  :parents (abstract-syntax)
  :short "Subset of the abstract syntax that has a formal semantics,
          and mappings with the abstract syntax in the language formalization."
  :long
  (xdoc::topstring
   (xdoc::p
    "The "
    (xdoc::seetopic "c$::syntax-for-tools" "C syntax for tools")
    " is designed to cover all of C,
     but the "
    (xdoc::seetopic "c::language" "formal language definition")
    " only covers a subset of C.
     More precisely:
     the abstract syntax of the formal language definition
     is a subset of the abstract syntax for tools;
     the static semantics of C is defined for
     a subset of the latter abstract syntax;
     and the dynamic semantics of C is defined for
     a subset of the subset for which the static semantics is defined.
     Note how these subsets are linearly ordered.")
   (xdoc::p
    "Since the abstract syntax is large,
     we separate the subset and mapping into three components:
     subset, direct mapping, and inverse mapping."))
  :order-subtopics t
  :default-parent t)
