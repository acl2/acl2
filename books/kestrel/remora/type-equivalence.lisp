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

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ type-equivalence
  :parents (static-semantics)
  :short "Equivalence of types."
  :long
  (xdoc::topstring
   (xdoc::p
    "The static semantics of Remora involves
     the equivalence of types.
     Currently type equivalence in Remora is decidable,
     but the language may evolve towards undecidability.")
   (xdoc::p
    "The current (decidable) equivalence of types
     is described in the arXiv paper and dissertation,
     in terms of inference rules
     that involve the semantic equivalence of indices;
     the latter is defined in terms of normalization
     (see @(see index-equivalence).
     We plan to formalize type equivalence,
     both at a high level and as executable code.
     For now we provide a placeholder."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-equivp ((type1 typep) (type2 typep))
  :returns (yes/no booleanp)
  :short "Check if two types are equivalent."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is an initial placeholder, which makes a strong check:
     the two types must be identical.
     This needs to be relaxed with the proper semantic equivalence,
     which is decidable for the current version of Remora,
     according to the arXiv paper and dissertation."))
  (equal (type-fix type1) (type-fix type2)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-list-equivp ((types1 type-listp) (types2 type-listp))
  :returns (yes/no booleanp)
  :short "Check if two lists of types are equivalent."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is also an initial placeholder, in line with @(tsee type-equivp):
     we require the two lists to be identical for now."))
  (equal (type-list-fix types1) (type-list-fix types2)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-list-all-equivp ((types type-listp))
  :returns (yes/no booleanp)
  :short "Check if all the types in a list are equivalent."
  (or (endp types)
      (endp (cdr types))
      (and (type-equivp (car types) (cadr types))
           (type-list-all-equivp (cdr types))))
  :prepwork ((local (in-theory (enable type-list-fix)))))
