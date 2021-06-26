; PFCS (Prime Field Constraint System) Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PFCS")

(include-book "abstract-syntax")
(include-book "abstract-syntax-operations")
(include-book "well-formedness")
(include-book "semantics")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ prime-field-constraint-systems
  :parents (acl2::kestrel-books acl2::projects)
  :short "A library for PFCS (Prime Field Constraint Systems)."
  :long
  (xdoc::topstring
   (xdoc::p
    "The notion of PFCS is introduced by this library;
     it is not an existing notion that this library formalizes.
     We use the acronym `PFCS' for
     both singular (`System') and plural (`Systems').")
   (xdoc::p
    "A PFCS is a system of constraints over a prime field;
     the constraints include variables that range over a prime field.
     The motivation for PFCS stems from zero-knowledge proofs,
     but there may be more general applications.
     PFCS generalize R1CS (Rank-1 Constraint Systems),
     which are used in zero-knowledge proofs,
     in two ways:")
   (xdoc::ul
    (xdoc::li
     "Constraints in PFCS are not limited to the R1CS form
      (i.e. equality between a product of two linear polynomials
      and a linear polynomial).
      They are equalities between any combinations of
      additions and multiplications (and perhaps more operations in the future);
      note that addition and multiplication
      suffice to describe arithmetic circuits.
      Thus, PFCS generalize R1CS, and likely (or eventually)
      other forms of constraints used in zero-knowledge proofs, e.g. PLONK.
      The richer representation also supports
      more elaborate transformations of the constraints.")
    (xdoc::li
     "Constraints in PFCS may be hierarchically organized,
      by naming sets of them as relations with parameters,
      which may be referenced (i.e. ``called'')
      in the definition of other relations.
      This explicates the natural hierarchical structure
      of zero-knowledge gadgets (R1CS or others),
      and supports more modular
      verification, analysis, transformation, and synthesis."))
   (xdoc::p
    "Currently this library contains an abstract syntax of PFCS,
     some operations on the abstract syntax,
     and a semantics expressed as a shallow embedding;
     see the documentation of these artifacts for more information.
     It also includes some examples.
     It is expected that this library will be extended
     with more artifacts related to PFCS.")
   (xdoc::p
    "Some of the concepts in this library are more general than prime fields.
     Thus, it may be possible to generalize some parts of this library
     to some more general form of constraints.")
   (xdoc::p
    "This library makes use of the "
    (xdoc::seetopic "pfield::prime-fields" "prime fields library")
    " and is related to the "
    (xdoc::seetopic "r1cs::r1cs" "R1CS library")
    " in the community books."))
  :order-subtopics t)
