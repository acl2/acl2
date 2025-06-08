; PFCS (Prime Field Constraint System) Library
;
; Copyright (C) 2025 Kestrel Institute (https://www.kestrel.edu)
; Copyright (C) 2025 Provable Inc. (https://www.provable.com)
;
; License: See the LICENSE file distributed with this library.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PFCS")

(include-book "concrete-syntax")

(include-book "abstract-syntax")

(include-book "parser-interface")

(include-book "abstract-syntax-operations")
(include-book "indexed-names")
(include-book "convenience-constructors")
(include-book "well-formedness")
(include-book "semantics")
(include-book "proof-support")
(include-book "lifting")
(include-book "r1cs-lib-ext")
(include-book "r1cs-subset")
(include-book "r1cs-bridge")
(include-book "pfield-lib-ext")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ pfcs
  :parents (acl2::projects)
  :short "A library for PFCSes (Prime Field Constraint Systems)."
  :long
  (xdoc::topstring
   (xdoc::p
    "The notion of PFCS (Prime Field Constraint System)
     is introduced by this library;
     it is not an existing notion that this library formalizes.
     We write `PFCS' for the singular `Prime Field Constraint System',
     and`PFCSes' for the plural `Prime Field Constraint Systems'.")
   (xdoc::p
    "A PFCS is a system of constraints over a prime field;
     the constraints include variables that range over a prime field.
     The motivation for PFCSes stems from zero-knowledge proofs,
     but there may be more general applications.
     PFCSes generalize R1CSes (Rank-1 Constraint Systems),
     which are used in zero-knowledge proofs,
     in two ways:")
   (xdoc::ul
    (xdoc::li
     "Constraints in PFCSes are not limited to the R1CS form
      (i.e. equality between a product of two linear polynomials
      and a linear polynomial).
      PFCS constraints are equalities between any combinations of
      additions and multiplications (and perhaps more operations in the future);
      note that addition and multiplication
      suffice to describe arithmetic circuits.
      Thus, PFCSes generalize R1CSes, and likely (or eventually)
      other forms of constraints used in zero-knowledge proofs, e.g. PLONKs.
      The richer representation can also support
      more elaborate transformations of the constraints.")
    (xdoc::li
     "PFCS constraints may be hierarchically organized,
      by naming sets of them as relations with parameters,
      which may be referenced (i.e. ``called'')
      in the definition of other relations.
      This explicates the natural hierarchical structure
      of zero-knowledge gadgets (in R1CS or other form),
      and can supports more modular
      verification, analysis, transformation, and synthesis."))
   (xdoc::p
    "Currently this library contains
     a concrete syntax of PFCSes and a parser to CSTs (concrete syntax trees),
     an abstract syntax of PFCSes
     and an abstractor from CSTs to ASTs (abstract syntax trees),
     parser interface functions to generate ASTs from strings,
     some operations on the abstract syntax,
     a notion of well-formedness,
     a semantics expressed as a shallow embedding,
     a semantics expressed as a deep embedding,
     and some tools to support proofs about PFCSes;
     see the documentation of these artifacts for more information.
     This library also includes some examples.
     This library is a work in progress;
     it is expected that it will be extended
     with more artifacts related to PFCSes.")
   (xdoc::p
    "Some of the concepts in this library are more general than prime fields.
     Thus, it may be possible to generalize some parts of this library
     to even more general form of constraints.")
   (xdoc::p
    "This library makes use of the "
    (xdoc::seetopic "pfield::prime-fields" "prime fields library")
    " and is related to the "
    (xdoc::seetopic "r1cs::r1cs" "R1CS library")
    ", both in the community books."))
  :order-subtopics t)
