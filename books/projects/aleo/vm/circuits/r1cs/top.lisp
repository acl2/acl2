; AleoVM Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOVM")

(include-book "bits-lt")
(include-book "bits-lt-prime")
(include-book "bits-lte-const")
(include-book "bits-lte-const-check")
(include-book "bits-mul-field")
(include-book "boolean-and")
(include-book "boolean-and-notleft")
(include-book "boolean-and-notright")
(include-book "boolean-check")
(include-book "boolean-nand")
(include-book "boolean-nor")
(include-book "boolean-or")
(include-book "boolean-or-notleft")
(include-book "boolean-xor")
(include-book "equal")
(include-book "field-bits-add-bits")
(include-book "field-const-pow")
(include-book "field-const-pow-bits")
(include-book "field-inverse")
(include-book "field-mul")
(include-book "field-pow-bits")
(include-book "field-pow-bits-const")
(include-book "field-square")
(include-book "field-to-bits")
(include-book "if")
(include-book "if-with-coeffs")
(include-book "indicator")
(include-book "one")
(include-book "pow2sum-vectors")
(include-book "pow2sum")
(include-book "vector-neg")
(include-book "zero")

(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc circuits-r1cs
  :parents (circuits)
  :short "AleoVM circuits in R1CS form."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(see circuits) for background.")
   (xdoc::p
    "We formalize and verify circuits
     for the operations (and sub-operations) in snarkVM.
     Each circuit is an ACL2 function that constructs R1CS constraints,
     paremeterized over the choice of variable names,
     and possibly over the choice of number of variables and constraints.
     This follows the approach described in
     the papers referenced in @(see circuits).")
   (xdoc::p
    "This approach is superseded by the approach in @(see circuit-pfcs),
     also described in the aforementioned papers,
     which also explain how the PFCS approach
     solves a scalability problem inherent to the R1CS approach.
     Thus, the formalization and verification of circuits in R1CS form
     is now essentially legacy code,
     which we keep mainly for historical and testing purposes,
     and also because not all the circuits in R1CS forms
     have been ported to PFCS form yet.")
   (xdoc::p
    "These circuits in R1CS form are documented with comments in the files,
     not in XDOC; thus, this XDOC topic has no subtopics for the circuits.")
   (xdoc::p
    "For some of these circuits in R1CS form,
     we prove both soundness and completeness,
     while for others, we only prove soundness;
     this was work in progress,
     but we switched to the PFCS approach at some point
     (see @(see circuits-pfcs)).
     See the papers referenced in @(see circuits)
     for the notions of `soundness' and `completeness' in this context.")))
