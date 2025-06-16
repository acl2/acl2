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

(include-book "babbage-multiplication")
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
(include-book "field-div")
(include-book "field-div-unchecked")
(include-book "field-from-bits")
(include-book "field-inverse")
(include-book "field-lt")
(include-book "field-mul")
(include-book "field-neq")
(include-book "field-neq-opt")
(include-book "field-pow")
(include-book "field-pow-bits")
(include-book "field-pow-bits-const")
(include-book "field-pow-const")
(include-book "field-square")
(include-book "field-square-root")
(include-book "field-ternary")
(include-book "field-to-bits")
(include-book "if")
(include-book "if-with-coeffs")
(include-book "indicator")
(include-book "integer-and")
(include-book "integer-or")
(include-book "integer-ternary")
(include-book "integer-xor")
(include-book "karatsuba-multiplication")
(include-book "one")
(include-book "pow2sum-vectors")
(include-book "pow2sum")
(include-book "signed-small-abs-checked")
(include-book "signed-small-abs-wrapped")
(include-book "signed-small-add-checked")
(include-book "signed-small-add-wrapped")
(include-book "signed-small-mul-wrapped")
(include-book "signed-small-neg")
(include-book "signed-small-neq")
(include-book "signed-small-neq-opt")
(include-book "signed-small-sub-checked")
(include-book "signed-small-sub-checked-const-var")
(include-book "signed-small-sub-wrapped")
(include-book "signed-small-sub-wrapped-const-var")
(include-book "unsigned-medium-mul-carry")
(include-book "unsigned-medium-mul-checked")
(include-book "unsigned-medium-div")
(include-book "unsigned-small-add")
(include-book "unsigned-small-add-checked")
(include-book "unsigned-small-add-checked-opt")
(include-book "unsigned-small-add-wrapped")
(include-book "unsigned-small-div")
(include-book "unsigned-small-lt")
(include-book "unsigned-small-mul")
(include-book "unsigned-small-mul-and-check")
(include-book "unsigned-small-mul-carry")
(include-book "unsigned-small-mul-checked")
(include-book "unsigned-small-mul-wrapped")
(include-book "unsigned-small-neq")
(include-book "unsigned-small-neq-opt")
(include-book "unsigned-small-nonzero")
(include-book "unsigned-small-sub")
(include-book "unsigned-small-sub-checked")
(include-book "unsigned-small-sub-const-var")
(include-book "unsigned-small-sub-opt")
(include-book "unsigned-small-sub-opt-const-var")
(include-book "unsigned-small-sub-wrapped")
(include-book "unsigned-small-sub-wrapped-const-var")
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
    "This approach is superseded by the approach in @(see circuits-pfcs),
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
