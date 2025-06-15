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

(include-book "boolean-and")
(include-book "boolean-and-notleft")
(include-book "boolean-check")
(include-book "equal")
(include-book "if")
(include-book "if-with-coeffs")
(include-book "indicator")
(include-book "one")
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
     not in XDOC; thus, this XDOC topic has no subtopics for the circuits.")))
