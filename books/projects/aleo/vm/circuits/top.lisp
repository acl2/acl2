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
(include-book "boolean-assert")
(include-book "boolean-assert-eq")
(include-book "boolean-assert-neq")
(include-book "boolean-assert-true")
(include-book "boolean-eq")
(include-book "boolean-if")
(include-book "boolean-nand")
(include-book "boolean-neq")
(include-book "boolean-nor")
(include-book "boolean-not")
(include-book "boolean-or")
(include-book "boolean-xor")
(include-book "field-add")
(include-book "field-double")
(include-book "field-mul")
(include-book "field-neg")
(include-book "field-sub")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ circuits
  :parents (aleovm)
  :short "AleoVM circuits."
  :long
  (xdoc::topstring
   (xdoc::p
    "The subset of the AleoVM language that executes off-chain
     is compiled to zero-knowledge circuits
     that are incorporated into the zero-knowledge proofs
     of off-chain execution.
     As in other forms of compilation,
     the same AleoVM code could be compiled
     to different zero-knowledge circuits,
     so long as they are functionally equivalent.")
   (xdoc::p
    "Here we formalize the zero-knowledge circuits
     that the AleoVM language is compiled to in "
    (xdoc::ahref "https://github.com/AleoNet/snarkVM" "snarkVM")
    ". We prove those circuits correct
     with respect to high-level specifications that we also provide.")
   (xdoc::p
    "snarkVM generates zero-knowledge circuits in R1CS form.
     We use our "
    (xdoc::seetopic "pfcs::pfcs" "PFCS")
    " formalism
     to formalize and verify the circuits in a compositional way,
     as described in our "
    (xdoc::ahref "https://eprint.iacr.org/2023/1278"
                 "SBC 2023 paper")
    " and in our "
    (xdoc::ahref "https://cgi.cse.unsw.edu.au/~eptcs/paper.cgi?ACL22023.9"
                 "ACL2-2023 Workshop paper")
    "."))
  :order-subtopics (boolean-and
                    boolean-assert
                    boolean-assert-eq
                    boolean-assert-neq
                    boolean-assert-true
                    boolean-eq
                    boolean-if
                    boolean-nand
                    boolean-neq
                    boolean-nor
                    boolean-not
                    boolean-or
                    boolean-xor
                    field-add
                    field-mul
                    field-neg
                    field-sub))
