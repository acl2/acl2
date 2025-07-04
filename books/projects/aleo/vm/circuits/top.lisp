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

(include-book "pfcs/top")
(include-book "r1cs/top")

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
     In @(see circuits-pfcs),
     we use our "
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
  :order-subtopics (pfcs
                    r1cs))
