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

(include-book "xdoc/defxdoc-plus" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ aleovm
  :parents (aleo::aleo)
  :short "An ACL2 library for the AleoVM."
  :long
  (xdoc::topstring
   (xdoc::p
    "AleoVM is the virtual machine of the "
    (xdoc::ahref "https://aleo.org" "Aleo blockchain")
    ". AleoVM is implemented in "
    (xdoc::ahref "https://github.com/AleoNet/snarkVM" "snarkVM")
    ".")
   (xdoc::p
    "AleoVM features an assembly-like language
     used for both off-chain and on-chain execution.
     The off-chain execution results in a zero-knowledge proof
     that is verified on chain;
     the on-chain execution happens after the proof is verified,
     via a `futures' mechanism.")))
