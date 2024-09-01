; AleoBFT Library
;
; Copyright (C) 2024 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOBFT-DYNAMIC")

(include-book "owned-certificates")
(include-book "same-owned-certificates")
(include-book "no-self-messages")
(include-book "no-self-buffer")
(include-book "no-self-endorsed")
(include-book "signer-records")
(include-book "fault-tolerance")
(include-book "committees-in-system")
(include-book "unequivocal-certificates-def-and-init")
(include-book "nonforking-blockchains-def-and-init")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ correctness
  :parents (aleobft-dynamic)
  :short "Correctness proofs of the AleoBFT labeled state transition system."
  :long
  (xdoc::topstring
   (xdoc::p
    "We formulate and prove a number of properties of the protocol.
     The main property that we are initially interested in
     is the non-forking of blockchains,
     which we have already proved for static committees;
     here we are generalizing it for dynamic committees."))
  :order-subtopics (owned-certificates
                    same-owned-certificates
                    no-self-messages
                    no-self-buffer
                    no-self-endorsed
                    signer-records
                    fault-tolerance
                    committees-in-system
                    unequivocal-certificates-def-and-init
                    nonforking-blockchains-def-and-init))

; TODO: continue
