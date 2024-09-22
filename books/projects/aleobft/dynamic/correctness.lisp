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

(include-book "certificates-of-validators")
(include-book "same-owned-certificates")
(include-book "no-self-messages")
(include-book "no-self-buffer")
(include-book "no-self-endorsed")
(include-book "signer-records")
(include-book "fault-tolerance")
(include-book "committees-in-system")
(include-book "quorum-intersection")
(include-book "last-blockchain-round")
(include-book "ordered-even-blocks")
(include-book "accepted-certificates-quorum")
(include-book "unequivocal-signed-certificates")
(include-book "unequivocal-accepted-certificates")
(include-book "nonforking-blockchains-def-and-init")
(include-book "same-committees")

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
  :order-subtopics (certificates-of-validators
                    same-owned-certificates
                    no-self-messages
                    no-self-buffer
                    no-self-endorsed
                    signer-records
                    fault-tolerance
                    committees-in-system
                    quorum-intersection
                    last-blockchain-round
                    ordered-even-blocks
                    accepted-certificates-quorum
                    unequivocal-signed-certificates
                    unequivocal-accepted-certificates
                    nonforking-blockchains-def-and-init
                    same-committees))

; TODO: continue
