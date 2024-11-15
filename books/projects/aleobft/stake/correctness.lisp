; AleoBFT Library
;
; Copyright (C) 2024 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOBFT-STAKE")

(include-book "fault-tolerance")
(include-book "backward-closure")
(include-book "last-blockchain-round")
(include-book "ordered-even-blocks")
(include-book "associated-certificates")
(include-book "same-associated-certificates")
(include-book "signed-certificates")
(include-book "no-self-messages")
(include-book "no-self-buffer")
(include-book "no-self-endorsed")
(include-book "signer-records")
(include-book "unequivocal-signed-certificates")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ correctness
  :parents (aleobft-stake)
  :short "Correctness proofs of the AleoBFT labeled state transition system."
  :long
  (xdoc::topstring
   (xdoc::p
    "We formulate and prove a number of properties of the protocol,
     culminating in the main property that we are interested in,
     namely the non-forking of blockchains."))
  :order-subtopics (fault-tolerance
                    backward-closure
                    last-blockchain-round
                    ordered-even-blocks
                    associated-certificates
                    same-associated-certificates
                    signed-certificates
                    no-self-messages
                    no-self-buffer
                    no-self-endorsed
                    signer-records
                    unequivocal-signed-certificates))
