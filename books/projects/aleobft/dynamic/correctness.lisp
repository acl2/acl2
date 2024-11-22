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
(include-book "accepted-certificate-committee")
(include-book "signer-quorum")
(include-book "backward-closure")
(include-book "unequivocal-signed-certificates")
(include-book "unequivocal-accepted-certificates-def-and-init")
(include-book "nonforking-blockchains-def-and-init")
(include-book "same-committees-def-and-implied")
(include-book "unequivocal-accepted-certificates-next")
(include-book "previous-quorum")
(include-book "last-anchor-def-and-init")
(include-book "last-anchor-present")
(include-book "successor-predecessor-intersection")
(include-book "dag-omni-paths")
(include-book "rounds-in-committees")
(include-book "dag-certificate-next")
(include-book "last-anchor-next")
(include-book "last-anchor-voters-def-and-init-and-next")
(include-book "omni-paths-def-and-implied")
(include-book "anchors-extension")
(include-book "committed-anchor-sequences")
(include-book "nonforking-anchors-def-and-init-and-next")
(include-book "committed-redundant-def-and-init-and-next")
(include-book "blockchain-redundant-def-and-init-and-next")
(include-book "nonforking-blockchains-next")
(include-book "simultaneous-induction")
(include-book "unequivocal-accepted-certificates")
(include-book "nonforking-blockchains")
(include-book "same-committees")
(include-book "last-anchor-voters")
(include-book "omni-paths")
(include-book "nonforking-anchors")
(include-book "committed-redundant")
(include-book "blockchain-redundant")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ correctness
  :parents (aleobft-dynamic)
  :short "Correctness proofs of the AleoBFT labeled state transition system."
  :long
  (xdoc::topstring
   (xdoc::p
    "We formulate and prove a number of properties of the protocol,
     culminating in the main property that we are interested in,
     namely the non-forking of blockchains."))
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
                    accepted-certificate-committee
                    signer-quorum
                    backward-closure
                    unequivocal-signed-certificates
                    unequivocal-accepted-certificates-def-and-init
                    nonforking-blockchains-def-and-init
                    same-committees-def-and-implied
                    unequivocal-accepted-certificates-next
                    previous-quorum
                    last-anchor-def-and-init
                    last-anchor-present
                    successor-predecessor-intersection
                    dag-omni-paths
                    rounds-in-committees
                    dag-certificate-next
                    last-anchor-next
                    last-anchor-voters-def-and-init-and-next
                    omni-paths-def-and-implied
                    anchors-extension
                    committed-anchors-sequences
                    nonforking-anchors-def-and-init-and-next
                    committed-redundant-def-and-init-and-next
                    blockchain-redundant-def-and-init-and-next
                    nonforking-blockchains-next
                    simultaneous-induction
                    unequivocal-accepted-certificates
                    nonforking-blockchains
                    same-committees
                    last-anchor-voters
                    omni-paths
                    nonforking-anchors
                    committed-redundant
                    blockchain-redundant))
