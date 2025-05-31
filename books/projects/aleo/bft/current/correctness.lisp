; AleoBFT Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOBFT-ARXIV")

(include-book "last-blockchain-round")
(include-book "ordered-even-blocks")
(include-book "backward-closure")
(include-book "signer-quorum")
(include-book "system-certificates")
(include-book "signed-certificates")
(include-book "signed-previous-quorum")
(include-book "no-self-endorsed")
(include-book "signer-records")
(include-book "unequivocal-signed-certificates")
(include-book "fault-tolerance")
(include-book "quorum-intersection")
(include-book "unequivocal-dags-def-and-init")
(include-book "nonforking-blockchains-def-and-init")
(include-book "same-committees-def-and-implied")
(include-book "unequivocal-dags-next")
(include-book "dag-previous-quorum-def-and-init-and-next")
(include-book "dag-certificate-next")
(include-book "last-anchor-def-and-init")
(include-book "last-anchor-present")
(include-book "last-anchor-next")
(include-book "last-anchor-voters-def-and-init-and-next")
(include-book "successor-predecessor-intersection")
(include-book "dag-omni-paths")
(include-book "omni-paths-def-and-implied")
(include-book "anchors-extension")
(include-book "committed-anchor-sequences")
(include-book "nonforking-anchors-def-and-init-and-next")
(include-book "committed-redundant-def-and-init-and-next")
(include-book "blockchain-redundant-def-and-init-and-next")
(include-book "nonforking-blockchains-next")
(include-book "simultaneous-induction")
(include-book "unequivocal-dags")
(include-book "dag-previous-quorum")
(include-book "nonforking-blockchains")
(include-book "same-committees")
(include-book "last-anchor-voters")
(include-book "omni-paths")
(include-book "nonforking-anchors")
(include-book "committed-redundant")
(include-book "blockchain-redundant")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ correctness
  :parents (aleobft-arxiv)
  :short "Correctness proofs of the AleoBFT labeled state transition system."
  :long
  (xdoc::topstring
   (xdoc::p
    "We formulate and prove a number of properties of the protocol,
     culminating in the main property that we are interested in,
     namely the non-forking of blockchains."))
  :order-subtopics (last-blockchain-round
                    ordered-even-blocks
                    backward-closure
                    signer-quorum
                    system-certificates
                    signed-certificates
                    signed-previous-quorum
                    no-self-endorsed
                    signer-records
                    unequivocal-signed-certificates
                    fault-tolerance
                    quorum-intersection
                    unequivocal-dags-def-and-init
                    nonforking-blockchains-def-and-init
                    same-committees-def-and-implied
                    unequivocal-dags-next
                    dag-previous-quorum-def-and-init-and-next
                    dag-certificate-next
                    last-anchor-def-and-init
                    last-anchor-present
                    last-anchor-next
                    last-anchor-voters-def-and-init-and-next
                    successor-predecessor-intersection
                    dag-omni-paths
                    omni-paths-def-and-implied
                    anchors-extension
                    committed-anchor-sequences
                    nonforking-anchors-def-and-init-and-next
                    committed-redundant-def-and-init-and-next
                    blockchain-redundant-def-and-init-and-next
                    nonforking-blockchains-next
                    simultaneous-induction
                    unequivocal-dags
                    dag-previous-quorum
                    nonforking-blockchains
                    same-committees
                    last-anchor-voters
                    omni-paths
                    nonforking-anchors
                    committed-redundant
                    blockchain-redundant))
