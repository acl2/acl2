; AleoBFT Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOBFT-PROPOSALS")

(include-book "round-after-last")
(include-book "last-blockchain-round")
(include-book "ordered-blockchain")
(include-book "active-committees-after-commit")
(include-book "proposal-to-other")
(include-book "endorsement-from-other")
(include-book "certificate-to-other")
(include-book "proposed-author-self")
(include-book "proposed-endorser-other")
(include-book "endorsed-author-other")
(include-book "proposal-in-author")
(include-book "endorsement-in-author")
(include-book "endorsement-in-endorser")
(include-book "endorsed-in-author")
(include-book "certificate-in-author")
(include-book "proposed-author-in-committee")
(include-book "proposed-endorser-in-committee")
(include-book "signer-quorum")
(include-book "proposed-round1-no-previous")
(include-book "endorsed-round1-no-previous")
(include-book "proposed-previous-closed")
(include-book "endorsed-previous-closed")
(include-book "dag-previous-closed")
(include-book "signed-proposals")
(include-book "signed-in-signer")
(include-book "author-round-pairs-in-validators")
(include-book "unequivocal-signed-proposals")
(include-book "unequivocal-proposed")
(include-book "fault-tolerance")
(include-book "quorum-intersection")
(include-book "nonforking-blockchains-def-and-init")
(include-book "same-committees-def-and-implied")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ correctness
  :parents (aleobft-proposals)
  :short "Correctness proofs of the AleoBFT labeled state transition system."
  :long
  (xdoc::topstring
   (xdoc::p
    "We formulate and prove a number of properties of the protocol,
     culminating in the main property that we are interested in,
     namely the non-forking of blockchains.")
   (xdoc::p
    "This is work in progress."))
  :order-subtopics (round-after-last
                    last-blockchain-round
                    ordered-blockchain
                    active-committees-after-commit
                    proposal-to-other
                    endorsement-from-other
                    certificate-to-other
                    proposed-author-self
                    proposed-endorser-other
                    endorsed-author-other
                    proposal-in-author
                    endorsement-in-author
                    endorsement-in-endorser
                    endorsed-in-author
                    certificate-in-author
                    proposed-author-in-committee
                    proposed-endorser-in-committee
                    signer-quorum
                    proposed-round1-no-previous
                    endorsed-round1-no-previous
                    proposed-previous-closed
                    endorsed-previous-closed
                    dag-previous-closed
                    signed-proposals
                    signed-in-signer
                    author-round-pairs-in-validators
                    unequivocal-signed-proposals
                    unequivocal-proposed
                    fault-tolerance
                    quorum-intersection
                    nonforking-blockchains-def-and-init
                    same-committees-def-and-implied))

; TODO: continue
