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
(include-book "proposed-author-self")
(include-book "proposal-to-other")
(include-book "endorsement-from-other")
(include-book "certificate-to-other")
(include-book "proposed-endorser-other")
(include-book "proposal-in-author")
(include-book "endorsement-in-author")
(include-book "endorsement-in-endorser")
(include-book "endorsed-in-author")
(include-book "certificate-in-author")
(include-book "proposed-has-previous")
(include-book "endorsed-has-previous")

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
                    proposed-author-self
                    proposal-to-other
                    endorsement-from-other
                    certificate-to-other
                    proposed-endorser-other
                    proposal-in-author
                    endorsement-in-author
                    endorsement-in-endorser
                    endorsed-in-author
                    certificate-in-author
                    proposed-has-previous
                    endorsed-has-previous))

; TODO: continue
