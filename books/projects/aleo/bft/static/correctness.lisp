; AleoBFT Library
;
; Copyright (C) 2024 Provable Inc.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOBFT-STATIC")

(include-book "operations-additional")
(include-book "properties-certificate-retrieval")
(include-book "properties-dags")
(include-book "properties-anchors")
(include-book "property-paths-to-voted-anchor")
(include-book "property-paths-to-other-voted-anchor")
(include-book "properties-anchors-extension")
(include-book "properties-blockchain")
(include-book "property-last-anchor-of-next-event")
(include-book "property-committed-anchors-of-next-event")
(include-book "invariant-addresses")
(include-book "invariant-max-faulty")
(include-book "invariant-quorum")
(include-book "invariant-fault-tolerance")
(include-book "invariant-no-self-messages")
(include-book "invariant-no-self-buffer")
(include-book "invariant-no-self-endorsed")
(include-book "invariant-messages-to-correct")
(include-book "invariant-same-certificates")
(include-book "invariant-signers-are-validators")
(include-book "invariant-dag-authors-are-validators")
(include-book "invariant-signers-have-author-round")
(include-book "invariant-signers-are-quorum")
(include-book "invariant-unequivocal-certificates")
(include-book "invariant-unequivocal-dag")
(include-book "invariant-unequivocal-dags")
(include-book "invariant-previous-are-quorum")
(include-book "invariant-dag-previous-are-quorum")
(include-book "invariant-previous-in-dag")
(include-book "invariant-last-is-even")
(include-book "invariant-last-before-current")
(include-book "invariant-last-anchor-present")
(include-book "invariant-last-anchor-voters")
(include-book "invariant-paths-to-last-anchor")
(include-book "invariant-paths-to-other-last-anchor")
(include-book "invariant-anchors-not-forking")
(include-book "invariant-certificate-retrieval")
(include-book "invariant-causal-histories")
(include-book "invariant-committed-redundant")
(include-book "invariant-blockchain-redundant")
(include-book "invariant-blockchain-not-forking")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ correctness
  :parents (aleobft-static)
  :short "Correctness proofs of our model of
          AleoBFT with static committees."
  :long
  (xdoc::topstring
   (xdoc::p
    "We introduce some additional operations used
     to formulate and prove the correctness of the protocol.")
   (xdoc::p
    "We prove a number of properties of both these additional operations
     and of the operations used in the definition of
     the labeled state transition system.")
   (xdoc::p
    "Many of these properties are in invariants of the system.
     We start with simple ones,
     and culminate into high-level properties of interest of the protocol.")
   (xdoc::p
    "The invariants are mostly state invariants,
     i.e. predicates that hold in the initial state
     and are preserved by every transition.
     There are also some transition invariants,
     i.e. predicates that hold of
     each pair of old and new states linked by a transition."))
  :order-subtopics (operations-additional
                    properties-certificate-retrieval
                    properties-dags
                    properties-anchors
                    property-paths-to-voted-anchor
                    property-paths-to-other-voted-anchor
                    properties-anchors-extension
                    properties-blockchain
                    property-last-anchor-of-next-event
                    property-committed-anchors-of-next-event
                    invariant-addresses
                    invariant-max-faulty
                    invariant-quorum
                    invariant-fault-tolerance
                    invariant-no-self-messages
                    invariant-no-self-buffer
                    invariant-no-self-endorsed
                    invariant-messages-to-correct
                    invariant-same-certificates
                    invariant-signers-are-validators
                    invariant-dag-authors-are-validators
                    invariant-signers-have-author-round
                    invariant-signers-are-quorum
                    invariant-unequivocal-certificates
                    invariant-unequivocal-dag
                    invariant-unequivocal-dags
                    invariant-previous-are-quorum
                    invariant-dag-previous-are-quorum
                    invariant-previous-in-dag
                    invariant-last-is-even
                    invariant-last-before-current
                    invariant-last-anchor-present
                    invariant-last-anchor-voters
                    invariant-paths-to-last-anchor
                    invariant-paths-to-other-last-anchor
                    invariant-anchors-not-forking
                    invariant-certificate-retrieval
                    invariant-causal-histories))
