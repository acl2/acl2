; AleoBFT Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOBFT")

(include-book "blocks")
(include-book "certificates")

(local (include-book "kestrel/utilities/nfix" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ validator-states
  :parents (states)
  :short "States of (correct) validators."
  :long
  (xdoc::topstring
   (xdoc::p
    "Validators have internal states.
     For correct validators,
     i.e. the ones that follow the protocol,
     the internal states must contain certain information
     that is prescribed by the protocol,
     which we model here.
     For faulty validators,
     i.e. the ones that do not (always) follow the protcol,
     we do not need to model the internal state,
     because what matters in our model is only
     the effect that faulty validators may have on correct ones,
     via messages exchanged over the network."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(encapsulate
  ()
  (set-induction-depth-limit 1)

  (fty::defomap proposal-address-set-map
    :short "Fixtype of maps from proposals to sets of addresses."
    :key-type proposal
    :val-type address-set
    :pred proposal-address-set-mapp

    ///

    (defruled proposal-setp-of-keys-when-proposal-address-set-mapp
      (implies (proposal-address-set-mapp map)
               (proposal-setp (omap::keys map)))
      :induct t
      :enable omap::keys)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod validator-state
  :short "Fixtype of states of a (correct) validator."
  :long
  (xdoc::topstring
   (xdoc::p
    "As explained in @(see validator-states),
     faulty validators are modeled with no internal state.
     So this fixtype only models the state of correct validators.")
   (xdoc::p
    "We model the state of a correct validator as consisting of:")
   (xdoc::ol
    (xdoc::li
     "The current round number that the validator is at.")
    (xdoc::li
     "The DAG of certificates, modeled as a set.
      Invariants about the uniqueness of author and round combinations
      are stated and proved elsewhere.")
    (xdoc::li
     "A finite map from each proposal created by the validator
      to the set of addresses of validators who have endorsed the proposal.
      When the validator has enough endorsements for a proposal,
      it creates a certificate out of the proposal and its endorsements,
      and adds that certificate to its DAG.")
    (xdoc::li
     "A set of endorsed proposals.
      These are proposals received from other validators,
      which the validator has endorsed by sending a signature.
      The validator needs to keep track of these signed proposals
      to avoid endorsing two equivocal proposals,
      i.e. two different proposals with the same author and round.
      After endorsing a proposal,
      it may take time for the validator to receive
      the full certificate with that proposal,
      if it receives it at all;
      so it is necessary to keep track of endorsed proposals.")
    (xdoc::li
     "The number of the last round at which
      the validator has committed an anchor,
      or 0 if no anchor has been committe yet.")
    (xdoc::li
     "The blockchain as seen by the validator.
      We model it as a list of blocks from right to left,
      i.e. the rightmost block is the oldest/earliest one
      and the leftmost block is the newest/latest one.
      We leave the genesis block implicit:
      the rightmost block in our list is actually
      the block just after the genesis block.
      The blockchain is actually calculable from other state components,
      as proved elsewhere.
      However, the reasons (i.e. proof) of this redundancy are somewhat complex,
      and thus it is better to include the blockchain in the validator state,
      so that the state transitions can be defined in a more natural way.")
    (xdoc::li
     "The set of all the certificates that have been committed so far,
      i.e. whose transactions have been included in the blockchain.
      These include not just the anchors,
      but also the certificates reachable from the anchors via the DAG edges.
      This state component serves to calculate the new certificates
      to be committed the next time anchors are committed,
      by computing the full causal history of each anchor
      but removing the already committed certificates.
      This state component actually calculable from other state components,
      as proved elsewhere.
      However, for the same reason explained above for the blockchain component,
      it is best to leave this component in the state,
      for a more natural definition of the state transitions."))
   (xdoc::p
    "The address of the validator, which never changes,
     is captured outside this fixtype,
     in the map from validator addresses to validator states
     that is in the system state.")
   (xdoc::p
    "There are many invariants on validator states,
     such as the ones mentioned above.
     These are stated and proved elsewhere.")
   (xdoc::p
    "Validators in AleoBFT include more information than modeled here,
     but this model is sufficient for our current purposes."))
  ((round pos)
   (dag certificate-set)
   (proposed proposal-address-set-map)
   (endorsed proposal-set)
   (last nat)
   (blockchain block-list)
   (committed certificate-set))
  :pred validator-statep)
