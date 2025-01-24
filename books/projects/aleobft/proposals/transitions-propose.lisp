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

(include-book "system-states")
(include-book "committees")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ transitions-propose
  :parents (parents)
  :short "Transitions for proposal creation."
  :long
  (xdoc::topstring
   (xdoc::p
    "Here we define the system state changes caused by @('propose') events.")
   (xdoc::p
    "A correct validator creates a proposal only under certain conditions;
     in particular, it never creates an equivocal proposal,
     i.e. one with the same author and round as an existing one.
     A faulty validator is much less constrained,
     but it cannot forge signatures
     (if a validator's private key is compromised,
     the validator is considered faulty).
     Either way, the proposal is broadcast to other validators.")
   (xdoc::p
    "If the validator is correct,
     it stores the proposal into its internal state,
     along with information about endorsements received by other validators;
     initially there are no endorsements."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define propose-possiblep ((prop proposalp)
                           (dests address-setp)
                           (systate system-statep))
  :returns (yes/no booleanp)
  :short "Check if a @('propose') event is possible in a system state."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('props') and @('dests') parameters of this function
     are the corresponding components of the @('propose') event.")
   (xdoc::p
    "The author of the proposal identifies
     the validator that creates the proposal.
     Since signatures cannot be forged,
     a faulty validator cannot impersonate a correct one,
     and thus the fact that the proposal's author is a correct validator
     means that the proposal is indeed created by that validator.
     If the author of the proposal is a faulty validator,
     there are no other requirements:
     our model assumes that all transactions are valid,
     and thus nothing prevents a faulty validator from
     generating a proposal with arbitrary
     round, transactions, and previous certificate addresses.")
   (xdoc::p
    "If the proposal's author is correct, additional conditions apply;
     that is, the event can happen only if these conditions are satisfied:")
   (xdoc::ul
    (xdoc::li
     "The round of the proposal
      must match the round of the validator.
      A correct validator always generates proposals for the current round.")
    (xdoc::li
     "The author must be in the active committee for that round.
      This means that the author must be able to calculate that committee.")
    (xdoc::li
     "The validator has not already created
      another proposal with the same round,
      because that would cause equivocation.
      Not only the DAG must include no certificate with that author and round,
      but also the pending proposals must not include a proposal with that round
      (as proved elsewhere, it is an invariant that
      all the pending proposals are authored by the validator,
      so there is no need to check the author).")
    (xdoc::li
     "The certificates referenced in the @('previous') component
      are present in the DAG,
      and their authors form a non-empty quorum in
      the active committee for the round just before the current one
      (which, as noted above, is the same as the proposal);
      note that the validator can always calculate this committee,
      if it can calculate the one for the current round, as mentioned above.
      This condition only applies if the round is not 1;
      if the round is 1, the @('previous') component must be empty."))
   (xdoc::p
    "Note that above we say `non-empty quorum', not just `quorum'.
     The two are equivalent only if
     the committee (at the previous round) is not empty.
     Our model allows committees to become empty,
     but this non-emptiness check of the previous quorum
     enforces, in the protocol, that committees do not actually become empty.")
   (xdoc::p
    "A correct validator broadcasts the proposal to
     exactly all the correct validators.
     In an implementation,
     a correct validator does not know which validators are correct or faulty,
     and so it will send it to all validators.
     The restrictions is just an artifact of our model:
     since, as explained in @(tsee system-state),
     we do not explicitly model (the states of) faulty validators,
     sending a message to a faulty validator would have no effect in our model,
     because faulty validators can behave arbitrarily
     (except for forging signatures and things like that)
     regardless of which messages they receive or not.")
   (xdoc::p
    "Although a correct validator broadcasts the message
     to all the correct validators,
     there is no guarantee, in our model,
     that the message is eventually received by those validators.
     Our model of the network is that the links are authenticated
     (based on the senders, which are explained in @(tsee message)),
     but delays are unbounded,
     possibly infinite (i.e. a message may never be received).")
   (xdoc::p
    "A faulty validator may choose to send the proposal
     to a subset of validators.
     Thus the only requirement in this case is that
     the destination addresses are a subset of the correct validators.
     There is no need to model the sending to faulty validators,
     for the same reasons explained above.
     By not necessarily sending the message to all correct validators,
     our model avoids assuming any form of reliable broadcast
     (in the technical sense of the BFT literature).
     Equivalently, we could have faulty validators
     send messages to all correct validators,
     since our model, as noted above,
     does not require messages to be eventually delivered.
     For the purpose of properties like blockchain nonforking,
     it does not in fact matter there there is any form of reliable broadcast;
     however, it matters for other kinds of properties,
     so we plan to refine our model when studying those other properties."))
  (b* (((proposal prop) prop)
       ((when (not (set::in prop.author (correct-addresses systate))))
        (set::subset (address-set-fix dests)
                     (correct-addresses systate)))
       ((unless (equal (address-set-fix dests)
                       (correct-addresses systate)))
        nil)
       ((validator-state vstate) (get-validator-state prop.author systate))
       ((unless (= prop.round vstate.round)) nil)
       (commtt (active-committee-at-round prop.round vstate.blockchain))
       ((unless commtt) nil)
       ((unless (set::in prop.author (committee-members commtt))) nil)
       ((unless (set::emptyp
                 (certs-with-author+round prop.author prop.round vstate.dag)))
        nil)
       ((unless (set::emptyp
                 (props-with-round prop.round (omap::keys vstate.proposed))))
        nil)
       ((when (= prop.round 1)) (set::emptyp prop.previous))
       ((when (set::emptyp prop.previous)) nil)
       ((unless (set::subset prop.previous
                             (cert-set->author-set
                              (certs-with-round (1- prop.round) vstate.dag))))
        nil)
       (prev-commtt
        (active-committee-at-round (1- prop.round) vstate.blockchain))
       ((unless (set::subset prop.previous
                             (committee-members prev-commtt)))
        nil)
       ((unless (>= (committee-members-stake prop.previous prev-commtt)
                    (committee-quorum-stake prev-commtt)))
        nil))
    t)
  :guard-hints
  (("Goal"
    :in-theory (enable posp active-committee-at-previous-round-when-at-round)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define propose-next ((prop proposalp)
                      (dests address-setp)
                      (systate system-statep))
  :guard (propose-possiblep prop dests systate)
  :returns (new-systate system-statep)
  :short "New system state resulting from a @('propose') event."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('props') and @('dests') parameters of this function
     are the corresponding components of the @('propose') event.")
   (xdoc::p
    "If the author of the proposal is faulty,
     the only change is to the network:
     a message with the proposal is added for each destination.
     If the author of the proposal is correct,
     the same happens to the network,
     and in addition the validator adds the proposal to
     the map of pending proposals, with associated the empty set,
     because the proposal has no endorsements yet."))
  (b* (((proposal prop) prop)
       (network (get-network-state systate))
       (dests (address-set-fix dests))
       (msgs (make-proposal-messages prop dests))
       (new-network (set::union network msgs))
       (systate (update-network-state new-network systate))
       ((unless (set::in prop.author (correct-addresses systate))) systate)
       ((validator-state vstate) (get-validator-state prop.author systate))
       (new-proposed (omap::update (proposal-fix prop) nil vstate.proposed))
       (new-vstate (change-validator-state vstate :proposed new-proposed))
       (systate (update-validator-state prop.author new-vstate systate)))
    systate)
  :hooks (:fix))
