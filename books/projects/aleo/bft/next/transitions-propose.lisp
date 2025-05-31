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

(include-book "system-states")
(include-book "committees")

(local (include-book "kestrel/utilities/nfix" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ transitions-propose
  :parents (transitions)
  :short "Transitions for proposal creation."
  :long
  (xdoc::topstring
   (xdoc::p
    "Here we define the system state changes caused by @('propose') events.")
   (xdoc::p
    "A correct validator creates a proposal only under certain conditions;
     in particular, it never creates an equivocal proposal,
     i.e. one with the same author and round as an existing one.
     A faulty validator is not so constrained,
     but it cannot forge signatures of correct validators
     (because if a validator's private key is compromised,
     the validator is considered faulty).")
   (xdoc::p
    "Either way, the proposal is broadcast to other validators.
     A correct validator sends it exactly to
     all the other members of the active committee;
     a faulty validator may send it to any validators.
     However, in order to model the possibility that
     a faulty validator in the committee
     forwards a proposal from a correct validator
     to a faulty validator not in the committee,
     so that the latter might endorse the proposal
     and send the endorsement back to the proposer,
     we relax our model of proposal broadcasting
     by allowing a proposal from a correct validator
     to be sent also to faulty validators not in the committee.")
   (xdoc::p
    "If the validator is correct,
     it stores the proposal into its internal state,
     along with information about endorsements received by other validators;
     initially there are no such endorsements."))
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
    "The @('prop') and @('dests') parameters of this function
     are the corresponding components of the @('propose') event.")
   (xdoc::p
    "The author of the proposal identifies
     the validator that creates the proposal.
     Since signatures of correct validators cannot be forged,
     a faulty validator cannot impersonate a correct one,
     and thus the fact that the proposal's author is a correct validator
     means that the proposal is indeed created by that validator.
     If the author of the proposal is faulty,
     it does not matter whether
     the proposal actually originates from that validator,
     or instead it originates from some other (faulty) validator
     impersonating the author;
     the correctness of the protocol does not not depend on that.
     If the author of the proposal is a faulty validator,
     there are almost no other requirements:
     nothing prevents a faulty validator from
     generating a proposal with arbitrary
     round, transactions, and previous certificate addresses.")
   (xdoc::p
    "The `almost' above refers to the fact that we constrain faulty validators
     to send a proposal to at least one validator.
     This is merely a modeling convenience, not a real restriction:
     if a faulty validator creates a proposal and sends it to nobody,
     the event would cause no actual change to our modeled system state,
     because faulty validators have no external state.
     If there is at least one destination for the proposal,
     then there is a state change, consisting of
     at least one message being added to the network.")
   (xdoc::p
    "If the proposal's author is correct, the following conditions apply;
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
     "The validator must not have already created
      another proposal with the same round,
      because that would cause equivocation.
      Not only the DAG must include no certificate with that author and round,
      but also the pending proposals must not include a proposal with that round
      (as proved elsewhere, it is an invariant that
      all the pending proposals are authored by the validator,
      so there is no need to check the author).")
    (xdoc::li
     "The certificates referenced in the @('previous') component
      must be present in the DAG,
      and their authors must form a non-empty quorum in
      the active committee for the round just before the current one
      (which, as noted above, is the same as the proposal);
      note that the validator can always calculate this committee,
      if it can calculate the one for the current round, as mentioned above.
      This condition only applies if the round is not 1;
      if the round is 1, the @('previous') component must be empty."))
   (xdoc::p
    "For the case of a round that is not 1,
     we use @(tsee committee-validators-stake) for the quorum test;
     we do not check that the previous certificate authors
     are in fact members of the committee at the previous round.
     As proved elsewhere, it is an invariant that
     those authors are indeed members of the committee;
     so the check can be safely skipped.")
   (xdoc::p
    "Note that above we say `non-empty quorum', not just `quorum'.
     The two are equivalent only if
     the committee (at the previous round) is not empty.
     Our model allows committees to become empty,
     but this non-emptiness check of the previous quorum
     enforces, in the protocol, that committees do not actually become empty.
     If they do, the protocol effectively stops;
     correct validators cannot create new certificates.")
   (xdoc::p
    "A correct validator broadcasts the proposal to
     all the other validators in the active committee,
     which it calculates as already mentioned above.
     These may include both correct and faulty validators:
     the proposal author cannot distinguish them.
     Additionally, we allow additional messages to other faulty validators,
     for the modeling reason described in @(see transitions-propose).")
   (xdoc::p
    "A faulty validator may send the proposal to any set of validators,
     correct or faulty, whether part of (any) committees or not.")
   (xdoc::p
    "Note that we do not model any form of reliable broadcast here.
     For the purpose of properties like blockchain nonforking,
     it does not matter there there is any form of reliable broadcast;
     however, it matters for other kinds of properties,
     so we plan to refine our model when studying those other properties."))
  (b* (((proposal prop) prop)
       ((when (not (set::in prop.author (correct-addresses systate))))
        (not (set::emptyp (address-set-fix dests))))
       ((validator-state vstate) (get-validator-state prop.author systate))
       ((unless (= prop.round vstate.round)) nil)
       (commtt (active-committee-at-round prop.round vstate.blockchain))
       ((unless commtt) nil)
       ((unless (set::in prop.author (committee-members commtt))) nil)
       ((unless (set::subset (set::delete prop.author
                                          (committee-members commtt))
                             (address-set-fix dests)))
        nil)
       ((when (set::in prop.author (address-set-fix dests))) nil)
       ((unless (set::subset (set::intersect (address-set-fix dests)
                                             (correct-addresses systate))
                             (committee-members commtt)))
        nil)
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
       ((unless (>= (committee-validators-stake prop.previous prev-commtt)
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
    "The @('prop') and @('dests') parameters of this function
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
       (msgs (make-proposal-messages prop dests))
       (new-network (set::union network msgs))
       (systate (update-network-state new-network systate))
       ((unless (set::in prop.author (correct-addresses systate))) systate)
       ((validator-state vstate) (get-validator-state prop.author systate))
       (new-proposed (omap::update (proposal-fix prop) nil vstate.proposed))
       (new-vstate (change-validator-state vstate :proposed new-proposed))
       (systate (update-validator-state prop.author new-vstate systate)))
    systate)
  :hooks (:fix)

  ///

  (defret correct-addresses-of-propose-next
    (equal (correct-addresses new-systate)
           (correct-addresses systate)))

  (local (in-theory (enable get-validator-state-of-update-validator-state)))

  (defret validator-state->round-of-propose-next
    (equal (validator-state->round (get-validator-state val new-systate))
           (validator-state->round (get-validator-state val systate))))

  (defret validator-state->dag-of-propose-next
    (equal (validator-state->dag (get-validator-state val new-systate))
           (validator-state->dag (get-validator-state val systate))))

  (defret validator-state->proposed-of-propose-next
    (equal (validator-state->proposed (get-validator-state val new-systate))
           (if (and (equal (address-fix val) (proposal->author prop))
                    (set::in (address-fix val) (correct-addresses systate)))
               (omap::update (proposal-fix prop)
                             nil
                             (validator-state->proposed
                              (get-validator-state val systate)))
             (validator-state->proposed (get-validator-state val systate)))))
  (in-theory (disable validator-state->proposed-of-propose-next))

  (defret validator-state->endorsed-of-propose-next
    (equal (validator-state->endorsed (get-validator-state val new-systate))
           (validator-state->endorsed (get-validator-state val systate))))

  (defret validator-state->last-of-propose-next
    (equal (validator-state->last (get-validator-state val new-systate))
           (validator-state->last (get-validator-state val systate))))

  (defret validator-state->blockchain-of-propose-next
    (equal (validator-state->blockchain (get-validator-state val new-systate))
           (validator-state->blockchain (get-validator-state val systate))))

  (defret validator-state->committed-of-propose-next
    (equal (validator-state->committed (get-validator-state val new-systate))
           (validator-state->committed (get-validator-state val systate))))

  (defret get-network-state-of-propose-next
    (equal (get-network-state new-systate)
           (set::union (get-network-state systate)
                       (make-proposal-messages prop dests))))
  (in-theory (disable get-network-state-of-propose-next)))
