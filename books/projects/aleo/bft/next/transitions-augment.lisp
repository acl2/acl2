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

(defxdoc+ transitions-augment
  :parents (transitions)
  :short "Transitions for proposal augmentation."
  :long
  (xdoc::topstring
   (xdoc::p
    "Here we define the system state changes caused by @('augment') events.")
   (xdoc::p
    "When a correct validator receives an endorsement from another validator,
     it records the endorsement, associated with the pending proposal.
     The endorsement must come from a validator
     in the active committee for the proposal's round.")
   (xdoc::p
    "This kind of events only makes sense for correct validators.
     Faulty validators do not have an explicit internal state in our model,
     so there is nothing to record in their internal state.
     However, as defined in the transitions for @('certify') events,
     faulty validators can still make use of endorsements,
     by using multiple ones at once, as part of creating a certificate."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define augment-possiblep ((prop proposalp)
                           (endor addressp)
                           (systate system-statep))
  :returns (yes/no booleanp)
  :short "Check if an @('augment') event is possible in a system state."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('prop') and @('endor') parameters of this function
     are the corresponding components of the @('augment') event.")
   (xdoc::p
    "The validator affected by this event is the author of the proposal,
     which must be correct in order for this event to happen,
     as explained in @(see transitions-augment).")
   (xdoc::p
    "This event occurs when the network contains an endorsement message
     consisting of the proposal and the endorser
     (which is thus isomorphic to the event).")
   (xdoc::p
    "The validator must have that proposal pending,
     in its finite map from proposals to endorsing addresses.")
   (xdoc::p
    "The validator must be able to calculate
     the active committee for the proposal's round,
     so it can check that the endorsement comes from a member of the committee.
     As explained in @(see transitions-propose),
     although a correct validator only sends proposals to committee members,
     our model allows it to send proposals
     also to faulty validators outside the committee,
     in order to model the possibility that a faulty validator in the committee
     shares the proposal with a faulty validator outside the committee,
     and that the latter validator, for whichever reason,
     endorses it, sending the endorsement to the proposer."))
  (b* (((proposal prop) prop)
       ((unless (set::in prop.author (correct-addresses systate))) nil)
       (msg (make-message-endorsement :proposal prop :endorser endor))
       ((unless (set::in msg (get-network-state systate))) nil)
       ((validator-state vstate) (get-validator-state prop.author systate))
       (prop+endors (omap::assoc (proposal-fix prop) vstate.proposed))
       ((unless prop+endors) nil)
       (commtt (active-committee-at-round prop.round vstate.blockchain))
       ((unless commtt) nil)
       ((unless (set::in (address-fix endor) (committee-members commtt))) nil))
    t)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define augment-next ((prop proposalp)
                      (endor addressp)
                      (systate system-statep))
  :guard (augment-possiblep prop endor systate)
  :returns (new-systate system-statep)
  :short "New system state resulting from an @('augment') event."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('prop') and @('endor') parameters of this function
     are the corresponding components of the @('augment') event.")
   (xdoc::p
    "The message is removed from the network; it is consumed.")
   (xdoc::p
    "The address of the endorser is added to the set of endorser addresses
     associated to the proposal in the finite map in the validator state.
     Recall that, in our model, these addresses represent signatures."))
  (b* (((proposal prop) prop)
       ((validator-state vstate) (get-validator-state prop.author systate))
       (msg (make-message-endorsement :proposal prop :endorser endor))
       (network (get-network-state systate))
       (new-network (set::delete msg network))
       (systate (update-network-state new-network systate))
       (endors (omap::lookup (proposal-fix prop) vstate.proposed))
       (new-endors (set::insert (address-fix endor) endors))
       (new-proposed
        (omap::update (proposal-fix prop) new-endors vstate.proposed))
       (new-vstate (change-validator-state vstate :proposed new-proposed))
       (systate (update-validator-state prop.author new-vstate systate)))
    systate)
  :guard-hints (("Goal" :in-theory (enable augment-possiblep)))
  :hooks (:fix)

  ///

  (defret correct-addresses-of-augment-next
    (equal (correct-addresses new-systate)
           (correct-addresses systate))
    :hyp (augment-possiblep prop endor systate)
    :hints (("Goal" :in-theory (enable augment-possiblep))))

  (local (in-theory (enable get-validator-state-of-update-validator-state)))

  (defret validator-state->round-of-augment-next
    (equal (validator-state->round (get-validator-state val new-systate))
           (validator-state->round (get-validator-state val systate))))

  (defret validator-state->dag-of-augment-next
    (equal (validator-state->dag (get-validator-state val new-systate))
           (validator-state->dag (get-validator-state val systate))))

  (defret validator-state->proposed-of-augment-next
    (equal (validator-state->proposed (get-validator-state val new-systate))
           (if (and (equal (address-fix val) (proposal->author prop))
                    (set::in (address-fix val) (correct-addresses systate)))
               (omap::update
                (proposal-fix prop)
                (set::insert (address-fix endor)
                             (omap::lookup
                              (proposal-fix prop)
                              (validator-state->proposed
                               (get-validator-state val systate))))
                (validator-state->proposed (get-validator-state val systate)))
             (validator-state->proposed (get-validator-state val systate))))
    :hyp (augment-possiblep prop endor systate)
    :hints (("Goal" :in-theory (enable augment-possiblep))))
  (in-theory (disable validator-state->proposed-of-augment-next))

  (defret validator-state->endorsed-of-augment-next
    (equal (validator-state->endorsed (get-validator-state val new-systate))
           (validator-state->endorsed (get-validator-state val systate))))

  (defret validator-state->last-of-augment-next
    (equal (validator-state->last (get-validator-state val new-systate))
           (validator-state->last (get-validator-state val systate))))

  (defret validator-state->blockchain-of-augment-next
    (equal (validator-state->blockchain (get-validator-state val new-systate))
           (validator-state->blockchain (get-validator-state val systate))))

  (defret validator-state->committed-of-augment-next
    (equal (validator-state->committed (get-validator-state val new-systate))
           (validator-state->committed (get-validator-state val systate))))

  (defret get-network-state-of-augment-next
    (equal (get-network-state new-systate)
           (set::delete (message-endorsement prop endor)
                        (get-network-state systate))))
  (in-theory (disable get-network-state-of-augment-next)))
