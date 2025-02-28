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

(defxdoc+ transitions-certify
  :parents (transitions)
  :short "Transitions for proposal certification."
  :long
  (xdoc::topstring
   (xdoc::p
    "Once a correct validator has received
     enough endorsing signatures for a pending proposal,
     i.e. the signers (author and endorsers) form a quorum,
     the validator creates and broadcasts a certificate.")
   (xdoc::p
    "A faulty validator may also create and broadcast a certificate,
     but it is not constrained to have a quorum of signers.
     However, in order to include the signature of a correct validator,
     that correct validator must have signed the proposal,
     i.e. there must be a message, in the network,
     from that correct validator that endorses the proposal.
     Since faulty validators have no internal state in our model,
     we model certificate creation by faulty validators as an atomic event,
     which uses zero or more endorsing messages from the network,
     and puts their signatures (represented as the endorsing addresses)
     into the certificate.
     Importantly, the endorsing messages are not consumed:
     this way, we can model the fact that a faulty validator
     may create different certificates with the same proposal
     but with different sets of endorsers,
     chosen among the ones available in endorsing messages.")
   (xdoc::p
    "Either way, the certificate is broadcast to a set of validators.
     For certain properties like blockchain nonforking,
     it does not matter that the certificate actually goes to all validators;
     there is no need to model any form of reliable broadcast."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define certify-possiblep ((cert certificatep)
                           (systate system-statep))
  :returns (yes/no booleanp)
  :short "Check if a @('certify') event is possible."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('cert') parameter of this function
     is the corresponding component of the @('certify') event.
     The other component of the event is not needed in this predicate.")
   (xdoc::p
    "The validator in question is the author of the certificate.")
   (xdoc::p
    "If the validator is faulty,
     for each endorser in the certificate,
     there must be a message, in the network,
     from that endorser for the proposal of the certificate.
     As a special case, if the certificate has no endorsers,
     no such message is required to be in the network:
     nothing prevents a faulty validator from authoring a proposal
     and immediately certifying with no additional signatures;
     the certificate will not be accepted by correct validators,
     but the certificate can still be generated.")
   (xdoc::p
    "If the validator is correct,
     no message is required to be in the network,
     because endorsing signatures are incorporated into the validator state
     via separate @('augment') events.
     The @('certify') event can happen when
     the proposal of the certificate is a pending one in the validator state,
     the endorsers are the ones associated to the proposal in the map,
     and the signers (author and endorsers) form a quorum
     in the active committee for the proposal's round."))
  (b* (((certificate cert) cert)
       ((proposal prop) cert.proposal)
       ((when (not (set::in prop.author (correct-addresses systate))))
        (set::subset (make-endorsement-messages prop cert.endorsers)
                     (get-network-state systate)))
       ((validator-state vstate) (get-validator-state prop.author systate))
       (prop+endors (omap::assoc prop vstate.proposed))
       ((unless prop+endors) nil)
       ((unless (equal cert.endorsers (cdr prop+endors))) nil))
    t)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define certify-next ((cert certificatep)
                      (dests address-setp)
                      (systate system-statep))
  :guard (certify-possiblep cert systate)
  :returns (new-systate system-statep)
  :short "New system state resulting from a @('certify') event."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the validator is correct,
     the proposal is removed from the map of pending proposals,
     and the certificate is added to the DAG.")
   (xdoc::p
    "Whether the validator is correct or faulty,
     a message with the certificate is added to the network,
     for each of the destinations indicated in the event."))
  (b* (((certificate cert) cert)
       ((proposal prop) cert.proposal)
       (network (get-network-state systate))
       (new-msgs (make-certificate-messages cert dests))
       (new-network (set::union new-msgs network))
       (systate (update-network-state new-network systate))
       ((when (not (set::in prop.author (correct-addresses systate))))
        systate)
       ((validator-state vstate) (get-validator-state prop.author systate))
       (new-proposed (omap::delete prop vstate.proposed))
       (new-dag (set::insert (certificate-fix cert) vstate.dag))
       (new-vstate
        (change-validator-state vstate :proposed new-proposed :dag new-dag))
       (systate (update-validator-state prop.author new-vstate systate)))
    systate)
  :hooks (:fix)

  ///

  (defret correct-addresses-of-certify-next
    (equal (correct-addresses new-systate)
           (correct-addresses systate)))

  (local (in-theory (enable get-validator-state-of-update-validator-state)))

  (defret validator-state->round-of-certify-next
    (equal (validator-state->round (get-validator-state val new-systate))
           (validator-state->round (get-validator-state val systate))))

  (defret validator-state->dag-of-certify-next
    (equal (validator-state->dag (get-validator-state val new-systate))
           (if (and (equal (address-fix val) (certificate->author cert))
                    (set::in (address-fix val) (correct-addresses systate)))
               (set::insert (certificate-fix cert)
                            (validator-state->dag
                             (get-validator-state val systate)))
             (validator-state->dag (get-validator-state val systate))))
    :hints (("Goal" :in-theory (enable certificate->author))))
  (in-theory (disable validator-state->dag-of-certify-next))

  (defret validator-state->proposed-of-certify-next
    (equal (validator-state->proposed (get-validator-state val new-systate))
           (if (and (equal (address-fix val) (certificate->author cert))
                    (set::in (address-fix val) (correct-addresses systate)))
               (omap::delete (certificate->proposal cert)
                             (validator-state->proposed
                              (get-validator-state val systate)))
             (validator-state->proposed (get-validator-state val systate))))
    :hints (("Goal" :in-theory (enable certificate->author))))
  (in-theory (disable validator-state->proposed-of-certify-next))

  (defret validator-state->endorsed-of-certify-next
    (equal (validator-state->endorsed (get-validator-state val new-systate))
           (validator-state->endorsed (get-validator-state val systate))))

  (defret validator-state->last-of-certify-next
    (equal (validator-state->last (get-validator-state val new-systate))
           (validator-state->last (get-validator-state val systate)))
    :hints (("Goal" :in-theory (enable nfix))))

  (defret validator-state->blockchain-of-certify-next
    (equal (validator-state->blockchain (get-validator-state val new-systate))
           (validator-state->blockchain (get-validator-state val systate))))

  (defret validator-state->committed-of-certify-next
    (equal (validator-state->committed (get-validator-state val new-systate))
           (validator-state->committed (get-validator-state val systate))))

  (defret get-network-state-of-certify-next
    (equal (get-network-state new-systate)
           (set::union (make-certificate-messages cert dests)
                       (get-network-state systate)))
    :hints (("Goal" :in-theory (enable certificate->author))))
  (in-theory (disable get-network-state-of-certify-next)))
