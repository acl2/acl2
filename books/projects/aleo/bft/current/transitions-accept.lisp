; AleoBFT Library
;
; Copyright (C) 2024 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOBFT-ARXIV")

(include-book "system-states")
(include-book "committees")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ transitions-accept
  :parents (transitions)
  :short "Transitions for certificate acceptance."
  :long
  (xdoc::topstring
   (xdoc::p
    "Here we define the system state transitions
     caused by @('accept') events.")
   (xdoc::p
    "As defined in @(see system-states),
     the network contains a set of messages,
     each of which consists of a certificate and a recipient address;
     these messages are added to the network via @('create') events.
     The receipt of a certificate is modeled by
     removing the message from the network
     and adding the certificate to the validator's DAG,
     under suitable conditions;
     if these conditions are not satisfied,
     the message is not delivered, and stays in the network,
     from where it may or may not be eventually delivered,
     should all the conditions become true.
     This is why this kind of event is
     called @('accept') and not @('receive'):
     it involves the validator accepting, not just receiving, the certificate.
     This means that, in our model, the network may actually model
     also certain ``incoming message buffers'' of validators:
     in an implementation, messages are delivered to validators,
     and the validators may delay them, or reject them outright;
     in our model, these situations correspond to
     the messages staying in the network component of the system state.")
   (xdoc::p
    "A message may be accepted by any validator in the system,
     not only validators in the current committee.
     The rationale for this modeling approach
     is explained in @(tsee create-next).")
   (xdoc::p
    "In order for the certificate to be accepted,
     all the previous certificates referenced by the certificate
     must be already in the DAG.
     This serves to preserve the backward closure of DAGs.
     Even though this condition may not be fulfilled at some point,
     it may be fulfilled in the future,
     after more certificates have been accepted by the validator;
     at that point, the certificate in question may be accepted.
     An AleoBFT implementation would normally actively request
     the missing predecessor certificates from other validators,
     but we keep our model simpler by not explicitly modeling that,
     but instead letting those certificates arrive non-deterministically,
     in line with our eventually reliable network model.")
   (xdoc::p
    "As also mentioned in @(tsee create-endorser-possiblep),
     nothing prevents a @('create') event from modeling
     the creation of an equivocal certificate,
     signed by only faulty validators.
     Thus, in order for the certificate to be accepted,
     the signers of the certificate must form a quorum
     in the active committee of the certificate's round.
     If this condition is not fulfilled at some point,
     it will never be fulfilled in the future,
     because it depends only on the certificate itself.
     Thus, the message will sit in the network forever.
     We could extend our model with events to discard that message,
     but that is not necessary for proving the current properties of interest.")
   (xdoc::p
    "If the certificate is accepted,
     and if the validator had endorsed the certificate,
     the author-round pair of the certificate is removed from
     the set of endorsed author-round pairs;
     see @(see transitions-create) about these pairs.
     This is because now the validator has the full certificate.")
   (xdoc::p
    "Certificate acceptance and certificate creation are
     the only events that involve the network component of the system state.
     All the other events involve just one validator.
     As explained in @(see transitions-create),
     certificate creation involves multiple validators;
     in constract, certificate acceptance involves just one validator."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define accept-possiblep ((msg messagep) (systate system-statep))
  :returns (yes/no booleanp)
  :short "Check if a certificate acceptance event is possible."
  :long
  (xdoc::topstring
   (xdoc::p
    "The input @('msg') of this function is
     the message in the @('accept') event;
     see @(tsee event).")
   (xdoc::p
    "The messages must be in the network.")
   (xdoc::p
    "The destination must be a correct validator in the system.
     Recall that, as explained in @(tsee create-next),
     in our model certificates are broadcast to all validators,
     not just the ones in the committee.")
   (xdoc::p
    "The certificate's signers must form a quorum
     in the active committee for the certificate's round,
     of which they must be members.
     Thus, the validator must be able to calculate (from its blockchain)
     the committee for the certificate's round, in order to perform the check.
     This check is important because, in our formal model,
     nothing prevents the creation of a new certificate
     with signers completely disjoint from the validator's committee;
     these would have to be faulty signers, but it can still happen.
     So this bad certificate could very well cause equivocation,
     if a validator blindly accepted it.
     Instead, by having the receiving validator check the signers,
     we avoid that, as proved elsewhere.")
   (xdoc::p
    "If the certificate's round number is 1,
     there is no requirement on the previous certificates,
     because there are no previous certificates.
     Otherwise, we obtain the certificates in the DAG at the previous round,
     and we check that their authors contain
     the addresses in the @('previous') component of the certificate."))
  (b* (((unless (set::in (message-fix msg)
                         (get-network-state systate)))
        nil)
       (dest (message->destination msg))
       ((unless (set::in dest (correct-addresses systate)))
        nil)
       ((validator-state vstate) (get-validator-state dest systate))
       ((certificate cert) (message->certificate msg))
       (commtt (active-committee-at-round cert.round vstate.blockchain))
       ((unless commtt)
        nil)
       (signers (certificate->signers cert))
       ((unless (set::subset signers (committee-members commtt)))
        nil)
       ((unless (>= (committee-members-stake signers commtt)
                    (committee-quorum-stake commtt)))
        nil)
       ((when (= cert.round 1))
        t)
       ((unless (set::subset cert.previous
                             (cert-set->author-set
                              (certs-with-round (1- cert.round) vstate.dag))))
        nil))
    t)
  :guard-hints (("Goal" :in-theory (enable posp)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define accept-next ((msg messagep) (systate system-statep))
  :guard (accept-possiblep msg systate)
  :returns (new-systate system-statep)
  :short "New system state resulting from an @('accept') event."
  :long
  (xdoc::topstring
   (xdoc::p
    "The certificate is added to the DAG of the destination validator.")
   (xdoc::p
    "If the validator has previously endorsed that certificate,
     the author-round pair is removed from the set of pairs,
     because the certificate is now in the DAG.
     The set deletion has no effect if the set does not have the pair,
     so we remove the element unconditionally.")
   (xdoc::p
    "The message is removed from the network."))
  (b* (((certificate cert) (message->certificate msg))
       (dest (message->destination msg))
       ((validator-state vstate) (get-validator-state dest systate))
       (new-dag (set::insert cert vstate.dag))
       (new-endorsed (set::delete (make-address+pos :address cert.author
                                                    :pos cert.round)
                                  vstate.endorsed))
       (new-vstate (change-validator-state vstate
                                           :dag new-dag
                                           :endorsed new-endorsed))
       (systate (update-validator-state dest new-vstate systate))
       (network (get-network-state systate))
       (new-network (set::delete (message-fix msg) network))
       (systate (update-network-state new-network systate)))
    systate)
  :guard-hints (("Goal" :in-theory (enable accept-possiblep)))
  :hooks (:fix)

  ///

  (defret correct-addresses-of-accept-next
    (equal (correct-addresses new-systate)
           (correct-addresses systate))
    :hyp (accept-possiblep msg systate)
    :hints (("Goal" :in-theory (enable accept-possiblep))))

  (defret validator-state->round-of-accept-next
    (equal (validator-state->round (get-validator-state val new-systate))
           (validator-state->round (get-validator-state val systate)))
    :hyp (accept-possiblep msg systate)
    :hints
    (("Goal" :in-theory (enable
                         accept-possiblep
                         get-validator-state-of-update-validator-state))))

  (defret validator-state->dag-of-accept-next
    (equal (validator-state->dag (get-validator-state val new-systate))
           (if (equal (address-fix val) (message->destination msg))
               (set::insert (message->certificate msg)
                            (validator-state->dag
                             (get-validator-state val systate)))
             (validator-state->dag (get-validator-state val systate))))
    :hyp (accept-possiblep msg systate)
    :hints
    (("Goal" :in-theory (enable accept-possiblep))))
  (in-theory (disable validator-state->dag-of-accept-next))

  (defret validator-state->endorsed-of-accept-next
    (equal (validator-state->endorsed (get-validator-state val new-systate))
           (if (equal (address-fix val) (message->destination msg))
               (set::delete (make-address+pos
                             :address (certificate->author
                                       (message->certificate msg))
                             :pos (certificate->round
                                   (message->certificate msg)))
                            (validator-state->endorsed
                             (get-validator-state val systate)))
             (validator-state->endorsed
              (get-validator-state val systate))))
    :hyp (accept-possiblep msg systate)
    :hints
    (("Goal"
      :in-theory (enable accept-possiblep))))
  (in-theory (disable validator-state->endorsed-of-accept-next))

  (defret validator-state->last-of-accept-next
    (equal (validator-state->last (get-validator-state val new-systate))
           (validator-state->last (get-validator-state val systate)))
    :hyp (accept-possiblep msg systate)
    :hints
    (("Goal" :in-theory (enable
                         accept-possiblep
                         get-validator-state-of-update-validator-state
                         nfix))))

  (defret validator-state->blockchain-of-accept-next
    (equal (validator-state->blockchain (get-validator-state val new-systate))
           (validator-state->blockchain (get-validator-state val systate)))
    :hyp (accept-possiblep msg systate)
    :hints
    (("Goal" :in-theory (enable
                         accept-possiblep
                         get-validator-state-of-update-validator-state))))

  (defret validator-state->committed-of-accept-next
    (equal (validator-state->committed (get-validator-state val new-systate))
           (validator-state->committed (get-validator-state val systate)))
    :hyp (accept-possiblep msg systate)
    :hints
    (("Goal" :in-theory (enable
                         accept-possiblep
                         get-validator-state-of-update-validator-state))))

  (defret get-network-state-of-accept-next
    (equal (get-network-state new-systate)
           (set::delete (message-fix msg)
                        (get-network-state systate))))
  (in-theory (disable get-network-state-of-accept-next)))
