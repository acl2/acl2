; AleoBFT Library
;
; Copyright (C) 2024 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOBFT-STAKE")

(include-book "system-states")
(include-book "committees")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ transitions-store
  :parents (transitions)
  :short "Transitions for certificate storage."
  :long
  (xdoc::topstring
   (xdoc::p
    "Here we define the system state transitions
     caused by @('store') events.")
   (xdoc::p
    "A certificate storage event involves just one correct validator.")
   (xdoc::p
    "The event identifies, besides a validator address, also a certificate,
     which is moved from the buffer to the DAG.
     In addition, if the validator had endorsed the certificate,
     the author-round pair of the certificate is removed from
     the set of endorsed author-round pairs;
     see @(see transitions-create) about these pairs.")
   (xdoc::p
    "But in order for this event to happen,
     the signers of the certificate must form a quorum
     in the active committee of the certificate's round.
     Thid checks is needed because
     an equivocal certificate could be signed by faulty validators
     and broadcast on the network, and make it to a validator's buffer.
     The check on signers is critical to prevent equivocation in DAGs
     (equivocal certificates may be in the network and buffers,
     but not in DAGs).")
   (xdoc::p
    "In addition, for this event to occur,
     all the previous certificates referenced by the certificate
     must be already in the DAG.
     This serves to preserve the backward closure of DAGs.
     The rationale, and its relation with AleoBFT implementations,
     is explained in @(see transitions-receive).")
   (xdoc::p
    "The storage of a certiicate into the DAG may result in
     advancing the current round of the validator.
     The rationale is to update a validator that is left behind,
     but this aspect of the model needs further study
     (it does not affect safety properties like blockchain non-forking).")
   (xdoc::p
    "A certificate storage event does not involve the network."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define store-possiblep ((val addressp)
                         (cert certificatep)
                         (systate system-statep))
  :returns (yes/no booleanp)
  :short "Check if a certificate storage event is possible."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('val') and @('cert') inputs of this function are
     the address and certificate in the @('store') event;
     see @(tsee event).")
   (xdoc::p
    "When a certificate is received,
     the (correct) validator puts it into the buffer:
     see @(see transitions-receive).
     From there, it is moved to the DAG
     when the DAG contains all the certificates
     referenced in the @('previous') component of the certificate.
     This is the reason for the buffer:
     certificates may be received out of order,
     and so we need a staging area (the buffer)
     for certificates that cannot be added to the DAG yet.")
   (xdoc::p
    "Importantly, a validator stores the certificate into the DAG
     only if its signers form a quorum
     in the active committee for the certificate's round,
     of which they must be members.
     Thus, the validator must be able to calculate (from its blockchain)
     the committee for the certificate's round, in order to perform the check.
     This check is important because, in our formal model,
     nothing prevents the creation of a new certificate
     with signers completely disjoint from the validator's committee;
     these would have to be faulty signers, but it can still happen.
     So this bad certificate could very well cause equivocation,
     if a validator blindly stored it into the DAG.
     Instead, by having the receiving validator check the signers,
     we avoid that, as proved elsewhere.")
   (xdoc::p
    "The address @('val') of the validator indicated in the event
     must be a correct validator of the system.
     The certificate must be in the buffer of the validator.
     If the certificate's round number is 1,
     there is no requirement on the previous certificates,
     because there are no previous certificates.
     Otherwise, we obtain the certificates in the DAG at the previous round,
     and we check that their authors contain
     the addresses in the @('previous') component of the certificate."))
  (b* (((unless (set::in (address-fix val)
                         (correct-addresses systate)))
        nil)
       ((validator-state vstate) (get-validator-state val systate))
       ((unless (set::in (certificate-fix cert)
                         vstate.buffer))
        nil)
       ((certificate cert) cert)
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

(define store-next ((val addressp)
                    (cert certificatep)
                    (systate system-statep))
  :guard (store-possiblep val cert systate)
  :returns (new-systate system-statep)
  :short "New system state resulting from a @('store') event."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('val') and @('cert') inputs of this function are
     the address and certificate in the @('store') event;
     see @(tsee event).")
   (xdoc::p
    "The certificate is added to the DAG and removed from the buffer.")
   (xdoc::p
    "Furthermore, if the validator has previously endorsed that certificate,
     the author-round pair is removed from the set of pairs,
     because the certificate is now in the DAG.
     The set deletion has no effect if the set does not have the pair,
     so we remove the element unconditionally.")
   (xdoc::p
    "In addition, if the certificate's round number is
     greater than the current round number plus one,
     the current round number is fast-forwarded to
     the certificate's round number minus one.
     The idea is that, if there are certificates,
     such as the one being stored in the DAG,
     which must necessarily come from another validator,
     which are two or more rounds ahead of the validator
     that is storing the certificate into the DAG,
     it indicates that this validator is behind.
     Note that, as required in @(tsee store-possiblep),
     the DAG must contain all the previous certificates,
     which must form a quorum;
     thus, if the validator's round is advanced to the certificate's round,
     the validator can immediately generate its own new certificate
     for that round in our model (or a proposal in a more detailed model).
     This aspect of the protocol needs further study,
     along with the logic for
     round advancement in @('advance') events.")
   (xdoc::p
    "If we advance the round, we also reset the timer,
     by setting it to `running'.
     Although the timer also needs further study,
     its purpose appears to be that a validator
     does not spend excessive time in a round,
     regardless of certificates received.
     In that case, it seems appropriate to reset the timer
     every time the round is advanced.")
   (xdoc::p
    "The network is unaffected."))
  (b* (((certificate cert) cert)
       ((validator-state vstate) (get-validator-state val systate))
       (new-dag (set::insert (certificate-fix cert) vstate.dag))
       (new-buffer (set::delete (certificate-fix cert) vstate.buffer))
       (new-endorsed (set::delete (make-address+pos :address cert.author
                                                    :pos cert.round)
                                  vstate.endorsed))
       ((mv new-round new-timer)
        (if (> cert.round (1+ vstate.round))
            (mv (1- cert.round) (timer-running))
          (mv vstate.round vstate.timer)))
       (new-vstate (change-validator-state vstate
                                           :round new-round
                                           :dag new-dag
                                           :buffer new-buffer
                                           :endorsed new-endorsed
                                           :timer new-timer))
       (systate (update-validator-state val new-vstate systate)))
    systate)
  :guard-hints (("Goal" :in-theory (enable store-possiblep
                                           posp)))
  :hooks (:fix)

  ///

  (defret correct-addresses-of-store-next
    (equal (correct-addresses new-systate)
           (correct-addresses systate))
    :hyp (store-possiblep val cert systate)
    :hints (("Goal" :in-theory (enable store-possiblep))))

  (defret validator-state->round-of-store-next
    (equal (validator-state->round (get-validator-state val1 new-systate))
           (if (and (equal (address-fix val1) (address-fix val))
                    (> (certificate->round cert)
                       (1+ (validator-state->round
                            (get-validator-state val systate)))))
               (1- (certificate->round cert))
             (validator-state->round (get-validator-state val1 systate))))
    :hyp (store-possiblep val cert systate)
    :hints
    (("Goal"
      :in-theory (enable store-possiblep
                         get-validator-state-of-update-validator-state
                         posp))))
  (in-theory (disable validator-state->round-of-store-next))

  (defret validator-state->dag-of-store-next
    (equal (validator-state->dag (get-validator-state val1 new-systate))
           (if (equal val1 (address-fix val))
               (set::insert (certificate-fix cert)
                            (validator-state->dag
                             (get-validator-state val1 systate)))
             (validator-state->dag (get-validator-state val1 systate))))
    :hyp (and (set::in val1 (correct-addresses systate))
              (store-possiblep val cert systate))
    :hints (("Goal" :in-theory (enable store-possiblep))))
  (in-theory (disable validator-state->dag-of-store-next))

  (defret validator-state->buffer-of-store-next
    (equal (validator-state->buffer (get-validator-state val1 new-systate))
           (if (equal val1 (address-fix val))
               (set::delete (certificate-fix cert)
                            (validator-state->buffer
                             (get-validator-state val1 systate)))
             (validator-state->buffer (get-validator-state val1 systate))))
    :hyp (and (set::in val1 (correct-addresses systate))
              (store-possiblep val cert systate))
    :hints (("Goal" :in-theory (enable store-possiblep))))
  (in-theory (disable validator-state->buffer-of-store-next))

  (defret validator-state->endorsed-of-store-next
    (equal (validator-state->endorsed (get-validator-state val1 new-systate))
           (if (equal (address-fix val1) (address-fix val))
               (set::delete (make-address+pos
                             :address (certificate->author cert)
                             :pos (certificate->round cert))
                            (validator-state->endorsed
                             (get-validator-state val systate)))
             (validator-state->endorsed
              (get-validator-state val1 systate))))
    :hyp (store-possiblep val cert systate)
    :hints
    (("Goal"
      :in-theory (enable store-possiblep
                         get-validator-state-of-update-validator-state))))
  (in-theory (disable validator-state->endorsed-of-store-next))

  (defret validator-state->last-of-store-next
    (equal (validator-state->last (get-validator-state val1 new-systate))
           (validator-state->last (get-validator-state val1 systate)))
    :hyp (store-possiblep val cert systate)
    :hints
    (("Goal"
      :in-theory (enable store-possiblep
                         get-validator-state-of-update-validator-state
                         nfix))))

  (defret validator-state->blockchain-of-store-next
    (equal (validator-state->blockchain (get-validator-state val1 new-systate))
           (validator-state->blockchain (get-validator-state val1 systate)))
    :hyp (store-possiblep val cert systate)
    :hints
    (("Goal"
      :in-theory (enable store-possiblep
                         get-validator-state-of-update-validator-state))))

  (defret validator-state->committed-of-store-next
    (equal (validator-state->committed (get-validator-state val1 new-systate))
           (validator-state->committed (get-validator-state val1 systate)))
    :hyp (store-possiblep val cert systate)
    :hints
    (("Goal"
      :in-theory (enable store-possiblep
                         get-validator-state-of-update-validator-state))))

  (defret validator-state->timer-of-store-next
    (equal (validator-state->timer (get-validator-state val1 new-systate))
           (if (and (equal (address-fix val1) (address-fix val))
                    (> (certificate->round cert)
                       (1+ (validator-state->round
                            (get-validator-state val systate)))))
               (timer-running)
             (validator-state->timer (get-validator-state val1 systate))))
    :hyp (store-possiblep val cert systate)
    :hints
    (("Goal"
      :in-theory (enable store-possiblep
                         get-validator-state-of-update-validator-state))))
  (in-theory (disable validator-state->timer-of-store-next))

  (defret get-network-state-of-store-next
    (equal (get-network-state (store-next val cert systate))
           (get-network-state systate))))
