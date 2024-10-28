; AleoBFT Library
;
; Copyright (C) 2024 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOBFT-DYNAMIC")

(include-book "system-states")
(include-book "committees")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ transitions-receive-certificate
  :parents (transitions)
  :short "Transitions for certificate receipt."
  :long
  (xdoc::topstring
   (xdoc::p
    "Here we define the system state transitions
     caused by @('receive-certificate') events.")
   (xdoc::p
    "As defined in @(see system-states),
     the network contains a set of messages,
     each of which consists of a certificate and a recipient address.
     The receipt of a certificate is modeled by
     removing the message from the network
     and adding the certificate to the validator's buffer.
     In addition, if the validator had endorsed the certificate,
     the author-round pair of the certificate is removed from
     the set of endorsed author-round pairs;
     see @(see transitions-create-certificate) about these pairs.")
   (xdoc::p
    "Importantly, a validator accepts the certificate from the network
     only if its signers form a quorum
     in the active committee for the certificate round.
     Thus, the validator must be able to calculate (from its blockchain)
     the committee for the certificate's round, in order to perform the check.
     This check is important because, in our formal model,
     nothing prevents the creation of a new certificate
     with signers completely disjoint from the validator's committee;
     these would have to be faulty signers,
     but our formal model, which models all possible validators,
     could contain many faulty validators that can sign a certificate.
     So this bad certificate could very well cause equivocation,
     if a validator blindly accepted it from the network.
     Instead, by having the receiving validator check the signers,
     we avoid that, as proved elsewhere.")
   (xdoc::p
    "Also importantly, and for a similar reason,
     a validator accepts the certificate from the network
     only if the referenced previous certificates
     form a quorum in the active committee
     of the round just before the certificate,
     unless the certificate's round is 1,
     in which case the certificate
     must have no references to previous certificates.
     If the certificate's round is not 1,
     in order to make the quorum check,
     the validator must be able to calculate that active committee.")
   (xdoc::p
    "A message may be received by any validator in the system,
     not only validators in the current committee.
     The rationale for this modeling approach
     is explained in @(tsee create-certificate-next).")
   (xdoc::p
    "The reason for putting the certificate into the buffer,
     and not into the DAG, is to ensure that DAGs are backward-closed.
     A certificate is moved from the buffer to the DAG
     only after all the predecessor certificates referenced by the certificate
     are already in the DAG.
     An AleoBFT implementation would normally actively request
     those certificates from other validators.
     We keep our model simpler by not explicitly modeling that,
     but instead letting those certificates arrive non-deterministically,
     in line with our eventually reliable network model.
     The move of certificates from buffers to DAGs
     is modeled via @('store-certificate') events.")
   (xdoc::p
    "Certificate receipt and certificate creation are
     the only events that involve the network component of the system state.
     All the other events involve just one validator.
     As explained in @(see transitions-create-certificate),
     certificate creation involves multiple validators;
     in constract, certificate receipt involve just one validator."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define receive-certificate-possiblep ((msg messagep) (systate system-statep))
  :returns (yes/no booleanp)
  :short "Check if a certificate receipt event is possible."
  :long
  (xdoc::topstring
   (xdoc::p
    "The input @('msg') of this function is
     the message in the @('receive-certificate') event;
     see @(tsee event).")
   (xdoc::p
    "The messages must be in the network.")
   (xdoc::p
    "The destination must be a validator in the system.
     Recall that, as explained in @(tsee create-certificate-next),
     in our model certificates are broadcast to all validators,
     not just the ones in the committee.")
   (xdoc::p
    "We actually make the stronger check that the validator is a correct one.
     This is in fact an invariant,
     because @(tsee create-certificate-next) only creates messages
     with addresses of correct validators as destination.
     But we do not have that invariant available here,
     since we prove that from the definitions of the transitions,
     which therefore must be defined before we can prove the invariant.")
   (xdoc::p
    "The validator must be able to calculate
     the active committee for the certificate's round,
     and the signers of the certificate must form a quorum.")
   (xdoc::p
    "If the certificate's round is 1,
     the certificate must have no references to previous certificates."))
  (b* (((unless (set::in (message-fix msg)
                         (get-network-state systate)))
        nil)
       (dest (message->destination msg))
       ((certificate cert) (message->certificate msg))
       ((unless (set::in dest (correct-addresses systate)))
        nil)
       (vstate (get-validator-state dest systate))
       (commtt (active-committee-at-round cert.round
                                          (validator-state->blockchain vstate)
                                          (all-addresses systate)))
       ((unless commtt) nil)
       (signers (certificate->signers cert))
       ((unless (set::subset signers (committee-members commtt)))
        nil)
       ((unless (= (set::cardinality signers)
                   (committee-quorum commtt)))
        nil))
    (if (= cert.round 1)
        (= (set::cardinality cert.previous)
           0)
      (b* ((prev-commtt (active-committee-at-round
                         (1- cert.round)
                         (validator-state->blockchain vstate)
                         (all-addresses systate))))
        (and prev-commtt
             (set::subset cert.previous (committee-members prev-commtt))
             (= (set::cardinality cert.previous)
                (committee-quorum prev-commtt))))))
  :guard-hints (("Goal" :in-theory (enable posp)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define receive-certificate-next ((msg messagep) (systate system-statep))
  :guard (receive-certificate-possiblep msg systate)
  :returns (new-systate system-statep)
  :short "New system state resulting from a @('receive-certificate') event."
  :long
  (xdoc::topstring
   (xdoc::p
    "The certificate is added to the buffer of the destination validator.
     Recall that @(tsee receive-certificate-possiblep) requires
     the destination address to be of a correct validator.")
   (xdoc::p
    "The message is removed from the network.")
   (xdoc::p
    "Furthermore, if the validator has previously endorsed that certificate,
     the author-round pair is removed from the set of pairs,
     because the certificate is now in the buffer.
     The set deletion has no effect if the set does not have the pair,
     so we remove the element unconditionally."))
  (b* (((certificate cert) (message->certificate msg))
       (dest (message->destination msg))
       ((validator-state vstate) (get-validator-state dest systate))
       (new-buffer (set::insert cert vstate.buffer))
       (new-endorsed (set::delete (make-address+pos :address cert.author
                                                    :pos cert.round)
                                  vstate.endorsed))
       (new-vstate (change-validator-state vstate
                                           :buffer new-buffer
                                           :endorsed new-endorsed))
       (systate (update-validator-state dest new-vstate systate))
       (network (get-network-state systate))
       (new-network (set::delete (message-fix msg) network))
       (systate (update-network-state new-network systate)))
    systate)
  :guard-hints (("Goal" :in-theory (enable receive-certificate-possiblep)))
  :hooks (:fix)

  ///

  (defret all-addresses-of-receive-certificate-next
    (equal (all-addresses new-systate)
           (all-addresses systate))
    :hyp (receive-certificate-possiblep msg systate)
    :hints (("Goal" :in-theory (enable receive-certificate-possiblep))))

  (defret correct-addresses-of-receive-certificate-next
    (equal (correct-addresses new-systate)
           (correct-addresses systate))
    :hyp (receive-certificate-possiblep msg systate)
    :hints (("Goal" :in-theory (enable receive-certificate-possiblep))))

  (defret faulty-addresses-of-receive-certificate-next
    (equal (faulty-addresses new-systate)
           (faulty-addresses systate))
    :hyp (receive-certificate-possiblep msg systate)
    :hints (("Goal" :in-theory (enable receive-certificate-possiblep))))

  (defret validator-state->dag-of-receive-certificate-next
    (equal (validator-state->dag (get-validator-state val new-systate))
           (validator-state->dag (get-validator-state val systate)))
    :hyp (receive-certificate-possiblep msg systate)
    :hints
    (("Goal" :in-theory (enable
                         receive-certificate-possiblep
                         get-validator-state-of-update-validator-state))))

  (defret validator-state->buffer-of-receive-certificate-next
    (equal (validator-state->buffer (get-validator-state val new-systate))
           (if (equal val (message->destination msg))
               (set::insert (message->certificate msg)
                            (validator-state->buffer
                             (get-validator-state val systate)))
             (validator-state->buffer (get-validator-state val systate))))
    :hyp (and (set::in val (correct-addresses systate))
              (receive-certificate-possiblep msg systate))
    :hints
    (("Goal" :in-theory (enable receive-certificate-possiblep))))

  (defret validator-state->endorsed-of-receive-certificate-next
    (equal (validator-state->endorsed
            (get-validator-state val new-systate))
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
    :hyp (receive-certificate-possiblep msg systate)
    :hints
    (("Goal"
      :in-theory (enable receive-certificate-possiblep
                         get-validator-state-of-update-validator-state))))

  (defret validator-state->last-of-receive-certificate-next
    (equal (validator-state->last (get-validator-state val new-systate))
           (validator-state->last (get-validator-state val systate)))
    :hyp (receive-certificate-possiblep msg systate)
    :hints
    (("Goal" :in-theory (enable
                         receive-certificate-possiblep
                         get-validator-state-of-update-validator-state
                         nfix))))

  (defret validator-state->blockchain-of-receive-certificate-next
    (equal (validator-state->blockchain (get-validator-state val new-systate))
           (validator-state->blockchain (get-validator-state val systate)))
    :hyp (receive-certificate-possiblep msg systate)
    :hints
    (("Goal" :in-theory (enable
                         receive-certificate-possiblep
                         get-validator-state-of-update-validator-state))))

  (defret validator-state->committed-of-receive-certificate-next
    (equal (validator-state->committed (get-validator-state val new-systate))
           (validator-state->committed (get-validator-state val systate)))
    :hyp (receive-certificate-possiblep msg systate)
    :hints
    (("Goal" :in-theory (enable
                         receive-certificate-possiblep
                         get-validator-state-of-update-validator-state))))

  (defret get-network-state-of-receive-certificate-next
    (equal (get-network-state new-systate)
           (set::delete (message-fix msg)
                        (get-network-state systate))))

  (in-theory (disable validator-state->dag-of-receive-certificate-next
                      validator-state->buffer-of-receive-certificate-next
                      validator-state->endorsed-of-receive-certificate-next
                      validator-state->last-of-receive-certificate-next
                      validator-state->blockchain-of-receive-certificate-next
                      validator-state->committed-of-receive-certificate-next
                      get-network-state-of-receive-certificate-next)))
