; AleoBFT Library
;
; Copyright (C) 2024 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOBFT-STATIC")

(include-book "system-states")
(include-book "operations-faults-and-quora")
(include-book "operations-author-round-pairs")
(include-book "operations-previous-certificates")
(include-book "operations-message-creation")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ transitions-create-certificate
  :parents (transitions)
  :short "Transitions for certificate creation."
  :long
  (xdoc::topstring
   (xdoc::p
    "Here we define the system state transitions
     caused by @('create-certificate') events."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define create-certificate-possiblep ((cert certificatep)
                                      (systate system-statep))
  :returns (yes/no booleanp)
  :short "Check if a @('create-certificate') event is possible."
  :long
  (xdoc::topstring
   (xdoc::p
    "The author of the certificate must be a validator in the system.
     The validator may be correct or faulty:
     nothing prevents a faulty validator from creating a good certificate
     signed by enough validators.")
   (xdoc::p
    "If the author is a correct validator,
     the round of the certificate must be the validator's current round.
     Correct validators always create certificates for their current round.
     If the author is a faulty validator,
     there is no such requirement:
     we make no assumptions on the internal state of a faulty validator.
     But note that the round cannot be completely arbitrary,
     because of some of the additional requirements, explained below.")
   (xdoc::p
    "There are no requirements on the transanctions,
     which we treat as opaque in our model,
     as explained in @(tsee transactions).")
   (xdoc::p
    "The number of previous certificates must be @($N - F$)
     (where @($F$) is introduced in @(tsee max-faulty-for-total)),
     unless the round number is 1,
     in which case there must be no previous certificates.")
   (xdoc::p
    "The endorsers of the certificate must be validators of the system.
     They may be correct or faulty validators:
     nothing prevents a faulty validator from endorsing a certificate
     with a good signature.")
   (xdoc::p
    "The endorsers of the certificate must differ from the author.
     The author also signs the certificate,
     but the @('endorsers') component of @(tsee certificate)
     only models the signers that differ from the author.
     Author and endorsers together form all the signers,
     returned by @(tsee certificate->signers).")
   (xdoc::p
    "There must be @($N - F - 1$) endorsers for the certificate
     (where @($F$) is introduced in @(tsee max-faulty-for-total)),
     which together with the validator itself makes @($N - F$) signers.")
   (xdoc::p
    "If the author is a correct validator,
     it must not already have, in its DAG,
     a certificate with the same author and round number:
     correct validators create at most one certificate per round.
     Additionally, each endorser that is a correct validator
     must not have, in its DAG or buffer,
     any certificate with the same author and round number,
     and must also not have alredy signed a proposal
     with the same author and round number;
     otherwise, the validator would not have signed this certificate.
     There are no such requirements on faulty authors and endorsers,
     because we make no assumptions on their internal states,
     and nothing prevents them from signing with good signatures.
     We use @(tsee signers-do-not-have-author+round-p)
     to check these conditions,
     treating all signers (author and endorsers) uniformly;
     for the author, it would suffice to check the DAG,
     but it makes no difference to also check
     the buffer and the signed author-round pairs.")
   (xdoc::p
    "If the author is a correct validator,
     it must have, in the DAG, all the previous certificates;
     if it did not, it would not create the new certificate.
     Similarly, for each endorser that is a correct validator,
     that endorser's DAG must have all the previous certificates;
     if they did not, they would not sign the certificate.
     There are no such requirements on faulty author and signers,
     because we make no assumptions on their internal states,
     and nothing prevents them from signing with good signatures.
     We use the @(tsee signers-have-previous-certificates-p)
     to check these conditions,
     treating all signers (author and endorsers) uniformly.")
   (xdoc::p
    "Since it is an invariant (proved elsewhere) that
     all the authors of certificates in DAGs are validators in the system,
     the requirement described in the previous paragraph implies that
     the addresses of the authors of the previous certificates of @('cert')
     are addresses of validators in the system."))
  (b* (((certificate cert) cert)
       ((unless (set::in cert.author (all-addresses systate))) nil)
       (vstate (get-validator-state cert.author systate))
       ((unless (or (not vstate)
                    (equal cert.round
                           (validator-state->round vstate))))
        nil)
       ((unless (if (equal cert.round 1)
                    (set::emptyp cert.previous)
                  (= (set::cardinality cert.previous)
                     (quorum systate))))
        nil)
       ((unless (set::subset cert.endorsers (all-addresses systate)))
        nil)
       ((when (set::in cert.author cert.endorsers)) nil)
       ((unless (= (set::cardinality cert.endorsers)
                   (1- (quorum systate))))
        nil)
       (signers (certificate->signers cert))
       ((unless (signers-do-not-have-author+round-p
                 signers cert.author cert.round systate))
        nil)
       ((unless (signers-have-previous-certificates-p
                 signers cert.previous cert.round systate))
        nil))
    t)
  :guard-hints (("Goal" :in-theory (enable certificate->signers)))

  ///

  (fty::deffixequiv create-certificate-possiblep
    :args ((systate system-statep)))

  (defruled no-author-dag-certificate-when-create-certificate-possiblep
    (implies (and (create-certificate-possiblep cert systate)
                  (set::in (certificate->author cert)
                           (correct-addresses systate)))
             (not (cert-with-author+round
                   (certificate->author cert)
                   (certificate->round cert)
                   (validator-state->dag
                    (get-validator-state
                     (certificate->author cert) systate)))))
    :enable (certificate->signers
             signer-does-not-have-author+round-p)
    :use (:instance signers-do-not-have-author+round-p-element
                    (signer (certificate->author cert))
                    (signers (certificate->signers cert))
                    (author (certificate->author cert))
                    (round (certificate->round cert)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define create-certificate-next ((cert certificatep) (systate system-statep))
  :guard (create-certificate-possiblep cert systate)
  :returns (new-systate system-statep)
  :short "New state resulting from a @('create-certificate') event."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the author of the new certificate is a correct validator,
     the certificate is added to the DAG of the validator.
     If instead the author of the new certificate is a faulty validator,
     there is no change to the state of the validator,
     which is always the indication of faulty validator.")
   (xdoc::p
    "Either way, regardless of the correctness or faultiness of the author,
     the certificate is reliably broadcasted to all the correct validators,
     by adding messages to the network consisting of
     the certificate and the address of all correct validators
     other than the author if correct;
     note that the removal of the author's address
     from the @(tsee correct-addresses) set
     has no effect if the author is a faulty validator.
     If the author is a correct validator,
     the reason for broadcasting to all the other correct validators
     should be obvious, since the validator follows the protocol.
     If the author is a faulty validator,
     the reason has to do with the nature of reliable broadcast,
     which in our model is assumed to be provided by the underlying layers:
     in reliable broadcast, if a correct validator receives the message,
     then every other correct validator must eventually receive the message.
     This is the case even if the faulty validator sends the message
     only to some of the validators,
     because reliable broadcast guarantees that
     there are enough correct validators
     to propagate the message to all the correct validators.
     So, either way, the message goes to all correct validators
     (except the author if correct, since it does not need it)
     by virtue of reliable broadcast.")
   (xdoc::p
    "There is no need to generate or even consider
     messages for faulty validators.
     They are free to behave arbitrarily anyhow
     (within the restrictions of reliable broadcast),
     and so it does not matter which messages they receive or not.")
   (xdoc::p
    "We also extend the states of the correct endorsers
     to record that they signed a certificate
     with the given author and pair.")
   (xdoc::p
    "We prove that, after this event,
     the set of certificates of each validator
     is the old set plus the new certificate.
     This is the case whether the certificate author is correct or faulty.
     If the author is correct, the certificate is added to its DAG,
     and messages with the certificate are sent
     for all the other correct validators.
     If the author is faulty,
     messages with that certificate are sent to all correct validators;
     this is the reliable broadcast assumption underlying the model.
     The addition of the new certificate affects all correct validators,
     not just the author (if correct).
     This is the only event that adds a certificate to
     the set of certificates for (each correct) validator."))
  (b* (((certificate cert) cert)
       (systate
        (if (set::in cert.author (correct-addresses systate))
            (b* ((vstate (get-validator-state cert.author systate))
                 (new-vstate (create-certificate-next-val cert vstate)))
              (update-validator-state cert.author new-vstate systate))
          systate))
       (systate (add-endorsed cert.endorsers cert.author cert.round systate))
       (network (get-network-state systate))
       (new-messages (messages-for-certificate
                      cert
                      (set::delete cert.author
                                   (correct-addresses systate))))
       (new-network (set::union new-messages network)))
    (update-network-state new-network systate))
  :guard-hints (("Goal" :in-theory (enable create-certificate-possiblep)))

  :prepwork
  ((define create-certificate-next-val ((cert certificatep)
                                        (vstate validator-statep))
     :returns (new-vstate validator-statep)
     :parents nil
     (b* ((dag (validator-state->dag vstate))
          (new-dag (set::insert cert dag)))
       (change-validator-state vstate :dag new-dag))))

  ///

  (fty::deffixequiv create-certificate-next
    :args ((systate system-statep)))

  (defruled validator-state->round-of-create-certificate-next
    (implies (and (certificatep cert)
                  (set::in val (correct-addresses systate)))
             (equal (validator-state->round
                     (get-validator-state val
                                          (create-certificate-next cert
                                                                   systate)))
                    (validator-state->round
                     (get-validator-state val systate))))
    :enable (create-certificate-next-val
             get-validator-state-of-update-validator-state
             validator-state->round-of-add-endorsed))

  (defruled validator-state->dag-of-create-certificate-next
    (implies (and (certificatep cert)
                  (set::in val (correct-addresses systate)))
             (equal (validator-state->dag
                     (get-validator-state val
                                          (create-certificate-next cert
                                                                   systate)))
                    (if (equal val (certificate->author cert))
                        (set::insert cert
                                     (validator-state->dag
                                      (get-validator-state val systate)))
                      (validator-state->dag
                       (get-validator-state val systate)))))
    :enable (create-certificate-next-val
             validator-state->dag-of-add-endorsed))

  (defruled validator-state->dag-subset-create-certificate-next
    (implies (and (set::in val (correct-addresses systate))
                  (certificatep cert)
                  (create-certificate-possiblep cert systate))
             (set::subset (validator-state->dag
                           (get-validator-state val systate))
                          (validator-state->dag
                           (get-validator-state
                            val (create-certificate-next cert systate)))))
    :enable validator-state->dag-of-create-certificate-next
    :disable create-certificate-next)

  (defruled validator-state->dag-of-create-certificate-next-same
    (implies (and (certificatep cert)
                  (set::in val (correct-addresses systate))
                  (not (equal val (certificate->author cert))))
             (equal (validator-state->dag
                     (get-validator-state val
                                          (create-certificate-next cert
                                                                   systate)))
                    (validator-state->dag
                     (get-validator-state val systate))))
    :enable validator-state->dag-of-create-certificate-next
    :disable create-certificate-next)

  (defruled validator-state->buffer-of-create-certificate-next
    (implies (and (certificatep cert)
                  (set::in val (correct-addresses systate)))
             (equal (validator-state->buffer
                     (get-validator-state val
                                          (create-certificate-next cert
                                                                   systate)))
                    (validator-state->buffer
                     (get-validator-state val systate))))
    :enable (create-certificate-next-val
             get-validator-state-of-update-validator-state
             validator-state->buffer-of-add-endorsed))

  (defruled validator-state->last-of-create-certificate-next
    (implies (set::in val (correct-addresses systate))
             (equal (validator-state->last
                     (get-validator-state val
                                          (create-certificate-next
                                           cert systate)))
                    (validator-state->last
                     (get-validator-state val systate))))
    :enable (create-certificate-next-val
             get-validator-state-of-update-validator-state
             nfix
             validator-state->last-of-add-endorsed))

  (defruled validator-state->blockchain-of-create-certificate-next
    (implies (set::in val (correct-addresses systate))
             (equal (validator-state->blockchain
                     (get-validator-state val
                                          (create-certificate-next
                                           cert systate)))
                    (validator-state->blockchain
                     (get-validator-state val systate))))
    :enable (create-certificate-next-val
             get-validator-state-of-update-validator-state
             validator-state->blockchain-of-add-endorsed))

  (defruled validator-state->committed-of-create-certificate-next
    (implies (set::in val (correct-addresses systate))
             (equal (validator-state->committed
                     (get-validator-state val
                                          (create-certificate-next
                                           cert systate)))
                    (validator-state->committed
                     (get-validator-state val systate))))
    :enable (create-certificate-next-val
             get-validator-state-of-update-validator-state
             validator-state->committed-of-add-endorsed))

  (defruled get-network-state-of-create-certificate-next
    (implies (set::subset (certificate->endorsers cert)
                          (all-addresses systate))
             (equal (get-network-state
                     (create-certificate-next cert systate))
                    (set::union
                     (get-network-state systate)
                     (messages-for-certificate
                      cert
                      (set::delete (certificate->author cert)
                                   (correct-addresses systate))))))
    :enable (in-all-addresses-when-in-correct-addresses
             set::expensive-rules)))
