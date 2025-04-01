; AleoBFT Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOBFT-STATIC")

(include-book "invariant-signers-are-validators")

(include-book "std/util/define-sk" :dir :system)

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ invariant-signers-have-author-round
  :parents (correctness)
  :short "Invariant that the signers of every certificate
          have a a record of the certificate's author and round."
  :long
  (xdoc::topstring
   (xdoc::p
    "A signer is the author or an endorser.
     The author of a certificate immediately stores the certificate in the DAG.
     An endorser first adds the author-round pair to its set of such pairs,
     then it may receive the actual certificate in the network,
     which removes the pair from the set
     but adds the whole certificate to the whole buffer,
     from where it may be moved to the DAG at some point.
     In any case, for both author and endorsers (i.e. for all signers),
     the author-round pair is always found
     in the DAG (as part of the whole certificate),
     or in the buffer (as part of the whole certificate),
     or in the set of author-round pairs (as just the pair).
     That is, the signer always has a record of the certificates it has signed,
     whether the signer has the whole certificate or not yet.")
   (xdoc::p
    "This is an important property to ensure non-equivocation of certificates.
     It motivates the presence of the author-round pair set
     as part of the validator state:
     without it, a validator may sign a certificate,
     but not have a record of that yet (still in transit in the network),
     and thus sign a different certificate with the same author and round
     (which would come from a faulty validator)."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define signer-has-author+round-p ((signer addressp)
                                   (author addressp)
                                   (round posp)
                                   (systate system-statep))
  :guard (set::in signer (all-addresses systate))
  :returns (yes/no booleanp)
  :short "Check that a validator (signer) has a record of
          a certificate author-round pair."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the validator is faulty, the check passes:
     the requirement of the invariant only applies to correct validators.
     For a correct validator, we check that
     @(tsee cert-with-author+round) is not @('nil')
     on the DAG or buffer
     (i.e. that a certificate with that author and round is there),
     or the pair is in the set of endorsed pairs."))
  (b* ((vstate (get-validator-state signer systate))
       ((when (not vstate)) t)
       ((validator-state vstate) vstate))
    (or
     (and (cert-with-author+round author round vstate.dag) t)
     (and (cert-with-author+round author round vstate.buffer) t)
     (set::in (make-address+pos :address author :pos round)
              vstate.endorsed)))

  ///

  (defruled signer-has-author+round-p-of-update-network-state
    (equal (signer-has-author+round-p signer author round
                                      (update-network-state network systate))
           (signer-has-author+round-p signer author round systate))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk system-signers-have-author+round-p ((systate system-statep))
  :guard (system-signers-are-validators-p systate)
  :returns (yes/no booleanp)
  :short "Definition of the invariant:
          the signers of every certificate of every validator
          have a record of the author and round of the certificate."
  :long
  (xdoc::topstring
   (xdoc::p
    "In order to verify the guards of this function, we need the "
    (xdoc::seetopic "invariant-signers-are-validators"
                    "invariant that signers are validators")
    ". That invariant is not needed to prove this invariant,
     but it needed (only) in the guard of this function.
     Since @(tsee signer-has-author+round-p) has a guard requiring
     the signer to be a validator,
     but the antecedents of the implication below
     only say that the the (universally quantified) signer
     is a signer of the certificate,
     we need the additional condition provided by
     that aforementioned invariant.
     Indeed, the rule associated to that invariant's definition
     is used in the guard hints
     (it does not apply as a rewrite rule)."))
  (forall (val cert signer)
          (implies
           (and (set::in val (correct-addresses systate))
                (set::in cert (certificates-for-validator val systate))
                (set::in signer (certificate->signers cert)))
           (signer-has-author+round-p signer
                                      (certificate->author cert)
                                      (certificate->round cert)
                                      systate)))
  :guard-hints
  (("Goal"
    :in-theory (enable* certificate-signers-are-validators-p
                        set::expensive-rules)
    :use
    (:instance
     system-signers-are-validators-p-necc
     (val (mv-nth 0 (system-signers-have-author+round-p-witness systate)))
     (cert (mv-nth 1 (system-signers-have-author+round-p-witness systate)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled system-signers-have-author+round-p-when-system-state-initp
  :short "Establishment of the invariant:
          the invariant holds on any initial system state."
  :long
  (xdoc::topstring
   (xdoc::p
    "Initially, the set of certificates of validators is empty."))
  (implies (system-state-initp systate)
           (system-signers-have-author+round-p systate))
  :enable (system-state-initp
           system-signers-have-author+round-p
           certificates-for-validator
           get-network-state
           validator-init-when-system-initp
           validator-init
           in-of-message-certificates-for-validator))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection system-signers-have-author+round-p-of-create-certificate-next
  :short "Preservation of the invariant by @('create-certificate') events."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the only kind of event that adds a new certificate.
     The event adds the certificate to the DAG of the author,
     so the author has a record of it;
     the event also adds an author-round pair to every endorser,
     so every endorser has a record of it.
     For the other existing certificates,
     there are no removals from DAGs, buffers, and endorsed pairs,
     so those certificates' signers still have
     the same record as they had before this event."))

  (defruled signer-has-author+round-p-of-create-certificate-next
    (implies (and (create-certificate-possiblep cert systate)
                  (certificatep cert)
                  (addressp author)
                  (posp round))
             (equal (signer-has-author+round-p signer author round
                                               (create-certificate-next
                                                cert systate))
                    (or (signer-has-author+round-p signer author round systate)
                        (and (set::in signer (certificate->signers cert))
                             (equal author (certificate->author cert))
                             (equal round (certificate->round cert))))))
    :enable (create-certificate-possiblep
             create-certificate-next
             create-certificate-next-val
             certificate->signers
             signer-has-author+round-p
             get-validator-state-iff-in-correct-addresses
             get-validator-state-of-update-validator-state
             cert-with-author+round-of-insert-iff
             validator-state->dag-of-add-endorsed
             validator-state->buffer-of-add-endorsed
             validator-state->endorsed-of-add-endorsed))

  (defruled system-signers-have-author+round-p-of-create-certificate-next
    (implies (and (system-signers-have-author+round-p systate)
                  (create-certificate-possiblep cert systate)
                  (certificatep cert))
             (system-signers-have-author+round-p
              (create-certificate-next cert systate)))
    :expand (system-signers-have-author+round-p
             (create-certificate-next cert systate))
    :enable (system-signers-have-author+round-p-necc
             certificates-for-validator-of-create-certificate-next
             signer-has-author+round-p-of-create-certificate-next)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection system-signers-have-author+round-p-of-receive-certificate-next
  :short "Preservation of the invariant by @('receive-certificate') events."
  :long
  (xdoc::topstring
   (xdoc::p
    "This kind of event may remove an endorsed pair from an endorser,
     but it adds the corresponding certificate to the buffer;
     so that endorser still have a record of te certificate.
     Other than that, nothing is removed from
     DAGs, buffer, and (other) endorsed pair sets.
     Note that this event may not involve the signer of a message,
     in which case the certificate is simply added to the buffer,
     without modifying the recipient's endorsed pairs."))

  (defruled signer-has-author+round-p-of-receive-certificate-next
    (implies (and (signer-has-author+round-p signer author round systate)
                  (receive-certificate-possiblep msg systate)
                  (addressp author)
                  (posp round))
             (signer-has-author+round-p
              signer author round (receive-certificate-next msg systate)))
    :enable (receive-certificate-possiblep
             receive-certificate-next
             receive-certificate-next-val
             signer-has-author+round-p
             get-validator-state-of-update-validator-state
             cert-with-author+round-of-insert-iff))

  (defruled system-signers-have-author+round-p-of-receive-certificate-next
    (implies (and (system-signers-have-author+round-p systate)
                  (receive-certificate-possiblep msg systate))
             (system-signers-have-author+round-p
              (receive-certificate-next msg systate)))
    :expand (system-signers-have-author+round-p
             (receive-certificate-next msg systate))
    :enable (system-signers-have-author+round-p-necc
             certificates-for-validator-of-receive-certificate-next
             signer-has-author+round-p-of-receive-certificate-next)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection system-signers-have-author+round-p-of-store-certificate-next
  :short "Preservation of the invariant by @('store-certificate') events."
  :long
  (xdoc::topstring
   (xdoc::p
    "This removes a certificate from a buffer but adds it to the DAG.
     So no record of signed certificates is lost.")
   (xdoc::p
    "For the proof, we need a lemma saying that
     if an author-pair is found in a set of certificates
     but not in the resulting of removing a certificate from that set,
     then the certificate must have that author and round.
     Note that, at this point, we do not have available
     the property that certificates have unique author-round pairs:
     mathematically, a DAG or buffer may well contain
     multiple certificates with the same author and round.
     So the lemma just mentioned is what we can prove here;
     a stronger lemma would need the author-round uniqueness property."))

  (defruled signer-has-author+round-p-of-store-certificate-next
    (implies (and (signer-has-author+round-p signer author round systate)
                  (store-certificate-possiblep cert val systate)
                  (addressp author)
                  (posp round))
             (signer-has-author+round-p
              signer author round (store-certificate-next cert val systate)))
    :enable (store-certificate-possiblep
             store-certificate-next
             store-certificate-next-val
             signer-has-author+round-p
             get-validator-state-of-update-validator-state
             cert-with-author+round-of-insert-iff)
    :prep-lemmas
    ((defrule lemma
       (implies (and (cert-with-author+round author round certs)
                     (addressp author)
                     (posp round)
                     (not (cert-with-author+round
                           author round (set::delete cert certs))))
                (and (equal (certificate->author cert) author)
                     (equal (certificate->round cert) round)))
       :induct t
       :enable (cert-with-author+round
                cert-with-author+round-of-insert-iff
                set::delete
                emptyp-of-certificate-set-fix))))

  (defruled system-signers-have-author+round-p-of-store-certificate-next
    (implies (and (system-signers-have-author+round-p systate)
                  (store-certificate-possiblep cert val systate))
             (system-signers-have-author+round-p
              (store-certificate-next cert val systate)))
    :expand (system-signers-have-author+round-p
             (store-certificate-next cert val systate))
    :enable (system-signers-have-author+round-p-necc
             certificates-for-validator-of-store-certificate-next
             signer-has-author+round-p-of-store-certificate-next)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection system-signers-have-author+round-p-of-advance-round-next
  :short "Preservation of the invariant by @('advance-round') events."
  :long
  (xdoc::topstring
   (xdoc::p
    "This kind of event does not modify any
     DAG, buffer, and set of endorsed pairs."))

  (defruled signer-has-author+round-p-of-advance-round-next
    (implies (and (signer-has-author+round-p signer author round systate)
                  (advance-round-possiblep val systate)
                  (addressp author)
                  (posp round))
             (signer-has-author+round-p
              signer author round (advance-round-next val systate)))
    :enable (advance-round-possiblep
             advance-round-next
             advance-round-next-val
             signer-has-author+round-p
             get-validator-state-of-update-validator-state))

  (defruled system-signers-have-author+round-p-of-advance-round-next
    (implies (and (system-signers-have-author+round-p systate)
                  (advance-round-possiblep val systate))
             (system-signers-have-author+round-p
              (advance-round-next val systate)))
    :expand (system-signers-have-author+round-p
             (advance-round-next val systate))
    :enable (system-signers-have-author+round-p-necc
             certificates-for-validator-of-advance-round-next
             signer-has-author+round-p-of-advance-round-next)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection system-signers-have-author+round-p-of-commit-anchors-next
  :short "Preservation of the invariant by @('commit-anchors') events."
  :long
  (xdoc::topstring
   (xdoc::p
    "This kind of event does not modify any
     DAG, buffer, and set of endorsed pairs."))

  (defruled signer-has-author+round-p-of-commit-anchors-next
    (implies (and (signer-has-author+round-p signer author round systate)
                  (commit-anchors-possiblep val systate)
                  (addressp author)
                  (posp round))
             (signer-has-author+round-p
              signer author round (commit-anchors-next val systate)))
    :enable (commit-anchors-possiblep
             commit-anchors-next
             commit-anchors-next-val
             signer-has-author+round-p
             get-validator-state-of-update-validator-state))

  (defruled system-signers-have-author+round-p-of-commit-anchors-next
    (implies (and (system-signers-have-author+round-p systate)
                  (commit-anchors-possiblep val systate))
             (system-signers-have-author+round-p
              (commit-anchors-next val systate)))
    :expand (system-signers-have-author+round-p
             (commit-anchors-next val systate))
    :enable (system-signers-have-author+round-p-necc
             certificates-for-validator-of-commit-anchors-next
             signer-has-author+round-p-of-commit-anchors-next)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection system-signers-have-author+round-p-of-timer-expires-next
  :short "Preservation of the invariant by @('timer-expires') events."
  :long
  (xdoc::topstring
   (xdoc::p
    "This kind of event does not modify any
     DAG, buffer, and set of endorsed pairs."))

  (defruled signer-has-author+round-p-of-timer-expires-next
    (implies (and (signer-has-author+round-p signer author round systate)
                  (timer-expires-possiblep val systate)
                  (addressp author)
                  (posp round))
             (signer-has-author+round-p
              signer author round (timer-expires-next val systate)))
    :enable (timer-expires-possiblep
             timer-expires-next
             timer-expires-next-val
             signer-has-author+round-p
             get-validator-state-of-update-validator-state
             certificates-for-validator-of-timer-expires-next))

  (defruled system-signers-have-author+round-p-of-timer-expires-next
    (implies (and (system-signers-have-author+round-p systate)
                  (timer-expires-possiblep val systate))
             (system-signers-have-author+round-p
              (timer-expires-next val systate)))
    :expand (system-signers-have-author+round-p
             (timer-expires-next val systate))
    :enable (system-signers-have-author+round-p-necc
             certificates-for-validator-of-timer-expires-next
             signer-has-author+round-p-of-timer-expires-next)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled system-signers-have-author+round-p-of-event-next
  :short "Preservation of the invariant by all events."
  :long
  (xdoc::topstring
   (xdoc::p
    "This follows from the theorems about the various kinds of events."))
  (implies (and (system-signers-have-author+round-p systate)
                (event-possiblep event systate))
           (system-signers-have-author+round-p (event-next event systate)))
  :enable (event-possiblep
           event-next))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled system-signers-have-author+round-p-of-events-next
  :short "Preservation of the invariant by every sequence of events."
  (implies (and (system-statep systate)
                (system-signers-have-author+round-p systate)
                (events-possiblep events systate))
           (system-signers-have-author+round-p (events-next events systate)))
  :induct t
  :disable ((:e tau-system))
  :enable (events-next
           events-possiblep
           system-signers-have-author+round-p-of-event-next))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled system-signers-have-author+round-p-when-reachable
  :short "The invariant holds in every reachable state."
  :long
  (xdoc::topstring
   (xdoc::p
    "Reachable states are characterized by an initial state and
     a sequence of possible events from that initial state."))
  (implies (and (system-statep systate)
                (system-state-initp systate)
                (events-possiblep events systate))
           (system-signers-have-author+round-p (events-next events systate)))
  :disable ((:e tau-system))
  :enable (system-signers-have-author+round-p-when-system-state-initp
           system-signers-have-author+round-p-of-events-next))
