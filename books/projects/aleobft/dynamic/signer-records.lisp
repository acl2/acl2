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

(include-book "owned-certificates")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ signer-records
  :parents (correctness)
  :short "Invariant that the correct signer of a certificate
          has a record of the certificate."
  :long
  (xdoc::topstring
   (xdoc::p
    "A signer of a certificate is either the author or an endorser.
     The author adds the certificate to its DAG as it creates the certificate,
     as defined in the transitions for @('create-certificate'),
     so it has a record of the certificate.
     As also defined in the transitions for @('create-certificate'),
     an endorser adds the certificate's author and round
     to the set of endorsed pair,
     which also constitutes a record of the certificate.
     Certificate creation also broadcasts the certificate to endorsers
     (as well as to other correct validators, except the author),
     so the endorser may receive the whole certificate at some point,
     via a @('receive-certificate') event,
     upon which it removes the author-round pair from the endorsed set,
     but it adds the whole certificate to the buffer,
     so it is still has a record of the certificate.
     A @('store-certificate') event may move the certificate
     from the buffer to the DAG,
     but again the endorser has thus a record of that certificate.
     Certificates are never removed from DAG by other events.")
   (xdoc::p
    "Thus, both in the case of the author and in the case of an endorser,
     the signer in question always has a record of the certificate,
     in its own validator state, in three possible forms:
     in the DAG (the whole certificate),
     or in the buffer (the whole certificate),
     or in the set of endorsed pairs (just author and round).")
   (xdoc::p
    "Note the difference between this notion and that of "
    (xdoc::seetopic "owned-certificates" "owned certificates")
    ": the latter consist of
     the certificates in the validator state
     or in transit in the network;
     these are all whole certificates,
     and apply to all correct validators.
     In contrast, certificate records are all in the validator state,
     but are not necessarily whole certificates
     (it could be just authors and rounds),
     and they only apply to the signers of the certificate.")
   (xdoc::p
    "It is tempting to formalize the notion of
     `a signer having a record of a certificate'
     as the disjunction of
     (i) the certificate is in the DAG of the signer,
     (ii) the certificate is in the buffer of the signer, and
     (iii) the author and round of the certificate form a pair
     in the set of endorsed pairs of the signer.
     However, this would be not quite preserved
     by @('receive-certificate') events.
     The validator receiving a certificate @('C')
     could already have a recordo of a certificate @('C0'),
     different from @('C') but with the same author and round,
     i.e. @('C.author = C0.author') and @('C.round = C0.round').
     This cannot happen because of non-equivocation,
     but we have not proved that yet,
     and in fact we need to use to use the notion of signer records
     to prove non-equivocation, so we cannot assume it here.
     The problem is that, upon receiving @('C'),
     if the record of @('C0') is in the set of endorsed pairs,
     and not in the DAG or in the buffer,
     the pair of the common author and round is removed from the set,
     and thus the validator no longer has a record of @('C0'),
     although it now has a record of @('C').
     So we need to weaken the notion of
     `a signer having a record of a certificate @('C')'
     to the disjunction of
     (i) the DAG of the signer has some certificate @('C\'')
     (the same as @('C') or not)
     with the author and round of @('C'),
     (ii) the buffer of the signer has some certificate @('C\'')
     (the same as @('C') or not)
     with the author and round of @('C'), and
     (iii) the author and round of @('C') form a pair
     in the set of endorsed pairs of the signer.
     This is the formulation we define and prove here."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define signer-record-p ((cert certificatep) (vstate validator-statep))
  :returns (yes/no booleanp)
  :short "Check if (the state of) a signer has a record of a certificate."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the case if
     the DAG has some certificate
     with the given certificate's author and round,
     the buffer has some certificate
     with the given certificate's author and round,
     or the given certificate's author and round
     are in the set of endorsed pairs.
     We express the first two conditions by saying that
     @(tsee get-certificate-with-author+round) does not return @('nil')."))
  (b* (((validator-state vstate) vstate)
       ((certificate cert) cert))
    (or (and (get-certificate-with-author+round cert.author
                                                cert.round
                                                vstate.dag)
             t)
        (and (get-certificate-with-author+round cert.author
                                                cert.round
                                                vstate.buffer)
             t)
        (set::in (make-address+pos :address cert.author :pos cert.round)
                 vstate.endorsed)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk signer-records-p ((systate system-statep))
  :returns (yes/no booleanp)
  :short "Definition of the invariant:
          for every certificate in the system,
          every correct signer has a record of that certificate."
  :long
  (xdoc::topstring
   (xdoc::p
    "The certificates in the system are
     the certificates owned by any correct validator;
     as proved in @(see same-owned-certificates),
     all correct validators own the same set of certificates,
     so we can pick any arbitrary correct validator."))
  (forall (val cert signer)
          (implies (and (set::in val (correct-addresses systate))
                        (set::in cert (certificates-owned-by val systate))
                        (set::in signer (certificate->signers cert))
                        (set::in signer (correct-addresses systate)))
                   (signer-record-p cert
                                    (get-validator-state signer systate)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled signer-records-p-when-init
  :short "Establishment of the invariant:
          the invariant holds on any initial system state."
  :long
  (xdoc::topstring
   (xdoc::p
    "Initially, there are no certificates (owned by any validator),
     so the invariant trivially holds."))
  (implies (system-initp systate)
           (signer-records-p systate))
  :enable (signer-records-p
           certificates-owned-by-when-init))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



(defsection signer-records-p-of-next
  :short "Preservation of the invariant:
          if the invariant holds in a system state,
          it also holds in the next system state."
  :long
  (xdoc::topstring
   (xdoc::p
    "A @('create-certificate') event creates a new certificate.
     We prove a theorem saying that the new certificate satisfies the invariant,
     which follows from the definition of the creation of the certificate,
     which adds the certificate to the author's DAG
     and the author-round pair to the endorsers' endorser sets.
     We prove another theorem saying that the old recorded certificates
     are still recorded in the new states,
     because there is no other change for those w.r.t. their records.
     Then we prove a theorem showing the preservation of the system invariant
     on all certificates after @('create-certificate'),
     via the two aforementioned theorems for new and old certificates.")
   (xdoc::p
    "For all other kinds of events, we prove two theorems:
     one is for each generic validator, and one is for the whole system.")
   (xdoc::p
    "A @('receive-certificate') event may remove an endorsed pair,
     but it also adds the certificate,
     whose author and round are the ones of the removed pair,
     to the buffer.
     So the invariant is preserved for that certificate.
     For the other certificates, the invariant is also preserved
     because nothing changes for them in terms of their records.")
   (xdoc::p
    "A @('store-certificate') event moves a certificate
     from the buffer to the DAG of a validator,
     so the record of the certificate is still there.
     For the other certificates, nothing changes in terms of records.")
   (xdoc::p
    "For the other kinds of events,
     nothing changes for any certificate in terms of their records."))

  ;; create-certificate:

  (defruled signer-record-p-of-create-certificate-next-new
    (implies (and (set::in signer (certificate->signers cert))
                  (set::in signer (correct-addresses systate)))
             (signer-record-p cert
                              (get-validator-state
                               signer (create-certificate-next cert systate))))
    :enable (signer-record-p
             validator-state->dag-of-create-certificate-next
             validator-state->buffer-of-create-certificate-next
             validator-state->endorsed-of-create-certificate-next
             certificate->signers
             get-certificate-with-author+round-of-insert-iff))

  (defruled signer-record-p-of-create-certificate-next-old
    (implies (and (set::in val (correct-addresses systate))
                  (signer-record-p cert1 (get-validator-state val systate)))
             (signer-record-p cert1
                              (get-validator-state
                               val (create-certificate-next cert systate))))
    :enable (signer-record-p
             validator-state->dag-of-create-certificate-next
             validator-state->buffer-of-create-certificate-next
             validator-state->endorsed-of-create-certificate-next
             get-certificate-with-author+round-of-insert-iff))

  (defruled signer-records-p-of-create-certificate-next
    (implies (signer-records-p systate)
             (signer-records-p (create-certificate-next cert systate)))
    :enable (certificates-owned-by-of-create-certificate-next
             signer-record-p-of-create-certificate-next-new
             signer-record-p-of-create-certificate-next-old
             signer-records-p
             signer-records-p-necc))

  ;; receive-certificate:

  (defruled signer-record-p-of-receive-certificate-next
    (implies (and (set::in val (correct-addresses systate))
                  (signer-record-p cert (get-validator-state val systate))
                  (receive-certificate-possiblep msg systate))
             (signer-record-p cert
                              (get-validator-state
                               val (receive-certificate-next msg systate))))
    :enable (signer-record-p
             validator-state->dag-of-receive-certificate-next
             validator-state->buffer-of-receive-certificate-next
             validator-state->endorsed-of-receive-certificate-next
             get-certificate-with-author+round-of-insert-iff))

  (defruled signer-records-p-of-receive-certificate-next
    (implies (and (signer-records-p systate)
                  (receive-certificate-possiblep msg systate))
             (signer-records-p (receive-certificate-next msg systate)))
    :enable (certificates-owned-by-of-receive-certificate-next
             signer-record-p-of-receive-certificate-next
             signer-records-p
             signer-records-p-necc))

  ;; store-certificate:

  (defruled signer-record-p-of-store-certificate-next
    (implies (and (set::in val (correct-addresses systate))
                  (signer-record-p cert (get-validator-state val systate))
                  (store-certificate-possiblep val1 cert1 systate))
             (signer-record-p cert
                              (get-validator-state
                               val (store-certificate-next val1 cert1 systate))))
    :enable (signer-record-p
             validator-state->dag-of-store-certificate-next
             validator-state->buffer-of-store-certificate-next
             validator-state->endorsed-of-store-certificate-next
             get-certificate-with-author+round-of-insert-iff
             get-certificate-with-author+round-of-delete))

  (defruled signer-records-p-of-store-certificate-next
    (implies (and (signer-records-p systate)
                  (store-certificate-possiblep val cert systate))
             (signer-records-p (store-certificate-next val cert systate)))
    :enable (certificates-owned-by-of-store-certificate-next
             signer-record-p-of-store-certificate-next
             signer-records-p
             signer-records-p-necc))

  ;; advance-round:

  (defruled signer-record-p-of-advance-round-next
    (implies (and (set::in val (correct-addresses systate))
                  (signer-record-p cert (get-validator-state val systate))
                  (advance-round-possiblep val1 systate))
             (signer-record-p cert
                              (get-validator-state
                               val (advance-round-next val1 systate))))
    :enable (signer-record-p
             validator-state->dag-of-advance-round-next
             validator-state->buffer-of-advance-round-next
             validator-state->endorsed-of-advance-round-next))

  (defruled signer-records-p-of-advance-round-next
    (implies (and (signer-records-p systate)
                  (advance-round-possiblep val systate))
             (signer-records-p (advance-round-next val systate)))
    :enable (certificates-owned-by-of-advance-round-next
             signer-record-p-of-advance-round-next
             signer-records-p
             signer-records-p-necc))

  ;; commit-anchors:

  (defruled signer-record-p-of-commit-anchors-next
    (implies (and (set::in val (correct-addresses systate))
                  (signer-record-p cert (get-validator-state val systate))
                  (commit-anchors-possiblep val1 systate))
             (signer-record-p cert
                              (get-validator-state
                               val (commit-anchors-next val1 systate))))
    :enable (signer-record-p
             validator-state->dag-of-commit-anchors-next
             validator-state->buffer-of-commit-anchors-next
             validator-state->endorsed-of-commit-anchors-next))

  (defruled signer-records-p-of-commit-anchors-next
    (implies (and (signer-records-p systate)
                  (commit-anchors-possiblep val systate))
             (signer-records-p (commit-anchors-next val systate)))
    :enable (certificates-owned-by-of-commit-anchors-next
             signer-record-p-of-commit-anchors-next
             signer-records-p
             signer-records-p-necc))

  ;; timer-expires:

  (defruled signer-record-p-of-timer-expires-next
    (implies (and (set::in val (correct-addresses systate))
                  (signer-record-p cert (get-validator-state val systate))
                  (timer-expires-possiblep val1 systate))
             (signer-record-p cert
                              (get-validator-state
                               val (timer-expires-next val1 systate))))
    :enable (signer-record-p
             validator-state->dag-of-timer-expires-next
             validator-state->buffer-of-timer-expires-next
             validator-state->endorsed-of-timer-expires-next))

  (defruled signer-records-p-of-timer-expires-next
    (implies (and (signer-records-p systate)
                  (timer-expires-possiblep val systate))
             (signer-records-p (timer-expires-next val systate)))
    :enable (certificates-owned-by-of-timer-expires-next
             signer-record-p-of-timer-expires-next
             signer-records-p
             signer-records-p-necc))

  ;; all events:

  (defruled signer-records-p-of-event-next
    (implies (and (signer-records-p systate)
                  (event-possiblep event systate))
             (signer-records-p (event-next event systate)))
    :enable (event-possiblep
             event-next)))
