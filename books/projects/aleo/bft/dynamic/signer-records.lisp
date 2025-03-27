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

(include-book "certificates-of-validators")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ signer-records
  :parents (correctness)
  :short "Invariant that each correct signer of each certificate
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
     to the set of endorsed pairs,
     which also constitutes a record of the certificate.
     Certificate creation also broadcasts the certificate to endorsers
     (as well as to other correct validators, except the author),
     so an endorser may receive the whole certificate at some point,
     via a @('receive-certificate') event,
     upon which it removes the author-round pair from the endorsed set,
     but it adds the whole certificate to the buffer,
     so it still has a record of the certificate.
     A @('store-certificate') event may move the certificate
     from the buffer to the DAG,
     but again the endorser still has a record of that certificate.
     Certificates are never removed by other events.")
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
    "It may be tempting to formalize the notion of
     `a signer having a record of a certificate'
     as the disjunction of
     (i) the certificate is in the DAG of the signer,
     (ii) the certificate is in the buffer of the signer, and
     (iii) the author and round of the certificate form a pair
     in the set of endorsed pairs of the signer.
     However, this would not be quite preserved
     by @('receive-certificate') events.
     The validator receiving a certificate @('C')
     could already have a record of a certificate @('C0'),
     different from @('C') but with the same author and round,
     i.e. @('C.author = C0.author') and @('C.round = C0.round').
     This cannot happen because of non-equivocation,
     but this property is not yet available
     at this point of this formal development,
     and in fact we need to use the notion of signer records
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

(define signer-record-p ((author addressp)
                         (round posp)
                         (vstate validator-statep))
  :returns (yes/no booleanp)
  :short "Check if (the state of) a signer has
          a record of a certificate author and round."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the case if
     the DAG has some certificate with the given author and round,
     the buffer has some certificate with the given author and round,
     or the given author and round are in the set of endorsed pairs.
     We express the first two conditions by saying that
     @(tsee certificate-with-author+round) does not return @('nil')."))
  (b* (((validator-state vstate) vstate)
       (author (address-fix author))
       (round (pos-fix round)))
    (or (and (certificate-with-author+round author round vstate.dag)
             t)
        (and (certificate-with-author+round author round vstate.buffer)
             t)
        (set::in (make-address+pos :address author :pos round)
                 vstate.endorsed)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk signer-records-p ((systate system-statep))
  :returns (yes/no booleanp)
  :short "Definition of the invariant:
          for every certificate signed by a correct validator,
          the validator has a record of that certificate."
  :long
  (xdoc::topstring
   (xdoc::p
    "We express this on the set of signed certificates
     defined by @(tsee signed-certificates)."))
  (forall (signer cert)
          (implies (and (set::in signer (correct-addresses systate))
                        (set::in cert (signed-certificates signer systate)))
                   (signer-record-p (certificate->author cert)
                                    (certificate->round cert)
                                    (get-validator-state signer systate))))
  ///
  (fty::deffixequiv-sk signer-records-p
    :args ((systate system-statep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled signer-records-p-when-init
  :short "Establishment of the invariant:
          the invariant holds in any initial system state."
  :long
  (xdoc::topstring
   (xdoc::p
    "Initially, there are no signed certificates,
     so the invariant trivially holds."))
  (implies (system-initp systate)
           (signer-records-p systate))
  :enable (signer-records-p
           signed-certificates-when-init))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection signer-records-p-of-next
  :short "Preservation of the invariant:
          if the invariant holds in a system state,
          it also holds in the next system state."
  :long
  (xdoc::topstring
   (xdoc::p
    "A @('create-certificate') event adds a new certificate
     to the set of certificates signed by each signer of the certificate.
     We prove a theorem saying that
     the author and round of the new certificate satisfy the invariant,
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
             (signer-record-p (certificate->author cert)
                              (certificate->round cert)
                              (get-validator-state
                               signer (create-certificate-next cert systate))))
    :enable (signer-record-p
             validator-state->dag-of-create-certificate-next
             validator-state->buffer-of-create-certificate-next
             validator-state->endorsed-of-create-certificate-next
             certificate->signers
             certificate-with-author+round-of-insert-iff))

  (defruled signer-record-p-of-create-certificate-next-old
    (implies (and (set::in signer (correct-addresses systate))
                  (signer-record-p (certificate->author cert1)
                                   (certificate->round cert1)
                                   (get-validator-state signer systate)))
             (signer-record-p (certificate->author cert1)
                              (certificate->round cert1)
                              (get-validator-state
                               signer (create-certificate-next cert systate))))
    :enable (signer-record-p
             validator-state->dag-of-create-certificate-next
             validator-state->buffer-of-create-certificate-next
             validator-state->endorsed-of-create-certificate-next
             certificate-with-author+round-of-insert-iff))

  (defruled signer-records-p-of-create-certificate-next
    (implies (signer-records-p systate)
             (signer-records-p (create-certificate-next cert systate)))
    :enable (signer-records-p
             signer-records-p-necc
             signed-certificates-of-create-certificate-next
             signer-record-p-of-create-certificate-next-new
             signer-record-p-of-create-certificate-next-old))

  ;; receive-certificate:

  (defruled signer-record-p-of-receive-certificate-next
    (implies (and (set::in signer (correct-addresses systate))
                  (signer-record-p (certificate->author cert)
                                   (certificate->round cert)
                                   (get-validator-state signer systate))
                  (receive-certificate-possiblep msg systate))
             (signer-record-p (certificate->author cert)
                              (certificate->round cert)
                              (get-validator-state
                               signer (receive-certificate-next msg systate))))
    :enable (signer-record-p
             validator-state->dag-of-receive-certificate-next
             validator-state->buffer-of-receive-certificate-next
             validator-state->endorsed-of-receive-certificate-next
             certificate-with-author+round-of-insert-iff))

  (defruled signer-records-p-of-receive-certificate-next
    (implies (and (signer-records-p systate)
                  (receive-certificate-possiblep msg systate))
             (signer-records-p (receive-certificate-next msg systate)))
    :enable (signed-certificates-of-receive-certificate-next
             signer-record-p-of-receive-certificate-next
             signer-records-p
             signer-records-p-necc))

  ;; store-certificate:

  (defruled signer-record-p-of-store-certificate-next
    (implies (and (set::in signer (correct-addresses systate))
                  (signer-record-p (certificate->author cert)
                                   (certificate->round cert)
                                   (get-validator-state signer systate))
                  (store-certificate-possiblep val1 cert1 systate))
             (signer-record-p (certificate->author cert)
                              (certificate->round cert)
                              (get-validator-state
                               signer (store-certificate-next val1
                                                              cert1
                                                              systate))))
    :enable (signer-record-p
             validator-state->dag-of-store-certificate-next
             validator-state->buffer-of-store-certificate-next
             validator-state->endorsed-of-store-certificate-next
             certificate-with-author+round-of-insert-iff
             certificate-with-author+round-of-delete))

  (defruled signer-records-p-of-store-certificate-next
    (implies (and (signer-records-p systate)
                  (store-certificate-possiblep val cert systate))
             (signer-records-p (store-certificate-next val cert systate)))
    :enable (signed-certificates-of-store-certificate-next
             signer-record-p-of-store-certificate-next
             signer-records-p
             signer-records-p-necc))

  ;; advance-round:

  (defruled signer-record-p-of-advance-round-next
    (implies (and (set::in signer (correct-addresses systate))
                  (signer-record-p (certificate->author cert)
                                   (certificate->round cert)
                                   (get-validator-state signer systate))
                  (advance-round-possiblep val systate))
             (signer-record-p (certificate->author cert)
                              (certificate->round cert)
                              (get-validator-state
                               signer (advance-round-next val systate))))
    :enable (signer-record-p
             validator-state->dag-of-advance-round-next
             validator-state->buffer-of-advance-round-next
             validator-state->endorsed-of-advance-round-next))

  (defruled signer-records-p-of-advance-round-next
    (implies (and (signer-records-p systate)
                  (advance-round-possiblep val systate))
             (signer-records-p (advance-round-next val systate)))
    :enable (signed-certificates-of-advance-round-next
             signer-record-p-of-advance-round-next
             signer-records-p
             signer-records-p-necc))

  ;; commit-anchors:

  (defruled signer-record-p-of-commit-anchors-next
    (implies (and (set::in signer (correct-addresses systate))
                  (signer-record-p (certificate->author cert)
                                   (certificate->round cert)
                                   (get-validator-state signer systate))
                  (commit-anchors-possiblep val systate))
             (signer-record-p (certificate->author cert)
                              (certificate->round cert)
                              (get-validator-state
                               signer (commit-anchors-next val systate))))
    :enable (signer-record-p
             validator-state->dag-of-commit-anchors-next
             validator-state->buffer-of-commit-anchors-next
             validator-state->endorsed-of-commit-anchors-next))

  (defruled signer-records-p-of-commit-anchors-next
    (implies (and (signer-records-p systate)
                  (commit-anchors-possiblep val systate))
             (signer-records-p (commit-anchors-next val systate)))
    :enable (signed-certificates-of-commit-anchors-next
             signer-record-p-of-commit-anchors-next
             signer-records-p
             signer-records-p-necc))

  ;; timer-expires:

  (defruled signer-record-p-of-timer-expires-next
    (implies (and (set::in signer (correct-addresses systate))
                  (signer-record-p (certificate->author cert)
                                   (certificate->round cert)
                                   (get-validator-state signer systate))
                  (timer-expires-possiblep val systate))
             (signer-record-p (certificate->author cert)
                              (certificate->round cert)
                              (get-validator-state
                               signer (timer-expires-next val systate))))
    :enable (signer-record-p
             validator-state->dag-of-timer-expires-next
             validator-state->buffer-of-timer-expires-next
             validator-state->endorsed-of-timer-expires-next))

  (defruled signer-records-p-of-timer-expires-next
    (implies (and (signer-records-p systate)
                  (timer-expires-possiblep val systate))
             (signer-records-p (timer-expires-next val systate)))
    :enable (signed-certificates-of-timer-expires-next
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection signer-records-p-always
  :short "The invariant holds in every state
          reachable from an initial state via a sequence of events."

  (defruled signer-records-p-of-events-next
    (implies (and (signer-records-p systate)
                  (events-possiblep events systate))
             (signer-records-p (events-next events systate)))
    :induct t
    :disable ((:e tau-system))
    :enable (events-possiblep
             events-next
             signer-records-p-of-event-next))

  (defruled signer-records-p-when-reachable
    (implies (and (system-initp systate)
                  (events-possiblep events systate))
             (signer-records-p (events-next events systate)))
    :disable ((:e tau-system))
    :enable (signer-records-p-when-init
             signer-records-p-of-events-next)))
