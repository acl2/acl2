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

(include-book "signer-records")
(include-book "no-self-buffer")
(include-book "no-self-endorsed")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ unequivocal-signed-certificates
  :parents (correctness)
  :short "Invariant that the certificates signed by a correct validator
          are unequivocal."
  :long
  (xdoc::topstring
   (xdoc::p
    "A correct validator signs a certificates
     under conditions formalized in @(tsee create-certificate-possiblep);
     recall that @('create-certificates') is the only kind of event
     that generates a new certificate.
     The conditions for certificate signing include the fact that
     the signer does not already have a record for
     a certificate with the same author and round:
     in other words, in order for the new certificate to be created,
     and thus be added to the set of certificates signed by the signer,
     the signer must not have a record for the certificate's author and round.
     But as proved in @(see signer-records),
     it is an invariant that each correct validator has
     a record of all the certificates it has signed present in the system.
     Therefore, a new certificate will be signed,
     and added to the set of signed certificates,
     only if it has a different author-round combination
     from all the existing signed certificates,
     thus preventing equivocation.")
   (xdoc::p
    "Note that this non-equivocation property is limited to
     the set of certificates signed by a single validator.
     There is no quorum intersection argument needed for this:
     the property comes from the internal consistency tests
     performed by a correct validator when it signs certificates.
     This invariant is then used to prove
     the broader non-equivocation property,
     which makes use of the quorum intersection argument."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk unequivocal-signed-certificates-p ((systate system-statep))
  :returns (yes/no booleanp)
  :short "Definition of the invariant:
          the set of certificates signed by each correct validator
          is unequivocal."
  (forall (signer)
          (implies (set::in signer (correct-addresses systate))
                   (certificate-set-unequivocalp
                    (signed-certificates signer systate))))
  ///
  (fty::deffixequiv-sk unequivocal-signed-certificates-p
    :args ((systate system-statep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled unequivocal-signed-certificates-p-when-init
  :short "Establishment of the invariant:
          the invariant holds in any initial system state."
  :long
  (xdoc::topstring
   (xdoc::p
    "Initially, there are no signed certificates,
     so the invariant trivially holds."))
  (implies (system-initp systate)
           (unequivocal-signed-certificates-p systate))
  :enable (system-initp
           signed-certificates-when-init
           unequivocal-signed-certificates-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection no-signer-record-when-create-certificate-possiblep
  :short "If @(tsee create-certificate-possiblep) holds,
          then @(tsee signer-record-p) is false for its correct signers."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a key fact needed to prove our invariant.
     It says that, in order for a new certificate to be created,
     its correct signers must have no records of its author and round.
     This is then used to show that equivocation is not possible
     for the set of certificates signed by a validator.")
   (xdoc::p
    "This fact follows from
     the definition of @(tsee create-certificate-possiblep),
     as well as from some previously proved system invariants.")
   (xdoc::p
    "Consider the author first.
     For the author, @(tsee create-certificate-possiblep) requires
     that no certificates in the DAG have
     the author and round of the new certificates.
     It says nothing about buffer and endorsed pairs,
     but two invariants come to the rescue here.
     The invariant @(tsee no-self-buffer-p) tells us that
     the certificate's author's buffer has no certificates
     authored by this validator,
     and so in particular it cannot have any certificate
     authored by this validator and with the certificate's round.
     The invariant @(tsee no-self-endorsed) tells us that
     the certificate's author's endorsed pairs include no pair
     whose first component is this validator,
     and so in particular the pair consisting of
     this validator plus the certificate's round.
     All together, these facts tell us that
     @(tsee signer-record-p) does not hold.")
   (xdoc::p
    "Consider an endorser next.
     Here @(tsee create-certificate-possiblep) directly requires
     the negation of all the disjunctions of @(tsee signer-record-p),
     which therefore is false.")
   (xdoc::p
    "We prove theorems for the predicates
     that make up @(tsee create-certificate-possiblep),
     culminating with the one for @(tsee create-certificate-possiblep).
     In the theorem about @(tsee create-certificate-author-possiblep),
     we add hypotheses corresponding to part of the bodies of
     @(tsee no-self-buffer-p) and @(tsee no-self-endorsed-p),
     which, in the theorem about @(tsee create-certificate-possiblep),
     get discharged via the @('-necc') rules of the two invariants."))

  (defruled no-signer-record-when-create-certificate-author-possiblep
    (implies (and (create-certificate-author-possiblep cert vstate all-vals)
                  (equal (certificates-with-author
                          (certificate->author cert)
                          (validator-state->buffer vstate))
                         nil)
                  (equal (get-address+pos-pairs-with-address
                          (certificate->author cert)
                          (validator-state->endorsed vstate))
                         nil))
             (not (signer-record-p (certificate->author cert)
                                   (certificate->round cert)
                                   vstate)))
    :enable (create-certificate-author-possiblep
             create-certificate-signer-possiblep
             signer-record-p
             no-cert-with-author+round-if-no-certificates-with-author
             no-author+round-pair-if-no-pairs-with-author))

  (defruled no-signer-record-when-create-certificate-endorser-possiblep
    (implies (create-certificate-endorser-possiblep cert vstate all-vals)
             (not (signer-record-p (certificate->author cert)
                                   (certificate->round cert)
                                   vstate)))
    :enable (create-certificate-endorser-possiblep
             create-certificate-signer-possiblep
             signer-record-p))

  (defruled no-signer-record-when-create-certificate-endorsers-possiblep-loop
    (implies (and (create-certificate-endorsers-possiblep-loop cert
                                                               endorsers
                                                               systate)
                  (set::in endorser endorsers)
                  (set::in endorser (correct-addresses systate)))
             (not (signer-record-p (certificate->author cert)
                                   (certificate->round cert)
                                   (get-validator-state endorser systate))))
    :induct t
    :enable (create-certificate-endorsers-possiblep-loop
             no-signer-record-when-create-certificate-endorser-possiblep))

  (defruled no-signer-record-when-create-certificate-endorsers-possiblep
    (implies (and (create-certificate-endorsers-possiblep cert systate)
                  (set::in endorser (certificate->endorsers cert))
                  (set::in endorser (correct-addresses systate)))
             (not (signer-record-p (certificate->author cert)
                                   (certificate->round cert)
                                   (get-validator-state endorser systate))))
    :enable (create-certificate-endorsers-possiblep
             no-signer-record-when-create-certificate-endorsers-possiblep-loop))

  (defruled no-signer-record-when-create-certificate-possiblep
    (implies (and (create-certificate-possiblep cert systate)
                  (set::in signer (certificate->signers cert))
                  (set::in signer (correct-addresses systate))
                  (no-self-buffer-p systate)
                  (no-self-endorsed-p systate))
             (not (signer-record-p (certificate->author cert)
                                   (certificate->round cert)
                                   (get-validator-state signer systate))))
    :enable (create-certificate-possiblep
             certificate->signers
             no-signer-record-when-create-certificate-author-possiblep
             no-signer-record-when-create-certificate-endorsers-possiblep
             no-self-buffer-p-necc
             no-self-endorsed-p-necc)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled signer-record-p-when-get-author+round-in-signed-certificates
  :short "If a certificate with a certain author and round
          can be obtained from the signed certificates of a validator,
          then the validator has a record of that author and round."
  :long
  (xdoc::topstring
   (xdoc::p
    "This has the opposite conclusion of
     @(tsee no-signer-record-when-create-certificate-possiblep),
     and in fact we use this and that theorem to prove by contradiction
     that @('create-certificate') preserves our invariant.")
   (xdoc::p
    "This theorem is a consequence of @(tsee signer-records-p).
     If @(tsee cert-with-author+round) returns a certificate,
     from the set of certificates signed by a validator,
     then we know from @('cert-with-author+round-element')
     that the certificate must be in the set.
     But then we can use @('signer-records-p-necc') to conclude that
     the validator has a record for the author and round."))
  (implies (and (signer-records-p systate)
                (set::in signer (correct-addresses systate))
                (cert-with-author+round
                 author round (signed-certificates signer systate)))
           (signer-record-p
            author round (get-validator-state signer systate)))
  :enable (cert-with-author+round-element
           certificate->author-of-cert-with-author+round
           certificate->round-of-cert-with-author+round)
  :use (:instance signer-records-p-necc
                  (cert (cert-with-author+round
                         author round (signed-certificates signer systate)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection unequivocal-signed-certificates-p-of-next
  :short "Preservation of the invariant:
          if the invariant holds in a system state,
          it also holds in the next system state."
  :long
  (xdoc::topstring
   (xdoc::p
    "The only kind of event that may change the set of signed certificates
     is @('create-certificate'), which adds the certificate to each signer.
     To show that no equivocation is introduced, we make use of
     @(tsee no-signer-record-when-create-certificate-possiblep)
     and @(tsee signer-record-p-when-get-author+round-in-signed-certificates),
     to effectively derive a contradiction
     should the new certificate have the same author and round
     as some existing certificate.
     The rule @('certificate-set-unequivocalp-of-insert')
     introduces @(tsee cert-with-author+round),
     which is why
     @(tsee signer-record-p-when-get-author+round-in-signed-certificates)
     is phrased in terms of that certificate retrieval function.")
   (xdoc::p
    "The other kinds of events do not change the sets of signed certificates,
     and thus it is easy to prove the preservation of the invariant."))

  ;; create-certificate:

  (defruled certificate-set-unequivocalp-of-create-certificate-next
    (implies (and (signer-records-p systate)
                  (set::in signer (correct-addresses systate))
                  (certificate-set-unequivocalp
                   (signed-certificates signer systate))
                  (create-certificate-possiblep cert systate)
                  (no-self-buffer-p systate)
                  (no-self-endorsed-p systate))
             (certificate-set-unequivocalp
              (signed-certificates
               signer (create-certificate-next cert systate))))
    :enable (signed-certificates-of-create-certificate-next
             certificate-set-unequivocalp-of-insert
             signer-record-p-when-get-author+round-in-signed-certificates)
    :use no-signer-record-when-create-certificate-possiblep)

  (defruled unequivocal-signed-certificates-p-of-create-certificate-next
    (implies (and (unequivocal-signed-certificates-p systate)
                  (signer-records-p systate)
                  (no-self-buffer-p systate)
                  (no-self-endorsed-p systate)
                  (create-certificate-possiblep cert systate))
             (unequivocal-signed-certificates-p
              (create-certificate-next cert systate)))
    :enable (unequivocal-signed-certificates-p
             unequivocal-signed-certificates-p-necc
             certificate-set-unequivocalp-of-create-certificate-next))

  ;; receive-certificate:

  (defruled unequivocal-signed-certificates-p-of-receive-certificate-next
    (implies (and (unequivocal-signed-certificates-p systate)
                  (receive-certificate-possiblep msg systate))
             (unequivocal-signed-certificates-p
              (receive-certificate-next msg systate)))
    :enable (unequivocal-signed-certificates-p
             unequivocal-signed-certificates-p-necc
             signed-certificates-of-receive-certificate-next))

  ;; store-certificate:

  (defruled unequivocal-signed-certificates-p-of-store-certificate-next
    (implies (and (unequivocal-signed-certificates-p systate)
                  (store-certificate-possiblep val cert systate))
             (unequivocal-signed-certificates-p
              (store-certificate-next val cert systate)))
    :enable (unequivocal-signed-certificates-p
             unequivocal-signed-certificates-p-necc
             signed-certificates-of-store-certificate-next))

  ;; advance-round:

  (defruled unequivocal-signed-certificates-p-of-advance-round-next
    (implies (and (unequivocal-signed-certificates-p systate)
                  (advance-round-possiblep val systate))
             (unequivocal-signed-certificates-p
              (advance-round-next val systate)))
    :enable (unequivocal-signed-certificates-p
             unequivocal-signed-certificates-p-necc
             signed-certificates-of-advance-round-next))

  ;; commit-anchors:

  (defruled unequivocal-signed-certificates-p-of-commit-anchors-next
    (implies (and (unequivocal-signed-certificates-p systate)
                  (commit-anchors-possiblep val systate))
             (unequivocal-signed-certificates-p
              (commit-anchors-next val systate)))
    :enable (unequivocal-signed-certificates-p
             unequivocal-signed-certificates-p-necc
             signed-certificates-of-commit-anchors-next))

  ;; timer-expires:

  (defruled unequivocal-signed-certificates-p-of-timer-expires-next
    (implies (and (unequivocal-signed-certificates-p systate)
                  (timer-expires-possiblep val systate))
             (unequivocal-signed-certificates-p
              (timer-expires-next val systate)))
    :enable (unequivocal-signed-certificates-p
             unequivocal-signed-certificates-p-necc
             signed-certificates-of-timer-expires-next))

  ;; all events:

  (defruled unequivocal-signed-certificates-p-of-event-next
    (implies (and (unequivocal-signed-certificates-p systate)
                  (signer-records-p systate)
                  (no-self-buffer-p systate)
                  (no-self-endorsed-p systate)
                  (event-possiblep event systate))
             (unequivocal-signed-certificates-p
              (event-next event systate)))
    :enable (event-possiblep
             event-next)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection unequivocal-signed-certificates-p-always
  :short "The invariant holds in every state
          reachable from an initial state via a sequence of events."

  (defruled unequivocal-signed-certificates-p-of-events-next
    (implies (and (unequivocal-signed-certificates-p systate)
                  (signer-records-p systate)
                  (no-self-messages-p systate)
                  (no-self-buffer-p systate)
                  (no-self-endorsed-p systate)
                  (events-possiblep events systate))
             (and (unequivocal-signed-certificates-p
                   (events-next events systate))
                  (signer-records-p (events-next events systate))
                  (no-self-messages-p (events-next events systate))
                  (no-self-buffer-p (events-next events systate))
                  (no-self-endorsed-p (events-next events systate))))
    :induct t
    :disable ((:e tau-system))
    :enable (events-possiblep
             events-next
             unequivocal-signed-certificates-p-of-event-next
             signer-records-p-of-event-next
             no-self-messages-p-of-event-next
             no-self-buffer-p-of-event-next
             no-self-endorsed-p-of-event-next))

  (defruled unequivocal-signed-certificates-p-when-reachable
    (implies (and (system-initp systate)
                  (events-possiblep events systate))
             (unequivocal-signed-certificates-p (events-next events systate)))
    :disable ((:e tau-system))
    :enable (unequivocal-signed-certificates-p-when-init
             signer-records-p-when-init
             no-self-messages-p-when-init
             no-self-buffer-p-when-init
             no-self-endorsed-p-when-init
             unequivocal-signed-certificates-p-of-events-next)))
