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

(include-book "signer-records")
(include-book "no-self-endorsed")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ unequivocal-signed-certificates
  :parents (correctness)
  :short "Invariant that
          the certificates signed by a correct validator are unequivocal."
  :long
  (xdoc::topstring
   (xdoc::p
    "A correct validator signs a certificates
     under conditions formalized in @(tsee create-possiblep);
     recall that @('create') is the only kind of event
     that generates a new certificate.
     The conditions for certificate signing include the fact that
     the signer does not already have a record for
     a certificate with the same author and round:
     in other words, in order for the new certificate to be created,
     and thus be added to the set of certificates signed by the signer,
     the signer must not have a record of the certificate's author and round.
     But as proved in @(see signer-records),
     it is an invariant that each correct validator has
     a record of all the certificates it has signed.
     Therefore, a new certificate will be signed,
     and added to the set of signed certificates,
     only if it has a different author-round combination
     from all the existing signed certificates,
     thus preventing equivocation.")
   (xdoc::p
    "This non-equivocation property is limited to
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

(define-sk unequivocal-signed-certs-p ((systate system-statep))
  :returns (yes/no booleanp)
  :short "Definition of the invariant:
          the set of certificates signed by each correct validator
          is unequivocal."
  (forall (signer)
          (implies (set::in signer (correct-addresses systate))
                   (certificate-set-unequivocalp
                    (signed-certs signer systate))))
  ///
  (fty::deffixequiv-sk unequivocal-signed-certs-p
    :args ((systate system-statep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled unequivocal-signed-certs-p-when-init
  :short "Establishment of the invariant:
          the invariant holds in any initial system state."
  :long
  (xdoc::topstring
   (xdoc::p
    "Initially, there are no signed certificates,
     so the invariant trivially holds."))
  (implies (system-initp systate)
           (unequivocal-signed-certs-p systate))
  :enable (system-initp
           signed-certs-when-init
           unequivocal-signed-certs-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection not-signer-record-p-when-create-possiblep
  :short "If @(tsee create-possiblep) holds,
          then @(tsee signer-record-p) is false for its correct signers."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a key fact needed to prove our invariant.
     It says that, in order for a new certificate to be created,
     its correct signers must have no record of its author and round.
     This is then used to show that equivocation is not possible
     for the set of certificates signed by a validator.")
   (xdoc::p
    "This fact follows from
     the definition of @(tsee create-possiblep),
     as well as from another previously proved system invariant.")
   (xdoc::p
    "Consider the author first.
     For the author, @(tsee create-possiblep) requires
     that no certificates in the DAG have
     the author and round of the new certificates.
     It says nothing endorsed pairs,
     but an invariant come to the rescue here:
     @(tsee no-self-endorsed) tells us that
     the certificate's author's endorsed pairs include no pair
     whose first component is this validator,
     and so in particular the pair consisting of
     this validator plus the certificate's round.
     All together, these facts tell us that
     @(tsee signer-record-p) does not hold.")
   (xdoc::p
    "Consider an endorser next.
     Here @(tsee create-possiblep) directly requires
     the negation of all the disjunctions of @(tsee signer-record-p),
     which therefore is false.")
   (xdoc::p
    "We prove theorems for the predicates
     that make up @(tsee create-possiblep),
     culminating with the one for @(tsee create-possiblep).
     In the theorem about @(tsee create-author-possiblep),
     we add hypotheses corresponding to
     part of the body of @(tsee no-self-endorsed-p),
     which, in the theorem about @(tsee create-possiblep),
     get discharged via the @('-necc') rule of the invariant."))

  (defruled not-signer-record-p-when-create-author-possiblep
    (implies (and (create-author-possiblep cert vstate)
                  (equal (address+pos-pairs-with-address
                          (certificate->author cert)
                          (validator-state->endorsed vstate))
                         nil))
             (not (signer-record-p (certificate->author cert)
                                   (certificate->round cert)
                                   vstate)))
    :enable (create-author-possiblep
             create-signer-possiblep
             signer-record-p
             no-author+round-pair-if-no-pairs-with-author))

  (defruled not-signer-record-p-when-create-endorser-possiblep
    (implies (create-endorser-possiblep cert vstate)
             (not (signer-record-p (certificate->author cert)
                                   (certificate->round cert)
                                   vstate)))
    :enable (create-endorser-possiblep
             create-signer-possiblep
             signer-record-p))

  (defruled not-signer-record-p-when-create-endorsers-possiblep-loop
    (implies (and (create-endorsers-possiblep-loop cert endorsers systate)
                  (set::in endorser endorsers)
                  (set::in endorser (correct-addresses systate)))
             (not (signer-record-p (certificate->author cert)
                                   (certificate->round cert)
                                   (get-validator-state endorser systate))))
    :induct t
    :enable (create-endorsers-possiblep-loop
             not-signer-record-p-when-create-endorser-possiblep))

  (defruled not-signer-record-p-when-create-endorsers-possiblep
    (implies (and (create-endorsers-possiblep cert systate)
                  (set::in endorser (certificate->endorsers cert))
                  (set::in endorser (correct-addresses systate)))
             (not (signer-record-p (certificate->author cert)
                                   (certificate->round cert)
                                   (get-validator-state endorser systate))))
    :enable (create-endorsers-possiblep
             not-signer-record-p-when-create-endorsers-possiblep-loop))

  (defruled not-signer-record-p-when-create-possiblep
    (implies (and (create-possiblep cert systate)
                  (set::in signer (certificate->signers cert))
                  (set::in signer (correct-addresses systate))
                  (no-self-endorsed-p systate))
             (not (signer-record-p (certificate->author cert)
                                   (certificate->round cert)
                                   (get-validator-state signer systate))))
    :enable (create-possiblep
             certificate->signers
             not-signer-record-p-when-create-author-possiblep
             not-signer-record-p-when-create-endorsers-possiblep
             no-self-endorsed-p-necc)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled signer-record-p-when-author+round-in-signed-certs
  :short "If a certificate with a certain author and round
          can be obtained from the signed certificates of a validator,
          then the validator has a record of that author and round."
  :long
  (xdoc::topstring
   (xdoc::p
    "This has the opposite conclusion of
     @(tsee not-signer-record-p-when-create-possiblep),
     and in fact we use this and that theorem to prove by contradiction
     that @('create') preserves our invariant.")
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
                (cert-with-author+round author
                                        round
                                        (signed-certs signer systate)))
           (signer-record-p author round (get-validator-state signer systate)))
  :enable cert-with-author+round-element
  :use (:instance signer-records-p-necc
                  (cert (cert-with-author+round
                         author round (signed-certs signer systate)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection unequivocal-signed-certs-p-of-next
  :short "Preservation of the invariant:
          if the invariant holds in a system state,
          it also holds in the next system state."
  :long
  (xdoc::topstring
   (xdoc::p
    "The only kind of event that may change the set of signed certificates
     is @('create'), which adds the certificate to each signer.
     To show that no equivocation is introduced, we make use of
     @(tsee not-signer-record-p-when-create-possiblep)
     and @(tsee signer-record-p-when-author+round-in-signed-certs),
     to effectively derive a contradiction
     should the new certificate have the same author and round
     as some existing certificate.
     The rule @('certificate-set-unequivocalp-of-insert')
     introduces @(tsee cert-with-author+round),
     which is why
     @(tsee signer-record-p-when-author+round-in-signed-certs)
     is phrased in terms of that certificate retrieval function.")
   (xdoc::p
    "The other kinds of events do not change the sets of signed certificates,
     and thus it is easy to prove the preservation of the invariant."))

  ;; create:

  (defruled certificate-set-unequivocalp-of-create-next
    (implies (and (signer-records-p systate)
                  (set::in signer (correct-addresses systate))
                  (certificate-set-unequivocalp (signed-certs signer systate))
                  (create-possiblep cert systate)
                  (no-self-endorsed-p systate))
             (certificate-set-unequivocalp
              (signed-certs signer (create-next cert systate))))
    :enable (signed-certs-of-create-next
             certificate-set-unequivocalp-of-insert
             signer-record-p-when-author+round-in-signed-certs)
    :use not-signer-record-p-when-create-possiblep)

  (defruled unequivocal-signed-certs-p-of-create-next
    (implies (and (unequivocal-signed-certs-p systate)
                  (signer-records-p systate)
                  (no-self-endorsed-p systate)
                  (create-possiblep cert systate))
             (unequivocal-signed-certs-p (create-next cert systate)))
    :enable (unequivocal-signed-certs-p
             unequivocal-signed-certs-p-necc
             certificate-set-unequivocalp-of-create-next))

  ;; receive:

  (defruled unequivocal-signed-certs-p-of-receive-next
    (implies (and (unequivocal-signed-certs-p systate)
                  (receive-possiblep msg systate))
             (unequivocal-signed-certs-p (receive-next msg systate)))
    :enable (unequivocal-signed-certs-p
             unequivocal-signed-certs-p-necc
             signed-certs-of-receive-next))

  ;; store:

  (defruled unequivocal-signed-certs-p-of-store-next
    (implies (and (unequivocal-signed-certs-p systate)
                  (store-possiblep val cert systate))
             (unequivocal-signed-certs-p (store-next val cert systate)))
    :enable (unequivocal-signed-certs-p
             unequivocal-signed-certs-p-necc
             signed-certs-of-store-next))

  ;; advance:

  (defruled unequivocal-signed-certs-p-of-advance-next
    (implies (and (unequivocal-signed-certs-p systate)
                  (advance-possiblep val systate))
             (unequivocal-signed-certs-p (advance-next val systate)))
    :enable (unequivocal-signed-certs-p
             unequivocal-signed-certs-p-necc
             signed-certs-of-advance-next))

  ;; commit:

  (defruled unequivocal-signed-certs-p-of-commit-next
    (implies (and (unequivocal-signed-certs-p systate)
                  (commit-possiblep val systate))
             (unequivocal-signed-certs-p (commit-next val systate)))
    :enable (unequivocal-signed-certs-p
             unequivocal-signed-certs-p-necc
             signed-certs-of-commit-next))

  ;; timeout:

  (defruled unequivocal-signed-certs-p-of-timeout-next
    (implies (and (unequivocal-signed-certs-p systate)
                  (timeout-possiblep val systate))
             (unequivocal-signed-certs-p (timeout-next val systate)))
    :enable (unequivocal-signed-certs-p
             unequivocal-signed-certs-p-necc
             signed-certs-of-timeout-next))

  ;; all events:

  (defruled unequivocal-signed-certs-p-of-event-next
    (implies (and (unequivocal-signed-certs-p systate)
                  (signer-records-p systate)
                  (no-self-endorsed-p systate)
                  (event-possiblep event systate))
             (unequivocal-signed-certs-p (event-next event systate)))
    :enable (event-possiblep
             event-next)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection unequivocal-signed-certs-p-always
  :short "The invariant holds in every state
          reachable from an initial state via a sequence of events."

  (defruled unequivocal-signed-certs-p-of-events-next
    (implies (and (unequivocal-signed-certs-p systate)
                  (signer-records-p systate)
                  (no-self-endorsed-p systate)
                  (events-possiblep events systate))
             (and (unequivocal-signed-certs-p (events-next events systate))
                  (signer-records-p (events-next events systate))
                  (no-self-endorsed-p (events-next events systate))))
    :induct t
    :enable (events-possiblep
             events-next))

  (defruled unequivocal-signed-certs-p-when-reachable
    (implies (and (system-initp systate)
                  (events-possiblep events systate))
             (unequivocal-signed-certs-p (events-next events systate)))))
