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

(include-book "unequivocal-dags-def-and-init")
(include-book "nonforking-blockchains-def-and-init")
(include-book "same-committees-def-and-implied")
(include-book "unequivocal-signed-certificates")
(include-book "quorum-intersection")
(include-book "signer-quorum")
(include-book "signed-and-associated-cerificates")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ unequivocal-dags-next
  :parents (correctness)
  :short "Invariant that DAGs are unequivocal:
          preservation."
  :long
  (xdoc::topstring
   (xdoc::p
    "As explained in @(see unequivocal-dags-def-and-init),
     in order to prove that the non-equivocation of DAG
     is preserved by state transitions,
     we need to assume that the old state satisfies
     not only the non-equivocation of DAGs,
     but also the non-forking of blockchains.
     From that, here we prove that the new state
     satisfies the non-equivocation of DAGs.")
   (xdoc::p
    "At a high level,
     the reason why DAGs are unequivocal is the following.
     By contradiction, suppose that two validators (which may be the same)
     have two equivocal certificates in DAGs, one for each validator,
     i.e. the two certificates have the same author and round,
     but they are different certificates.
     Each certificate would be signed by a quorum of validators,
     in the active committee for the round of both certificates.
     Each validator calculates its own active committee for that round,
     but because of the assumed non-forking of blockchains,
     those two calculated active committees are the same
     (see @(see same-committees-def-and-implied)).
     Thus, by quorum intersection,
     and assuming that the committee is fault-tolerant,
     we must have at least one correct validator in both signer sets.
     But a correct validator would not have signed
     two different certificates with the same author and round,
     so the initial premise must not hold,
     i.e. there cannot exist equivocal certificates.
     The just mentioned fact that a correct validator
     does not sign two equivocal certificates
     amounts to the already proved invariant that
     the set of the certificates signed by a correct validator
     is unequivocal (see @(see unequivocal-signed-certificates)),
     which we use to prove this new invariant.")
   (xdoc::p
    "The above argument has to be spelled out more precisely for ACL2.
     The only two kinds of events that may extend DAGs
     (and could therefore potentially break non-equivocation)
     are @('create') and @('store').")
   (xdoc::p
    "A @('create') event concerns the (correct) author of the certificate,
     which checks that the signers, including itself, of the new certificate
     are in the active committee and form a quorum.
     If a validator (the author or other) had already, in its DAG,
     a different certificate with the same author and round,
     the two certificates must have at least one common correct signer,
     whose signed certificates would thus be equivocal,
     but we know they are not,
     as already proved in @(see unequivocal-signed-certificates).")
   (xdoc::p
    "A @('store') event concerns the (correct) validator
     who moves the certificate from the buffer to the DAG;
     the validator checks that the signers are in the active committee.
     If a validator (the one storing the certificate, or another one)
     had already, in its DAG,
     a different certificate with the same author and round,
     the two certificates must have at least one common correct signer,
     whose signed certificates would thus be equivocal,
     but we know they are not,
     as already proved in @(see unequivocal-signed-certificates).")
   (xdoc::p
    "Elsewhere we prove that
     the invariant holds in every reachable state."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection unequivocal-dags-p-of-next
  :short "Preservation of the invariant:
          if the invariant holds in a system state,
          it also holds in the next system state."
  :long
  (xdoc::topstring
   (xdoc::p
    "The only two kinds of events that change the certificates in DAGs
     are @('create') and @('store').
     The former adds a certificate to the author's DAG;
     the latter adds a certificate to the storer's DAG.")
   (xdoc::p
    "The @('create') case is handled by first proving a lemma
     saying that if @('create') is possible
     then the DAG of any correct validator
     does not have any certificate with the same author and round
     as the newly created certificate.
     This fact is expressed via @(tsee cert-with-author+round)
     applied to the DAG.
     This fact is proved essentially as follows,
     where it is easier to think of the proof being by contradiction,
     i.e. assuming that a certificate with that author and round can be obtained
     from the DAG of a correct validator @('val'),
     and deriving a contradiction, meaning that in fact
     such a certificate cannot be obtained.
     This hypothetical certificate is of course
     @('(cert-with-author+round ...)') in the theorem.
     We use a quorum intersection argument on
     the signers of that certificate
     and the signers of the new certificate @('cert').
     The committee is the one calculated by
     the author of the certificate (which is assumed correct)
     and the generic correct validator @('val').
     We use the invariant that they calculate the same committee,
     which depends on the blockchain non-forking invariant,
     which has not been proved yet but that is assumed,
     as induction hypothesis, to hold in the current state
     (that actual proof by induction is done elsewhere);
     as explained in @(see unequivocal-dags-def-and-init),
     we prove blockchain non-forking and non-equivocation
     by simultaneous induction (elsewhere).
     So the quorum intersection argument applies to that common committee.
     We also need several invariants to satisfy the hypotheses
     of the quorum intersection theorem.
     We then use @(tsee not-signer-record-p-when-create-possiblep)
     and @(tsee signer-quorum-p) to derive the contradiction:
     according to the first one, if @('create') is possible,
     the correct signer in the quorum intersection
     has no record of the author and round of @('cert');
     according to the second one,
     the correct signer in the quorum intersection
     has a record of the author and round of
     @('(cert-with-author+round ...)'),
     which has the same author and round as @('cert').
     This is an impossibility.
     With that lemma in hand,
     the theorem about @('create') follows.
     We use rules to rewrite calls of @(tsee certificate-set-unequivocalp)
     and @(tsee certificate-sets-unequivocalp) applied to @(tsee set::insert)
     in terms of @(tsee cert-with-author+round),
     so that the lemma described above applies.
     The proof takes care of the different cases.")
   (xdoc::p
    "The @('store') case is handled similarly at a high level,
     but there are some differences.
     Here the certificates in question are
     the one moved into the DAG from the buffer by the target validator,
     and a generic @('(cert-with-author+round ...)')
     with the same author and round in the DAG of some generic validator.
     We first prove a lemma similar to the one for @('create'),
     where we say that @('(cert-with-author+round ...)')
     returns @('nil'), i.e. no such certificate can be retrieved.
     Again, it is easier to think of the proof by contradiction,
     i.e. assuming that @('(cert-with-author+round ...)') exists,
     and deriving a contradiction.
     We use a quorum intersection argument again,
     with the (common) committee calculated by the two validators.
     Since both certificates already exist
     (unlike @('cert') in the @('create') case),
     we can use the previously proved non-equivocation
     of the set of certificates signed by a correct validator,
     namely the validator in the quorum intersection,
     which has signed both certificates.
     They cannot be equivocal, so we have derived a contradiction.
     With this lemma in hand,
     the theorem about @('store')
     is proved in a manner similar to
     the theorem about @('create'),
     via rewrite rules about sets of unequivocal certificates.")
   (xdoc::p
    "Note that the lemmas mentioned above have fairly generic names,
     but they are local to this @(tsee defsection).")
   (xdoc::p
    "The proofs for the other four kinds of events are easy,
     because there is no change in the DAGs."))

  ;; create:

  (defruledl create-lemma
    (implies (and (system-committees-fault-tolerant-p systate)
                  (same-associated-certs-p systate)
                  (no-self-endorsed-p systate)
                  (signer-records-p systate)
                  (dag-committees-p systate)
                  (signer-quorum-p systate)
                  (same-committees-p systate)
                  (create-possiblep cert systate)
                  (set::in (certificate->author cert)
                           (correct-addresses systate))
                  (set::in val (correct-addresses systate)))
             (not (cert-with-author+round
                   (certificate->author cert)
                   (certificate->round cert)
                   (validator-state->dag (get-validator-state val systate)))))
    :enable (system-committees-fault-tolerant-p-necc
             validator-committees-fault-tolerant-p-necc
             dag-committees-p-necc
             validator-signer-quorum-p
             author-quorum-when-create-possiblep
             associated-certs
             in-signed-certs-when-in-associated-and-signer
             same-committees-p-necc
             cert-with-author+round-element
             committee-nonemptyp-when-nonempty-subset)
    :use ((:instance quorum-intersection-has-correct-validator
                     (commtt (active-committee-at-round
                              (certificate->round cert)
                              (validator-state->blockchain
                               (get-validator-state val systate))))
                     (vals1 (certificate->signers cert))
                     (vals2 (certificate->signers
                             (cert-with-author+round
                              (certificate->author cert)
                              (certificate->round cert)
                              (validator-state->dag
                               (get-validator-state val systate))))))
          (:instance dag-has-committees-p-necc
                     (cert (cert-with-author+round
                            (certificate->author cert)
                            (certificate->round cert)
                            (validator-state->dag
                             (get-validator-state val systate))))
                     (dag (validator-state->dag
                           (get-validator-state val systate)))
                     (blockchain (validator-state->blockchain
                                  (get-validator-state val systate))))
          (:instance same-active-committees-p-necc
                     (blocks1 (validator-state->blockchain
                               (get-validator-state val systate)))
                     (blocks2 (validator-state->blockchain
                               (get-validator-state
                                (certificate->author cert) systate)))
                     (round (certificate->round cert)))
          (:instance signer-quorum-p-necc
                     (cert (cert-with-author+round
                            (certificate->author cert)
                            (certificate->round cert)
                            (validator-state->dag
                             (get-validator-state val systate)))))
          (:instance not-signer-record-p-when-create-possiblep
                     (signer (pick-common-correct-validator
                              (certificate->signers cert)
                              (certificate->signers
                               (cert-with-author+round
                                (certificate->author cert)
                                (certificate->round cert)
                                (validator-state->dag
                                 (get-validator-state val systate))))
                              systate)))
          (:instance signer-records-p-necc
                     (signer (pick-common-correct-validator
                              (certificate->signers cert)
                              (certificate->signers
                               (cert-with-author+round
                                (certificate->author cert)
                                (certificate->round cert)
                                (validator-state->dag
                                 (get-validator-state val systate))))
                              systate))
                     (cert (cert-with-author+round
                            (certificate->author cert)
                            (certificate->round cert)
                            (validator-state->dag
                             (get-validator-state val systate)))))))

  (defruled unequivocal-dags-p-of-create-next
    (implies (and (unequivocal-dags-p systate)
                  (system-committees-fault-tolerant-p systate)
                  (same-associated-certs-p systate)
                  (no-self-endorsed-p systate)
                  (signer-records-p systate)
                  (dag-committees-p systate)
                  (signer-quorum-p systate)
                  (same-committees-p systate)
                  (create-possiblep cert systate))
             (unequivocal-dags-p (create-next cert systate)))
    :enable (unequivocal-dags-p
             unequivocal-dags-p-necc
             validator-state->dag-of-create-next
             certificate-sets-unequivocalp-of-insert
             certificate-sets-unequivocalp-of-same-set
             certificate-set-unequivocalp-of-insert
             certificate-sets-unequivocalp-commutative
             unequivocal-dags-p-necc-single
             create-lemma))

  ;; receive:

  (defruled unequivocal-dags-p-of-receive-next
    (implies (and (unequivocal-dags-p systate)
                  (receive-possiblep msg systate))
             (unequivocal-dags-p (receive-next msg systate)))
    :enable (unequivocal-dags-p
             unequivocal-dags-p-necc))

  ;; store:

  (defruledl store-lemma
    (implies (and (system-committees-fault-tolerant-p systate)
                  (same-associated-certs-p systate)
                  (dag-committees-p systate)
                  (signer-quorum-p systate)
                  (unequivocal-signed-certs-p systate)
                  (same-committees-p systate)
                  (store-possiblep val1 cert systate)
                  (addressp val1)
                  (certificatep cert)
                  (set::in val (correct-addresses systate))
                  (not (set::in cert
                                (validator-state->dag
                                 (get-validator-state val systate)))))
             (not (cert-with-author+round
                   (certificate->author cert)
                   (certificate->round cert)
                   (validator-state->dag (get-validator-state val systate)))))
    :enable (system-committees-fault-tolerant-p-necc
             validator-committees-fault-tolerant-p-necc
             dag-committees-p-necc
             validator-signer-quorum-p
             store-possiblep
             unequivocal-signed-certs-p-necc
             associated-certs
             in-signed-certs-when-in-associated-and-signer
             same-committees-p-necc
             committee-nonemptyp-when-nonempty-subset)
    :use ((:instance quorum-intersection-has-correct-validator
                     (commtt (active-committee-at-round
                              (certificate->round cert)
                              (validator-state->blockchain
                               (get-validator-state val systate))))
                     (vals1 (certificate->signers cert))
                     (vals2 (certificate->signers
                             (cert-with-author+round
                              (certificate->author cert)
                              (certificate->round cert)
                              (validator-state->dag
                               (get-validator-state val systate))))))
          (:instance dag-has-committees-p-necc
                     (cert (cert-with-author+round
                            (certificate->author cert)
                            (certificate->round cert)
                            (validator-state->dag
                             (get-validator-state val systate))))
                     (dag (validator-state->dag
                           (get-validator-state val systate)))
                     (blockchain (validator-state->blockchain
                                  (get-validator-state val systate))))
          (:instance same-active-committees-p-necc
                     (blocks1 (validator-state->blockchain
                               (get-validator-state val systate)))
                     (blocks2 (validator-state->blockchain
                               (get-validator-state val1 systate)))
                     (round (certificate->round cert)))
          (:instance signer-quorum-p-necc
                     (cert (cert-with-author+round
                            (certificate->author cert)
                            (certificate->round cert)
                            (validator-state->dag
                             (get-validator-state val systate)))))
          (:instance certificate-set-unequivocalp-necc
                     (cert1 cert)
                     (cert2 (cert-with-author+round
                             (certificate->author cert)
                             (certificate->round cert)
                             (validator-state->dag
                              (get-validator-state val systate))))
                     (certs (signed-certs
                             (pick-common-correct-validator
                              (certificate->signers cert)
                              (certificate->signers
                               (cert-with-author+round
                                (certificate->author cert)
                                (certificate->round cert)
                                (validator-state->dag
                                 (get-validator-state val systate))))
                              systate)
                             systate)))
          (:instance cert-with-author+round-element
                     (author (certificate->author cert))
                     (round (certificate->round cert))
                     (certs (validator-state->dag
                             (get-validator-state val systate))))))

  (defruled unequivocal-dags-p-of-store-next
    (implies (and (unequivocal-dags-p systate)
                  (system-committees-fault-tolerant-p systate)
                  (same-associated-certs-p systate)
                  (dag-committees-p systate)
                  (signer-quorum-p systate)
                  (unequivocal-signed-certs-p systate)
                  (same-committees-p systate)
                  (store-possiblep val cert systate)
                  (addressp val)
                  (certificatep cert))
             (unequivocal-dags-p (store-next val cert systate)))
    :enable (unequivocal-dags-p
             unequivocal-dags-p-necc
             validator-state->dag-of-store-next
             certificate-sets-unequivocalp-of-insert
             certificate-sets-unequivocalp-of-same-set
             certificate-set-unequivocalp-of-insert
             certificate-sets-unequivocalp-commutative
             unequivocal-dags-p-necc-single
             store-lemma))

  ;; advance:

  (defruled unequivocal-dags-p-of-advance-next
    (implies (and (unequivocal-dags-p systate)
                  (advance-possiblep val systate))
             (unequivocal-dags-p (advance-next val systate)))
    :enable (unequivocal-dags-p
             unequivocal-dags-p-necc))

  ;; commit:

  (defruled unequivocal-dags-p-of-commit-next
    (implies (and (unequivocal-dags-p systate)
                  (commit-possiblep val systate))
             (unequivocal-dags-p (commit-next val systate)))
    :enable (unequivocal-dags-p
             unequivocal-dags-p-necc))

  ;; timeout:

  (defruled unequivocal-dags-p-of-timeout-next
    (implies (and (unequivocal-dags-p systate)
                  (timeout-possiblep val systate))
             (unequivocal-dags-p (timeout-next val systate)))
    :enable (unequivocal-dags-p
             unequivocal-dags-p-necc))

  ;; all events:

  (defruled unequivocal-dags-p-of-event-next
    (implies (and (unequivocal-dags-p systate)
                  (system-committees-fault-tolerant-p systate)
                  (same-associated-certs-p systate)
                  (no-self-endorsed-p systate)
                  (signer-records-p systate)
                  (dag-committees-p systate)
                  (signer-quorum-p systate)
                  (unequivocal-signed-certs-p systate)
                  (same-committees-p systate)
                  (event-possiblep event systate))
             (unequivocal-dags-p (event-next event systate)))
    :enable (event-possiblep
             event-next)))
