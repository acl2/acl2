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

(include-book "unequivocal-accepted-certificates-def-and-init")
(include-book "nonforking-blockchains-def-and-init")
(include-book "same-committees-def-and-implied")
(include-book "unequivocal-signed-certificates")
(include-book "committees-in-system")
(include-book "quorum-intersection")
(include-book "signer-quorum")
(include-book "same-owned-certificates")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ unequivocal-accepted-certificates-next
  :parents (correctness)
  :short "Invariant that accepted certificates are unequivocal:
          preservation."
  :long
  (xdoc::topstring
   (xdoc::p
    "As explained in @(see unequivocal-accepted-certificates-def-and-init),
     in order to prove that the non-equivocation of accepted certificates
     is preserved by state transitions,
     we need to assume that the old state satisfies
     not only the non-equivocation of accepted certificates,
     but also the non-forking of blockchains.
     From that, here we prove that the new state
     satisfies the non-equivocation of accepted certificates.")
   (xdoc::p
    "At a high level,
     the reason why accepted certificates are unequivocal is the following.
     By contradiction, suppose that two validators (which may be the same)
     have two equivocal certificates, one for each validator,
     i.e. the two certificates have the same author and round,
     but they are different certificates.
     Each certificate would be signed by a quorum of validators,
     in the active committee for the round of both certificates.
     Each validator calculates its own active committee for that round,
     but because of the assumed non-forking of blockchains,
     those two calculated active committees are the same
     (see @(see same-committees)).
     Thus, by quorum intersection,
     and assuming that the committee is fault-tolerant,
     we must have at least one correct validator in both signer sets.
     But a correct validator would not have signed
     two different certificates with the same author and round,
     so the initial premise must not hold,
     i.e. there cannot exist equivocal certificates.
     The latter fact amounts to the already proved invariant that
     the set of the certificates signed by a correct validator
     is unequivocal (see @(see unequivocal-signed-certificates)),
     which we use to prove this new invariant.")
   (xdoc::p
    "The above argument has to be spelled out more precisely for ACL2.
     As proved in @(tsee accepted-certificates),
     sets of accepted certificates may be extended by two kinds of events,
     namely @('create-certificate') and @('receive-certificate').")
   (xdoc::p
    "The first one concerns the (correct) author of the certificate,
     which checks that the signers, including itself, of the new certificate
     are in the active committee and form a quorum.
     If a validator (the author or other) had already accepted
     a different certificate with the same author and round,
     the two certificates must have at least one common correct signer,
     whose signed certificates would thus be equivocal,
     but we know they are not as already proved.")
   (xdoc::p
    "The second one concerns the (correct) recipient of a message,
     which checks that the signers are in the active committee.
     If a validator (the recipient or other) had already accepted
     a different certificate with the same author and round,
     the two certificates must have at least one common correct signer,
     whose signed certificates would thus be equivocal,
     but we know they are not as already proved.")
   (xdoc::p
    "In @(see unequivocal-accepted-certificates), we prove that
     the invariant holds in every reachable state."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection unequivocal-accepted-certificates-p-of-next
  :short "Preservation of the invariant:
          if the invariant holds in a system state,
          it also holds in the next system state."
  :long
  (xdoc::topstring
   (xdoc::p
    "The only two kinds of events that change the accepted certificates
     are @('create-certificate') and @('receive-certificate').
     The former adds an accepted certificate to the author;
     the latter adds an accepted certificate to the recipient.")
   (xdoc::p
    "The @('create-certificate') case is handled by first proving a lemma
     saying that if @('create-certificate') is possible
     then the accepted certificates of any correct validator
     do not have any certificate with the same author and round
     as the newly created certificate.
     This fact is expressed via @(tsee certificate-with-author+round)
     applied to @(tsee accepted-certificates).
     This fact is proved essentially as follows,
     where it is easier to think of the proof being by contradiction,
     i.e. assuming that a certificate with that author and round can be obtained
     from the accepted certificates of a correct validator @('val'),
     and deriving a contradiction, meaning that in fact
     such a certificate cannot be obtained.
     This hypothetical certificate is of course
     @('(certificate-with-author+round ...)') in the theorem.
     We use a quorum intersection argument on
     the signers of that certificate
     and the signers of the new certificate @('cert').
     The committee is the one calculated by
     the author of the certificate (which is assumed correct)
     and the generic correct validator @('val').
     We use the invariant that they calculate the same committee,
     which depends on the blockchain non-forking invariant,
     which has not been proved yet but that holds in the current state;
     as explained in @(see unequivocal-accepted-certificates-def-and-init),
     we prove blockchain non-forking and non-equivocation
     by simultaneous induction.
     So the quorum intersection argument applies to that common committee.
     We also need several invariants to satisfy the hypotheses
     of the quorum intersection theorem.
     We then use @(tsee no-signer-record-when-create-certificate-possiblep)
     and @(tsee signer-quorum-p) to derive the contradiction:
     according to the first one, if @('create-certificate') is possible,
     the correct signer in the quorum intersection
     has no record of the author and round of @('cert');
     according to the second one,
     the correct signer in the quorum intersection
     has a record of the author and round of
     @('(certificate-with-author+round ...)'),
     which has the same author and round as @('cert').
     This is an impossibility.
     With that lemma in hand,
     the theorem about @('create-certificate') follows.
     We use rules to rewrite calls of @(tsee certificate-set-unequivocalp)
     and @(tsee certificate-sets-unequivocalp) applied to @(tsee set::insert)
     in terms of @(tsee certificate-with-author+round),
     so that the lemma described above applies.
     The proof takes care of the different cases.")
   (xdoc::p
    "The @('receive-certificate') case is handled similarly at a high level,
     but there are some differences.
     Here the certificates in question are
     the one received from the network by the destination validator,
     and a generic @('(certificate-with-author+round ...)')
     with the same author and round accepted by some validator.
     We first prove a lemma similar to the one for @('create-certificate'),
     where we say that @('(certificate-with-author+round ...)')
     returns @('nil'), i.e. no such certificate can be retrieved.
     Again, it is easier to think of the proof by contradiction,
     i.e. assuming that @('(certificate-with-author+round ...)') exists,
     and deriving a contradiction.
     We use a quorum intersection argument,
     with the (common) committee calculated by
     @('val') and the message's destination.
     Since both certificates already exist
     (unlike @('cert') in the @('create-certificate') case),
     we can use the previously proved non-equivocation
     of the set of certificates signed by a correct validator,
     namely the validator in the quorum intersection,
     which has signed both certificates.
     They cannot be equivocal, so we have derived a contradiction.
     With this lemma in hand,
     the theorem about @('receive-certificate')
     is proved in a manner similar to
     the theorem about @('create-certificate'),
     via rewrite rules about sets of unequivocal certificates.")
   (xdoc::p
    "Note that the lemmas mentioned above have fairly generic names,
     but they are local to this @(tsee defsection).")
   (xdoc::p
    "The proofs for the other four kinds of events are easy,
     because there is no change in the set of accepted certificates."))

  ;; create-certificate:

  (defruledl create-certificate-lemma
    (implies (and (signer-records-p systate)
                  (committees-in-system-p systate)
                  (system-fault-tolerant-p systate)
                  (signer-quorum-p systate)
                  (same-committees-p systate)
                  (no-self-buffer-p systate)
                  (no-self-endorsed-p systate)
                  (same-owned-certificates-p systate)
                  (accepted-certificate-committee-p systate)
                  (create-certificate-possiblep cert systate)
                  (set::in (certificate->author cert) (correct-addresses systate))
                  (set::in val (correct-addresses systate))
                  (not (in (certificate-fix cert)
                           (accepted-certificates val systate)))
                  (not (in (certificate-fix cert)
                           (accepted-certificates
                            (certificate->author cert) systate))))
             (not (certificate-with-author+round
                   (certificate->author cert)
                   (certificate->round cert)
                   (accepted-certificates val systate))))
    :enable (committees-in-system-p-necc
             validator-committees-in-system-p-necc-when-address-setp
             validator-signer-quorum-p
             certificate-with-author+round-element
             author-quorum-when-create-certificate-possiblep
             system-fault-tolerant-p-necc
             validator-fault-tolerant-p-necc
             in-owned-certificates-when-in-accepted-certificates
             in-signed-certificates-when-in-owned-and-signer
             certificate->author-of-certificate-with-author+round
             certificate->round-of-certificate-with-author+round
             same-committees-p-necc)
    :use ((:instance accepted-certificate-committee-p-necc
                     (cert (certificate-with-author+round
                            (certificate->author cert)
                            (certificate->round cert)
                            (accepted-certificates val systate))))
          (:instance quorum-intersection-has-correct-validator
                     (commtt
                      (active-committee-at-round
                       (certificate->round cert)
                       (validator-state->blockchain
                        (get-validator-state val systate))
                       (all-addresses systate)))
                     (vals1 (certificate->signers cert))
                     (vals2 (certificate->signers
                             (certificate-with-author+round
                              (certificate->author cert)
                              (certificate->round cert)
                              (accepted-certificates val systate)))))
          (:instance signer-quorum-p-necc
                     (cert (certificate-with-author+round
                            (certificate->author cert)
                            (certificate->round cert)
                            (accepted-certificates val systate))))
          (:instance same-active-committees-p-necc
                     (blocks1 (validator-state->blockchain
                               (get-validator-state val systate)))
                     (blocks2 (validator-state->blockchain
                               (get-validator-state (certificate->author cert)
                                                    systate)))
                     (all-vals (all-addresses systate))
                     (round (certificate->round cert)))
          (:instance no-signer-record-when-create-certificate-possiblep
                     (signer
                      (pick-common-correct-validator
                       (certificate->signers cert)
                       (certificate->signers
                        (certificate-with-author+round
                         (certificate->author cert)
                         (certificate->round cert)
                         (accepted-certificates val systate)))
                       systate)))
          (:instance signer-records-p-necc
                     (signer
                      (pick-common-correct-validator
                       (certificate->signers cert)
                       (certificate->signers
                        (certificate-with-author+round
                         (certificate->author cert)
                         (certificate->round cert)
                         (accepted-certificates val systate)))
                       systate))
                     (cert (certificate-with-author+round
                            (certificate->author cert)
                            (certificate->round cert)
                            (accepted-certificates val systate))))))

  (defruled unequivocal-accepted-certificates-p-of-create-certificate-next
    (implies (and (unequivocal-accepted-certificates-p systate)
                  (signer-records-p systate)
                  (committees-in-system-p systate)
                  (system-fault-tolerant-p systate)
                  (signer-quorum-p systate)
                  (same-committees-p systate)
                  (no-self-buffer-p systate)
                  (no-self-endorsed-p systate)
                  (same-owned-certificates-p systate)
                  (accepted-certificate-committee-p systate)
                  (create-certificate-possiblep cert systate))
             (unequivocal-accepted-certificates-p
              (create-certificate-next cert systate)))
    :enable (unequivocal-accepted-certificates-p
             unequivocal-accepted-certificates-p-necc
             accepted-certificates-of-create-certificate-next
             certificate-sets-unequivocalp-of-insert
             certificate-sets-unequivocalp-of-same-set
             certificate-set-unequivocalp-of-insert
             certificate-sets-unequivocalp-commutative
             unequivocal-accepted-certificates-p-necc-single
             create-certificate-lemma))

  ;; receive-certificate:

  (defruledl receive-certificate-lemma
    (implies (and (unequivocal-signed-certificates-p systate)
                  (same-owned-certificates-p systate)
                  (committees-in-system-p systate)
                  (system-fault-tolerant-p systate)
                  (signer-quorum-p systate)
                  (same-committees-p systate)
                  (accepted-certificate-committee-p systate)
                  (receive-certificate-possiblep msg systate)
                  (set::in (message->destination msg)
                           (correct-addresses systate))
                  (set::in val (correct-addresses systate))
                  (not (set::in (message->certificate msg)
                                (accepted-certificates val systate)))
                  (not (set::in (message->certificate msg)
                                (accepted-certificates
                                 (message->destination msg) systate))))
             (not (certificate-with-author+round
                   (certificate->author (message->certificate msg))
                   (certificate->round (message->certificate msg))
                   (accepted-certificates val systate))))
    :enable (committees-in-system-p-necc
             validator-committees-in-system-p-necc-when-address-setp
             validator-signer-quorum-p
             receive-certificate-possiblep
             system-fault-tolerant-p-necc
             validator-fault-tolerant-p-necc
             unequivocal-signed-certificates-p-necc
             in-owned-certificates-when-in-accepted-certificates
             in-signed-certificates-when-in-owned-and-signer
             message-certificate-in-owned-certificates
             certificate->author-of-certificate-with-author+round
             certificate->round-of-certificate-with-author+round
             same-committees-p-necc)
    :use ((:instance accepted-certificate-committee-p-necc
                     (cert (certificate-with-author+round
                            (certificate->author (message->certificate msg))
                            (certificate->round (message->certificate msg))
                            (accepted-certificates val systate))))
          (:instance quorum-intersection-has-correct-validator
                     (commtt
                      (active-committee-at-round
                       (certificate->round (message->certificate msg))
                       (validator-state->blockchain
                        (get-validator-state val systate))
                       (all-addresses systate)))
                     (vals1 (certificate->signers
                             (message->certificate msg)))
                     (vals2 (certificate->signers
                             (certificate-with-author+round
                              (certificate->author (message->certificate msg))
                              (certificate->round (message->certificate msg))
                              (accepted-certificates val systate)))))
          (:instance signer-quorum-p-necc
                     (cert (certificate-with-author+round
                            (certificate->author (message->certificate msg))
                            (certificate->round (message->certificate msg))
                            (accepted-certificates val systate))))
          (:instance same-active-committees-p-necc
                     (blocks1 (validator-state->blockchain
                               (get-validator-state val systate)))
                     (blocks2 (validator-state->blockchain
                               (get-validator-state (message->destination msg)
                                                    systate)))
                     (all-vals (all-addresses systate))
                     (round (certificate->round (message->certificate msg))))
          (:instance certificate-set-unequivocalp-necc
                     (cert1 (message->certificate msg))
                     (cert2 (certificate-with-author+round
                             (certificate->author (message->certificate msg))
                             (certificate->round (message->certificate msg))
                             (accepted-certificates val systate)))
                     (certs (signed-certificates
                             (pick-common-correct-validator
                              (certificate->signers (message->certificate msg))
                              (certificate->signers
                               (certificate-with-author+round
                                (certificate->author (message->certificate msg))
                                (certificate->round (message->certificate msg))
                                (accepted-certificates val systate)))
                              systate)
                             systate)))
          (:instance certificate-with-author+round-element
                     (author (certificate->author (message->certificate msg)))
                     (round (certificate->round (message->certificate msg)))
                     (certs (accepted-certificates val systate)))))

  (defruled unequivocal-accepted-certificates-p-of-receive-certificate-next
    (implies (and (unequivocal-accepted-certificates-p systate)
                  (unequivocal-signed-certificates-p systate)
                  (same-owned-certificates-p systate)
                  (committees-in-system-p systate)
                  (system-fault-tolerant-p systate)
                  (signer-quorum-p systate)
                  (same-committees-p systate)
                  (accepted-certificate-committee-p systate)
                  (receive-certificate-possiblep msg systate))
             (unequivocal-accepted-certificates-p
              (receive-certificate-next msg systate)))
    :enable (unequivocal-accepted-certificates-p
             unequivocal-accepted-certificates-p-necc
             accepted-certificates-of-receive-certificate-next
             certificate-sets-unequivocalp-of-insert
             certificate-sets-unequivocalp-of-same-set
             certificate-set-unequivocalp-of-insert
             certificate-sets-unequivocalp-commutative
             unequivocal-accepted-certificates-p-necc-single
             receive-certificate-lemma))

  ;; store-certificate:

  (defruled unequivocal-accepted-certificates-p-of-store-certificate-next
    (implies (and (unequivocal-accepted-certificates-p systate)
                  (store-certificate-possiblep val cert systate))
             (unequivocal-accepted-certificates-p
              (store-certificate-next val cert systate)))
    :enable (unequivocal-accepted-certificates-p
             unequivocal-accepted-certificates-p-necc
             accepted-certificates-of-store-certificate-next))

  ;; advance-round:

  (defruled unequivocal-accepted-certificates-p-of-advance-round-next
    (implies (and (unequivocal-accepted-certificates-p systate)
                  (advance-round-possiblep val systate))
             (unequivocal-accepted-certificates-p
              (advance-round-next val systate)))
    :enable (unequivocal-accepted-certificates-p
             unequivocal-accepted-certificates-p-necc
             accepted-certificates-of-advance-round-next))

  ;; commit-anchors:

  (defruled unequivocal-accepted-certificates-p-of-commit-anchors-next
    (implies (and (unequivocal-accepted-certificates-p systate)
                  (commit-anchors-possiblep val systate))
             (unequivocal-accepted-certificates-p
              (commit-anchors-next val systate)))
    :enable (unequivocal-accepted-certificates-p
             unequivocal-accepted-certificates-p-necc
             accepted-certificates-of-commit-anchors-next))

  ;; timer-expires:

  (defruled unequivocal-accepted-certificates-p-of-timer-expires-next
    (implies (and (unequivocal-accepted-certificates-p systate)
                  (timer-expires-possiblep val systate))
             (unequivocal-accepted-certificates-p
              (timer-expires-next val systate)))
    :enable (unequivocal-accepted-certificates-p
             unequivocal-accepted-certificates-p-necc
             accepted-certificates-of-timer-expires-next))

  ;; all events:

  (defruled unequivocal-accepted-certificates-p-of-event-next
    (implies (and (unequivocal-accepted-certificates-p systate)
                  (unequivocal-signed-certificates-p systate)
                  (same-owned-certificates-p systate)
                  (committees-in-system-p systate)
                  (system-fault-tolerant-p systate)
                  (signer-quorum-p systate)
                  (same-committees-p systate)
                  (no-self-buffer-p systate)
                  (no-self-endorsed-p systate)
                  (signer-records-p systate)
                  (accepted-certificate-committee-p systate)
                  (event-possiblep event systate))
             (unequivocal-accepted-certificates-p
              (event-next event systate)))
    :enable (event-possiblep
             event-next)))
