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

(include-book "unequivocal-signed-certificates")
(include-book "committees-in-system")
(include-book "quorum-intersection")
(include-book "accepted-certificates-quorum")
(include-book "same-owned-certificates")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ unequivocal-accepted-certificates
  :parents (correctness)
  :short "Invariant that the certificates accepted by a correct validator
          are unequivocal."
  :long
  (xdoc::topstring
   (xdoc::p
    "In the model of AleoBFT with static committees,
     certificates are unequivocal across the whole system,
     i.e. all the certificates in the system have
     unique combinations of author and round.
     With our current model of dynamic committees,
     this property must be weakened slightly in order to be proved.
     The reason is that, in our model, the system always includes
     all possible validators that may form committees.
     Consider, for simplicity, the first few rounds, and the genesis committee.
     Even with the fault tolerance assumptions
     formalized in @(see fault-tolerance),
     there may well be a set of faulty validators,
     outside the genesis committee,
     who sign a new certificate that has
     the same author and round as an existing certificate,
     the latter having been properly created by the genesis committee.
     This event is perfectly possible
     according to our model of @('create-certificate').
     This equivocal certificate is broadcast to all correct validators,
     according to our model of reliable broadcast.
     However, our model of @('receive-certificate') says that
     a correct validator will accept a certificate
     only if its signers form a quorum in the active committee.
     Therefore, in the hypothetical situation sketched above,
     a correct validator will not accept the equivocal certificate,
     which will forever sit in the network,
     replicated in several messages (one per correct validator),
     but will never move from the network to a validator state.
     So this is how the non-equivocation property must be weakened:
     it must only apply to the set of accepted certificates,
     i.e. the ones in DAG and buffer; see @(tsee accepted-certificates).")
   (xdoc::p
    "At a high level,
     the reason why accepted certificates are unequivocal is the following.
     By contradiction, suppose that a validator has accepted
     two equivocal certificates,
     i.e. two different certificates with the same author and round.
     Each certificate would be signed by a quorum of validators,
     in the active committee for the round of both certificates.
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
     In fact, as proved in @(tsee accepted-certificates),
     sets of accepted certificates may be extended by two kinds of events,
     namely @('create-certificate') and @('receive-certificate').")
   (xdoc::p
    "The first one concerns the author of the certificate,
     and it actually uses a different argument from the one sketched above:
     the certificate author generates a certificate only if
     its DAG does not already have a certificate with that author and round,
     and we know from a previously proved invariant that
     the buffer does not contain certificates authored by the validator;
     therefore the new certificate cannot introduce equivocation.")
   (xdoc::p
    "The second one concerns the recipient of a message,
     which checks that the signers are in the active committee.
     Here the argument sketched earlier applies:
     if the validator had already accepted
     a different certificate with the same author and round,
     the two certificates must have at least one common correct signer,
     whose signed certificates would thus be equivocal,
     but we know they are not as already proved."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk unequivocal-accepted-certificates-p ((systate system-statep))
  :returns (yes/no booleanp)
  :short "Definition of the invariant:
          the set of certificates accepted by each correct validator
          is unequivocal."
  (forall (val)
          (implies (set::in val (correct-addresses systate))
                   (certificate-set-unequivocalp
                    (accepted-certificates val systate)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled unequivocal-accepted-certificates-p-when-init
  :short "Establishment of the invariant:
          the invariant holds in any initial system state."
  :long
  (xdoc::topstring
   (xdoc::p
    "Initially, there are no accepted certificates,
     so the invariant trivially holds."))
  (implies (system-initp systate)
           (unequivocal-accepted-certificates-p systate))
  :enable (unequivocal-accepted-certificates-p
           accepted-certificates-when-init))

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
     then the accepted certificates of the author
     do not have any certificate with the same author and round
     as the newly created certificate.
     This fact is expressed via @(tsee get-certificate-with-author+round)
     applied to @(tsee accepted-certificates).
     By opening up the latter, the proof reduces to showing that
     a certificate with that author and round is found
     neither in the DAG nor in the buffer.
     The fact that it is not in the DAG is explicitly checked
     by @(tsee create-certificate-possiblep),
     precisely by @(tsee create-certificate-signer-possiblep).
     The fact that it is not in the buffer
     is a consequence of the previously proved invariant
     that the buffer has no certificates authored by the validator.
     With this ley lemma in hand,
     we prove the preservation of the invariant for the whole system;
     only the new certificate's author gets a new accepted certificate,
     the other validators keep the same set of accepted certificates.
     We use @('certificate-set-unequivocalp-of-insert')
     to handle the extended set,
     which generates the call of @(tsee get-certificate-with-author+round),
     which is taken care of by the lemma.")
   (xdoc::p
    "The @('receive-certificate') case is more complex.
     It is easier to start with the top-level theorem for that, namely
     @('unequivocal-accepted-certificates-p-of-receive-certificate-next').
     Here @('accepted-certificates-of-receive-certificate-next')
     exposes @(tsee certificate-set-unequivocalp) of @(tsee set::insert),
     which @('certificate-set-unequivocalp-of-insert')
     rewrites to expose @(tsee get-certificate-with-author+round),
     similarly to the @('create-certificate') case.
     This is taken care of by @('receive-certificate-lemma4'),
     which contains most of the proof work here.
     Proving @('(not (get-certificate-with-author+round ...))')
     is like proving that @('(get-certificate-with-author+round ...)')
     implies @('nil'), which is a proof by contradiction.
     The assumption @('(get-certificate-with-author+round ...)')
     means that that certificate is among the accepted certificates,
     via @('get-certificate-with-author+round-element'),
     which we need to put in a @(':use') hints
     because the proof fails if we use it as a rewrite rule.
     So we have two certificates,
     namely @('(get-certificate-with-author+round ...)')
     and @('(message->certificate msg)'),
     for which we instantiate the quorum intersection argument,
     via the @(':use') hints with
     @(tsee quorum-intersection-has-correct-validator).
     To establish the hypotheses of this theorem,
     we need additional previously proved invariants.
     And then we instantiate @('certificate-set-unequivocalp-necc')
     for the two certificates,
     based on the fact that
     they are both in the set of certificates signed by
     the picked common validator in the quorum intersection,
     and on the fact that that set has already been proved unequivocal.
     But in order to show that the two certificates
     are in @(tsee signed-certificates),
     we need another lemma, namely @('receive-certificate-lemma3'),
     which concludes membership in @(tsee signed-certificates)
     under some other assumptions, including, critically,
     the fact that validators have the same owned certificates.
     This lemma applies twice, once for each certificates,
     but we need two additional lemmas to show that
     the two certificates are among the owned certificates.
     This is what @('receive-certificate-lemma1')
     and @('receive-certificate-lemma2') are for.")
   (xdoc::p
    "Note that the lemmas mentioned above have fairly generic names,
     but they are local to this @(tsee defsection).")
   (xdoc::p
    "The proofs for the other four kinds of events are easy,
     because there is no change in the set of accepted certificates."))

  ;; create-certificate:

  (defruledl create-certificate-lemma
    (implies (and (no-self-buffer-p systate)
                  (create-certificate-possiblep cert systate)
                  (set::in (certificate->author cert)
                           (correct-addresses systate)))
             (not (get-certificate-with-author+round
                   (certificate->author cert)
                   (certificate->round cert)
                   (accepted-certificates (certificate->author cert)
                                          systate))))
    :enable
    (accepted-certificates
     get-certificate-with-author+round-of-union-iff
     create-certificate-possiblep
     create-certificate-author-possiblep
     create-certificate-signer-possiblep
     no-self-buffer-p-necc
     no-certificate-with-author+round-if-no-certificates-with-author))

  (defruled unequivocal-accepted-certificates-p-of-create-certificate-next
    (implies (and (unequivocal-accepted-certificates-p systate)
                  (no-self-buffer-p systate)
                  (create-certificate-possiblep cert systate))
             (unequivocal-accepted-certificates-p
              (create-certificate-next cert systate)))
    :enable
    (unequivocal-accepted-certificates-p
     unequivocal-accepted-certificates-p-necc
     accepted-certificates-of-create-certificate-next
     certificate-set-unequivocalp-of-insert
     create-certificate-lemma))

  ;; receive-certificate:

  (defruledl receive-certificate-lemma1
    (implies (set::in (message-fix msg) (get-network-state systate))
             (set::in (message->certificate msg)
                      (owned-certificates (message->destination msg) systate)))
    :enable (owned-certificates
             in-of-message-certificates-with-destination))

  (defruledl receive-certificate-lemma2
    (implies (set::in cert (accepted-certificates val systate))
             (set::in cert (owned-certificates val systate)))
    :enable (accepted-certificates
             owned-certificates))

  (defruledl receive-certificate-lemma3
    (implies (and (same-owned-certificates-p systate)
                  (set::in val (correct-addresses systate))
                  (set::in cert (owned-certificates val systate))
                  (set::in signer (certificate->signers cert))
                  (set::in signer (correct-addresses systate)))
             (set::in cert (signed-certificates signer systate)))
    :enable (signed-certificates
             in-of-get-certificates-with-signer)
    :use (:instance same-owned-certificates-p-necc
                    (val1 val)
                    (val2 signer)))

  (defruledl receive-certificate-lemma4
    (implies (and (unequivocal-signed-certificates-p systate)
                  (same-owned-certificates-p systate)
                  (committees-in-system-p systate)
                  (system-fault-tolerant-p systate)
                  (accepted-certificates-quorum-p systate)
                  (receive-certificate-possiblep msg systate)
                  (not (set::in (message->certificate msg)
                                (accepted-certificates
                                 (message->destination msg) systate))))
             (not (get-certificate-with-author+round
                   (certificate->author (message->certificate msg))
                   (certificate->round (message->certificate msg))
                   (accepted-certificates
                    (message->destination msg) systate))))
    :enable (receive-certificate-possiblep
             validator-committees-in-system-p-necc
             committees-in-system-p-necc
             validator-certificate-quorum-p
             system-fault-tolerant-p-necc
             validator-fault-tolerant-p-necc
             unequivocal-signed-certificates-p-necc
             receive-certificate-lemma1
             receive-certificate-lemma2
             receive-certificate-lemma3)
    :use ((:instance quorum-intersection-has-correct-validator
                     (commtt
                      (active-committee-at-round
                       (certificate->round (message->certificate msg))
                       (validator-state->blockchain
                        (get-validator-state (message->destination msg)
                                             systate))
                       (all-addresses systate)))
                     (vals1 (certificate->signers
                             (message->certificate msg)))
                     (vals2 (certificate->signers
                             (get-certificate-with-author+round
                              (certificate->author (message->certificate msg))
                              (certificate->round (message->certificate msg))
                              (accepted-certificates
                               (message->destination msg) systate)))))
          (:instance accepted-certificates-quorum-p-necc
                     (val (message->destination msg))
                     (cert (get-certificate-with-author+round
                            (certificate->author (message->certificate msg))
                            (certificate->round (message->certificate msg))
                            (accepted-certificates
                             (message->destination msg) systate))))
          (:instance certificate-set-unequivocalp-necc
                     (cert1 (message->certificate msg))
                     (cert2 (get-certificate-with-author+round
                             (certificate->author (message->certificate msg))
                             (certificate->round (message->certificate msg))
                             (accepted-certificates
                              (message->destination msg) systate)))
                     (certs (signed-certificates
                             (pick-common-correct-validator
                              (certificate->signers (message->certificate msg))
                              (certificate->signers
                               (get-certificate-with-author+round
                                (certificate->author (message->certificate msg))
                                (certificate->round (message->certificate msg))
                                (accepted-certificates
                                 (message->destination msg) systate)))
                              systate)
                             systate)))
          (:instance get-certificate-with-author+round-element
                     (author (certificate->author (message->certificate msg)))
                     (round (certificate->round (message->certificate msg)))
                     (certs (accepted-certificates
                             (message->destination msg) systate)))))

  (defruled unequivocal-accepted-certificates-p-of-receive-certificate-next
    (implies (and (unequivocal-accepted-certificates-p systate)
                  (unequivocal-signed-certificates-p systate)
                  (same-owned-certificates-p systate)
                  (committees-in-system-p systate)
                  (system-fault-tolerant-p systate)
                  (accepted-certificates-quorum-p systate)
                  (receive-certificate-possiblep msg systate))
             (unequivocal-accepted-certificates-p
              (receive-certificate-next msg systate)))
    :enable (unequivocal-accepted-certificates-p
             unequivocal-accepted-certificates-p-necc
             accepted-certificates-of-receive-certificate-next
             certificate-set-unequivocalp-of-insert
             receive-certificate-lemma4))

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
                  (accepted-certificates-quorum-p systate)
                  (no-self-buffer-p systate)
                  (event-possiblep event systate))
             (unequivocal-accepted-certificates-p
              (event-next event systate)))
    :enable (event-possiblep
             event-next)))
