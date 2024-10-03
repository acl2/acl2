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

(include-book "signer-quorum")
(include-book "ordered-even-blocks")

(local (include-book "arithmetic-3/top" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ previous-quorum
  :parents (correctness)
  :short "Invariant that each certificate accepted by a validator
          has references to previous certificates
          that form a quorum in the committee,
          unless the round is 1,
          in which case there are no references to previous certificates."
  :long
  (xdoc::topstring
   (xdoc::p
    "When a new certificate is created via a @('create-certificate') event,
     that event's preconditions require that the certificate includes
     a quorum of references to certificates in the previous round,
     unless the certificate round is 1,
     in which case there must be no references.
     This applies to all the certificates accepted by validators,
     i.e. the certificates in their DAGs and buffers,
     because
     ")
   (xdoc::p
    "The names for this invariant,
     i.e. this XDOC topic as well as the function and theorem names,
     just mention `quorum' for brevity,
     even though that does not apply to round 1.
     But rounds greater than 1 are the ``normal'' case,
     while round 1 is a special case."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define validator-previous-quorum-p ((cert certificatep)
                                     (vstate validator-statep)
                                     (all-vals address-setp))
  :returns (yes/no booleanp)
  :short "Check if the certificate accepted by
          a validator (represented by its state)
          satisfies the invariant."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used by @(tsee previous-quorum-p) to define our invariant.
     The validator whose state is @('vstate') is
     the one that has the accepted certificate.")
   (xdoc::p
    "If the certificate's round is 1,
     it must have no references to previous certificates;
     this check does not actually depend on the validator state.
     If the certificate's round is not 1,
     then the validator must be able to calculate
     the active committee at the previous round,
     and the references to the previous certificates
     must form a quorum in that committee."))
  (b* (((validator-state vstate) vstate)
       ((certificate cert) cert))
    (if (= cert.round 1)
        (set::emptyp cert.previous)
      (b* ((commtt (active-committee-at-round (1- cert.round)
                                              vstate.blockchain
                                              all-vals)))
        (and commtt
             (set::subset cert.previous (committee-members commtt))
             (equal (set::cardinality cert.previous)
                    (committee-quorum commtt))))))
  :guard-hints (("Goal" :in-theory (enable posp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk previous-quorum-p ((systate system-statep))
  :returns (yes/no booleanp)
  :short "Definition of the invariant:
          for each certificate accepted by a validator,
          either the certificate's round is 1
          and the certificate has no references to previous certificates,
          or the certificate's round is not 1
          and the validator can calculate
          the active committee in the previous round
          where the referenced previous certificates form a quorum."
  (forall (val cert)
          (implies (and (set::in val (correct-addresses systate))
                        (set::in cert (accepted-certificates val systate)))
                   (validator-previous-quorum-p
                    cert
                    (get-validator-state val systate)
                    (all-addresses systate)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule previous-quorum-p-when-init
  :short "Establishment of the invariant:
          the invariant holds in any initial system state."
  :long
  (xdoc::topstring
   (xdoc::p
    "Initially there are no accepted certificates in the system,
     so the universal quantification is trivially true."))
  (implies (system-initp systate)
           (previous-quorum-p systate))
  :enable (previous-quorum-p
           accepted-certificates-when-init))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection previous-quorum-p-of-next
  :short "Preservation of the invariant:
          if the invariant holds in a system state,
          it also holds in the next system state."
  :long
  (xdoc::topstring
   (xdoc::p
    "The proof is somewhat analogous to @(see signer-quorum-p-of-next):
     see that documentation.
     But there is an additional complication for @('create-certificate').
     For the new certificate, @(tsee create-certificate-possiblep)
     only checks that the references to the previous certificates
     are among the authors of the certificates in the preceding round;
     it does not check that they are members of
     the active committee at that preceding round.
     However, because of the previously proved invariant
     that certificate signers form a quorum
     (see @(see signer-quorum)),
     we know that the certificates at that preceding round,
     which are in the DAG and therefore among the accepted certificates,
     have signers, and in particular authors,
     in the active committee of that preceding round.
     So we assume that invariant in order to prove this invariant.
     We use that invariant to prove a sequence of theorems
     culminating with the one for the new certificate."))

  ;; create-certificate:

  (defruled validator-previous-quorum-p-of-create-certificate-next-old
    (implies (and (set::in val (correct-addresses systate))
                  (validator-previous-quorum-p
                   cert1
                   (get-validator-state val systate)
                   (all-addresses systate)))
             (validator-previous-quorum-p
              cert1
              (get-validator-state
               val (create-certificate-next cert systate))
              (all-addresses systate)))
    :enable (validator-previous-quorum-p
             validator-state->blockchain-of-create-certificate-next))

  (defruled signer-in-committee-when-validator-signer-quorum-p
    (implies (and (validator-signer-quorum-p cert vstate all-vals)
                  (set::in signer (certificate->signers cert)))
             (b* ((commtt (active-committee-at-round
                           (certificate->round cert)
                           (validator-state->blockchain vstate)
                           all-vals)))
               (set::in signer (committee-members commtt))))
    :enable (validator-signer-quorum-p
             set::expensive-rules))

  (defruled signer-in-committee-when-signer-quorum-p
    (implies (and (signer-quorum-p systate)
                  (set::in val (correct-addresses systate))
                  (set::in cert (accepted-certificates val systate))
                  (set::in signer (certificate->signers cert)))
             (b* ((commtt (active-committee-at-round
                           (certificate->round cert)
                           (validator-state->blockchain
                            (get-validator-state val systate))
                           (all-addresses systate))))
               (set::in signer (committee-members commtt))))
    :enable (signer-in-committee-when-validator-signer-quorum-p
             signer-quorum-p-necc))

  (defruled signer-in-committee-at-round-when-signer-quorum-p
    (implies (and (signer-quorum-p systate)
                  (set::in val (correct-addresses systate))
                  (set::in cert (certificates-with-round
                                 round
                                 (validator-state->dag
                                  (get-validator-state val systate))))
                  (set::in signer (certificate->signers cert)))
             (b* ((commtt (active-committee-at-round
                           round
                           (validator-state->blockchain
                            (get-validator-state val systate))
                           (all-addresses systate))))
               (set::in signer (committee-members commtt))))
    :use (:instance signer-in-committee-when-signer-quorum-p)
    :enable (accepted-certificates
             in-of-certificates-with-round))

  (defruled author-in-committee-at-round-when-signer-quorum-p
    (implies (and (signer-quorum-p systate)
                  (set::in val (correct-addresses systate))
                  (set::in cert (certificates-with-round
                                 round
                                 (validator-state->dag
                                  (get-validator-state val systate)))))
             (b* ((commtt (active-committee-at-round
                           round
                           (validator-state->blockchain
                            (get-validator-state val systate))
                           (all-addresses systate))))
               (set::in (certificate->author cert)
                        (committee-members commtt))))
    :use (:instance
          signer-in-committee-at-round-when-signer-quorum-p
          (signer (certificate->author cert)))
    :enable certificate->signers)

  (defruled authors-in-committee-at-round-when-signer-quorum-p
    (implies (and (signer-quorum-p systate)
                  (set::in val (correct-addresses systate)))
             (b* ((commtt (active-committee-at-round
                           round
                           (validator-state->blockchain
                            (get-validator-state val systate))
                           (all-addresses systate))))
               (set::subset (certificate-set->author-set
                             (certificates-with-round
                              round
                              (validator-state->dag
                               (get-validator-state val systate))))
                            (committee-members commtt))))
    :enable set::expensive-rules
    :prep-lemmas
    ((defrule lemma
       (implies (and (signer-quorum-p systate)
                     (set::in val (correct-addresses systate))
                     (addressp author))
                (b* ((commtt (active-committee-at-round
                              round
                              (validator-state->blockchain
                               (get-validator-state val systate))
                              (all-addresses systate))))
                  (implies (set::in author
                                    (certificate-set->author-set
                                     (certificates-with-round
                                      round
                                      (validator-state->dag
                                       (get-validator-state val systate)))))
                           (set::in author (committee-members commtt)))))
       :enable (certificates-with-author-subset
                in-of-certificates-with-author)
       :use ((:instance
              in-certificate-set->author-set-iff-certificates-with-author
              (certs (certificates-with-round
                      round
                      (validator-state->dag (get-validator-state val systate)))))
             (:instance
              author-in-committee-at-round-when-signer-quorum-p
              (cert (set::head (certificates-with-author
                                author
                                (certificates-with-round
                                 round
                                 (validator-state->dag
                                  (get-validator-state val systate)))))))
             (:instance set::in-head
                        (x (certificates-with-author
                            author
                            (certificates-with-round
                             round
                             (validator-state->dag
                              (get-validator-state val systate)))))))
       :disable set::in-head)))

  (defruled validator-previous-quorum-p-of-create-certificate-next-new
    (implies (and (signer-quorum-p systate)
                  (create-certificate-possiblep cert systate)
                  (set::in (certificate->author cert)
                           (correct-addresses systate)))
             (validator-previous-quorum-p
              cert
              (get-validator-state (certificate->author cert)
                                   (create-certificate-next cert systate))
              (all-addresses systate)))
    :enable (validator-previous-quorum-p
             create-certificate-possiblep
             create-certificate-author-possiblep
             create-certificate-signer-possiblep
             validator-state->blockchain-of-create-certificate-next
             active-committee-at-earlier-round-when-at-later-round
             posp
             authors-in-committee-at-round-when-signer-quorum-p
             set::expensive-rules))

  (defruled previous-quorum-p-of-create-certificate-next
    (implies (and (previous-quorum-p systate)
                  (signer-quorum-p systate)
                  (create-certificate-possiblep cert systate))
             (previous-quorum-p
              (create-certificate-next cert systate)))
    :use (:instance lemma (cert (certificate-fix cert)))
    :prep-lemmas
    ((defruled lemma
       (implies (and (certificatep cert)
                     (previous-quorum-p systate)
                     (signer-quorum-p systate)
                     (create-certificate-possiblep cert systate))
                (previous-quorum-p
                 (create-certificate-next cert systate)))
       :enable
       (previous-quorum-p
        previous-quorum-p-necc
        accepted-certificates-of-create-certificate-next
        validator-previous-quorum-p-of-create-certificate-next-old
        validator-previous-quorum-p-of-create-certificate-next-new))))

  ;; receive-certificate:

  (defruled validator-previous-quorum-p-of-receive-certificate-next-old
    (implies (and (set::in val (correct-addresses systate))
                  (validator-previous-quorum-p
                   cert
                   (get-validator-state val systate)
                   (all-addresses systate))
                  (receive-certificate-possiblep msg systate))
             (validator-previous-quorum-p
              cert
              (get-validator-state
               val (receive-certificate-next msg systate))
              (all-addresses systate)))
    :enable (validator-previous-quorum-p
             validator-state->blockchain-of-receive-certificate-next))

  (defruled validator-previous-quorum-p-of-receive-certificate-next-new
    (implies (receive-certificate-possiblep msg systate)
             (validator-previous-quorum-p
              (message->certificate msg)
              (get-validator-state (message->destination msg)
                                   (receive-certificate-next msg systate))
              (all-addresses systate)))
    :enable (validator-previous-quorum-p
             receive-certificate-possiblep
             validator-state->blockchain-of-receive-certificate-next))

  (defruled previous-quorum-p-of-receive-certificate-next
    (implies (and (previous-quorum-p systate)
                  (receive-certificate-possiblep msg systate))
             (previous-quorum-p
              (receive-certificate-next msg systate)))
    :enable (previous-quorum-p
             previous-quorum-p-necc
             accepted-certificates-of-receive-certificate-next
             validator-previous-quorum-p-of-receive-certificate-next-old
             validator-previous-quorum-p-of-receive-certificate-next-new))

  ;; store-certificate:

  (defruled validator-previous-quorum-p-of-store-certificate-next
    (implies (and (set::in val1 (correct-addresses systate))
                  (validator-previous-quorum-p
                   cert1
                   (get-validator-state val1 systate)
                   (all-addresses systate))
                  (store-certificate-possiblep val cert systate))
             (validator-previous-quorum-p
              cert1
              (get-validator-state
               val1 (store-certificate-next val cert systate))
              (all-addresses systate)))
    :enable (validator-previous-quorum-p
             validator-state->blockchain-of-store-certificate-next))

  (defruled previous-quorum-p-of-store-certificate-next
    (implies (and (previous-quorum-p systate)
                  (store-certificate-possiblep val cert systate))
             (previous-quorum-p
              (store-certificate-next val cert systate)))
    :enable (previous-quorum-p
             previous-quorum-p-necc
             accepted-certificates-of-store-certificate-next
             validator-previous-quorum-p-of-store-certificate-next))

  ;; advance-round:

  (defruled validator-previous-quorum-p-of-advance-round-next
    (implies (and (set::in val1 (correct-addresses systate))
                  (validator-previous-quorum-p
                   cert
                   (get-validator-state val1 systate)
                   (all-addresses systate))
                  (advance-round-possiblep val systate))
             (validator-previous-quorum-p
              cert
              (get-validator-state
               val1 (advance-round-next val systate))
              (all-addresses systate)))
    :enable (validator-previous-quorum-p
             validator-state->blockchain-of-advance-round-next))

  (defruled previous-quorum-p-of-advance-round-next
    (implies (and (previous-quorum-p systate)
                  (advance-round-possiblep val systate))
             (previous-quorum-p
              (advance-round-next val systate)))
    :enable (previous-quorum-p
             previous-quorum-p-necc
             accepted-certificates-of-advance-round-next
             validator-previous-quorum-p-of-advance-round-next))

  ;; commit-anchors:

  (defruled validator-previous-quorum-p-of-commit-anchors-next
    (implies (and (ordered-even-p systate)
                  (last-blockchain-round-p systate)
                  (set::in val1 (correct-addresses systate))
                  (validator-previous-quorum-p
                   cert
                   (get-validator-state val1 systate)
                   (all-addresses systate))
                  (commit-anchors-possiblep val systate))
             (validator-previous-quorum-p
              cert
              (get-validator-state
               val1 (commit-anchors-next val systate))
              (all-addresses systate)))
    :enable (validator-previous-quorum-p
             validator-state->blockchain-of-commit-anchors-next
             active-committee-at-round-of-extend-blockchain-no-change
             blocks-ordered-even-p-of-extend-blockchain
             certificates-ordered-even-p-of-collect-anchors
             commit-anchors-possiblep
             ordered-even-p-necc-fixing
             collect-anchors-above-last-committed-round
             last-blockchain-round-p-necc-fixing
             blocks-last-round
             posp
             pos-fix
             evenp))

  (defruled previous-quorum-p-of-commit-anchors-next
    (implies (and (ordered-even-p systate)
                  (last-blockchain-round-p systate)
                  (previous-quorum-p systate)
                  (commit-anchors-possiblep val systate))
             (previous-quorum-p
              (commit-anchors-next val systate)))
    :enable (previous-quorum-p
             previous-quorum-p-necc
             accepted-certificates-of-commit-anchors-next
             validator-previous-quorum-p-of-commit-anchors-next))

  ;; timer-expires:

  (defruled validator-previous-quorum-p-of-timer-expires-next
    (implies (and (set::in val1 (correct-addresses systate))
                  (validator-previous-quorum-p
                   cert
                   (get-validator-state val1 systate)
                   (all-addresses systate))
                  (timer-expires-possiblep val systate))
             (validator-previous-quorum-p
              cert
              (get-validator-state
               val1 (timer-expires-next val systate))
              (all-addresses systate)))
    :enable (validator-previous-quorum-p
             validator-state->blockchain-of-timer-expires-next))

  (defruled previous-quorum-p-of-timer-expires-next
    (implies (and (previous-quorum-p systate)
                  (timer-expires-possiblep val systate))
             (previous-quorum-p
              (timer-expires-next val systate)))
    :enable (previous-quorum-p
             previous-quorum-p-necc
             accepted-certificates-of-timer-expires-next
             validator-previous-quorum-p-of-timer-expires-next))

  ;; all events:

  (defruled previous-quorum-p-of-event-next
    (implies (and (signer-quorum-p systate)
                  (ordered-even-p systate)
                  (last-blockchain-round-p systate)
                  (previous-quorum-p systate)
                  (event-possiblep event systate))
             (previous-quorum-p (event-next event systate)))
    :enable (event-possiblep
             event-next)))
