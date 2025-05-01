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
(include-book "backward-closure")
(include-book "unequivocal-accepted-certificates-def-and-init")

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
     in which case there must be no references.")
   (xdoc::p
    "When a certificate is received via a @('receive-certificate') event,
     that event's preconditions impose a similar requirement.")
   (xdoc::p
    "Thus, all the certificates accepted by a validator
     satisfy that requirement.
     Recall that a @('store-certificate') event
     does not change the set of accepted certificates;
     it just moves a certificate between buffer and DAG.")
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
  :guard (or (equal (certificate->round cert) 1)
             (active-committee-at-round (1- (certificate->round cert))
                                        (validator-state->blockchain vstate)
                                        all-vals))
  :returns (yes/no booleanp)
  :short "Check if either a certificate has round 1
          or its references to previous certificates
          are in the committee for the certificate's round
          and form a quorum in that committee,
          where the committee is calculated by a validator
          (represented by its state)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used by @(tsee previous-quorum-p) to define our invariant.
     The validator whose state is @('vstate') is
     the one that has accepted the certificate.
     The guard ensures that the validator can calculate the committee.")
   (xdoc::p
    "We prove a theorem about the cardinality of the predecessors of @('cert'),
     which we use to prove @(tsee dag-predecessor-cardinality-p)
     from @(tsee previous-quorum-p) later.
     Under certain invariant conditions,
     the number of references to previous certificates
     is the same as the number of predecessor certificates;
     these invariant conditions are backward closure and non-equivocation.
     The key rule is
     @('cardinality-of-certs-with-authors+round-when-subset'),
     since @(tsee predecessors) is defined
     in terms of @(tsee certs-with-authors+round).
     This rule gives us the desired equality to prove the theorem,
     but we need to discharge the hypothesis that
     the set of references to previous certificates
     is a subset of the authors of
     the certificates at the preceding round,
     i.e. backward closure.
     The non-equivocation is one of the hypothesis of that key rule too."))
  (b* (((validator-state vstate) vstate)
       ((certificate cert) cert))
    (if (= cert.round 1)
        (set::emptyp cert.previous)
      (b* ((commtt (active-committee-at-round (1- cert.round)
                                              vstate.blockchain
                                              all-vals)))
        (and (set::subset cert.previous (committee-members commtt))
             (equal (set::cardinality cert.previous)
                    (committee-quorum commtt))))))
  :guard-hints (("Goal" :in-theory (enable posp)))
  :hooks (:fix)

  ///

  (defruled cardinality-of-predecessors-when-validator-previous-quorum-p
    (implies (and (validator-previous-quorum-p cert vstate all-vals)
                  (certificate-set-unequivocalp (validator-state->dag vstate))
                  (certificate-previous-in-dag-p
                   cert (validator-state->dag vstate)))
             (equal (set::cardinality
                     (predecessors cert (validator-state->dag vstate)))
                    (if (equal (certificate->round cert) 1)
                        0
                      (b* ((commtt (active-committee-at-round
                                    (1- (certificate->round cert))
                                    (validator-state->blockchain vstate)
                                    all-vals)))
                        (committee-quorum commtt)))))
    :enable (predecessors
             cardinality-of-certs-with-authors+round-when-subset
             certificate-previous-in-dag-p)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk previous-quorum-p ((systate system-statep))
  :guard (accepted-certificate-committee-p systate)
  :returns (yes/no booleanp)
  :short "Definition of the invariant:
          for each certificate accepted by a validator,
          either the certificate's round is 1
          and the certificate has no references to previous certificates,
          or the certificate's round is not 1
          and the references to previous certificates
          form a quorum in the committee of
          the preceding round of the certificate."
  :long
  (xdoc::topstring
   (xdoc::p
    "This invariant, along with backward closure and non-equivocation,
     guarantees that @(tsee dag-predecessor-cardinality-p) holds.
     The key lemma is
     @('cardinality-of-predecessors-when-validator-previous-quorum-p')
     proved in @(tsee validator-previous-quorum-p).
     Here we just need to enable some rules
     to establish the hypotheses of that lemma."))
  (forall (val cert)
          (implies (and (set::in val (correct-addresses systate))
                        (set::in cert (accepted-certificates val systate)))
                   (validator-previous-quorum-p
                    cert
                    (get-validator-state val systate)
                    (all-addresses systate))))
  :guard-hints
  (("Goal"
    :in-theory (enable accepted-certificate-committee-p-necc
                       active-committee-at-previous-round-when-at-round
                       posp)))

  ///

  (fty::deffixequiv-sk previous-quorum-p
    :args ((systate system-statep)))

  (defruled dag-predecessor-cardinality-p-when-previous-quorum-p
    (implies (and (previous-quorum-p systate)
                  (backward-closed-p systate)
                  (unequivocal-accepted-certificates-p systate)
                  (set::in val (correct-addresses systate)))
             (dag-predecessor-cardinality-p
              (validator-state->dag (get-validator-state val systate))
              (validator-state->blockchain (get-validator-state val systate))
              (all-addresses systate)))
    :use (:instance
          cardinality-of-predecessors-when-validator-previous-quorum-p
          (cert (dag-predecessor-cardinality-p-witness
                 (validator-state->dag
                  (get-validator-state val systate))
                 (validator-state->blockchain
                  (get-validator-state val systate))
                 (all-addresses systate)))
          (vstate (get-validator-state val systate))
          (all-vals (all-addresses systate)))
    :enable (predecessors
             dag-predecessor-cardinality-p
             previous-quorum-p-necc
             accepted-certificates
             certificate-set-unequivocalp-when-unequivocal-accepted
             dag-closedp-necc
             backward-closed-p-necc)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled previous-quorum-p-when-init
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
             validator-state->blockchain-of-create-certificate-next
             certificate->author-of-path-to-author+round))

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
                  (set::in cert (certs-with-round
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
             in-of-certs-with-round))

  (defruled author-in-committee-at-round-when-signer-quorum-p
    (implies (and (signer-quorum-p systate)
                  (set::in val (correct-addresses systate))
                  (set::in cert (certs-with-round
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
               (set::subset (cert-set->author-set
                             (certs-with-round
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
                                    (cert-set->author-set
                                     (certs-with-round
                                      round
                                      (validator-state->dag
                                       (get-validator-state val systate)))))
                           (set::in author (committee-members commtt)))))
       :enable in-of-certs-with-author
       :use ((:instance
              in-cert-set->author-set-to-nonempty-certs-with-author
              (certs (certs-with-round
                      round
                      (validator-state->dag (get-validator-state val systate)))))
             (:instance
              author-in-committee-at-round-when-signer-quorum-p
              (cert (set::head (certs-with-author
                                author
                                (certs-with-round
                                 round
                                 (validator-state->dag
                                  (get-validator-state val systate)))))))
             (:instance set::in-head
                        (x (certs-with-author
                            author
                            (certs-with-round
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
             active-committee-at-previous-round-when-at-round
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
                  (accepted-certificate-committee-p systate)
                  (set::in val1 (correct-addresses systate))
                  (set::in cert (accepted-certificates val1 systate))
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
    :enable (active-committee-at-previous-round-when-at-round
             validator-previous-quorum-p
             validator-state->blockchain-of-commit-anchors-next
             active-committee-at-round-of-extend-blockchain-no-change
             blocks-ordered-even-p-of-extend-blockchain
             certificates-ordered-even-p-of-collect-anchors
             commit-anchors-possiblep
             ordered-even-p-necc-fixing
             collect-anchors-above-last-committed-round
             last-blockchain-round-p-necc-fixing
             posp
             pos-fix
             evenp
             accepted-certificate-committee-p-necc-fixing-binding
             certificate->round-of-cert-with-author+round))

  (defruled previous-quorum-p-of-commit-anchors-next
    (implies (and (ordered-even-p systate)
                  (last-blockchain-round-p systate)
                  (previous-quorum-p systate)
                  (accepted-certificate-committee-p systate)
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
                  (accepted-certificate-committee-p systate)
                  (previous-quorum-p systate)
                  (event-possiblep event systate))
             (previous-quorum-p (event-next event systate)))
    :enable (event-possiblep
             event-next)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection previous-quorum-p-always
  :short "The invariant holds in every state
          reachable from an initial state via a sequence of events."

  (defruled previous-quorum-p-of-events-next
    (implies (and (previous-quorum-p systate)
                  (signer-quorum-p systate)
                  (accepted-certificate-committee-p systate)
                  (ordered-even-p systate)
                  (last-blockchain-round-p systate)
                  (events-possiblep events systate))
             (and (previous-quorum-p (events-next events systate))
                  (signer-quorum-p (events-next events systate))
                  (accepted-certificate-committee-p
                   (events-next events systate))
                  (ordered-even-p (events-next events systate))
                  (last-blockchain-round-p (events-next events systate))))
    :induct t
    :disable ((:e tau-system))
    :enable (events-possiblep
             events-next
             previous-quorum-p-of-event-next
             signer-quorum-p-of-event-next
             accepted-certificate-committee-p-of-event-next
             ordered-even-p-of-event-next
             last-blockchain-round-p-of-event-next))

  (defruled previous-quorum-p-when-reachable
    (implies (and (system-initp systate)
                  (events-possiblep events systate))
             (previous-quorum-p (events-next events systate)))
    :disable ((:e tau-system))
    :enable (previous-quorum-p-when-init
             signer-quorum-p-when-init
             accepted-certificate-committee-p-when-init
             ordered-even-p-when-init
             last-blockchain-round-p-when-init
             previous-quorum-p-of-events-next)))
