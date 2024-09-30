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
(include-book "ordered-even-blocks")

(local (include-book "arithmetic-3/top" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ accepted-certificates-quorum
  :parents (correctness)
  :short "Invariant that each certificate accepted by a validator
          has signers that form a quorum in the committee."
  :long
  (xdoc::topstring
   (xdoc::p
    "The set of certificates accepted by a validator
     is defined in @(tsee accepted-certificates) as
     the certificates in the DAG or buffer of the validator.
     It is the case that, for each such certificate,
     the validator can calculate the active committee for the certificate round
     and the certificate signers form a quorum in that committee;
     we prove this invariant here.")
   (xdoc::p
    "There are two possible ways in which a validator accepts a new certificate.
     One is when the validator authors the certificate,
     and adds it to the DAG (besides broadcasting it to other validators).
     For correct validators
     (which are the ones we are interested here,
     since the notion of accepted certificates is only defined for them),
     a @('create-certificate') event is only possible if
     the signers form a quorum in the committee calculated by the author,
     which maintains the invariant.
     The other way in which a validator accepts a new certificate
     is by receiving it from the network,
     but in this case a @('receive-certificate') event is possible
     only if the receiving validator
     can calculate the committee for the certificate round
     and the signers of the certificate form a quorum in that committee;
     that again maintains the invariant."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define validator-certificate-quorum-p ((cert certificatep)
                                        (vstate validator-statep)
                                        (all-vals address-setp))
  :returns (yes/no booleanp)
  :short "Check if
          (i) a validator (represented by its state)
          can calculate the active committee for a certificate,
          (ii) the committee contains all the signers, and
          (iii) the signers form a quorum in the committee."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used by @(tsee accepted-certificates-quorum-p)
     to define our invariant.
     The validator whose state is @('vstate') is
     the one that has the accepted certificate."))
  (b* (((validator-state vstate) vstate)
       ((certificate cert) cert)
       (commtt
        (active-committee-at-round cert.round vstate.blockchain all-vals)))
    (and commtt
         (set::subset (certificate->signers cert)
                      (committee-members commtt))
         (equal (set::cardinality (certificate->signers cert))
                (committee-quorum commtt)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk accepted-certificates-quorum-p ((systate system-statep))
  :returns (yes/no booleanp)
  :short "Definition of the invariant:
          the signers of every accepted certificate of every correct validator
          form a quorum in the committee for the certificate's round
          calculated by the validator from its own blockchain."
  (forall (val cert)
          (implies (and (set::in val (correct-addresses systate))
                        (set::in cert (accepted-certificates val systate)))
                   (validator-certificate-quorum-p
                    cert
                    (get-validator-state val systate)
                    (all-addresses systate)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled accepted-certificates-quorum-p-when-init
  :short "Establishment of the invariant:
          the invariant holds on any initial system state."
  :long
  (xdoc::topstring
   (xdoc::p
    "Initially there are no accepted certificates in the system,
     so the universal quantification is trivially true."))
  (implies (system-initp systate)
           (accepted-certificates-quorum-p systate))
  :enable (accepted-certificates-quorum-p
           accepted-certificates-when-init))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection accepted-certificates-quorum-p-of-next
  :short "Preservation of the invariant:
          if the invariant holds in a system state,
          it also holds in the next system state."
  :long
  (xdoc::topstring
   (xdoc::p
    "The only two kinds of events that may change the accepted certificates
     are @('create-certificate') and @('receive-certificate').")
   (xdoc::p
    "For @('create-certificate'),
     there are two cases to consider.
     For an existing (i.e. old) accepted certificate,
     we just need to show that the quorum signer property is preserved:
     this is easy, and relies on the fact that
     the blockchain, from which the committee is calculated,
     does not change for @('create-certificate').
     For a newly created certificate in @('create-certificate'),
     the only change to the accepted certificates is for the author:
     the other validator are sent the certificate in messages,
     but the messages are in the network,
     not in the buffer or DAG.
     The certificate's author adds the certificate directly to the DAG,
     so it gets added to the accepted certificates.
     But @(tsee create-certificate-possiblep)
     explicitly checks the quorum properties,
     from which the property is established for the new certificate.")
   (xdoc::p
    "For @('receive-certificate'), we have a similar split,
     considering an already accepted (i.e. old) certificate,
     and the newly accepted certificate received from the network.
     The case of an old certificate is similar to @('create-certificate');
     again, we use the rule saying that the blockchain
     does not change under a @('receive-certificate') event.
     In the case of a newly accepted certificate,
     it comes from the network,
     but @(tsee receive-certificate-possiblep)
     explicitly checks the quorum properties,
     thus establishing the property for the newly accepted certificate.")
   (xdoc::p
    "The set of accepted certificates does not change
     for the other four kinds of events,
     so the proofs for them always rely on the preservaton of the properties.
     For each kind of event,
     we prove a lemma about @(tsee validator-certificate-quorum-p)
     and then a theorem about @(tsee accepted-certificates-quorum-p).
     For @('store-certificate'), @('advance-round'), and @('timer-expires')
     there is no change to the blockchain, so the proof is fairly easy.
     For @('commit-anchors'), the blockchain changes,
     but we use the fact that extending the blockchain
     does not affect the calculation of committees
     calculated prior to the extension.
     But this property depends on the previously proved invariants
     that blockchain rounds are even and ordered,
     and that the last committed round in the validator state
     matches the latest block's round
     (or they are both 0 if there are no blocks);
     so we need to add these invariants as hypothesis,
     which therefore propagate to the theorem about @(tsee event-next)."))

  ;; create-certificate:

  (defruled validator-certificates-quorum-p-of-create-certificate-next-old
    (implies (and (set::in val (correct-addresses systate))
                  (validator-certificate-quorum-p
                   cert1
                   (get-validator-state val systate)
                   (all-addresses systate)))
             (validator-certificate-quorum-p
              cert1
              (get-validator-state
               val (create-certificate-next cert systate))
              (all-addresses systate)))
    :enable (validator-certificate-quorum-p
             validator-state->blockchain-of-create-certificate-next))

  (defruled validator-certificates-quorum-p-of-create-certificate-next-new
    (implies (and (create-certificate-possiblep cert systate)
                  (set::in (certificate->author cert)
                           (correct-addresses systate)))
             (validator-certificate-quorum-p
              cert
              (get-validator-state (certificate->author cert)
                                   (create-certificate-next cert systate))
              (all-addresses systate)))
    :enable (validator-certificate-quorum-p
             create-certificate-possiblep
             create-certificate-author-possiblep
             create-certificate-signer-possiblep
             validator-state->blockchain-of-create-certificate-next
             certificate->signers
             set::expensive-rules))

  (defruled accepted-certificates-quorum-p-of-create-certificate-next
    (implies (and (accepted-certificates-quorum-p systate)
                  (create-certificate-possiblep cert systate))
             (accepted-certificates-quorum-p
              (create-certificate-next cert systate)))
    :use (:instance lemma (cert (certificate-fix cert)))
    :prep-lemmas
    ((defruled lemma
       (implies (and (certificatep cert)
                     (accepted-certificates-quorum-p systate)
                     (create-certificate-possiblep cert systate))
                (accepted-certificates-quorum-p
                 (create-certificate-next cert systate)))
       :enable
       (accepted-certificates-quorum-p
        accepted-certificates-quorum-p-necc
        accepted-certificates-of-create-certificate-next
        validator-certificates-quorum-p-of-create-certificate-next-old
        validator-certificates-quorum-p-of-create-certificate-next-new))))

  ;; receive-certificate:

  (defruled validator-certificates-quorum-p-of-receive-certificate-next-old
    (implies (and (set::in val (correct-addresses systate))
                  (validator-certificate-quorum-p
                   cert
                   (get-validator-state val systate)
                   (all-addresses systate))
                  (receive-certificate-possiblep msg systate))
             (validator-certificate-quorum-p
              cert
              (get-validator-state
               val (receive-certificate-next msg systate))
              (all-addresses systate)))
    :enable (validator-certificate-quorum-p
             validator-state->blockchain-of-receive-certificate-next))

  (defruled validator-certificates-quorum-p-of-receive-certificate-next-new
    (implies (receive-certificate-possiblep msg systate)
             (validator-certificate-quorum-p
              (message->certificate msg)
              (get-validator-state (message->destination msg)
                                   (receive-certificate-next msg systate))
              (all-addresses systate)))
    :enable (validator-certificate-quorum-p
             receive-certificate-possiblep
             validator-state->blockchain-of-receive-certificate-next))

  (defruled accepted-certificates-quorum-p-of-receive-certificate-next
    (implies (and (accepted-certificates-quorum-p systate)
                  (receive-certificate-possiblep msg systate))
             (accepted-certificates-quorum-p
              (receive-certificate-next msg systate)))
    :enable (accepted-certificates-quorum-p
             accepted-certificates-quorum-p-necc
             accepted-certificates-of-receive-certificate-next
             validator-certificates-quorum-p-of-receive-certificate-next-old
             validator-certificates-quorum-p-of-receive-certificate-next-new))

  ;; store-certificate:

  (defruled validator-certificate-quorum-p-of-store-certificate-next
    (implies (and (set::in val1 (correct-addresses systate))
                  (validator-certificate-quorum-p
                   cert1
                   (get-validator-state val1 systate)
                   (all-addresses systate))
                  (store-certificate-possiblep val cert systate))
             (validator-certificate-quorum-p
              cert1
              (get-validator-state
               val1 (store-certificate-next val cert systate))
              (all-addresses systate)))
    :enable (validator-certificate-quorum-p
             validator-state->blockchain-of-store-certificate-next))

  (defruled accepted-certificates-quorum-p-of-store-certificate-next
    (implies (and (accepted-certificates-quorum-p systate)
                  (store-certificate-possiblep val cert systate))
             (accepted-certificates-quorum-p
              (store-certificate-next val cert systate)))
    :enable (accepted-certificates-quorum-p
             accepted-certificates-quorum-p-necc
             accepted-certificates-of-store-certificate-next
             validator-certificate-quorum-p-of-store-certificate-next))

  ;; advance-round:

  (defruled validator-certificate-quorum-p-of-advance-round-next
    (implies (and (set::in val1 (correct-addresses systate))
                  (validator-certificate-quorum-p
                   cert
                   (get-validator-state val1 systate)
                   (all-addresses systate))
                  (advance-round-possiblep val systate))
             (validator-certificate-quorum-p
              cert
              (get-validator-state
               val1 (advance-round-next val systate))
              (all-addresses systate)))
    :enable (validator-certificate-quorum-p
             validator-state->blockchain-of-advance-round-next))

  (defruled accepted-certificates-quorum-p-of-advance-round-next
    (implies (and (accepted-certificates-quorum-p systate)
                  (advance-round-possiblep val systate))
             (accepted-certificates-quorum-p
              (advance-round-next val systate)))
    :enable (accepted-certificates-quorum-p
             accepted-certificates-quorum-p-necc
             accepted-certificates-of-advance-round-next
             validator-certificate-quorum-p-of-advance-round-next))

  ;; commit-anchors:

  (defruled validator-certificate-quorum-p-of-commit-anchors-next
    (implies (and (ordered-even-p systate)
                  (last-blockchain-round-p systate)
                  (set::in val1 (correct-addresses systate))
                  (validator-certificate-quorum-p
                   cert
                   (get-validator-state val1 systate)
                   (all-addresses systate))
                  (commit-anchors-possiblep val systate))
             (validator-certificate-quorum-p
              cert
              (get-validator-state
               val1 (commit-anchors-next val systate))
              (all-addresses systate)))
    :enable (validator-certificate-quorum-p
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

  (defruled accepted-certificates-quorum-p-of-commit-anchors-next
    (implies (and (ordered-even-p systate)
                  (last-blockchain-round-p systate)
                  (accepted-certificates-quorum-p systate)
                  (commit-anchors-possiblep val systate))
             (accepted-certificates-quorum-p
              (commit-anchors-next val systate)))
    :enable (accepted-certificates-quorum-p
             accepted-certificates-quorum-p-necc
             accepted-certificates-of-commit-anchors-next
             validator-certificate-quorum-p-of-commit-anchors-next))

  ;; timer-expires:

  (defruled validator-certificate-quorum-p-of-timer-expires-next
    (implies (and (set::in val1 (correct-addresses systate))
                  (validator-certificate-quorum-p
                   cert
                   (get-validator-state val1 systate)
                   (all-addresses systate))
                  (timer-expires-possiblep val systate))
             (validator-certificate-quorum-p
              cert
              (get-validator-state
               val1 (timer-expires-next val systate))
              (all-addresses systate)))
    :enable (validator-certificate-quorum-p
             validator-state->blockchain-of-timer-expires-next))

  (defruled accepted-certificates-quorum-p-of-timer-expires-next
    (implies (and (accepted-certificates-quorum-p systate)
                  (timer-expires-possiblep val systate))
             (accepted-certificates-quorum-p
              (timer-expires-next val systate)))
    :enable (accepted-certificates-quorum-p
             accepted-certificates-quorum-p-necc
             accepted-certificates-of-timer-expires-next
             validator-certificate-quorum-p-of-timer-expires-next))

  ;; all events:

  (defruled accepted-certificates-quorum-p-of-event-next
    (implies (and (ordered-even-p systate)
                  (last-blockchain-round-p systate)
                  (accepted-certificates-quorum-p systate)
                  (event-possiblep event systate))
             (accepted-certificates-quorum-p (event-next event systate)))
    :enable (event-possiblep
             event-next)))
