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

(include-book "dag-committees")

(local (include-book "arithmetic-3/top" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ signer-quorum
  :parents (correctness)
  :short "Invariant that each certificate in the DAG of a validator
          has signers that form a quorum in the committee."
  :long
  (xdoc::topstring
   (xdoc::p
    "For each such certificate in the DAG of a validator,
     the signers form a quorum in the committee for the certificate round
     (which the validator can calculate, as proved in @(see dag-committees));
     we prove this invariant here.")
   (xdoc::p
    "There are two possible ways in which a validator's DAG is extended.
     One is when the validator authors the certificate,
     and adds it to the DAG (besides broadcasting it to other validators).
     A @('create') event is only possible if
     the signers form a quorum in the committee calculated by the author,
     which therefore maintains the invariant.
     The other way in which a DAG is extended is when
     a validator moves it to the DAG from the buffer;
     in this case, a @('store') event is possible
     only if the validator can calculate
     the committee for the certificate round
     and the signers of the certificate form a quorum in that committee;
     that again maintains the invariant."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define validator-signer-quorum-p ((cert certificatep)
                                   (vstate validator-statep))
  :guard (active-committee-at-round (certificate->round cert)
                                    (validator-state->blockchain vstate))
  :returns (yes/no booleanp)
  :short "Check if the signers of a certificate
          are a subset of the committee for a certificate's round
          and form a quorum in that committee,
          where the committee is calculated by a validator
          (represented by its state)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used by @(tsee signer-quorum-p) to define our invariant.
     The guard ensures that the validator can calculate the committee."))
  (b* (((validator-state vstate) vstate)
       ((certificate cert) cert)
       (commtt (active-committee-at-round cert.round vstate.blockchain)))
    (and (set::subset (certificate->signers cert)
                      (committee-members commtt))
         (>= (committee-members-stake (certificate->signers cert) commtt)
             (committee-quorum-stake commtt))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk signer-quorum-p ((systate system-statep))
  :guard (dag-committees-p systate)
  :returns (yes/no booleanp)
  :short "Definition of the invariant:
          the signers of every certificate
          in the DAG of every correct validator
          form a quorum in the committee for the certificate's round,
          calculated by the validator from its own blockchain."
  (forall (val cert)
          (implies (and (set::in val (correct-addresses systate))
                        (set::in cert (validator-state->dag
                                       (get-validator-state val systate))))
                   (validator-signer-quorum-p
                    cert (get-validator-state val systate))))
  :guard-hints (("Goal" :in-theory (enable dag-committees-p-necc
                                           dag-has-committees-p-necc-bind-dag)))
  ///
  (fty::deffixequiv-sk signer-quorum-p
    :args ((systate system-statep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled signer-quorum-p-when-init
  :short "Establishment of the invariant:
          the invariant holds in any initial system state."
  :long
  (xdoc::topstring
   (xdoc::p
    "Initially there are no DAG certificates in the system,
     so the universal quantification is trivially true."))
  (implies (system-initp systate)
           (signer-quorum-p systate))
  :enable (signer-quorum-p
           system-initp
           system-validators-initp-necc
           validator-init))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection signer-quorum-p-of-next
  :short "Preservation of the invariant:
          if the invariant holds in a system state,
          it also holds in the next system state."
  :long
  (xdoc::topstring
   (xdoc::p
    "The only two kinds of events that may change the DAG
     are @('create') and @('store').")
   (xdoc::p
    "For @('create'),
     there are two cases to consider.
     For an existing (i.e. old) certificate in the DAG,
     we just need to show that the signer quorum property is preserved:
     this is easy, and relies on the fact that
     the blockchain, from which the committee is calculated,
     does not change for @('create').
     For a newly created certificate in @('create'),
     the only change to the DAG is for the author:
     the other validators are sent the certificate in messages,
     but the messages are in the network, not in their DAGs.
     The certificate's author adds the certificate directly to the DAG.
     But @(tsee create-possiblep)
     explicitly checks the signer quorum condition.")
   (xdoc::p
    "For @('store'), we have a similar split,
     considering a certificate already in the DAG (i.e. old),
     and the newly stored certificate, moved from the buffer.
     The case of an old certificate is similar to @('create');
     again, we use the fact that the blockchain
     does not change under a @('receive') event.
     In the case of the newly stored certificate,
     it comes from the buffer,
     but @(tsee store-possiblep)
     explicitly checks the quorum properties,
     thus establishing the property for the new certificate.")
   (xdoc::p
    "DAGs do not change for the other four kinds of events,
     so the proofs for them always rely on the preservaton of the properties.
     For each kind of event,
     we prove a lemma about @(tsee validator-signer-quorum-p)
     and then a theorem about @(tsee signer-quorum-p).
     For @('receive'), @('advance'), and @('timeout')
     there is no change to the blockchain, so the proof is fairly easy.
     For @('commit'), the blockchain changes,
     but we use the fact that extending the blockchain
     does not affect the committees calculated prior to the extension.
     This property depends on the previously proved invariants
     that blockchain rounds are even and ordered,
     that the last committed round in the validator state
     matches the latest block's round
     (or they are both 0 if there are no blocks),
     and that a validator can calculate the active committees
     at all the rounds in which it has certificates;
     so we need to add these invariants as hypothesis,
     which therefore propagate to the theorem about @(tsee event-next)."))

  ;; create:

  (defruled validator-signer-quorum-p-of-create-next-old
    (implies (validator-signer-quorum-p
              cert1
              (get-validator-state val systate))
             (validator-signer-quorum-p
              cert1
              (get-validator-state val (create-next cert systate))))
    :enable validator-signer-quorum-p)

  (defruled validator-signer-quorum-p-of-create-next-new
    (implies (and (create-possiblep cert systate)
                  (set::in (certificate->author cert)
                           (correct-addresses systate)))
             (validator-signer-quorum-p
              cert
              (get-validator-state (certificate->author cert)
                                   (create-next cert systate))))
    :enable (validator-signer-quorum-p
             create-possiblep
             create-author-possiblep
             create-signer-possiblep
             certificate->signers))

  (defruled signer-quorum-p-of-create-next
    (implies (and (signer-quorum-p systate)
                  (create-possiblep cert systate))
             (signer-quorum-p (create-next cert systate)))
    :enable (signer-quorum-p
             signer-quorum-p-necc
             validator-state->dag-of-create-next
             validator-signer-quorum-p-of-create-next-old
             validator-signer-quorum-p-of-create-next-new))

  ;; receive:

  (defruled validator-signer-quorum-p-of-receive-next
    (implies (and (validator-signer-quorum-p
                   cert1
                   (get-validator-state val1 systate))
                  (receive-possiblep msg systate))
             (validator-signer-quorum-p
              cert1
              (get-validator-state val1 (receive-next msg systate))))
    :enable validator-signer-quorum-p)

  (defruled signer-quorum-p-of-receive-next
    (implies (and (signer-quorum-p systate)
                  (receive-possiblep msg systate))
             (signer-quorum-p (receive-next msg systate)))
    :enable (signer-quorum-p
             signer-quorum-p-necc
             validator-signer-quorum-p-of-receive-next))

  ;; store:

  (defruled validator-signer-quorum-p-of-store-next-old
    (implies (and (validator-signer-quorum-p
                   cert1
                   (get-validator-state val1 systate))
                  (store-possiblep val cert systate))
             (validator-signer-quorum-p
              cert1
              (get-validator-state val1 (store-next val cert systate))))
    :enable validator-signer-quorum-p)

  (defruled validator-signer-quorum-p-of-store-next-new
    (implies (store-possiblep val cert systate)
             (validator-signer-quorum-p
              cert
              (get-validator-state val (store-next val cert systate))))
    :enable (validator-signer-quorum-p
             store-possiblep))

  (defruled signer-quorum-p-of-store-next
    (implies (and (signer-quorum-p systate)
                  (store-possiblep val cert systate)
                  (addressp val))
             (signer-quorum-p (store-next val cert systate)))
    :enable (signer-quorum-p
             signer-quorum-p-necc
             validator-state->dag-of-store-next
             validator-signer-quorum-p-of-store-next-old
             validator-signer-quorum-p-of-store-next-new))

  ;; advance:

  (defruled validator-signer-quorum-p-of-advance-next
    (implies (and (validator-signer-quorum-p
                   cert
                   (get-validator-state val1 systate))
                  (advance-possiblep val systate))
             (validator-signer-quorum-p
              cert
              (get-validator-state val1 (advance-next val systate))))
    :enable validator-signer-quorum-p)

  (defruled signer-quorum-p-of-advance-next
    (implies (and (signer-quorum-p systate)
                  (advance-possiblep val systate))
             (signer-quorum-p (advance-next val systate)))
    :enable (signer-quorum-p
             signer-quorum-p-necc
             validator-signer-quorum-p-of-advance-next))

  ;; commit:

  (defruled validator-signer-quorum-p-of-commit-next
    (implies (and (last-blockchain-round-p systate)
                  (ordered-even-p systate)
                  (dag-committees-p systate)
                  (set::in val1 (correct-addresses systate))
                  (set::in cert
                           (validator-state->dag
                            (get-validator-state val1 systate)))
                  (validator-signer-quorum-p
                   cert
                   (get-validator-state val1 systate))
                  (commit-possiblep val systate)
                  (addressp val))
             (validator-signer-quorum-p
              cert
              (get-validator-state val1 (commit-next val systate))))
    :enable (dag-committees-p-necc
             dag-has-committees-p-necc-bind-dag
             validator-signer-quorum-p
             validator-state->blockchain-of-commit-next
             active-committee-at-round-of-extend-blockchain-no-change
             blocks-ordered-even-p-of-extend-blockchain
             certificates-ordered-even-p-of-collect-anchors
             commit-possiblep
             ordered-even-p-necc-fixing
             collect-anchors-above-last-committed-round
             last-blockchain-round-p-necc-fixing
             posp
             pos-fix
             evenp))

  (defruled signer-quorum-p-of-commit-next
    (implies (and (signer-quorum-p systate)
                  (last-blockchain-round-p systate)
                  (ordered-even-p systate)
                  (dag-committees-p systate)
                  (commit-possiblep val systate)
                  (addressp val))
             (signer-quorum-p (commit-next val systate)))
    :enable (signer-quorum-p
             signer-quorum-p-necc
             validator-signer-quorum-p-of-commit-next))

  ;; timeout:

  (defruled validator-signer-quorum-p-of-timeout-next
    (implies (and (validator-signer-quorum-p
                   cert
                   (get-validator-state val1 systate))
                  (timeout-possiblep val systate))
             (validator-signer-quorum-p
              cert
              (get-validator-state val1 (timeout-next val systate))))
    :enable validator-signer-quorum-p)

  (defruled signer-quorum-p-of-timeout-next
    (implies (and (signer-quorum-p systate)
                  (timeout-possiblep val systate))
             (signer-quorum-p (timeout-next val systate)))
    :enable (signer-quorum-p
             signer-quorum-p-necc
             validator-signer-quorum-p-of-timeout-next))

  ;; all events:

  (defruled signer-quorum-p-of-event-next
    (implies (and (signer-quorum-p systate)
                  (last-blockchain-round-p systate)
                  (ordered-even-p systate)
                  (dag-committees-p systate)
                  (event-possiblep event systate))
             (signer-quorum-p (event-next event systate)))
    :enable (event-possiblep
             event-next)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection signer-quorum-p-always
  :short "The invariant holds in every state
          reachable from an initial state via a sequence of events."

  (defruled signer-quorum-p-of-events-next
    (implies (and (signer-quorum-p systate)
                  (last-blockchain-round-p systate)
                  (ordered-even-p systate)
                  (dag-committees-p systate)
                  (events-possiblep events systate))
             (and (signer-quorum-p (events-next events systate))
                  (last-blockchain-round-p (events-next events systate))
                  (ordered-even-p (events-next events systate))
                  (dag-committees-p (events-next events systate))))
    :induct t
    :enable (events-possiblep
             events-next))

  (defruled signer-quorum-p-when-reachable
    (implies (and (system-initp systate)
                  (events-possiblep events systate))
             (signer-quorum-p (events-next events systate)))))
