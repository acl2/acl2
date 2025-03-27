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

(include-book "backward-closure")
(include-book "dag-committees")
(include-book "signed-previous-quorum")
(include-book "same-committees-def-and-implied")
(include-book "fault-tolerance")
(include-book "signed-and-associated-cerificates")

(local (include-book "arithmetic-3/top" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ previous-quorum-def-and-init-and-next
  :parents (correctness)
  :short "Invariant that each certificate in a DAG
          has references to previous certificates
          that form a non-zero quorum in the committee for the previous round,
          unless the round is 1,
          in which case there are no references to previous certificates:
          definition, establishment, and preservation."
  :long
  (xdoc::topstring
   (xdoc::p
    "When a new certificate is created via a @('create') event,
     that event's preconditions require that the certificate includes
     a non-zero quorum of references to certificates in the previous round,
     unless the certificate round is 1,
     in which case there must be no references.")
   (xdoc::p
    "When a certificate is stored into the DAG via a @('store') event,
     the validator checks that the certificate is signed by a quorum.
     Under fault tolerance assumptions,
     that quorum must contain at least one correct validator,
     which must have signed the certificate only if
     the references to previous certificates
     form a non-zero quorum
     (in the previous committee of the certiicate's round).
     Under the invariant that validators agree on committees
     (see @(see same-committees-def-and-implied)),
     the correct signer and the storing validator
     agree on the committee, and thus on the stake requirement.")
   (xdoc::p
    "Thus, all the certificates in a validator's DAG satisfy the invariant.
     The other events do not modify DAGs.")
   (xdoc::p
    "The names for this invariant,
     i.e. this XDOC topic as well as the function and theorem names,
     just mention `quorum' for brevity,
     even though that does not apply to round 1.
     But rounds greater than 1 are the ``normal'' case,
     while round 1 is a special case.
     The names do not mention the `non-zero' requirement either,
     but the quorum aspect is the main one here.")
   (xdoc::p
    "Here we define the invariant,
     we prove that it holds in all initial states,
     and we prove that it is preserved by all transitions.
     Elsewhere we prove that
     the invariant holds in every reachable state."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define validator-previous-quorum-p ((cert certificatep)
                                     (vstate validator-statep))
  :guard (or (equal (certificate->round cert) 1)
             (active-committee-at-round (1- (certificate->round cert))
                                        (validator-state->blockchain vstate)))
  :returns (yes/no booleanp)
  :short "Check if either a certificate has round 1
          and it has no references to previous certificates,
          or the round is not 1 and
          the certificate's references to previous certificates
          are in the committee for the round just before the certificate round
          and form a non-zero quorum in that committee,
          where the committee is calculated by a validator
          (represented by its state)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used by @(tsee previous-quorum-p) to define our invariant.
     The validator whose state is @('vstate') is
     the one that has the certificate in the DAG.
     The guard ensures that the validator can calculate the committee.")
   (xdoc::p
    "To check the non-zeroness of the quorum,
     we equivalently check the non-emptiness of the previous references.")
   (xdoc::p
    "We prove a theorem about the predecessors of @('cert'),
     which we use to prove @(tsee dag-predecessor-quorum-p)
     from @(tsee previous-quorum-p) later.
     The theorem says that, under the invariant, for certificates after round 1,
     the stake of the authors of the predecessor certificates
     is at least the quorum stake for the committee at the previous round.
     This is the case under the backward closure hypothesis
     (which is an already proved invariant):
     the authors of the predecessors are
     exactly the previous certificate references (addresses) in the certificate.
     Without the backward closure hypothesis,
     the authors of the predecessors are the intersection of
     the previous reference authors
     and the authors of the certificates actually present in the previous round;
     the closure tells us the the former is a subset of the latter,
     which simplifies the intersection."))
  (b* (((validator-state vstate) vstate)
       ((certificate cert) cert))
    (if (= cert.round 1)
        (set::emptyp cert.previous)
      (b* ((commtt
            (active-committee-at-round (1- cert.round) vstate.blockchain)))
        (and (not (set::emptyp cert.previous))
             (set::subset cert.previous
                          (committee-members commtt))
             (>= (committee-members-stake cert.previous commtt)
                 (committee-quorum-stake commtt))))))
  :guard-hints (("Goal" :in-theory (enable posp)))
  :hooks (:fix)

  ///

  (defruled predecessor-quorum-when-validator-previous-quorum-p
    (implies (and (validator-previous-quorum-p cert vstate)
                  (certificate-previous-in-dag-p
                   cert (validator-state->dag vstate))
                  (not (equal (certificate->round cert) 1)))
             (b* ((commtt (active-committee-at-round
                           (1- (certificate->round cert))
                           (validator-state->blockchain vstate)))
                  (stake (committee-members-stake
                          (cert-set->author-set
                           (predecessors cert (validator-state->dag vstate)))
                          commtt)))
               (and (> stake 0)
                    (>= stake
                        (committee-quorum-stake commtt)))))
    :enable (predecessors
             certs-with-authors+round-to-authors-of-round
             cert-set->author-set-of-certs-with-authors
             certificate-previous-in-dag-p
             committee-members-stake-0-to-emptyp-members
             set::expensive-rules)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk previous-quorum-p ((systate system-statep))
  :guard (dag-committees-p systate)
  :returns (yes/no booleanp)
  :short "Definition of the invariant:
          for each certificate in the DAG of each validator,
          either the certificate's round is 1
          and the certificate has no references to previous certificates,
          or the certificate's round is not 1
          and the references to previous certificates
          form a non-zero quorum in the committee of
          the preceding round of the certificate."
  :long
  (xdoc::topstring
   (xdoc::p
    "This invariant, along with backward closure and non-equivocation,
     guarantees that @(tsee dag-predecessor-quorum-p) holds, as we prove here.
     The key lemma is
     @('predecessor-quorum-when-validator-previous-quorum-p')
     proved in @(tsee validator-previous-quorum-p).
     Here we just need to enable some rules
     to establish the hypotheses of that lemma."))
  (forall (val cert)
          (implies (and (set::in val (correct-addresses systate))
                        (set::in cert (validator-state->dag
                                       (get-validator-state val systate))))
                   (validator-previous-quorum-p
                    cert
                    (get-validator-state val systate))))
  :guard-hints
  (("Goal"
    :in-theory (enable dag-committees-p-necc
                       dag-has-committees-p-necc-bind-dag
                       active-committee-at-previous-round-when-at-round )))

  ///

  (fty::deffixequiv-sk previous-quorum-p
    :args ((systate system-statep)))

  (defruled dag-predecessor-quorum-p-when-previous-quorum-p
    (implies (and (previous-quorum-p systate)
                  (backward-closed-p systate)
                  (set::in val (correct-addresses systate)))
             (dag-predecessor-quorum-p
              (validator-state->dag (get-validator-state val systate))
              (validator-state->blockchain (get-validator-state val systate))))
    :enable (predecessor-quorum-when-validator-previous-quorum-p
             dag-predecessor-quorum-p
             backward-closed-p-necc
             dag-closedp-necc)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled previous-quorum-p-when-init
  :short "Establishment of the invariant:
          the invariant holds in any initial system state."
  :long
  (xdoc::topstring
   (xdoc::p
    "Initially all the DAGs are empty,
     so the universal quantification is trivially true."))
  (implies (system-initp systate)
           (previous-quorum-p systate))
  :enable (previous-quorum-p
           system-initp
           system-validators-initp-necc
           validator-init))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection previous-quorum-p-of-next
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
     we just need to show that the previous quorum property is preserved:
     this is easy, and relies on the fact that
     the blockchain, from which the committee is calculated,
     does not change for @('create').
     For a newly created certificate in @('create'),
     the only change to the DAG is for the author:
     the other validators are sent the certificate in messages,
     but the messages are in the network, not in their DAGs.
     The certificate's author adds the certificate directly to the DAG.
     But @(tsee create-possiblep)
     explicitly checks the previous quorum condition.")
   (xdoc::p
    "For @('store'), we have a similar split,
     considering a certificate already in the DAG (i.e. old),
     and the newly stored certificate, moved from the buffer.
     The case of an old certificate is similar to @('create');
     again, we use the fact that the blockchain
     does not change under a @('receive') event.
     The case of the newly stored certificate is more complicated.
     The conditions in @(tsee store-possiblep) include the fact that
     the certificate is signed by a quorum,
     which, assuming fault tolerance (which we do),
     must contain at least one correct validator:
     see @('pick-correct-validator-when-fault-tolerant-and-geq-quorum')
     in @(tsee pick-correct-validator).
     We appeal to the previously proved
     invariant @(tsee signed-previous-quorum-p)
     to obtain that the previous quorum condition is satisfied
     with respect to the signing validator
     (which may differ from the target validator of @('store')).
     Then we use the invariant @(tsee same-committees-p)
     to show that, if signer and storer differ,
     they agree on that committee,
     and thus on the previous quorum requirement.
     Fault tolerance and the other invariants used in the proof
     propagate to the theorem about @(tsee event-next).")
   (xdoc::p
    "DAGs do not change for the other four kinds of events,
     so the proofs for them always rely on the preservaton of the properties.
     For each kind of event,
     we prove a lemma about @(tsee validator-previous-quorum-p)
     and then a theorem about @(tsee previous-quorum-p).
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

  (defruled validator-previous-quorum-p-of-create-next-old
    (implies (validator-previous-quorum-p
              cert1
              (get-validator-state val systate))
             (validator-previous-quorum-p
              cert1
              (get-validator-state val (create-next cert systate))))
    :enable (validator-previous-quorum-p
             validator-state->blockchain-of-create-next
             certificate->author-of-path-to-author+round))

  (defruled validator-previous-quorum-p-of-create-next-new
    (implies (and (create-possiblep cert systate)
                  (set::in (certificate->author cert)
                           (correct-addresses systate)))
             (validator-previous-quorum-p
              cert
              (get-validator-state (certificate->author cert)
                                   (create-next cert systate))))
    :enable (validator-previous-quorum-p
             create-possiblep
             create-author-possiblep
             create-signer-possiblep
             certificate->signers))

  (defruled previous-quorum-p-of-create-next
    (implies (and (previous-quorum-p systate)
                  (create-possiblep cert systate))
             (previous-quorum-p (create-next cert systate)))
    :enable (previous-quorum-p
             previous-quorum-p-necc
             validator-state->dag-of-create-next
             validator-previous-quorum-p-of-create-next-old
             validator-previous-quorum-p-of-create-next-new))

  ;; receive:

  (defruled validator-previous-quorum-p-of-receive-next
    (implies (and (validator-previous-quorum-p
                   cert
                   (get-validator-state val systate))
                  (receive-possiblep msg systate))
             (validator-previous-quorum-p
              cert
              (get-validator-state val (receive-next msg systate))))
    :enable validator-previous-quorum-p)

  (defruled previous-quorum-p-of-receive-next
    (implies (and (previous-quorum-p systate)
                  (receive-possiblep msg systate))
             (previous-quorum-p (receive-next msg systate)))
    :enable (previous-quorum-p
             previous-quorum-p-necc
             validator-previous-quorum-p-of-receive-next))

  ;; store:

  (defruled validator-previous-quorum-p-of-store-next-old
    (implies (and (validator-previous-quorum-p
                   cert1
                   (get-validator-state val1 systate))
                  (store-possiblep val cert systate))
             (validator-previous-quorum-p
              cert1
              (get-validator-state val1 (store-next val cert systate))))
    :enable (validator-previous-quorum-p))

  (defruled validator-previous-quorum-p-of-store-next-new
    (implies (and (system-committees-fault-tolerant-p systate)
                  (same-associated-certs-p systate)
                  (signed-previous-quorum-p systate)
                  (same-committees-p systate)
                  (store-possiblep val cert systate)
                  (certificatep cert)
                  (addressp val))
             (validator-previous-quorum-p
              cert
              (get-validator-state val (store-next val cert systate))))
    :enable (validator-previous-quorum-p
             store-possiblep
             pick-correct-validator-is-correct
             pick-correct-validator-in-set
             in-signed-certs-when-in-associated-and-signer
             associated-certs
             validator-signed-previous-quorum-p
             same-committees-p-necc
             active-committee-at-previous-round-when-at-round
             posp
             system-committees-fault-tolerant-p-necc
             validator-committees-fault-tolerant-p-necc
             committee-nonemptyp-when-nonempty-subset)
    :use ((:instance pick-correct-validator-when-fault-tolerant-and-geq-quorum
                     (vals (certificate->signers cert))
                     (commtt (active-committee-at-round
                              (certificate->round cert)
                              (validator-state->blockchain
                               (get-validator-state val systate)))))
          (:instance signed-previous-quorum-p-necc
                     (val (pick-correct-validator
                           (certificate->signers cert) systate)))
          (:instance same-active-committees-p-necc
                     (round (1- (certificate->round cert)))
                     (blocks1 (validator-state->blockchain
                               (get-validator-state val systate)))
                     (blocks2 (validator-state->blockchain
                               (get-validator-state
                                (pick-correct-validator
                                 (certificate->signers cert) systate)
                                systate))))))

  (defruled previous-quorum-p-of-store-next
    (implies (and (previous-quorum-p systate)
                  (system-committees-fault-tolerant-p systate)
                  (same-associated-certs-p systate)
                  (signed-previous-quorum-p systate)
                  (same-committees-p systate)
                  (store-possiblep val cert systate)
                  (certificatep cert)
                  (addressp val))
             (previous-quorum-p (store-next val cert systate)))
    :enable (previous-quorum-p
             previous-quorum-p-necc
             validator-state->dag-of-store-next
             validator-previous-quorum-p-of-store-next-old
             validator-previous-quorum-p-of-store-next-new))

  ;; advance:

  (defruled validator-previous-quorum-p-of-advance-next
    (implies (and (validator-previous-quorum-p
                   cert
                   (get-validator-state val1 systate))
                  (advance-possiblep val systate))
             (validator-previous-quorum-p
              cert
              (get-validator-state val1 (advance-next val systate))))
    :enable validator-previous-quorum-p)

  (defruled previous-quorum-p-of-advance-next
    (implies (and (previous-quorum-p systate)
                  (advance-possiblep val systate))
             (previous-quorum-p (advance-next val systate)))
    :enable (previous-quorum-p
             previous-quorum-p-necc
             validator-previous-quorum-p-of-advance-next))

  ;; commit:

  (defruled validator-previous-quorum-p-of-commit-next
    (implies (and (last-blockchain-round-p systate)
                  (ordered-even-p systate)
                  (dag-committees-p systate)
                  (set::in val1 (correct-addresses systate))
                  (set::in cert
                           (validator-state->dag
                            (get-validator-state val1 systate)))
                  (validator-previous-quorum-p
                   cert
                   (get-validator-state val1 systate))
                  (commit-possiblep val systate)
                  (addressp val))
             (validator-previous-quorum-p
              cert
              (get-validator-state val1 (commit-next val systate))))
    :enable (dag-committees-p-necc
             dag-has-committees-p-necc-bind-dag
             validator-previous-quorum-p
             validator-state->blockchain-of-commit-next
             active-committee-at-round-of-extend-blockchain-no-change
             active-committee-at-previous-round-when-at-round
             blocks-ordered-even-p-of-extend-blockchain
             certificates-ordered-even-p-of-collect-anchors
             commit-possiblep
             ordered-even-p-necc-fixing
             collect-anchors-above-last-committed-round
             last-blockchain-round-p-necc-fixing
             posp
             pos-fix
             evenp))

  (defruled previous-quorum-p-of-commit-next
    (implies (and (previous-quorum-p systate)
                  (last-blockchain-round-p systate)
                  (ordered-even-p systate)
                  (dag-committees-p systate)
                  (commit-possiblep val systate)
                  (addressp val))
             (previous-quorum-p (commit-next val systate)))
    :enable (previous-quorum-p
             previous-quorum-p-necc
             validator-previous-quorum-p-of-commit-next))

  ;; timeout:

  (defruled validator-previous-quorum-p-of-timeout-next
    (implies (and (validator-previous-quorum-p
                   cert
                   (get-validator-state val1 systate))
                  (timeout-possiblep val systate))
             (validator-previous-quorum-p
              cert
              (get-validator-state val1 (timeout-next val systate))))
    :enable validator-previous-quorum-p)

  (defruled previous-quorum-p-of-timeout-next
    (implies (and (previous-quorum-p systate)
                  (timeout-possiblep val systate))
             (previous-quorum-p (timeout-next val systate)))
    :enable (previous-quorum-p
             previous-quorum-p-necc
             validator-previous-quorum-p-of-timeout-next))

  ;; all events:

  (defruled previous-quorum-p-of-event-next
    (implies (and (previous-quorum-p systate)
                  (system-committees-fault-tolerant-p systate)
                  (last-blockchain-round-p systate)
                  (ordered-even-p systate)
                  (same-associated-certs-p systate)
                  (signed-previous-quorum-p systate)
                  (dag-committees-p systate)
                  (same-committees-p systate)
                  (event-possiblep event systate))
             (previous-quorum-p (event-next event systate)))
    :enable (event-possiblep
             event-next)))
