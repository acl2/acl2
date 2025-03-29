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

(include-book "dag-certificate-next")
(include-book "last-anchor-present")

(local (include-book "arithmetic-3/top" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ last-anchor-next
  :parents (correctness)
  :short "Last anchor committed by a validator:
          how events change the result."
  :long
  (xdoc::topstring
   (xdoc::p
    "As mentioned in @(see last-anchor-def-and-init),
     the theorems about the changes to the result of this operation
     are separate from its definition and proofs of initial result.
     The reason is that the theorems about changes under events
     need other theorems that depend on the definition."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection last-anchor-of-next
  :short "How the last committed anchor in a validator state
          changes (or not) for each transition."
  :long
  (xdoc::topstring
   (xdoc::p
    "A @('create-certificate') or @('store-certificate') event
     does not change the last committed round or the blockchain,
     but it extends the DAG.
     However, given the already proved invariant that
     the last committed anchor is already present,
     we can use @('cert-with-author+round-of-create-certificate-next')
     to show that the last committed anchor does not change.")
   (xdoc::p
    "A @('commit-anchors') changes, for the target validator,
     the last committed round and the blockchain, but not the DAG.
     The last committed anchor is expressed
     in terms of @(tsee cert-with-author+round)
     applied to the last committed round
     and the leader for that round;
     since the leader is expressed using the initial blockchain,
     we need to show, as in other proofs,
     that the extension of the blockchain does not change
     the active committee at that round.
     For other validators, there is no change to
     the last committed round or the blockchain or the DAG,
     and thus the last committed anchor does not change.")
   (xdoc::p
    "The other three kinds of events do not change
     the last committed round or the blockchain or the DAG,
     and thus the last committed anchor does not change."))

  (defruled last-anchor-of-create-certificate-next
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
                  (last-anchor-present-p systate)
                  (set::in val (correct-addresses systate))
                  (create-certificate-possiblep cert systate))
             (equal (last-anchor (get-validator-state
                                  val (create-certificate-next cert systate))
                                 (all-addresses systate))
                    (last-anchor (get-validator-state val systate)
                                 (all-addresses systate))))
    :enable (last-anchor
             validator-state->last-of-create-certificate-next
             validator-state->blockchain-of-create-certificate-next
             cert-with-author+round-of-create-certificate-next)
    :use last-anchor-present-p-necc)

  (defruled last-anchor-of-receive-certificate-next
    (implies (and (set::in val (correct-addresses systate))
                  (receive-certificate-possiblep msg systate))
             (equal (last-anchor (get-validator-state
                                  val (receive-certificate-next msg systate))
                                 (all-addresses systate))
                    (last-anchor (get-validator-state val systate)
                                 (all-addresses systate))))
    :enable (last-anchor
             validator-state->last-of-receive-certificate-next
             validator-state->blockchain-of-receive-certificate-next
             validator-state->dag-of-receive-certificate-next))

  (defruled last-anchor-of-store-certificate-next
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
                  (last-anchor-present-p systate)
                  (set::in val (correct-addresses systate))
                  (store-certificate-possiblep cert val1 systate))
             (equal (last-anchor (get-validator-state
                                  val
                                  (store-certificate-next cert val1 systate))
                                 (all-addresses systate))
                    (last-anchor (get-validator-state val systate)
                                 (all-addresses systate))))
    :enable (last-anchor
             validator-state->last-of-store-certificate-next
             validator-state->blockchain-of-store-certificate-next
             cert-with-author+round-of-store-certificate-next)
    :use last-anchor-present-p-necc)

  (defruled last-anchor-of-advance-round-next
    (implies (and (set::in val (correct-addresses systate))
                  (advance-round-possiblep val1 systate))
             (equal (last-anchor (get-validator-state
                                  val (advance-round-next val1 systate))
                                 (all-addresses systate))
                    (last-anchor (get-validator-state val systate)
                                 (all-addresses systate))))
    :enable (last-anchor
             validator-state->last-of-advance-round-next
             validator-state->blockchain-of-advance-round-next
             validator-state->dag-of-advance-round-next))

  (defruled last-anchor-of-commit-anchors-next
    (implies (and (ordered-even-p systate)
                  (last-blockchain-round-p systate)
                  (accepted-certificate-committee-p systate)
                  (set::in val (correct-addresses systate))
                  (commit-anchors-possiblep val1 systate))
             (equal (last-anchor (get-validator-state
                                  val (commit-anchors-next val1 systate))
                                 (all-addresses systate))
                    (if (equal (address-fix val1) val)
                        (b* ((round (1- (validator-state->round
                                         (get-validator-state val systate))))
                             (commtt (active-committee-at-round
                                      round
                                      (validator-state->blockchain
                                       (get-validator-state val systate))
                                      (all-addresses systate))))
                          (cert-with-author+round
                           (leader-at-round round commtt)
                           round
                           (validator-state->dag
                            (get-validator-state val systate))))
                      (last-anchor (get-validator-state val systate)
                                   (all-addresses systate)))))
    :use (:instance lemma (val1 (address-fix val1)))
    :prep-lemmas
    ((defruled lemma
       (implies (and (ordered-even-p systate)
                     (last-blockchain-round-p systate)
                     (accepted-certificate-committee-p systate)
                     (set::in val (correct-addresses systate))
                     (commit-anchors-possiblep val1 systate)
                     (addressp val1))
                (equal (last-anchor (get-validator-state
                                     val (commit-anchors-next val1 systate))
                                    (all-addresses systate))
                       (if (equal val1 val)
                           (b* ((round (1- (validator-state->round
                                            (get-validator-state val systate))))
                                (commtt (active-committee-at-round
                                         round
                                         (validator-state->blockchain
                                          (get-validator-state val systate))
                                         (all-addresses systate))))
                             (cert-with-author+round
                              (leader-at-round round commtt)
                              round
                              (validator-state->dag
                               (get-validator-state val systate))))
                         (last-anchor (get-validator-state val systate)
                                      (all-addresses systate)))))
       :enable (active-committee-at-previous-round-when-at-round
                last-anchor
                commit-anchors-possiblep
                commit-anchors-next
                active-committee-at-round-of-extend-blockchain-no-change
                blocks-ordered-even-p-of-extend-blockchain
                certificates-ordered-even-p-of-collect-anchors
                ordered-even-p-necc-fixing
                collect-anchors-above-last-committed-round
                last-blockchain-round-p-necc-fixing
                posp
                pos-fix
                evenp
                nfix
                certificate->round-of-cert-with-author+round))))

  (defruled last-anchor-of-timer-expires-next
    (implies (and (set::in val (correct-addresses systate))
                  (timer-expires-possiblep val1 systate))
             (equal (last-anchor (get-validator-state
                                  val (timer-expires-next val1 systate))
                                 (all-addresses systate))
                    (last-anchor (get-validator-state val systate)
                                 (all-addresses systate))))
    :enable (last-anchor
             validator-state->last-of-timer-expires-next
             validator-state->blockchain-of-timer-expires-next
             validator-state->dag-of-timer-expires-next)))
