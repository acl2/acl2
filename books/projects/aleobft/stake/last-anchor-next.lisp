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
     are separate from its definition and its proof of initial result.
     The reason is that the theorems about changes under events
     need other theorems that depend on the definition,
     which in turn depend on the definition of @(tsee last-anchor):
     the theorems in question are in @(tsee last-anchor-present)."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection last-anchor-of-next
  :short "How the last committed anchor in a validator state
          changes (or not) for each transition."
  :long
  (xdoc::topstring
   (xdoc::p
    "A @('create') or @('store') event
     does not change the last committed round or the blockchain,
     but it extends the DAG.
     However, given the already proved invariant that
     the last committed anchor is already present,
     we can use the theorems in @(see cert-with-author+round-of-next)
     to show that the last committed anchor does not change.")
   (xdoc::p
    "A @('commit') changes, for the target validator,
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

  (defrule last-anchor-of-create-next
    (implies (and (system-committees-fault-tolerant-p systate)
                  (same-associated-certs-p systate)
                  (no-self-endorsed-p systate)
                  (signer-records-p systate)
                  (dag-committees-p systate)
                  (signer-quorum-p systate)
                  (unequivocal-dags-p systate)
                  (same-committees-p systate)
                  (last-anchor-present-p systate)
                  (set::in val (correct-addresses systate))
                  (create-possiblep cert systate))
             (equal (last-anchor (get-validator-state
                                  val (create-next cert systate)))
                    (last-anchor (get-validator-state val systate))))
    :enable (last-anchor
             cert-with-author+round-of-create-next)
    :use last-anchor-present-p-necc)

  (defrule last-anchor-of-receive-next
    (implies (and (set::in val (correct-addresses systate))
                  (receive-possiblep msg systate))
             (equal (last-anchor (get-validator-state
                                  val (receive-next msg systate)))
                    (last-anchor (get-validator-state val systate))))
    :enable last-anchor)

  (defrule last-anchor-of-store-next
    (implies (and (system-committees-fault-tolerant-p systate)
                  (same-associated-certs-p systate)
                  (dag-committees-p systate)
                  (signer-quorum-p systate)
                  (unequivocal-signed-certs-p systate)
                  (unequivocal-dags-p systate)
                  (same-committees-p systate)
                  (last-anchor-present-p systate)
                  (set::in val (correct-addresses systate))
                  (store-possiblep val1 cert systate)
                  (addressp val1)
                  (certificatep cert))
             (equal (last-anchor (get-validator-state
                                  val (store-next val1 cert systate)))
                    (last-anchor (get-validator-state val systate))))
    :enable (last-anchor
             cert-with-author+round-of-store-next)
    :use last-anchor-present-p-necc)

  (defrule last-anchor-of-advance-next
    (implies (and (set::in val (correct-addresses systate))
                  (advance-possiblep val1 systate))
             (equal (last-anchor (get-validator-state
                                  val (advance-next val1 systate)))
                    (last-anchor (get-validator-state val systate))))
    :enable last-anchor)

  (defruled last-anchor-of-commit-next
    (implies (and (last-blockchain-round-p systate)
                  (ordered-even-p systate)
                  (dag-committees-p systate)
                  (set::in val (correct-addresses systate))
                  (commit-possiblep val1 systate)
                  (addressp val1))
             (equal (last-anchor (get-validator-state
                                  val (commit-next val1 systate)))
                    (if (equal val1 val)
                        (b* ((round (1- (validator-state->round
                                         (get-validator-state val systate))))
                             (commtt (active-committee-at-round
                                      round
                                      (validator-state->blockchain
                                       (get-validator-state val systate)))))
                          (cert-with-author+round
                           (leader-at-round round commtt)
                           round
                           (validator-state->dag
                            (get-validator-state val systate))))
                      (last-anchor (get-validator-state val systate)))))
    :enable (active-committee-at-previous-round-when-at-round
             last-anchor
             commit-possiblep
             commit-next
             active-committee-at-round-of-extend-blockchain-no-change
             blocks-ordered-even-p-of-extend-blockchain
             certificates-ordered-even-p-of-collect-anchors
             ordered-even-p-necc-fixing
             collect-anchors-above-last-committed-round
             last-blockchain-round-p-necc-fixing
             posp
             evenp
             nfix))

  (defrule last-anchor-of-timeout-next
    (implies (and (set::in val (correct-addresses systate))
                  (timeout-possiblep val1 systate))
             (equal (last-anchor (get-validator-state
                                  val (timeout-next val1 systate)))
                    (last-anchor (get-validator-state val systate))))
    :enable last-anchor))
