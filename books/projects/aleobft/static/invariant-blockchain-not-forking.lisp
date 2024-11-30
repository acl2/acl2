; AleoBFT Library
;
; Copyright (C) 2024 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOBFT-STATIC")

(include-book "invariant-anchors-not-forking")
(include-book "invariant-blockchain-redundant")

(include-book "std/util/define-sk" :dir :system)

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ invariant-blockchain-not-forking
  :parents (correctness)
  :short "Invariant that blockchains do not fork."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is perhaps the most important correctness property of the protocol.
     It says that blockchains of different validators never fork.
     One may be ahead of another, but they never diverge.
     The formulation is similar to "
    (xdoc::seetopic "invariant-anchors-not-forking"
                    "the invariant that anchors do not fork")
    ", and the proof of non-forking blockchains relies on
     the invariants of non-forking anchors,
     which was proved for the purpose of proving that blockchains do not fork.
     "))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk system-blockchain-nofork-p ((systate system-statep))
  :returns (yes/no booleanp)
  :short "Definition of the invariant:
          given two correct validators in the system,
          their blockchains do not fork."
  :long
  (xdoc::topstring
   (xdoc::p
    "We use @(tsee lists-noforkp), as in @(tsee system-anchors-nofork-p)."))
  (forall (val1 val2)
          (implies (and (set::in val1 (correct-addresses systate))
                        (set::in val2 (correct-addresses systate)))
                   (lists-noforkp
                    (validator-state->blockchain
                     (get-validator-state val1 systate))
                    (validator-state->blockchain
                     (get-validator-state val2 systate)))))
  :guard-hints
  (("Goal" :in-theory (enable in-all-addresses-when-in-correct-addresses))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled lists-noforkp-of-calculate-blockchain
  :short "The blockchains calculated in two validators do not fork."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the code of the proof of non-forking of blockchains.
     Although the property is formulated on
     the blockchain state components of validator states,
     we know that the blockchain state component is redundant,
     and equal to calling @(tsee calculate-blockchain)
     on the committed anchor sequence.
     This way, we can leverage the non-forking of anchors
     to prove the property on @(tsee calculate-blockchain),
     and then later transfer that to the blockchain state components.")
   (xdoc::p
    "So here we prove the property on @(tsee calculate-blockchain).
     We assume the non-forking of anchors (which has been proved previously),
     and expand @(tsee lists-noforkp) so that we get
     different cases based on the lengths.
     But we have proved elsewhere the equality between
     the length of the blockchain and the length of the anchor sequence,
     so the case analysis for blockchains matches the one for anchors.
     Also, the assumption on anchors exposes @(tsee nthcdr),
     but we have also proved elsewhere that
     @(tsee nthcdr) over @(tsee calculate-blockchain)
     reduces to @(tsee calculate-blockchain) over
     the @(tsee nthcdr) of the anchors,
     and so we can leverage the hypotheses on anchors.
     We also need to use the previously proved
     @(tsee calculate-blockchain-of-unequivocal-dags),
     which ensures consistency of blockchains across different DAGs."))
  (implies (and (system-anchors-nofork-p systate)
                (system-unequivocal-dag-p systate)
                (system-unequivocal-dags-p systate)
                (system-previous-in-dag-p systate)
                (system-last-anchor-present-p systate)
                (set::in val1 (correct-addresses systate))
                (set::in val2 (correct-addresses systate)))
           (lists-noforkp
            (calculate-blockchain
             (committed-anchors (get-validator-state val1 systate)
                                (all-addresses systate))
             (validator-state->dag (get-validator-state val1 systate)))
            (calculate-blockchain
             (committed-anchors (get-validator-state val2 systate)
                                (all-addresses systate))
             (validator-state->dag (get-validator-state val2 systate)))))
  :enable (lists-noforkp
           len-of-calculate-blockchain
           nthcdr-of-calculate-blockchain
           system-unequivocal-dag-p-necc
           system-unequivocal-dags-p-necc
           system-previous-in-dag-p-necc
           list-in-when-certificate-list-pathp
           last-anchor-in-dag
           certificate-list-pathp-of-committed-anchors
           fix)
  :use (system-anchors-nofork-p-necc
        (:instance calculate-blockchain-of-unequivocal-dags
                   (dag1 (validator-state->dag
                          (get-validator-state val1 systate)))
                   (dag2 (validator-state->dag
                          (get-validator-state val2 systate)))
                   (anchors (committed-anchors
                             (get-validator-state val1 systate)
                             (all-addresses systate))))
        (:instance calculate-blockchain-of-unequivocal-dags
                   (dag1 (validator-state->dag
                          (get-validator-state val1 systate)))
                   (dag2 (validator-state->dag
                          (get-validator-state val2 systate)))
                   (anchors (committed-anchors
                             (get-validator-state val2 systate)
                             (all-addresses systate))))
        (:instance system-last-anchor-present-p-necc (val val1))
        (:instance system-last-anchor-present-p-necc (val val2))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled lists-noforkp-of-validator-state->blockchain
  :short "The blockchain state components do not fork."
  :long
  (xdoc::topstring
   (xdoc::p
    "We transfer @(tsee lists-noforkp-of-calculate-blockchain)
     to the blockchain state components of validators,
     which are known to be equal to @(tsee calculate-blockchain)."))
  (implies (and (system-anchors-nofork-p systate)
                (system-unequivocal-dag-p systate)
                (system-unequivocal-dags-p systate)
                (system-previous-in-dag-p systate)
                (system-last-anchor-present-p systate)
                (system-blockchain-redundantp systate)
                (set::in val1 (correct-addresses systate))
                (set::in val2 (correct-addresses systate)))
           (lists-noforkp
            (validator-state->blockchain
             (get-validator-state val1 systate))
            (validator-state->blockchain
             (get-validator-state val2 systate))))
  :enable validator-blockchain-redundantp
  :use (lists-noforkp-of-calculate-blockchain
        (:instance system-blockchain-redundantp-necc (val val1))
        (:instance system-blockchain-redundantp-necc (val val2))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule system-blockchain-nofork-p-when-anchors-nofork-p
  :short "Proof of the invariant from other invariants."
  :long
  (xdoc::topstring
   (xdoc::p
    "The theorem @(tsee lists-noforkp-of-validator-state->blockchain)
     is enough to prove the desired system invariant.
     Note that this is proved from previously proved invariants,
     mainly the non-forking of anchors,
     which is singled out in the name of this theorem."))
  (implies (and (system-anchors-nofork-p systate)
                (system-unequivocal-dag-p systate)
                (system-unequivocal-dags-p systate)
                (system-previous-in-dag-p systate)
                (system-last-anchor-present-p systate)
                (system-blockchain-redundantp systate))
           (system-blockchain-nofork-p systate))
  :enable (system-blockchain-nofork-p
           lists-noforkp-of-validator-state->blockchain))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled system-blockchain-nofork-p-when-reachable
  :short "The invariant holds in every reachable state."
  :long
  (xdoc::topstring
   (xdoc::p
    "Reachable states are characterized by an initial state and
     a sequence of possible events from that initial state."))
  (implies (and (system-statep systate)
                (system-state-initp systate)
                (events-possiblep events systate)
                (fault-tolerant-p systate))
           (system-blockchain-nofork-p (events-next events systate)))
  :disable ((:e tau-system))
  :enable (system-blockchain-nofork-p-when-anchors-nofork-p
           system-anchors-nofork-p-when-reachable
           system-unequivocal-dag-p-when-reachable
           system-unequivocal-dags-p-when-reachable
           system-previous-in-dag-p-when-reachable
           system-last-anchor-present-p-when-reachable
           system-blockchain-redundantp-when-reachable))
