; AleoBFT Library
;
; Copyright (C) 2024 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOBFT-STAKE2")

(include-book "committed-redundant-def-and-init-and-next")
(include-book "committed-anchor-sequences")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ blockchain-redundant-def-and-init-and-next
  :parents (correctness)
  :short "Invariant that the blockchain is redundant:
          definition, establishment, and preservation."
  :long
  (xdoc::topstring
   (xdoc::p
    "The state of each validator includes (their view of) the blockchain.
     This is initially empty, and gets extended, one or more blocks at a time,
     when anchors are committed.
     However, because of the stability properties of
     paths in the DAG, causal histories, etc.,
     the full blockchain can always be recalculated from scratch,
     from the sequence of committed anchors and from the DAG.
     In other words, the blockchain state component is redundant.")
   (xdoc::p
    "Here we define the invariant,
     we prove that it holds in all initial states,
     and we prove that it is preserved by all transitions.
     Elsewhere we prove that
     the invariant holds in every reachable state."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define validator-blockchain-redundant-p ((vstate validator-statep))
  :guard (and (evenp (validator-state->last vstate))
              (or (equal (validator-state->last vstate) 0)
                  (last-anchor vstate)))
  :returns (yes/no booleanp)
  :short "Check if the blockchain of a validator is equal to
          its calculation from the committed anchors and DAG."
  (equal (validator-state->blockchain vstate)
         (calculate-blockchain (committed-anchors vstate)
                               (validator-state->dag vstate)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk blockchain-redundant-p ((systate system-statep))
  :guard (and (last-blockchain-round-p systate)
              (ordered-even-p systate)
              (last-anchor-present-p systate))
  :returns (yes/no booleanp)
  :short "Definition of the invariant:
          the blockchain of each validator is redundant,
          equal to its calculation from the committed anchors and DAG."
  (forall (val)
          (implies (set::in val (correct-addresses systate))
                   (validator-blockchain-redundant-p
                    (get-validator-state val systate))))
  :guard-hints
  (("Goal" :in-theory (enable last-anchor-present-p-necc
                              evenp-of-blocks-last-round
                              ordered-even-p-necc
                              last-blockchain-round-p-necc)))
  ///
  (fty::deffixequiv-sk blockchain-redundant-p
    :args ((systate system-statep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled blockchain-redundant-p-when-init
  :short "Establishment of the invariant:
          the invariant holds in any initial state."
  :long
  (xdoc::topstring
   (xdoc::p
    "Initially the blockchain is empty
     and there are no committed anchors,
     so the proof is easy."))
  (implies (system-initp systate)
           (blockchain-redundant-p systate))
  :enable (blockchain-redundant-p
           validator-blockchain-redundant-p
           system-initp
           system-validators-initp-necc
           validator-init
           committed-anchors-when-init))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection blockchain-redundant-p-of-next
  :short "Preservation of the invariant:
          if the invariant holds in a system state,
          it also holds in the next system state."
  :long
  (xdoc::topstring
   (xdoc::p
    "A @('create') or @('accept') event
     does not change the blockchain or the committed anchors,
     but it extends the DAG with a certificate.
     However, the blockchain calculation of @(tsee calculate-blockchain)
     is stable under DAG growth, as proved in
     @('calculate-blockchain-of-unequivocal-superdag').
     As in other proofs, we need the fact that
     the extended DAG is unequivocal, and so we instantiate
     @('unequivocal-dags-p-necc-single') with the new state,
     making use of @('unequivocal-dags-p-of-create-next').")
   (xdoc::p
    "A @('commit') event changes
     the blockchain and the committed anchors, but not the DAG.
     But it does so in a way that the invariant is preserved.
     The blockchain is extended via @(tsee extend-blockchain)
     applied to the new anchors obtained via @(tsee collect-anchors).
     The blockchain calculated by @(tsee calculate-blockchain)
     also makes use of @(tsee extend-blockchain),
     and the fact that the new @(tsee committed-anchors)
     expands to an @(tsee append) of the new ones with the old ones,
     makes @('extend-blockchain-of-append') applicable.
     We also need the previously proved invariant that
     the set of committed certificates is redundant,
     which says that the committed certificates before the extension
     are the causal history of the last anchor before the extension.")
   (xdoc::p
    "An @('advance') event does not change
     the blockchain or the committed anchors  or the DAG,
     and thus the proof is easy."))

  ;; create:

  (defruled validator-blockchain-redundant-p-of-create-next
    (implies (and (system-committees-fault-tolerant-p systate)
                  (backward-closed-p systate)
                  (signer-records-p systate)
                  (no-self-endorsed-p systate)
                  (signer-quorum-p systate)
                  (unequivocal-dags-p systate)
                  (same-committees-p systate)
                  (last-anchor-present-p systate)
                  (set::in val (correct-addresses systate))
                  (create-possiblep cert systate)
                  (validator-blockchain-redundant-p
                   (get-validator-state val systate)))
             (validator-blockchain-redundant-p
              (get-validator-state val (create-next cert systate))))
    :enable (validator-blockchain-redundant-p
             validator-state->dag-of-create-next
             unequivocal-dags-p-of-create-next
             list-in-when-certificates-dag-paths-p
             certificates-dag-paths-p-of-committed-anchors
             last-anchor-present-p-necc
             last-anchor-in-dag
             backward-closed-p-necc)
    :use ((:instance calculate-blockchain-of-unequivocal-superdag
                     (dag0 (validator-state->dag
                            (get-validator-state (certificate->author cert)
                                                 systate)))
                     (dag (validator-state->dag
                           (get-validator-state
                            (certificate->author cert)
                            (create-next cert systate))))
                     (anchors (committed-anchors
                               (get-validator-state (certificate->author cert)
                                                    systate))))
          (:instance unequivocal-dags-p-necc-single
                     (val (certificate->author cert))
                     (systate (create-next cert systate)))))

  (defruled blockchain-redundant-p-of-create-next
    (implies (and (blockchain-redundant-p systate)
                  (system-committees-fault-tolerant-p systate)
                  (backward-closed-p systate)
                  (signer-records-p systate)
                  (no-self-endorsed-p systate)
                  (signer-quorum-p systate)
                  (unequivocal-dags-p systate)
                  (same-committees-p systate)
                  (last-anchor-present-p systate)
                  (create-possiblep cert systate))
             (blockchain-redundant-p (create-next cert systate)))
    :enable (blockchain-redundant-p
             blockchain-redundant-p-necc
             validator-blockchain-redundant-p-of-create-next))

  ;; accept:

  (defruled validator-blockchain-redundant-p-of-accept-next
    (implies (and (system-committees-fault-tolerant-p systate)
                  (backward-closed-p systate)
                  (signer-quorum-p systate)
                  (unequivocal-signed-certs-p systate)
                  (unequivocal-dags-p systate)
                  (same-committees-p systate)
                  (last-anchor-present-p systate)
                  (set::in val (correct-addresses systate))
                  (accept-possiblep msg systate)
                  (messagep msg)
                  (validator-blockchain-redundant-p
                   (get-validator-state val systate)))
             (validator-blockchain-redundant-p
              (get-validator-state val (accept-next msg systate))))
    :enable (validator-blockchain-redundant-p
             validator-state->dag-of-accept-next
             unequivocal-dags-p-of-accept-next
             list-in-when-certificates-dag-paths-p
             certificates-dag-paths-p-of-committed-anchors
             last-anchor-present-p-necc
             last-anchor-in-dag
             backward-closed-p-necc)
    :use ((:instance calculate-blockchain-of-unequivocal-superdag
                     (dag0 (validator-state->dag
                            (get-validator-state (message->destination msg)
                                                 systate)))
                     (dag (validator-state->dag
                           (get-validator-state
                            (message->destination msg)
                            (accept-next msg systate))))
                     (anchors (committed-anchors
                               (get-validator-state (message->destination msg)
                                                    systate))))
          (:instance unequivocal-dags-p-necc-single
                     (systate (accept-next msg systate)))))

  (defruled blockchain-redundant-p-of-accept-next
    (implies (and (blockchain-redundant-p systate)
                  (system-committees-fault-tolerant-p systate)
                  (backward-closed-p systate)
                  (signer-quorum-p systate)
                  (unequivocal-signed-certs-p systate)
                  (unequivocal-dags-p systate)
                  (same-committees-p systate)
                  (last-anchor-present-p systate)
                  (accept-possiblep msg systate)
                  (messagep msg))
             (blockchain-redundant-p (accept-next msg systate)))
    :enable (blockchain-redundant-p
             blockchain-redundant-p-necc
             validator-blockchain-redundant-p-of-accept-next))

  ;; advance:

  (defruled validator-blockchain-redundant-p-of-advance-next
    (implies (and (set::in val (correct-addresses systate))
                  (advance-possiblep val1 systate)
                  (validator-blockchain-redundant-p
                   (get-validator-state val systate)))
             (validator-blockchain-redundant-p
              (get-validator-state val (advance-next val1 systate))))
    :enable validator-blockchain-redundant-p)

  (defruled blockchain-redundant-p-of-advance-next
    (implies (and (blockchain-redundant-p systate)
                  (advance-possiblep val systate))
             (blockchain-redundant-p (advance-next val systate)))
    :enable (blockchain-redundant-p
             blockchain-redundant-p-necc
             validator-blockchain-redundant-p-of-advance-next))

  ;; commit:

  (defruled validator-blockchain-redundant-p-of-commit-next-same
    (implies (and (last-blockchain-round-p systate)
                  (ordered-even-p systate)
                  (signer-quorum-p systate)
                  (unequivocal-dags-p systate)
                  (last-anchor-present-p systate)
                  (omni-paths-p systate)
                  (committed-redundant-p systate)
                  (set::in val (correct-addresses systate))
                  (commit-possiblep val systate)
                  (addressp val)
                  (validator-blockchain-redundant-p
                   (get-validator-state val systate)))
             (validator-blockchain-redundant-p
              (get-validator-state val (commit-next val systate))))
    :enable (validator-blockchain-redundant-p
             validator-state->blockchain-of-commit-next
             committed-anchors-of-commit-next
             calculate-blockchain
             extend-blockchain-of-append
             validator-committed-redundant-p
             new-committed-certs-of-extend-blockchain
             unequivocal-dags-p-necc-single
             certificates-dag-paths-p-of-committed-anchors
             last-anchor-present-p-necc
             last-anchor-in-dag
             car-of-committed-anchors)
    :use committed-redundant-p-necc)

  (defruled validator-blockchain-redundant-p-of-commit-next-diff
    (implies (and (last-blockchain-round-p systate)
                  (ordered-even-p systate)
                  (signer-quorum-p systate)
                  (unequivocal-dags-p systate)
                  (last-anchor-present-p systate)
                  (omni-paths-p systate)
                  (set::in val (correct-addresses systate))
                  (commit-possiblep val1 systate)
                  (addressp val1)
                  (validator-blockchain-redundant-p
                   (get-validator-state val systate))
                  (not (equal val (address-fix val1))))
             (validator-blockchain-redundant-p
              (get-validator-state val (commit-next val1 systate))))
    :enable (validator-blockchain-redundant-p
             validator-state->blockchain-of-commit-next
             committed-anchors-of-commit-next))

  (defruled validator-blockchain-redundant-p-of-commit-next
    (implies (and (last-blockchain-round-p systate)
                  (ordered-even-p systate)
                  (signer-quorum-p systate)
                  (unequivocal-dags-p systate)
                  (last-anchor-present-p systate)
                  (omni-paths-p systate)
                  (committed-redundant-p systate)
                  (set::in val (correct-addresses systate))
                  (commit-possiblep val1 systate)
                  (addressp val1)
                  (validator-blockchain-redundant-p
                   (get-validator-state val systate)))
             (validator-blockchain-redundant-p
              (get-validator-state val (commit-next val1 systate))))
    :use (validator-blockchain-redundant-p-of-commit-next-same
          validator-blockchain-redundant-p-of-commit-next-diff))

  (defruled blockchain-redundant-p-of-commit-next
    (implies (and (blockchain-redundant-p systate)
                  (last-blockchain-round-p systate)
                  (ordered-even-p systate)
                  (signer-quorum-p systate)
                  (unequivocal-dags-p systate)
                  (last-anchor-present-p systate)
                  (omni-paths-p systate)
                  (committed-redundant-p systate)
                  (commit-possiblep val systate)
                  (addressp val))
             (blockchain-redundant-p (commit-next val systate)))
    :enable (blockchain-redundant-p
             blockchain-redundant-p-necc
             validator-blockchain-redundant-p-of-commit-next))

  ;; all events:

  (defruled blockchain-redundant-p-of-event-next
    (implies (and (blockchain-redundant-p systate)
                  (system-committees-fault-tolerant-p systate)
                  (backward-closed-p systate)
                  (last-blockchain-round-p systate)
                  (ordered-even-p systate)
                  (signer-records-p systate)
                  (no-self-endorsed-p systate)
                  (signer-quorum-p systate)
                  (unequivocal-signed-certs-p systate)
                  (unequivocal-dags-p systate)
                  (same-committees-p systate)
                  (last-anchor-present-p systate)
                  (omni-paths-p systate)
                  (committed-redundant-p systate)
                  (event-possiblep event systate))
             (blockchain-redundant-p (event-next event systate)))
    :enable (event-possiblep
             event-next)))
