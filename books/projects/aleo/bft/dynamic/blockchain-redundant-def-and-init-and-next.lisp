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
     In @(see blockchain-redundant) we prove that
     the invariant holds in every reachable state."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define validator-blockchain-redundant-p ((vstate validator-statep)
                                          (all-vals address-setp))
  :guard (and (evenp (validator-state->last vstate))
              (or (equal (validator-state->last vstate) 0)
                  (last-anchor vstate all-vals)))
  :returns (yes/no booleanp)
  :short "Check if the blockchain of a validator is equal to
          its calculation from the committed anchors and DAG."
  (equal (validator-state->blockchain vstate)
         (calculate-blockchain (committed-anchors vstate all-vals)
                               (validator-state->dag vstate))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk blockchain-redundant-p ((systate system-statep))
  :guard (and (last-anchor-present-p systate)
              (ordered-even-p systate)
              (last-blockchain-round-p systate))
  :returns (yes/no booleanp)
  :short "Definition of the invariant:
          the blockchain of a validator is redundant,
          equal to its calculation from the committed anchors and DAG."
  (forall (val)
          (implies (set::in val (correct-addresses systate))
                   (validator-blockchain-redundant-p
                    (get-validator-state val systate)
                    (all-addresses systate))))
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
           committed-anchors))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection blockchain-redundant-p-of-next
  :short "Preservation of the invariant:
          if the invariant holds in a system state,
          it also holds in the next system state."
  :long
  (xdoc::topstring
   (xdoc::p
    "A @('create-certificate') or @('store-certificate') event
     does not change the blockchain or the committed anchors,
     but it extends the DAG with a certificate.
     However, the blockchain calculation of @(tsee calculate-blockchain)
     is stable under DAG growth, as proved in
     @('calculate-blockchain-of-unequivocal-superdag').
     As in other proofs, we need the fact that
     the extended DAG is unequivocal, and so we instantiate
     @('certificate-set-unequivocalp-when-unequivocal-accepted')
     with the new state, making use of
     @('unequivocal-accepted-certificates-p-of-create-certificate-next');
     we disable tau so we explicate its use, given that,
     as in other proofs, otherwise tau apparently use it implicitly.")
   (xdoc::p
    "A @('commit-anchors') event changes
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
    "The other three kinds of events do not change
     the blockchain or the committed anchors  or the DAG,
     and thus the proof is easy."))

  ;; create-certificate:

  (defruled validator-blockchain-redundant-p-of-create-certificate-next
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
                  (backward-closed-p systate)
                  (set::in val (correct-addresses systate))
                  (create-certificate-possiblep cert systate)
                  (validator-blockchain-redundant-p
                   (get-validator-state val systate)
                   (all-addresses systate)))
             (validator-blockchain-redundant-p
              (get-validator-state val (create-certificate-next cert systate))
              (all-addresses systate)))
    :disable ((:e tau-system))
    :enable (validator-blockchain-redundant-p
             validator-state->last-of-create-certificate-next
             validator-state->dag-of-create-certificate-next
             validator-state->blockchain-of-create-certificate-next
             committed-anchors-of-create-certificate-next
             unequivocal-accepted-certificates-p-of-create-certificate-next
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
                            (create-certificate-next cert systate))))
                     (anchors (committed-anchors
                               (get-validator-state (certificate->author cert)
                                                    systate)
                               (all-addresses systate))))
          (:instance certificate-set-unequivocalp-when-unequivocal-accepted
                     (val (certificate->author cert))
                     (systate (create-certificate-next cert systate)))))

  (defruled blockchain-redundant-p-of-create-certificate-next
    (implies (and (blockchain-redundant-p systate)
                  (unequivocal-accepted-certificates-p systate)
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
                  (backward-closed-p systate)
                  (create-certificate-possiblep cert systate))
             (blockchain-redundant-p
              (create-certificate-next cert systate)))
    :enable (blockchain-redundant-p
             blockchain-redundant-p-necc
             validator-blockchain-redundant-p-of-create-certificate-next))

  ;; receive-certificate:

  (defruled validator-blockchain-redundant-p-of-receive-certificate-next
    (implies (and (set::in val (correct-addresses systate))
                  (receive-certificate-possiblep msg systate)
                  (validator-blockchain-redundant-p
                   (get-validator-state val systate)
                   (all-addresses systate)))
             (validator-blockchain-redundant-p
              (get-validator-state val (receive-certificate-next msg systate))
              (all-addresses systate)))
    :enable (validator-blockchain-redundant-p
             validator-state->last-of-receive-certificate-next
             validator-state->blockchain-of-receive-certificate-next
             validator-state->dag-of-receive-certificate-next
             committed-anchors-of-receive-certificate-next))

  (defruled blockchain-redundant-p-of-receive-certificate-next
    (implies (and (blockchain-redundant-p systate)
                  (receive-certificate-possiblep msg systate))
             (blockchain-redundant-p (receive-certificate-next msg systate)))
    :enable (blockchain-redundant-p
             blockchain-redundant-p-necc
             validator-blockchain-redundant-p-of-receive-certificate-next))

  ;; store-certificate:

  (defruled validator-blockchain-redundant-p-of-store-certificate-next
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
                  (backward-closed-p systate)
                  (set::in val (correct-addresses systate))
                  (store-certificate-possiblep val1 cert systate)
                  (validator-blockchain-redundant-p
                   (get-validator-state val systate)
                   (all-addresses systate)))
             (validator-blockchain-redundant-p
              (get-validator-state
               val (store-certificate-next val1 cert systate))
              (all-addresses systate)))
    :use (:instance lemma (val1 (address-fix val1)))
    :prep-lemmas
    ((defruled lemma
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
                     (backward-closed-p systate)
                     (set::in val (correct-addresses systate))
                     (store-certificate-possiblep val1 cert systate)
                     (validator-blockchain-redundant-p
                      (get-validator-state val systate)
                      (all-addresses systate))
                     (addressp val1))
                (validator-blockchain-redundant-p
                 (get-validator-state
                  val (store-certificate-next val1 cert systate))
                 (all-addresses systate)))
       :disable ((:e tau-system))
       :enable (validator-blockchain-redundant-p
                validator-state->last-of-store-certificate-next
                validator-state->dag-of-store-certificate-next
                validator-state->blockchain-of-store-certificate-next
                committed-anchors-of-store-certificate-next
                unequivocal-accepted-certificates-p-of-store-certificate-next
                list-in-when-certificates-dag-paths-p
                certificates-dag-paths-p-of-committed-anchors
                last-anchor-present-p-necc
                last-anchor-in-dag
                backward-closed-p-necc)
       :use ((:instance calculate-blockchain-of-unequivocal-superdag
                        (dag0 (validator-state->dag
                               (get-validator-state val1 systate)))
                        (dag (validator-state->dag
                              (get-validator-state
                               val1 (store-certificate-next val1 cert systate))))
                        (anchors (committed-anchors
                                  (get-validator-state val1 systate)
                                  (all-addresses systate))))
             (:instance certificate-set-unequivocalp-when-unequivocal-accepted
                        (val val1)
                        (systate (store-certificate-next val1 cert systate)))))))

  (defruled blockchain-redundant-p-of-store-certificate-next
    (implies (and (blockchain-redundant-p systate)
                  (unequivocal-accepted-certificates-p systate)
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
                  (backward-closed-p systate)
                  (store-certificate-possiblep val1 cert systate))
             (blockchain-redundant-p
              (store-certificate-next val1 cert systate)))
    :enable (blockchain-redundant-p
             blockchain-redundant-p-necc
             validator-blockchain-redundant-p-of-store-certificate-next))

  ;; advance-round:

  (defruled validator-blockchain-redundant-p-of-advance-round-next
    (implies (and (set::in val (correct-addresses systate))
                  (advance-round-possiblep val1 systate)
                  (validator-blockchain-redundant-p
                   (get-validator-state val systate)
                   (all-addresses systate)))
             (validator-blockchain-redundant-p
              (get-validator-state val (advance-round-next val1 systate))
              (all-addresses systate)))
    :enable (validator-blockchain-redundant-p
             validator-state->last-of-advance-round-next
             validator-state->blockchain-of-advance-round-next
             validator-state->dag-of-advance-round-next
             committed-anchors-of-advance-round-next))

  (defruled blockchain-redundant-p-of-advance-round-next
    (implies (and (blockchain-redundant-p systate)
                  (advance-round-possiblep val systate))
             (blockchain-redundant-p (advance-round-next val systate)))
    :enable (blockchain-redundant-p
             blockchain-redundant-p-necc
             validator-blockchain-redundant-p-of-advance-round-next))

  ;; commit-anchors:

  (defruled validator-blockchain-redundant-p-of-commit-anchors-next-same
    (implies (and (unequivocal-accepted-certificates-p systate)
                  (ordered-even-p systate)
                  (last-blockchain-round-p systate)
                  (accepted-certificate-committee-p systate)
                  (omni-paths-p systate)
                  (last-anchor-present-p systate)
                  (committed-redundant-p systate)
                  (set::in val (correct-addresses systate))
                  (commit-anchors-possiblep val systate)
                  (validator-blockchain-redundant-p
                   (get-validator-state val systate)
                   (all-addresses systate)))
             (validator-blockchain-redundant-p
              (get-validator-state val (commit-anchors-next val systate))
              (all-addresses systate)))
    :enable (validator-blockchain-redundant-p
             validator-state->dag-of-commit-anchors-next
             validator-state->blockchain-of-commit-anchors-next
             committed-anchors-of-commit-anchors-next
             calculate-blockchain
             extend-blockchain-of-append
             validator-committed-redundant-p
             new-committed-certs-of-extend-blockchain
             certificate-set-unequivocalp-when-unequivocal-accepted
             certificates-dag-paths-p-of-committed-anchors
             last-anchor-present-p-necc
             last-anchor-in-dag
             car-of-committed-anchors)
    :use committed-redundant-p-necc)

  (defruled validator-blockchain-redundant-p-of-commit-anchors-next-diff
    (implies (and (ordered-even-p systate)
                  (last-blockchain-round-p systate)
                  (accepted-certificate-committee-p systate)
                  (unequivocal-accepted-certificates-p systate)
                  (omni-paths-p systate)
                  (last-anchor-present-p systate)
                  (set::in val (correct-addresses systate))
                  (commit-anchors-possiblep val1 systate)
                  (validator-blockchain-redundant-p
                   (get-validator-state val systate)
                   (all-addresses systate))
                  (not (equal val (address-fix val1))))
             (validator-blockchain-redundant-p
              (get-validator-state val (commit-anchors-next val1 systate))
              (all-addresses systate)))
    :enable (validator-blockchain-redundant-p
             validator-state->blockchain-of-commit-anchors-next
             validator-state->dag-of-commit-anchors-next
             committed-anchors-of-commit-anchors-next))

  (defruled validator-blockchain-redundant-p-of-commit-anchors-next
    (implies (and (unequivocal-accepted-certificates-p systate)
                  (ordered-even-p systate)
                  (last-blockchain-round-p systate)
                  (accepted-certificate-committee-p systate)
                  (omni-paths-p systate)
                  (last-anchor-present-p systate)
                  (committed-redundant-p systate)
                  (set::in val (correct-addresses systate))
                  (commit-anchors-possiblep val1 systate)
                  (validator-blockchain-redundant-p
                   (get-validator-state val systate)
                   (all-addresses systate)))
             (validator-blockchain-redundant-p
              (get-validator-state val (commit-anchors-next val1 systate))
              (all-addresses systate)))
    :use (validator-blockchain-redundant-p-of-commit-anchors-next-same
          (:instance
           validator-blockchain-redundant-p-of-commit-anchors-next-diff
           (val1 (address-fix val1)))))

  (defruled blockchain-redundant-p-of-commit-anchors-next
    (implies (and (blockchain-redundant-p systate)
                  (unequivocal-accepted-certificates-p systate)
                  (ordered-even-p systate)
                  (last-blockchain-round-p systate)
                  (accepted-certificate-committee-p systate)
                  (omni-paths-p systate)
                  (last-anchor-present-p systate)
                  (committed-redundant-p systate)
                  (commit-anchors-possiblep val systate))
             (blockchain-redundant-p (commit-anchors-next val systate)))
    :enable (blockchain-redundant-p
             blockchain-redundant-p-necc
             validator-blockchain-redundant-p-of-commit-anchors-next))

  ;; timer-expires:

  (defruled validator-blockchain-redundant-p-of-timer-expires-next
    (implies (and (set::in val (correct-addresses systate))
                  (timer-expires-possiblep val1 systate)
                  (validator-blockchain-redundant-p
                   (get-validator-state val systate)
                   (all-addresses systate)))
             (validator-blockchain-redundant-p
              (get-validator-state val (timer-expires-next val1 systate))
              (all-addresses systate)))
    :enable (validator-blockchain-redundant-p
             validator-state->last-of-timer-expires-next
             validator-state->blockchain-of-timer-expires-next
             validator-state->dag-of-timer-expires-next
             committed-anchors-of-timer-expires-next))

  (defruled blockchain-redundant-p-of-timer-expires-next
    (implies (and (blockchain-redundant-p systate)
                  (timer-expires-possiblep val systate))
             (blockchain-redundant-p (timer-expires-next val systate)))
    :enable (blockchain-redundant-p
             blockchain-redundant-p-necc
             validator-blockchain-redundant-p-of-timer-expires-next))

  ;; all events:

  (defruled blockchain-redundant-p-of-event-next
    (implies (and (blockchain-redundant-p systate)
                  (committed-redundant-p systate)
                  (unequivocal-accepted-certificates-p systate)
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
                  (backward-closed-p systate)
                  (ordered-even-p systate)
                  (last-blockchain-round-p systate)
                  (omni-paths-p systate)
                  (event-possiblep event systate))
             (blockchain-redundant-p (event-next event systate)))
    :enable (event-possiblep
             event-next)))
