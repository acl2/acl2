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

(include-book "last-anchor-next")
(include-book "backward-closure")
(include-book "omni-paths-def-and-implied")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ committed-redundant-def-and-init-and-next
  :parents (correctness)
  :short "Invariant that the set of committed certificates is redundant:
          definition, establishment, and preservation."
  :long
  (xdoc::topstring
   (xdoc::p
    "The state of each validator includes
     the set of all the certificates committed so far;
     see @(tsee validator-state).
     This is useful for defining the state transitions of the system,
     since the block for each committed anchor contains
     the transactions in the causal history of the anchor,
     except for the already committed anchors,
     whose set is in the state component being discussed here.")
   (xdoc::p
    "However, it turns out that that state component,
     the set of all committed certificates so far,
     is redundant, and can be calculated from the other state components.
     Specifically, it is always equal to
     the causal history of the last committed anchor,
     or to the empty set if there is no committed anchor.
     Here we prove this property, as a system invariant.")
   (xdoc::p
    "Here we define the invariant,
     we prove that it holds in all initial states,
     and we prove that it is preserved by all transitions.
     In @(see committed-redundant) we prove that
     the invariant holds in every reachable state."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define validator-committed-redundant-p ((vstate validator-statep)
                                         (all-vals address-setp))
  :guard (or (equal (validator-state->last vstate) 0)
             (last-anchor vstate all-vals))
  :returns (yes/no booleanp)
  :short "Check if the set of committed certificates of a validator
          is the causal history of its last committed anchor."
  (equal (validator-state->committed vstate)
         (if (equal (validator-state->last vstate) 0)
             nil
           (certificate-causal-history (last-anchor vstate all-vals)
                                       (validator-state->dag vstate))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk committed-redundant-p ((systate system-statep))
  :guard (last-anchor-present-p systate)
  :returns (yes/no booleanp)
  :short "Definition of the invariant:
          the set of committed certificates of each correct validator
          is redundant,
          equal to the causal history of the last committed anchor."
  (forall (val)
          (implies (set::in val (correct-addresses systate))
                   (validator-committed-redundant-p
                    (get-validator-state val systate)
                    (all-addresses systate))))
  :guard-hints (("Goal" :in-theory (enable last-anchor-present-p-necc)))
  ///
  (fty::deffixequiv-sk committed-redundant-p
    :args ((systate system-statep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled committed-redundant-p-when-init
  :short "Establishment of the invariant:
          the invariant holds in any initial state."
  :long
  (xdoc::topstring
   (xdoc::p
    "Initially the last committed round is 0
     and the set of committed certificates is empty,
     so the proof is easy."))
  (implies (system-initp systate)
           (committed-redundant-p systate))
  :enable (committed-redundant-p
           validator-committed-redundant-p
           system-initp
           system-validators-initp-necc
           validator-init))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection committed-redundant-p-of-next
  :short "Preservation of the invariant:
          if the invariant holds in a system state,
          it also holds in the next system state."
  :long
  (xdoc::topstring
   (xdoc::p
    "A @('create-certificate') or @('store-certificate') event
     does not change the set of committed certificates or the last anchor,
     but it extends the DAGs with a certificate.
     However, since the last anchor is already present,
     its causal history does not change,
     because the newly added certificate cannot be in its causal history;
     the key theorem used in this proof is
     @('certificate-causal-history-of-unequivocal-superdag').
     To discharge its hypothesis that the extended DAG is unequivocal,
     we use the already proved preservation theorem
     @('unequivocal-accepted-certificates-p-of-create-certificate-next'),
     along with a @(':use') hint to force the application of non-equivocation
     on the new state rather than the old one.
     Interestingly, that theorem does not need to be enabled
     in order for these proofs to go through,
     apparently thanks to tau;
     but since this seems too ``hidden'',
     we disable tau and explicitly enable the theorem.")
   (xdoc::p
    "A @('commit-anchors') event changes, for the target validator,
     the last anchor and the set of committed certificates, but not the DAG.
     According to the theorem @('new-committed-certs-of-extend-blockchain')
     proved in @(tsee extend-blockchain),
     the new set of committed certificates is
     the union of the old ones with the causal history of the new anchor.
     But the invariant in the old state tells us that
     the old set of committed anchors is
     the causal history of the old last anchor:
     so the new set of committed certificates is the union of
     the causal history of the new last anchor
     and the causal history of the old last anchor.
     But, as previously proved, there is a path in the DAG
     from the new last anchor and the old last anchor,
     and therefore by @(tsee certificate-causal-history-subset-when-path)
     the causal history of the old last anchor is a subset of
     the causal history of the new last anchor:
     thus the union reduces to the latter,
     and the invariant is re-established in the new state.")
   (xdoc::p
    "The other three kinds of events do not change
     the set of committed certificates or the last anchor or the DAG,
     and thus the proof is easy."))

  ;; create-certificate:

  (defruled validator-committed-redundant-p-of-create-certificate-next
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
                  (validator-committed-redundant-p
                   (get-validator-state val systate)
                   (all-addresses systate))
                  (create-certificate-possiblep cert systate))
             (validator-committed-redundant-p
              (get-validator-state
               val (create-certificate-next cert systate))
              (all-addresses systate)))
    :disable ((:e tau-system))
    :enable (validator-committed-redundant-p
             validator-state->dag-of-create-certificate-next
             validator-state->last-of-create-certificate-next
             validator-state->committed-of-create-certificate-next
             last-anchor-of-create-certificate-next
             last-anchor-present-p-necc
             last-anchor-in-dag
             backward-closed-p-necc
             unequivocal-accepted-certificates-p-of-create-certificate-next)
    :use ((:instance certificate-causal-history-of-unequivocal-superdag
                     (dag0 (validator-state->dag
                            (get-validator-state (certificate->author cert)
                                                 systate)))
                     (dag (validator-state->dag
                           (get-validator-state
                            (certificate->author cert)
                            (create-certificate-next cert systate))))
                     (cert (last-anchor (get-validator-state
                                         (certificate->author cert)
                                         systate)
                                        (all-addresses systate))))
          (:instance certificate-set-unequivocalp-when-unequivocal-accepted
                     (val (certificate->author cert))
                     (systate (create-certificate-next cert systate)))))

  (defruled committed-redundant-p-of-create-certificate-next
    (implies (and (committed-redundant-p systate)
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
             (committed-redundant-p
              (create-certificate-next cert systate)))
    :enable (committed-redundant-p
             committed-redundant-p-necc
             validator-committed-redundant-p-of-create-certificate-next))

  ;; receive-certificate:

  (defruled validator-committed-redundant-p-of-receive-certificate-next
    (implies (and (set::in val (correct-addresses systate))
                  (receive-certificate-possiblep msg systate)
                  (validator-committed-redundant-p
                   (get-validator-state val systate)
                   (all-addresses systate)))
             (validator-committed-redundant-p
              (get-validator-state val (receive-certificate-next msg systate))
              (all-addresses systate)))
    :enable (validator-committed-redundant-p
             validator-state->last-of-receive-certificate-next
             validator-state->committed-of-receive-certificate-next
             validator-state->dag-of-receive-certificate-next
             last-anchor-of-receive-certificate-next))

  (defruled committed-redundant-p-of-receive-certificate-next
    (implies (and (committed-redundant-p systate)
                  (receive-certificate-possiblep msg systate))
             (committed-redundant-p (receive-certificate-next msg systate)))
    :enable (committed-redundant-p
             committed-redundant-p-necc
             validator-committed-redundant-p-of-receive-certificate-next))

  ;; store-certificate:

  (defruled validator-committed-redundant-p-of-store-certificate-next
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
                  (validator-committed-redundant-p
                   (get-validator-state val systate)
                   (all-addresses systate))
                  (store-certificate-possiblep val1 cert systate))
             (validator-committed-redundant-p
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
                     (validator-committed-redundant-p
                      (get-validator-state val systate)
                      (all-addresses systate))
                     (store-certificate-possiblep val1 cert systate)
                     (addressp val1))
                (validator-committed-redundant-p
                 (get-validator-state
                  val (store-certificate-next val1 cert systate))
                 (all-addresses systate)))
       :disable ((:e tau-system))
       :enable (validator-committed-redundant-p
                validator-state->dag-of-store-certificate-next
                validator-state->last-of-store-certificate-next
                validator-state->committed-of-store-certificate-next
                last-anchor-of-store-certificate-next
                last-anchor-present-p-necc
                last-anchor-in-dag
                backward-closed-p-necc
                unequivocal-accepted-certificates-p-of-store-certificate-next)
       :use ((:instance certificate-causal-history-of-unequivocal-superdag
                        (dag0 (validator-state->dag
                               (get-validator-state val1 systate)))
                        (dag (validator-state->dag
                              (get-validator-state
                               val1
                               (store-certificate-next val1 cert systate))))
                        (cert (last-anchor (get-validator-state val1 systate)
                                           (all-addresses systate))))
             (:instance certificate-set-unequivocalp-when-unequivocal-accepted
                        (val val1)
                        (systate
                         (store-certificate-next val1 cert systate)))))))

  (defruled committed-redundant-p-of-store-certificate-next
    (implies (and (committed-redundant-p systate)
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
                  (store-certificate-possiblep val cert systate))
             (committed-redundant-p
              (store-certificate-next val cert systate)))
    :enable (committed-redundant-p
             committed-redundant-p-necc
             validator-committed-redundant-p-of-store-certificate-next))

  ;; advance-round:

  (defruled validator-committed-redundant-p-of-advance-round-next
    (implies (and (set::in val (correct-addresses systate))
                  (advance-round-possiblep val1 systate)
                  (validator-committed-redundant-p
                   (get-validator-state val systate)
                   (all-addresses systate)))
             (validator-committed-redundant-p
              (get-validator-state val (advance-round-next val1 systate))
              (all-addresses systate)))
    :enable (validator-committed-redundant-p
             validator-state->last-of-advance-round-next
             validator-state->committed-of-advance-round-next
             validator-state->dag-of-advance-round-next
             last-anchor-of-advance-round-next))

  (defruled committed-redundant-p-of-advance-round-next
    (implies (and (committed-redundant-p systate)
                  (advance-round-possiblep val systate))
             (committed-redundant-p (advance-round-next val systate)))
    :enable (committed-redundant-p
             committed-redundant-p-necc
             validator-committed-redundant-p-of-advance-round-next))

  ;; commit-anchors:

  (defruled validator-committed-redundant-p-of-commit-anchors-next-same
    (implies (and (unequivocal-accepted-certificates-p systate)
                  (ordered-even-p systate)
                  (last-blockchain-round-p systate)
                  (accepted-certificate-committee-p systate)
                  (omni-paths-p systate)
                  (last-anchor-present-p systate)
                  (set::in val (correct-addresses systate))
                  (commit-anchors-possiblep val systate)
                  (validator-committed-redundant-p
                   (get-validator-state val systate)
                   (all-addresses systate)))
             (validator-committed-redundant-p
              (get-validator-state val (commit-anchors-next val systate))
              (all-addresses systate)))
    :enable (validator-committed-redundant-p
             validator-state->dag-of-commit-anchors-next
             validator-state->blockchain-of-commit-anchors-next
             validator-state->last-of-commit-anchors-next
             validator-state->committed-of-commit-anchors-next
             last-anchor-of-commit-anchors-next
             commit-anchors-possiblep
             new-committed-certs-of-extend-blockchain
             certificate-set-unequivocalp-when-unequivocal-accepted
             certificates-dag-paths-p-of-collect-anchors
             cert-with-author+round-element
             certificate->round-of-cert-with-author+round
             car-of-collect-anchors
             omni-paths-p-necc
             set::expensive-rules
             last-anchor-present-p-necc
             last-anchor-in-dag
             certificate->author-of-last-anchor
             certificate->round-of-last-anchor
             last-blockchain-round-p-necc
             ordered-even-p-necc
             evenp-of-blocks-last-round
             evenp-lemma)
    :use ((:instance certificate-causal-history-subset-when-path
                     (dag (validator-state->dag
                           (get-validator-state val systate)))
                     (cert (last-anchor
                            (get-validator-state
                             val (commit-anchors-next val systate))
                            (all-addresses systate)))
                     (author (certificate->author
                              (last-anchor (get-validator-state val systate)
                                           (all-addresses systate))))
                     (round (certificate->round
                             (last-anchor (get-validator-state val systate)
                                          (all-addresses systate)))))
          (:instance dag-omni-paths-p-necc
                     (cert (last-anchor (get-validator-state val systate)
                                        (all-addresses systate)))
                     (cert1 (last-anchor
                             (get-validator-state
                              val (commit-anchors-next val systate))
                             (all-addresses systate)))
                     (dag (validator-state->dag
                           (get-validator-state val systate)))))
    :prep-lemmas
    ((defruled evenp-lemma
       (implies (and (integerp round)
                     (integerp last)
                     (evenp last)
                     (not (evenp round)))
                (not (equal last (- round 2))))
       :enable evenp)))

  (defruled validator-committed-redundant-p-of-commit-anchors-next-diff
    (implies (and (ordered-even-p systate)
                  (last-blockchain-round-p systate)
                  (accepted-certificate-committee-p systate)
                  (set::in val (correct-addresses systate))
                  (commit-anchors-possiblep val1 systate)
                  (validator-committed-redundant-p
                   (get-validator-state val systate)
                   (all-addresses systate))
                  (not (equal val (address-fix val1))))
             (validator-committed-redundant-p
              (get-validator-state val (commit-anchors-next val1 systate))
              (all-addresses systate)))
    :enable (validator-committed-redundant-p
             validator-state->last-of-commit-anchors-next
             validator-state->committed-of-commit-anchors-next
             validator-state->dag-of-commit-anchors-next
             last-anchor-of-commit-anchors-next))

  (defruled validator-committed-redundant-p-of-commit-anchors-next
    (implies (and (unequivocal-accepted-certificates-p systate)
                  (ordered-even-p systate)
                  (last-blockchain-round-p systate)
                  (accepted-certificate-committee-p systate)
                  (omni-paths-p systate)
                  (last-anchor-present-p systate)
                  (set::in val (correct-addresses systate))
                  (commit-anchors-possiblep val1 systate)
                  (validator-committed-redundant-p
                   (get-validator-state val systate)
                   (all-addresses systate)))
             (validator-committed-redundant-p
              (get-validator-state val (commit-anchors-next val1 systate))
              (all-addresses systate)))
    :use (validator-committed-redundant-p-of-commit-anchors-next-same
          (:instance validator-committed-redundant-p-of-commit-anchors-next-diff
                     (val1 (address-fix val1)))))

  (defruled committed-redundant-p-of-commit-anchors-next
    (implies (and (committed-redundant-p systate)
                  (unequivocal-accepted-certificates-p systate)
                  (ordered-even-p systate)
                  (last-blockchain-round-p systate)
                  (accepted-certificate-committee-p systate)
                  (omni-paths-p systate)
                  (last-anchor-present-p systate)
                  (commit-anchors-possiblep val systate))
             (committed-redundant-p (commit-anchors-next val systate)))
    :enable (committed-redundant-p
             committed-redundant-p-necc
             validator-committed-redundant-p-of-commit-anchors-next))

  ;; timer-expires:

  (defruled validator-committed-redundant-p-of-timer-expires-next
    (implies (and (set::in val (correct-addresses systate))
                  (timer-expires-possiblep val1 systate)
                  (validator-committed-redundant-p
                   (get-validator-state val systate)
                   (all-addresses systate)))
             (validator-committed-redundant-p
              (get-validator-state val (timer-expires-next val1 systate))
              (all-addresses systate)))
    :enable (validator-committed-redundant-p
             validator-state->last-of-timer-expires-next
             validator-state->committed-of-timer-expires-next
             validator-state->dag-of-timer-expires-next
             last-anchor-of-timer-expires-next))

  (defruled committed-redundant-p-of-timer-expires-next
    (implies (and (committed-redundant-p systate)
                  (timer-expires-possiblep val systate))
             (committed-redundant-p (timer-expires-next val systate)))
    :enable (committed-redundant-p
             committed-redundant-p-necc
             validator-committed-redundant-p-of-timer-expires-next))

  ;; all events:

  (defruled committed-redundant-p-of-event-next
    (implies (and (committed-redundant-p systate)
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
             (committed-redundant-p (event-next event systate)))
    :enable (event-possiblep
             event-next)))
