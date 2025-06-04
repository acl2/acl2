; AleoBFT Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOBFT")

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
     Elsewhere we prove that
     the invariant holds in every reachable state."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define validator-committed-redundant-p ((vstate validator-statep))
  :guard (or (equal (validator-state->last vstate) 0)
             (last-anchor vstate))
  :returns (yes/no booleanp)
  :short "Check if the set of committed certificates of a validator
          is the causal history of its last committed anchor."
  (equal (validator-state->committed vstate)
         (if (equal (validator-state->last vstate) 0)
             nil
           (certificate-causal-history (last-anchor vstate)
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
                    (get-validator-state val systate))))
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
    "A @('create') or @('accept') event
     does not change the set of committed certificates or the last anchor,
     but it extends the DAGs with a certificate.
     However, since the last anchor is already present,
     its causal history does not change,
     because the newly added certificate cannot be in its causal history;
     the key theorem used in this proof is
     @('certificate-causal-history-of-unequivocal-superdag').
     To discharge its hypothesis that the extended DAG is unequivocal,
     we use the already proved preservation theorem
     @('unequivocal-dags-certificates-p-of-create-next'),
     along with a @(':use') hint to force the application of non-equivocation
     on the new state rather than the old one.")
   (xdoc::p
    "A @('commit') event changes, for the target validator,
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
    "An @('advance') event does not change
     the set of committed certificates or the last anchor or the DAG,
     and thus the proof is easy."))

  ;; create:

  (defruled validator-committed-redundant-p-of-create-next
    (implies (and (system-committees-fault-tolerant-p systate)
                  (backward-closed-p systate)
                  (signer-records-p systate)
                  (no-self-endorsed-p systate)
                  (signer-quorum-p systate)
                  (unequivocal-dags-p systate)
                  (same-committees-p systate)
                  (last-anchor-present-p systate)
                  (set::in val (correct-addresses systate))
                  (validator-committed-redundant-p
                   (get-validator-state val systate))
                  (create-possiblep cert systate))
             (validator-committed-redundant-p
              (get-validator-state val (create-next cert systate))))
    :enable (validator-committed-redundant-p
             validator-state->dag-of-create-next
             last-anchor-present-p-necc
             last-anchor-in-dag
             backward-closed-p-necc)
    :use ((:instance certificate-causal-history-of-unequivocal-superdag
                     (dag0 (validator-state->dag
                            (get-validator-state (certificate->author cert)
                                                 systate)))
                     (dag (validator-state->dag
                           (get-validator-state
                            (certificate->author cert)
                            (create-next cert systate))))
                     (cert (last-anchor (get-validator-state
                                         (certificate->author cert) systate))))
          (:instance unequivocal-dags-p-necc-single
                     (val (certificate->author cert))
                     (systate (create-next cert systate)))))

  (defruled committed-redundant-p-of-create-next
    (implies (and (committed-redundant-p systate)
                  (system-committees-fault-tolerant-p systate)
                  (backward-closed-p systate)
                  (signer-records-p systate)
                  (no-self-endorsed-p systate)
                  (signer-quorum-p systate)
                  (unequivocal-dags-p systate)
                  (same-committees-p systate)
                  (last-anchor-present-p systate)
                  (create-possiblep cert systate))
             (committed-redundant-p (create-next cert systate)))
    :enable (committed-redundant-p
             committed-redundant-p-necc
             validator-committed-redundant-p-of-create-next))

  ;; accept:

  (defruled validator-committed-redundant-p-of-accept-next
    (implies (and (system-committees-fault-tolerant-p systate)
                  (backward-closed-p systate)
                  (signer-quorum-p systate)
                  (unequivocal-signed-certs-p systate)
                  (unequivocal-dags-p systate)
                  (same-committees-p systate)
                  (last-anchor-present-p systate)
                  (set::in val (correct-addresses systate))
                  (validator-committed-redundant-p
                   (get-validator-state val systate))
                  (accept-possiblep msg systate)
                  (messagep msg))
             (validator-committed-redundant-p
              (get-validator-state val (accept-next msg systate))))
    :enable (validator-committed-redundant-p
             validator-state->dag-of-accept-next
             last-anchor-present-p-necc
             last-anchor-in-dag
             backward-closed-p-necc
             unequivocal-dags-p-of-accept-next)
    :use ((:instance certificate-causal-history-of-unequivocal-superdag
                     (dag0 (validator-state->dag
                            (get-validator-state (message->destination msg)
                                                 systate)))
                     (dag (validator-state->dag
                           (get-validator-state
                            (message->destination msg)
                            (accept-next msg systate))))
                     (cert (last-anchor (get-validator-state
                                         (message->destination msg)
                                         systate))))
          (:instance unequivocal-dags-p-necc-single
                     (systate (accept-next msg systate)))))

  (defruled committed-redundant-p-of-accept-next
    (implies (and (committed-redundant-p systate)
                  (system-committees-fault-tolerant-p systate)
                  (backward-closed-p systate)
                  (signer-quorum-p systate)
                  (unequivocal-signed-certs-p systate)
                  (unequivocal-dags-p systate)
                  (same-committees-p systate)
                  (last-anchor-present-p systate)
                  (accept-possiblep msg systate)
                  (messagep msg))
             (committed-redundant-p (accept-next msg systate)))
    :enable (committed-redundant-p
             committed-redundant-p-necc
             validator-committed-redundant-p-of-accept-next))

  ;; advance:

  (defruled validator-committed-redundant-p-of-advance-next
    (implies (and (set::in val (correct-addresses systate))
                  (advance-possiblep val1 systate)
                  (validator-committed-redundant-p
                   (get-validator-state val systate)))
             (validator-committed-redundant-p
              (get-validator-state val (advance-next val1 systate))))
    :enable validator-committed-redundant-p)

  (defruled committed-redundant-p-of-advance-next
    (implies (and (committed-redundant-p systate)
                  (advance-possiblep val systate))
             (committed-redundant-p (advance-next val systate)))
    :enable (committed-redundant-p
             committed-redundant-p-necc
             validator-committed-redundant-p-of-advance-next))

  ;; commit:

  (defruled validator-committed-redundant-p-of-commit-next-same
    (implies (and (last-blockchain-round-p systate)
                  (ordered-blockchain-p systate)
                  (signer-quorum-p systate)
                  (unequivocal-dags-p systate)
                  (last-anchor-present-p systate)
                  (omni-paths-p systate)
                  (set::in val (correct-addresses systate))
                  (commit-possiblep val systate)
                  (addressp val)
                  (validator-committed-redundant-p
                   (get-validator-state val systate)))
             (validator-committed-redundant-p
              (get-validator-state val (commit-next val systate))))
    :enable (validator-committed-redundant-p
             validator-state->blockchain-of-commit-next
             validator-state->last-of-commit-next
             validator-state->committed-of-commit-next
             last-anchor-of-commit-next
             commit-possiblep
             new-committed-certs-of-extend-blockchain
             unequivocal-dags-p-necc-single
             certificates-dag-paths-p-of-collect-anchors
             cert-with-author+round-element
             car-of-collect-anchors
             omni-paths-p-necc
             last-anchor-present-p-necc
             last-anchor-in-dag
             last-blockchain-round-p-necc
             certificate->author-of-last-anchor
             certificate->round-of-last-anchor
             ordered-blockchain-p-necc
             evenp-lemma
             set::expensive-rules)
    :use ((:instance certificate-causal-history-subset-when-path
                     (dag (validator-state->dag
                           (get-validator-state val systate)))
                     (cert (last-anchor
                            (get-validator-state
                             val (commit-next val systate))))
                     (author (certificate->author
                              (last-anchor (get-validator-state val systate))))
                     (round (certificate->round
                             (last-anchor (get-validator-state val systate)))))
          (:instance dag-omni-paths-p-necc
                     (cert (last-anchor (get-validator-state val systate)))
                     (cert1 (last-anchor
                             (get-validator-state
                              val (commit-next val systate))))
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

  (defruled validator-committed-redundant-p-of-commit-next-diff
    (implies (and (last-blockchain-round-p systate)
                  (ordered-blockchain-p systate)
                  (signer-quorum-p systate)
                  (set::in val (correct-addresses systate))
                  (commit-possiblep val1 systate)
                  (addressp val1)
                  (validator-committed-redundant-p
                   (get-validator-state val systate))
                  (not (equal val val1)))
             (validator-committed-redundant-p
              (get-validator-state val (commit-next val1 systate))))
    :enable (validator-committed-redundant-p
             validator-state->last-of-commit-next
             validator-state->committed-of-commit-next
             last-anchor-of-commit-next))

  (defruled validator-committed-redundant-p-of-commit-next
    (implies (and (last-blockchain-round-p systate)
                  (ordered-blockchain-p systate)
                  (signer-quorum-p systate)
                  (unequivocal-dags-p systate)
                  (last-anchor-present-p systate)
                  (omni-paths-p systate)
                  (set::in val (correct-addresses systate))
                  (commit-possiblep val1 systate)
                  (addressp val1)
                  (validator-committed-redundant-p
                   (get-validator-state val systate)))
             (validator-committed-redundant-p
              (get-validator-state val (commit-next val1 systate))))
    :use (validator-committed-redundant-p-of-commit-next-same
          validator-committed-redundant-p-of-commit-next-diff))

  (defruled committed-redundant-p-of-commit-next
    (implies (and (committed-redundant-p systate)
                  (last-blockchain-round-p systate)
                  (ordered-blockchain-p systate)
                  (signer-quorum-p systate)
                  (unequivocal-dags-p systate)
                  (last-anchor-present-p systate)
                  (omni-paths-p systate)
                  (commit-possiblep val systate)
                  (addressp val))
             (committed-redundant-p (commit-next val systate)))
    :enable (committed-redundant-p
             committed-redundant-p-necc
             validator-committed-redundant-p-of-commit-next))

  ;; all events:

  (defruled committed-redundant-p-of-event-next
    (implies (and (committed-redundant-p systate)
                  (system-committees-fault-tolerant-p systate)
                  (backward-closed-p systate)
                  (last-blockchain-round-p systate)
                  (ordered-blockchain-p systate)
                  (signer-records-p systate)
                  (no-self-endorsed-p systate)
                  (signer-quorum-p systate)
                  (unequivocal-signed-certs-p systate)
                  (unequivocal-dags-p systate)
                  (same-committees-p systate)
                  (last-anchor-present-p systate)
                  (omni-paths-p systate)
                  (event-possiblep event systate))
             (committed-redundant-p (event-next event systate)))
    :enable (event-possiblep
             event-next)))
