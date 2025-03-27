; AleoBFT Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOBFT-STATIC")

(include-book "property-committed-anchors-of-next-event")
(include-book "properties-blockchain")
(include-book "invariant-previous-in-dag")
(include-book "invariant-committed-redundant")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ invariant-blockchain-redundant
  :parents (correctness)
  :short "Invariant that the blockchain is redundant."
  :long
  (xdoc::topstring
   (xdoc::p
    "The state of each validator includes (their view of) the blockchain.
     This is initially empty, and gets extended, one or more blocks at a time,
     when anchors are committed.
     However, because of the stability properties of
     paths in the DAG, causal histories, etc.,
     the full blockchain can always be recalculated from scratch,
     from the sequence of committed anchors and from the DAG.")
   (xdoc::p
    "In other words, the blockchain state component is redundant.
     It still seems convenient to include that state component
     in the definition of (correct) validator states,
     so that the definition of the state transitions is more natural,
     closer to how the protocol actually works.
     But we prove this redundancy as an invariant of the protocol."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define validator-blockchain-redundantp ((vstate validator-statep)
                                          (vals address-setp))
  :guard (and (not (set::emptyp vals))
              (evenp (validator-state->last vstate))
              (or (equal (validator-state->last vstate) 0)
                  (last-anchor vstate vals)))
  :returns (yes/no booleanp)
  :short "Check if the blockchain of a validator
          is equal to its calculation from the committed anchors and DAG."
  (equal (validator-state->blockchain vstate)
         (calculate-blockchain (committed-anchors vstate vals)
                               (validator-state->dag vstate))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk system-blockchain-redundantp ((systate system-statep))
  :guard (and (not (set::emptyp (all-addresses systate)))
              (system-last-is-even-p systate)
              (system-last-anchor-present-p systate))
  :returns (yes/no booleanp)
  :short "Definition of the invariant:
          the blockchain of a validator is redundant,
          equal to its calculation from the committed anchors and DAG."
  (forall (val)
          (implies (set::in val (correct-addresses systate))
                   (validator-blockchain-redundantp
                    (get-validator-state val systate)
                    (all-addresses systate))))
  :guard-hints
  (("Goal" :in-theory (enable system-last-is-even-p-necc
                              system-last-anchor-present-p-necc
                              in-all-addresses-when-in-correct-addresses))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled system-blockchain-redundantp-when-system-state-initp
  :short "Establishment of the invariant:
          the invariant holds on any initial state."
  :long
  (xdoc::topstring
   (xdoc::p
    "Initially the blockchain is empty
     and there are no committed anchors,
     so the invariant holds."))
  (implies (system-state-initp systate)
           (system-blockchain-redundantp systate))
  :enable (system-state-initp
           validator-init-when-system-initp
           validator-init
           system-blockchain-redundantp
           validator-blockchain-redundantp
           committed-anchors))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection system-blockchain-redundantp-of-create-certificate-next
  :short "Preservation of the invariant by @('create-certificate') events."
  :long
  (xdoc::topstring
   (xdoc::p
    "Neither the blockchain nor the sequence of committed anchors
     change under this event;
     the calculation of the blockchain is stable under DAG growth,
     as proved in @(tsee calculate-blockchain-of-unequivocal-dag-superset)."))

  (defrule validator-blockchain-redundantp-of-create-certificate-next
    (implies (and (system-signers-are-validators-p systate)
                  (system-signers-are-quorum-p systate)
                  (system-signers-have-author+round-p systate)
                  (system-unequivocal-certificates-p systate)
                  (system-last-anchor-present-p systate)
                  (system-previous-in-dag-p systate)
                  (fault-tolerant-p systate)
                  (set::in val (correct-addresses systate))
                  (certificatep cert)
                  (create-certificate-possiblep cert systate)
                  (validator-blockchain-redundantp
                   (get-validator-state val systate)
                   (all-addresses systate)))
             (validator-blockchain-redundantp
              (get-validator-state
               val (create-certificate-next cert systate))
              (all-addresses systate)))
    :enable (validator-blockchain-redundantp
             system-unequivocal-dag-p-when-system-unequivocal-certificates-p
             system-unequivocal-dag-p-necc
             system-previous-in-dag-p-necc
             system-last-anchor-present-p-necc
             list-in-when-certificate-list-pathp
             validator-state->dag-subset-create-certificate-next
             validator-state->blockchain-of-create-certificate-next
             last-anchor-in-dag
             certificate-list-pathp-of-committed-anchors
             committed-anchors-of-create-certificate-next
             system-unequivocal-certificates-p-of-create-certificate-next)
    :use (:instance calculate-blockchain-of-unequivocal-dag-superset
                    (dag (validator-state->dag
                          (get-validator-state val systate)))
                    (dag2 (validator-state->dag
                           (get-validator-state
                            val (create-certificate-next cert systate))))
                    (anchors (committed-anchors
                              (get-validator-state val systate)
                              (all-addresses systate))))
    :disable validator-state->dag-of-create-certificate-next)

  (defrule system-blockchain-redundantp-of-create-certificate-next
    (implies (and (system-signers-are-validators-p systate)
                  (system-signers-are-quorum-p systate)
                  (system-signers-have-author+round-p systate)
                  (system-unequivocal-certificates-p systate)
                  (system-last-anchor-present-p systate)
                  (system-previous-in-dag-p systate)
                  (fault-tolerant-p systate)
                  (certificatep cert)
                  (create-certificate-possiblep cert systate)
                  (system-blockchain-redundantp systate))
             (system-blockchain-redundantp
              (create-certificate-next cert systate)))
    :expand (system-blockchain-redundantp
             (create-certificate-next cert systate))
    :enable system-blockchain-redundantp-necc))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection system-blockchain-redundantp-of-receive-certificate-next
  :short "Preservation of the invariant by @('receive-certificate') events."
  :long
  (xdoc::topstring
   (xdoc::p
    "Neither the blockchain nor the sequence of committed anchors nor the DAG
     change under this event, so the proof is easy."))

  (defrule validator-blockchain-redundantp-of-receive-certificate-next
    (implies (and (set::in val (correct-addresses systate))
                  (receive-certificate-possiblep msg systate)
                  (validator-blockchain-redundantp
                   (get-validator-state val systate)
                   (all-addresses systate)))
             (validator-blockchain-redundantp
              (get-validator-state
               val (receive-certificate-next msg systate))
              (all-addresses systate)))
    :enable (validator-blockchain-redundantp
             validator-state->dag-of-receive-certificate-next
             validator-state->blockchain-of-receive-certificate-next
             committed-anchors-of-receive-certificate-next))

  (defrule system-blockchain-redundantp-of-receive-certificate-next
    (implies (and (receive-certificate-possiblep msg systate)
                  (system-blockchain-redundantp systate))
             (system-blockchain-redundantp
              (receive-certificate-next msg systate)))
    :expand (system-blockchain-redundantp
             (receive-certificate-next msg systate))
    :enable system-blockchain-redundantp-necc))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection system-blockchain-redundantp-of-store-certificate-next
  :short "Preservation of the invariant by @('store-certificate') events."
  :long
  (xdoc::topstring
   (xdoc::p
    "Neither the blockchain nor the sequence of committed anchors
     change under this event;
     the calculation of the blockchain is stable under DAG growth,
     as proved in @(tsee calculate-blockchain-of-unequivocal-dag-superset)."))

  (defrule validator-blockchain-redundantp-of-store-certificate-next
    (implies (and (system-signers-are-validators-p systate)
                  (system-signers-are-quorum-p systate)
                  (system-signers-have-author+round-p systate)
                  (system-unequivocal-certificates-p systate)
                  (system-last-anchor-present-p systate)
                  (system-previous-in-dag-p systate)
                  (fault-tolerant-p systate)
                  (set::in val (correct-addresses systate))
                  (store-certificate-possiblep cert val1 systate)
                  (validator-blockchain-redundantp
                   (get-validator-state val systate)
                   (all-addresses systate)))
             (validator-blockchain-redundantp
              (get-validator-state
               val (store-certificate-next cert val1 systate))
              (all-addresses systate)))
    :enable (validator-blockchain-redundantp
             system-unequivocal-dag-p-when-system-unequivocal-certificates-p
             system-unequivocal-dag-p-necc
             system-previous-in-dag-p-necc
             system-last-anchor-present-p-necc
             list-in-when-certificate-list-pathp
             validator-state->dag-subset-store-certificate-next
             validator-state->blockchain-of-store-certificate-next
             last-anchor-in-dag
             certificate-list-pathp-of-committed-anchors
             committed-anchors-of-store-certificate-next
             system-unequivocal-certificates-p-of-store-certificate-next)
    :use (:instance calculate-blockchain-of-unequivocal-dag-superset
                    (dag (validator-state->dag
                          (get-validator-state val systate)))
                    (dag2 (validator-state->dag
                           (get-validator-state
                            val (store-certificate-next cert val1 systate))))
                    (anchors (committed-anchors
                              (get-validator-state val systate)
                              (all-addresses systate)))))

  (defrule system-blockchain-redundantp-of-store-certificate-next
    (implies (and (system-signers-are-validators-p systate)
                  (system-signers-are-quorum-p systate)
                  (system-signers-have-author+round-p systate)
                  (system-unequivocal-certificates-p systate)
                  (system-last-anchor-present-p systate)
                  (system-previous-in-dag-p systate)
                  (fault-tolerant-p systate)
                  (store-certificate-possiblep cert val1 systate)
                  (system-blockchain-redundantp systate))
             (system-blockchain-redundantp
              (store-certificate-next cert val1 systate)))
    :expand (system-blockchain-redundantp
             (store-certificate-next cert val1 systate))
    :enable system-blockchain-redundantp-necc))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection system-blockchain-redundantp-of-advance-round-next
  :short "Preservation of the invariant by @('advance-round') events."
  :long
  (xdoc::topstring
   (xdoc::p
    "Neither the blockchain nor the sequence of committed anchors nor the DAG
     change under this event, so the proof is easy."))

  (defrule validator-blockchain-redundantp-of-advance-round-next
    (implies (and (set::in val (correct-addresses systate))
                  (advance-round-possiblep val1 systate)
                  (validator-blockchain-redundantp
                   (get-validator-state val systate)
                   (all-addresses systate)))
             (validator-blockchain-redundantp
              (get-validator-state
               val (advance-round-next val1 systate))
              (all-addresses systate)))
    :enable (validator-blockchain-redundantp
             validator-state->dag-of-advance-round-next
             validator-state->blockchain-of-advance-round-next
             committed-anchors-of-advance-round-next))

  (defrule system-blockchain-redundantp-of-advance-round-next
    (implies (and (advance-round-possiblep val1 systate)
                  (system-blockchain-redundantp systate))
             (system-blockchain-redundantp
              (advance-round-next val1 systate)))
    :expand (system-blockchain-redundantp
             (advance-round-next val1 systate))
    :enable system-blockchain-redundantp-necc))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection system-blockchain-redundantp-of-commit-anchors-next
  :short "Preservation of the invariant by @('commit-anchors') events."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the only event that changes (both)
     the blockchain and the sequence of committed rounds.
     But it does so in a way that the relation is preserved.
     The blockchain state component is extended via @(tsee extend-blockchain)
     applied to the new anchors obtained via @(tsee collect-anchors).
     The blockchain calculated by @(tsee calculate-blockchain)
     also makes use of @(tsee extend-blockchain),
     and the fact that the new @(tsee committed-anchors)
     expand to an @(tsee append) of the new ones with the old ones,
     results in the firing of the @('extend-blockchain-of-append') theorem.
     We also need the previously proved invariant that "
    (xdoc::seetopic "invariant-committed-redundant"
                    "the set of committed certificates is redundant")
    ", which says that the committed certificates before the extension
     are the causal history of the last anchor before the extension."))

  (defrule validator-blockchain-redundantp-of-commit-anchors
    (implies (and (system-last-anchor-present-p systate)
                  (system-unequivocal-dag-p systate)
                  (system-last-is-even-p systate)
                  (system-paths-to-last-anchor-p systate)
                  (system-committed-redundantp systate)
                  (set::in val (correct-addresses systate))
                  (commit-anchors-possiblep val1 systate)
                  (validator-blockchain-redundantp
                   (get-validator-state val systate)
                   (all-addresses systate)))
             (validator-blockchain-redundantp
              (get-validator-state
               val (commit-anchors-next val1 systate))
              (all-addresses systate)))
    :enable (validator-blockchain-redundantp
             calculate-blockchain
             validator-committed-redundantp
             new-committed-certs-of-extend-blockchain
             system-unequivocal-dag-p-when-system-unequivocal-certificates-p
             system-unequivocal-dag-p-necc
             system-last-anchor-present-p-necc
             extend-blockchain-of-nil
             extend-blockchain-of-append
             validator-state->dag-of-commit-anchors-next
             validator-state->blockchain-of-commit-anchors-next
             last-anchor-in-dag
             car-of-committed-anchors
             certificate-list-pathp-of-committed-anchors
             committed-anchors-of-commit-anchors)
    :use system-committed-redundantp-necc)

  (defrule system-blockchain-redundantp-of-commit-anchors-next
    (implies (and (system-last-anchor-present-p systate)
                  (system-unequivocal-dag-p systate)
                  (system-last-is-even-p systate)
                  (system-paths-to-last-anchor-p systate)
                  (system-committed-redundantp systate)
                  (commit-anchors-possiblep val1 systate)
                  (system-blockchain-redundantp systate))
             (system-blockchain-redundantp
              (commit-anchors-next val1 systate)))
    :expand (system-blockchain-redundantp
             (commit-anchors-next val1 systate))
    :enable system-blockchain-redundantp-necc))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection system-blockchain-redundantp-of-timer-expires-next
  :short "Preservation of the invariant by @('timer-expires') events."
  :long
  (xdoc::topstring
   (xdoc::p
    "Neither the blockchain nor the sequence of committed anchors nor the DAG
     change under this event, so the proof is easy."))

  (defrule validator-blockchain-redundantp-of-timer-expires-next
    (implies (and (set::in val (correct-addresses systate))
                  (timer-expires-possiblep val1 systate)
                  (validator-blockchain-redundantp
                   (get-validator-state val systate)
                   (all-addresses systate)))
             (validator-blockchain-redundantp
              (get-validator-state
               val (timer-expires-next val1 systate))
              (all-addresses systate)))
    :enable (validator-blockchain-redundantp
             validator-state->dag-of-timer-expires-next
             validator-state->blockchain-of-timer-expires-next
             committed-anchors-of-timer-expires-next))

  (defrule system-blockchain-redundantp-of-timer-expires-next
    (implies (and (timer-expires-possiblep val1 systate)
                  (system-blockchain-redundantp systate))
             (system-blockchain-redundantp
              (timer-expires-next val1 systate)))
    :expand (system-blockchain-redundantp
             (timer-expires-next val1 systate))
    :enable system-blockchain-redundantp-necc))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule system-blockchain-redundantp-of-event-next
  :short "Preservation of the invariant by all the events."
  :long
  (xdoc::topstring
   (xdoc::p
    "This follows from the theorems about the various kinds of events."))
  (implies (and (system-blockchain-redundantp systate)
                (system-authors-are-validators-p systate)
                (system-dag-previous-are-quorum-p systate)
                (system-last-anchor-present-p systate)
                (system-last-anchor-voters-p systate)
                (system-last-is-even-p systate)
                (system-paths-to-last-anchor-p systate)
                (system-previous-in-dag-p systate)
                (system-signers-are-quorum-p systate)
                (system-signers-are-validators-p systate)
                (system-signers-have-author+round-p systate)
                (system-unequivocal-certificates-p systate)
                (system-committed-redundantp systate)
                (fault-tolerant-p systate)
                (event-possiblep event systate))
           (system-blockchain-redundantp (event-next event systate)))
  :enable (event-possiblep
           event-next))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled system-blockchain-redundantp-of-events-next
  :short "Preservation of the invariant by every sequence of events."
  :long
  (xdoc::topstring
   (xdoc::p
    "Since this invariant's single-event preservation
     depends on other invariants,
     we need to include all invariants to prove
     multi-event preservation by induction.")
   (xdoc::p
    "We explicitly include only the invariants
     that have theorems about the next state after an event;
     the invariants that are proved directly from other invariants,
     which are among the hypotheses of the single-event preservation theorem,
     are handled using the theorems that prove those invariants from others."))
  (implies
   (and (system-statep systate)
        (system-blockchain-redundantp systate)
        (system-signers-are-validators-p systate)
        (system-previous-are-quorum-p systate)
        (system-last-anchor-present-p systate)
        (system-last-anchor-voters-p systate)
        (system-last-is-even-p systate)
        (system-previous-in-dag-p systate)
        (system-signers-are-quorum-p systate)
        (system-signers-have-author+round-p systate)
        (system-unequivocal-certificates-p systate)
        (system-committed-redundantp systate)
        (events-possiblep events systate)
        (fault-tolerant-p systate))
   (and (system-blockchain-redundantp (events-next events systate))
        (system-signers-are-validators-p (events-next events systate))
        (system-previous-are-quorum-p (events-next events systate))
        (system-last-anchor-present-p (events-next events systate))
        (system-last-anchor-voters-p (events-next events systate))
        (system-last-is-even-p (events-next events systate))
        (system-previous-in-dag-p (events-next events systate))
        (system-signers-are-quorum-p (events-next events systate))
        (system-signers-have-author+round-p (events-next events systate))
        (system-unequivocal-certificates-p (events-next events systate))
        (system-committed-redundantp (events-next events systate))))
  :induct t
  :disable ((:e tau-system))
  :enable (events-next
           events-possiblep
           system-blockchain-redundantp-of-event-next
           system-signers-are-validators-p-of-event-next
           system-previous-are-quorum-p-of-event-next
           system-last-anchor-present-p-of-event-next
           system-last-anchor-voters-p-of-event-next
           system-last-is-even-p-of-event-next
           system-previous-in-dag-p-of-event-next
           system-signers-are-quorum-p-of-event-next
           system-signers-have-author+round-p-of-event-next
           system-unequivocal-certificates-p-of-event-next
           system-blockchain-redundantp-of-event-next
           system-authors-are-validators-p-when-signers-are-validators
           system-dag-previous-are-quorum-p-when-all-previous-are-quorum
           system-paths-to-last-anchor-p-when-other-invariants
           system-unequivocal-dag-p-when-system-unequivocal-certificates-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled system-blockchain-redundantp-when-reachable
  :short "The invariant holds in every reachable state."
  :long
  (xdoc::topstring
   (xdoc::p
    "Reachable states are characterized by an initial state and
     a sequence of possible events from that initial state.")
   (xdoc::p
    "This does not mention the other invariant,
     because it holds in the initial state
     and that it establishes the hypothesis of
     the multi-event preservation theorem."))
  (implies (and (system-statep systate)
                (system-state-initp systate)
                (events-possiblep events systate)
                (fault-tolerant-p systate))
           (system-blockchain-redundantp (events-next events systate)))
  :disable ((:e tau-system))
  :enable (system-blockchain-redundantp-when-system-state-initp
           system-signers-are-validators-p-when-system-state-initp
           system-previous-are-quorum-p-when-system-state-initp
           system-last-anchor-present-p-when-system-state-initp
           system-last-anchor-voters-p-when-system-state-initp
           system-last-is-even-p-when-system-state-initp
           system-previous-in-dag-p-when-system-state-initp
           system-signers-are-quorum-p-when-system-state-initp
           system-signers-have-author+round-p-when-system-state-initp
           system-unequivocal-certificates-p-when-system-state-initp
           system-committed-redundantp-when-system-state-initp
           system-blockchain-redundantp-of-events-next))
