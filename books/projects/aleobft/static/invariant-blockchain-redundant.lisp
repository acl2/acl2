; Aleo Library
;
; Copyright (C) 2024 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEO")

(include-book "property-validator-anchors-of-next-event")
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
     However, because the stability properties of
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
         (calculate-blockchain (validator-anchors vstate vals)
                               (validator-state->dag vstate))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk system-blockchain-redundantp ((systate system-statep))
  :guard (and (not (set::emptyp (validator-addresses systate)))
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
                    (validator-addresses systate))))
  :guard-hints
  (("Goal" :in-theory (enable system-last-is-even-p-necc
                              system-last-anchor-present-p-necc))))

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
           validator-init
           system-blockchain-redundantp
           validator-blockchain-redundantp
           validator-anchors))

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
                   (validator-addresses systate)))
             (validator-blockchain-redundantp
              (get-validator-state
               val (create-certificate-next cert systate))
              (validator-addresses systate)))
    :enable (validator-blockchain-redundantp
             system-unequivocal-dag-p-when-system-unequivocal-certificates-p
             system-unequivocal-dag-p-necc
             system-previous-in-dag-p-necc
             system-last-anchor-present-p-necc
             list-in-when-certificate-list-pathp)
    :use (:instance calculate-blockchain-of-unequivocal-dag-superset
                    (dag (validator-state->dag
                          (get-validator-state val systate)))
                    (dag2 (validator-state->dag
                           (get-validator-state
                            val (create-certificate-next cert systate))))
                    (anchors (validator-anchors
                              (get-validator-state val systate)
                              (validator-addresses systate))))
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
                   (validator-addresses systate)))
             (validator-blockchain-redundantp
              (get-validator-state
               val (receive-certificate-next msg systate))
              (validator-addresses systate)))
    :enable (validator-blockchain-redundantp))

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
                   (validator-addresses systate)))
             (validator-blockchain-redundantp
              (get-validator-state
               val (store-certificate-next cert val1 systate))
              (validator-addresses systate)))
    :enable (validator-blockchain-redundantp
             system-unequivocal-dag-p-when-system-unequivocal-certificates-p
             system-unequivocal-dag-p-necc
             system-previous-in-dag-p-necc
             system-last-anchor-present-p-necc
             list-in-when-certificate-list-pathp)
    :use (:instance calculate-blockchain-of-unequivocal-dag-superset
                    (dag (validator-state->dag
                          (get-validator-state val systate)))
                    (dag2 (validator-state->dag
                           (get-validator-state
                            val (store-certificate-next cert val1 systate))))
                    (anchors (validator-anchors
                              (get-validator-state val systate)
                              (validator-addresses systate))))
    :disable validator-state->dag-of-store-certificate-next)

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
                   (validator-addresses systate)))
             (validator-blockchain-redundantp
              (get-validator-state
               val (advance-round-next val1 systate))
              (validator-addresses systate)))
    :enable (validator-blockchain-redundantp))

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
     and the fact that the new @(tsee validator-anchors)
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
                   (validator-addresses systate)))
             (validator-blockchain-redundantp
              (get-validator-state
               val (commit-anchors-next val1 systate))
              (validator-addresses systate)))
    :enable (validator-blockchain-redundantp
             calculate-blockchain
             validator-committed-redundantp
             new-committed-certs-of-extend-blockchain
             system-unequivocal-dag-p-when-system-unequivocal-certificates-p
             system-unequivocal-dag-p-necc
             system-last-anchor-present-p-necc)
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
                   (validator-addresses systate)))
             (validator-blockchain-redundantp
              (get-validator-state
               val (timer-expires-next val1 systate))
              (validator-addresses systate)))
    :enable (validator-blockchain-redundantp))

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
