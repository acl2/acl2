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

(include-book "properties-certificate-retrieval")
(include-book "properties-blockchain")
(include-book "property-last-anchor-of-next-event")
(include-book "invariant-unequivocal-dag")
(include-book "invariant-last-is-even")
(include-book "invariant-last-anchor-present")
(include-book "invariant-previous-in-dag")
(include-book "invariant-certificate-retrieval")
(include-book "invariant-causal-histories")
(include-book "invariant-paths-to-last-anchor")

(include-book "std/util/define-sk" :dir :system)

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ invariant-committed-redundant
  :parents (correctness)
  :short "Invariant that the set of committed certificates is redundant."
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
     whose set is in the state component being discussed here.
     This definition of the state transitions models the implementation.")
   (xdoc::p
    "However, it turns out that that state component,
     the set of all committed certificates so far,
     is redundant, and can be calculated from the other state components.
     Specifically, it is always equal to
     the causal history of the last committed anchor,
     or to the empty set if there is no committed anchor.
     Here we prove this property, as a system invariant.")
   (xdoc::p
    "Given this, it would be possible to simplify
     the definition of the validator states
     to remove that redundant component,
     and to rephrase the state transitions
     to re-calculate it when needed.
     However, for now it seems better to keep that state component,
     in order to model more closely the implementation of the protocol,
     and to show the redundancy of that state component as an invariant."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define validator-committed-redundantp ((vstate validator-statep)
                                        (vals address-setp))
  :guard (and (not (set::emptyp vals))
              (evenp (validator-state->last vstate))
              (or (equal (validator-state->last vstate) 0)
                  (last-anchor vstate vals)))
  :returns (yes/no booleanp)
  :short "Check if the set of committed certificates of a validator
          is the causal history of its last committed anchor."
  (equal (validator-state->committed vstate)
         (if (equal (validator-state->last vstate) 0)
             nil
           (certificate-causal-history (last-anchor vstate vals)
                                       (validator-state->dag vstate)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk system-committed-redundantp ((systate system-statep))
  :guard (and (not (set::emptyp (all-addresses systate)))
              (system-last-is-even-p systate)
              (system-last-anchor-present-p systate))
  :returns (yes/no booleanp)
  :short "Definition of the invariant:
          the set of committed certificates of a validator is redundant,
          equal to the causal history of the last committed anchor."
  (forall (val)
          (implies (set::in val (correct-addresses systate))
                   (validator-committed-redundantp
                    (get-validator-state val systate)
                    (all-addresses systate))))
  :guard-hints
  (("Goal" :in-theory (enable system-last-is-even-p-necc
                              system-last-anchor-present-p-necc
                              in-all-addresses-when-in-correct-addresses))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled system-committed-redundantp-when-system-state-initp
  :short "Establishment of the invariant:
          the invariant holds on any initial state."
  :long
  (xdoc::topstring
   (xdoc::p
    "Initially the last committed round is 0
     and the set of committed certificates is empty,
     so the invariant holds."))
  (implies (system-state-initp systate)
           (system-committed-redundantp systate))
  :enable (system-state-initp
           validator-init-when-system-initp
           validator-init
           system-committed-redundantp
           validator-committed-redundantp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection system-committed-redundantp-of-create-certificate-next
  :short "Preservation of the invariant by @('create-certificate') events."
  :long
  (xdoc::topstring
   (xdoc::p
    "Neither the set of committed certificates nor the last committed anchor
     change under this event, so the proof is easy.
     It relies on @(tsee last-anchor-of-create-certificate-next)."))

  (defrule validator-committed-redundantp-of-create-certificate-next
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
                  (validator-committed-redundantp
                   (get-validator-state val systate)
                   (all-addresses systate)))
             (validator-committed-redundantp
              (get-validator-state val (create-certificate-next cert systate))
              (all-addresses systate)))
    :enable (validator-committed-redundantp
             system-last-anchor-present-p-necc
             validator-state->last-of-create-certificate-next
             validator-state->committed-of-create-certificate-next
             last-anchor-in-dag
             last-anchor-of-create-certificate-next))

  (defrule system-committed-redundantp-of-create-certificate-next
    (implies (and (system-committed-redundantp systate)
                  (system-signers-are-validators-p systate)
                  (system-signers-are-quorum-p systate)
                  (system-signers-have-author+round-p systate)
                  (system-unequivocal-certificates-p systate)
                  (system-last-anchor-present-p systate)
                  (system-previous-in-dag-p systate)
                  (fault-tolerant-p systate)
                  (create-certificate-possiblep cert systate)
                  (certificatep cert))
             (system-committed-redundantp
              (create-certificate-next cert systate)))
    :expand (system-committed-redundantp
             (create-certificate-next cert systate))
    :enable system-committed-redundantp-necc))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection system-committed-redundantp-of-receive-certificate-next
  :short "Preservation of the invariant by @('receive-certificate') events."
  :long
  (xdoc::topstring
   (xdoc::p
    "Neither the set of committed certificates nor the last committed anchor
     change under this event, so the proof is easy.
     It relies on @(tsee last-anchor-of-receive-certificate-next)."))

  (defrule validator-committed-redundantp-of-receive-certificate-next
    (implies (and (set::in val (correct-addresses systate))
                  (receive-certificate-possiblep msg systate)
                  (validator-committed-redundantp
                   (get-validator-state val systate)
                   (all-addresses systate)))
             (validator-committed-redundantp
              (get-validator-state val (receive-certificate-next msg systate))
              (all-addresses systate)))
    :enable (validator-committed-redundantp
             validator-state->last-of-receive-certificate-next
             validator-state->committed-of-receive-certificate-next
             last-anchor-of-receive-certificate-next))

  (defrule system-committed-redundantp-of-receive-certificate-next
    (implies (and (system-committed-redundantp systate)
                  (receive-certificate-possiblep msg systate))
             (system-committed-redundantp
              (receive-certificate-next msg systate)))
    :expand (system-committed-redundantp
             (receive-certificate-next msg systate))
    :enable system-committed-redundantp-necc))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection system-committed-redundantp-of-store-certificate-next
  :short "Preservation of the invariant by @('store-certificate') events."
  :long
  (xdoc::topstring
   (xdoc::p
    "Neither the set of committed certificates nor the last committed anchor
     change under this event, so the proof is easy.
     It relies on @(tsee last-anchor-of-store-certificate-next)."))

  (defrule validator-committed-redundantp-of-store-certificate-next
    (implies (and (system-signers-are-validators-p systate)
                  (system-signers-are-quorum-p systate)
                  (system-signers-have-author+round-p systate)
                  (system-unequivocal-certificates-p systate)
                  (system-last-anchor-present-p systate)
                  (system-previous-in-dag-p systate)
                  (set::in val (correct-addresses systate))
                  (store-certificate-possiblep cert val1 systate)
                  (validator-committed-redundantp
                   (get-validator-state val systate)
                   (all-addresses systate)))
             (validator-committed-redundantp
              (get-validator-state
               val (store-certificate-next cert val1 systate))
              (all-addresses systate)))
    :enable (validator-committed-redundantp
             system-last-anchor-present-p-necc
             validator-state->last-of-store-certificate-next
             validator-state->committed-of-store-certificate-next
             last-anchor-in-dag
             last-anchor-of-store-certificate-next))

  (defrule system-committed-redundantp-of-store-certificate-next
    (implies (and (system-committed-redundantp systate)
                  (system-signers-are-validators-p systate)
                  (system-signers-are-quorum-p systate)
                  (system-signers-have-author+round-p systate)
                  (system-unequivocal-certificates-p systate)
                  (system-last-anchor-present-p systate)
                  (system-previous-in-dag-p systate)
                  (store-certificate-possiblep cert val systate))
             (system-committed-redundantp
              (store-certificate-next cert val systate)))
    :expand (system-committed-redundantp
             (store-certificate-next cert val systate))
    :enable system-committed-redundantp-necc))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection system-committed-redundantp-of-advance-round-next
  :short "Preservation of the invariant by @('advance-round') events."
  :long
  (xdoc::topstring
   (xdoc::p
    "Neither the set of committed certificates nor the last committed anchor
     change under this event, so the proof is easy.
     It relies on @(tsee last-anchor-of-advance-round-next)."))

  (defrule validator-committed-redundantp-of-advance-round-next
    (implies (and (set::in val (correct-addresses systate))
                  (advance-round-possiblep val1 systate)
                  (validator-committed-redundantp
                   (get-validator-state val systate)
                   (all-addresses systate)))
             (validator-committed-redundantp
              (get-validator-state val (advance-round-next val1 systate))
              (all-addresses systate)))
    :enable (validator-committed-redundantp
             validator-state->last-of-advance-round-next
             validator-state->committed-of-advance-round-next
             last-anchor-of-advance-round-next))

  (defrule system-committed-redundantp-of-advance-round-next
    (implies (and (system-committed-redundantp systate)
                  (advance-round-possiblep val systate))
             (system-committed-redundantp
              (advance-round-next val systate)))
    :expand (system-committed-redundantp
             (advance-round-next val systate))
    :enable system-committed-redundantp-necc))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection system-committed-redundantp-of-commit-anchors-next
  :short "Preservation of the invariant by @('commit-anchors') events."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the only event that changes (both)
     the set of committed certificates and the last committed round and anchor.
     As proved in @(tsee new-committed-certs-of-extend-blockchain),
     when the blockchain is extended,
     the new set of committed certificates consists of
     the causal history of the last committed anchor
     plus the old set of committed certificates.
     But the latter is, by induction hypothesis of the invariant,
     the causal history of the old last committed anchors.
     The new last committed anchor has a path to the old one,
     and thus as proved in @(tsee certificate-causal-history-subset-when-path),
     the causal history of the new one is a superset of the old one.
     So when we take the union we get just the causal history of the new one,
     thus re-establishing the invariant in the new state."))

  (defrule validator-committed-redundantp-of-commit-anchors-next
    (implies (and (system-unequivocal-certificates-p systate)
                  (system-paths-to-last-anchor-p systate)
                  (system-previous-in-dag-p systate)
                  (system-dag-previous-are-quorum-p systate)
                  (system-authors-are-validators-p systate)
                  (system-last-is-even-p systate)
                  (system-last-anchor-present-p systate)
                  (system-last-anchor-voters-p systate)
                  (set::in val (correct-addresses systate))
                  (commit-anchors-possiblep val1 systate)
                  (validator-committed-redundantp
                   (get-validator-state val systate)
                   (all-addresses systate)))
             (validator-committed-redundantp
              (get-validator-state val (commit-anchors-next val1 systate))
              (all-addresses systate)))
    :enable (validator-committed-redundantp
             commit-anchors-possiblep
             commit-anchors-next
             commit-anchors-next-val
             nfix
             last-anchor
             system-unequivocal-dag-p-when-system-unequivocal-certificates-p
             system-unequivocal-dag-p-necc
             system-paths-to-last-anchor-p-when-other-invariants
             certificate-list-pathp-of-collect-anchors
             new-committed-certs-of-extend-blockchain
             cert-with-author+round-element
             system-paths-to-last-anchor-p-when-other-invariants
             set::expensive-rules
             evenp
             get-validator-state-of-update-validator-state
             certificate->author-of-cert-with-author+round
             certificate->round-of-cert-with-author+round
             car-of-collect-anchors)
    :use ((:instance
           dag-all-path-to-p-necc
           (cert (last-anchor (get-validator-state val systate)
                              (all-addresses systate)))
           (dag (validator-state->dag (get-validator-state val systate)))
           (cert1 (cert-with-author+round
                   (leader-at-round
                    (+ -1
                       (validator-state->round
                        (get-validator-state val systate)))
                    (all-addresses systate))
                   (+ -1
                      (validator-state->round
                       (get-validator-state val systate)))
                   (validator-state->dag (get-validator-state val systate)))))
          system-paths-to-last-anchor-p-necc
          system-last-anchor-present-p-necc
          system-last-is-even-p-necc
          (:instance
           certificate-causal-history-subset-when-path
           (cert (cert-with-author+round
                  (leader-at-round
                   (+ -1
                      (validator-state->round
                       (get-validator-state val systate)))
                   (all-addresses systate))
                  (+ -1
                     (validator-state->round (get-validator-state val systate)))
                  (validator-state->dag (get-validator-state val systate))))
           (author (leader-at-round
                    (validator-state->last (get-validator-state val systate))
                    (all-addresses systate)))
           (round (validator-state->last (get-validator-state val systate)))
           (dag (validator-state->dag (get-validator-state val systate))))))

  (defrule system-committed-redundantp-of-commit-anchors-next
    (implies (and (system-committed-redundantp systate)
                  (system-unequivocal-certificates-p systate)
                  (system-paths-to-last-anchor-p systate)
                  (system-previous-in-dag-p systate)
                  (system-dag-previous-are-quorum-p systate)
                  (system-authors-are-validators-p systate)
                  (system-last-is-even-p systate)
                  (system-last-anchor-present-p systate)
                  (system-last-anchor-voters-p systate)
                  (commit-anchors-possiblep val systate))
             (system-committed-redundantp
              (commit-anchors-next val systate)))
    :expand (system-committed-redundantp
             (commit-anchors-next val systate))
    :enable system-committed-redundantp-necc))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection system-committed-redundantp-of-timer-expires-next
  :short "Preservation of the invariant by @('timer-expires') events."
  :long
  (xdoc::topstring
   (xdoc::p
    "Neither the set of committed certificates nor the last committed anchor
     change under this event, so the proof is easy.
     It relies on @(tsee last-anchor-of-advance-round-next)."))

  (defrule validator-committed-redundantp-of-timer-expires-next
    (implies (and (set::in val (correct-addresses systate))
                  (timer-expires-possiblep val1 systate)
                  (validator-committed-redundantp
                   (get-validator-state val systate)
                   (all-addresses systate)))
             (validator-committed-redundantp
              (get-validator-state val (timer-expires-next val1 systate))
              (all-addresses systate)))
    :enable (validator-committed-redundantp
             validator-state->last-of-timer-expires-next
             validator-state->committed-of-timer-expires-next
             last-anchor-of-timer-expires-next))

  (defrule system-committed-redundantp-of-timer-expires-next
    (implies (and (system-committed-redundantp systate)
                  (timer-expires-possiblep val systate))
             (system-committed-redundantp
              (timer-expires-next val systate)))
    :expand (system-committed-redundantp
             (timer-expires-next val systate))
    :enable system-committed-redundantp-necc))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule system-committed-redundantp-of-event-next
  :short "Preservation of the invariant by all the events."
  :long
  (xdoc::topstring
   (xdoc::p
    "This follows from the theorems about the various kinds of events."))
  (implies (and (system-committed-redundantp systate)
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
                (fault-tolerant-p systate)
                (event-possiblep event systate))
           (system-committed-redundantp (event-next event systate)))
  :enable (event-possiblep
           event-next))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled system-committed-redundantp-of-events-next
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
        (system-committed-redundantp systate)
        (system-signers-are-validators-p systate)
        (system-previous-are-quorum-p systate)
        (system-last-anchor-present-p systate)
        (system-last-anchor-voters-p systate)
        (system-last-is-even-p systate)
        (system-previous-in-dag-p systate)
        (system-signers-are-quorum-p systate)
        (system-signers-have-author+round-p systate)
        (system-unequivocal-certificates-p systate)
        (events-possiblep events systate)
        (fault-tolerant-p systate))
   (and (system-committed-redundantp (events-next events systate))
        (system-signers-are-validators-p (events-next events systate))
        (system-previous-are-quorum-p (events-next events systate))
        (system-last-anchor-present-p (events-next events systate))
        (system-last-anchor-voters-p (events-next events systate))
        (system-last-is-even-p (events-next events systate))
        (system-previous-in-dag-p (events-next events systate))
        (system-signers-are-quorum-p (events-next events systate))
        (system-signers-have-author+round-p (events-next events systate))
        (system-unequivocal-certificates-p (events-next events systate))))
  :induct t
  :disable ((:e tau-system))
  :enable (events-next
           events-possiblep
           system-committed-redundantp-of-event-next
           system-signers-are-validators-p-of-event-next
           system-previous-are-quorum-p-of-event-next
           system-last-anchor-present-p-of-event-next
           system-last-anchor-voters-p-of-event-next
           system-last-is-even-p-of-event-next
           system-previous-in-dag-p-of-event-next
           system-signers-are-quorum-p-of-event-next
           system-signers-have-author+round-p-of-event-next
           system-unequivocal-certificates-p-of-event-next
           system-authors-are-validators-p-when-signers-are-validators
           system-dag-previous-are-quorum-p-when-all-previous-are-quorum
           system-paths-to-last-anchor-p-when-other-invariants
           system-unequivocal-dag-p-when-system-unequivocal-certificates-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled system-committed-redundantp-when-reachable
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
           (system-committed-redundantp (events-next events systate)))
  :disable ((:e tau-system))
  :enable (system-committed-redundantp-when-system-state-initp
           system-signers-are-validators-p-when-system-state-initp
           system-previous-are-quorum-p-when-system-state-initp
           system-last-anchor-present-p-when-system-state-initp
           system-last-anchor-voters-p-when-system-state-initp
           system-last-is-even-p-when-system-state-initp
           system-previous-in-dag-p-when-system-state-initp
           system-signers-are-quorum-p-when-system-state-initp
           system-signers-have-author+round-p-when-system-state-initp
           system-unequivocal-certificates-p-when-system-state-initp
           system-committed-redundantp-of-events-next))
