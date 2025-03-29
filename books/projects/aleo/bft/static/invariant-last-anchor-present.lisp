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

(include-book "invariant-last-is-even")
(include-book "operations-anchors")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ invariant-last-anchor-present
  :parents (correctness)
  :short "Invariant that the last committed round, if non-zero,
          has an anchor certificate."
  :long
  (xdoc::topstring
   (xdoc::p
    "Initially the last committed round is 0, so the invariant trivially holds.
     The only kind of event that modifies the last committed round
     is @('commit-anchors'), which is conditioned under the fact that
     there is a certificate anchor for the new last committed round;
     see @(tsee commit-anchors-possiblep).
     The other events do not change the last committed round,
     and certificates are never removed from the DAG,
     so if there was an anchor at the last committed round before the event,
     there is still one after the event."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk system-last-anchor-present-p ((systate system-statep))
  :guard (and (system-last-is-even-p systate)
              (not (set::emptyp (all-addresses systate))))
  :returns (yes/no booleanp)
  :short "Definition of the invariant:
          for each correct validator,
          if the last committed round is not 0,
          there is an anchor at that round."
  (forall (val)
          (implies (set::in val (correct-addresses systate))
                   (b* ((vstate (get-validator-state val systate)))
                     (implies (not (equal (validator-state->last vstate) 0))
                              (last-anchor vstate
                                           (all-addresses systate))))))
  :guard-hints
  (("Goal" :in-theory (enable system-last-is-even-p-necc
                              in-all-addresses-when-in-correct-addresses))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule system-last-anchor-present-p-when-system-state-initp
  :short "Establishment of the invariant:
          the invariant holds on any initial state."
  :long
  (xdoc::topstring
   (xdoc::p
    "The last committed round is initially 0, so the proof is trivial."))
  (implies (system-state-initp systate)
           (system-last-anchor-present-p systate))
  :enable (system-last-anchor-present-p
           system-state-initp
           validator-init-when-system-initp
           validator-init))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection system-last-anchor-present-p-of-create-certificate-next
  :short "Preservation of the invariant by @('create-certificate') events."
  :long
  (xdoc::topstring
   (xdoc::p
    "This kind of events does not modify any last committed round.
     It adds a certificate to the DAG of the certificate author,
     and leaves the other DAGs unchanged."))

  (defrule last-anchor-not-nil-of-create-certificate-next
    (implies (and (set::in val (correct-addresses systate))
                  (certificatep cert)
                  (last-anchor (get-validator-state val systate)
                               (all-addresses systate)))
             (last-anchor (get-validator-state
                           val (create-certificate-next cert systate))
                          (all-addresses systate)))
    :enable (last-anchor
             cert-with-author+round-of-insert-iff
             validator-state->dag-of-create-certificate-next
             validator-state->last-of-create-certificate-next))

  (defrule system-last-anchor-present-p-of-create-certificate-next
    (implies (and (system-last-anchor-present-p systate)
                  (create-certificate-possiblep cert systate)
                  (certificatep cert))
             (system-last-anchor-present-p
              (create-certificate-next cert systate)))
    :expand (system-last-anchor-present-p
             (create-certificate-next cert systate))
    :enable (system-last-anchor-present-p-necc
             validator-state->last-of-create-certificate-next)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection system-last-anchor-present-p-of-receive-certificate-next
  :short "Preservation of the invariant by @('receive-certificate') events."
  :long
  (xdoc::topstring
   (xdoc::p
    "This kind of events does not modify any last committed round or DAG."))

  (defrule last-anchor-not-nil-of-receive-certificate-next
    (implies (and (set::in val (correct-addresses systate))
                  (receive-certificate-possiblep msg systate)
                  (last-anchor (get-validator-state val systate)
                               (all-addresses systate)))
             (last-anchor (get-validator-state
                           val (receive-certificate-next msg systate))
                          (all-addresses systate)))
    :enable (last-anchor
             validator-state->dag-of-receive-certificate-next
             validator-state->last-of-receive-certificate-next))

  (defrule system-last-anchor-present-p-of-receive-certificate-next
    (implies (and (system-last-anchor-present-p systate)
                  (receive-certificate-possiblep msg systate))
             (system-last-anchor-present-p
              (receive-certificate-next msg systate)))
    :expand (system-last-anchor-present-p
             (receive-certificate-next msg systate))
    :enable (system-last-anchor-present-p-necc
             validator-state->last-of-receive-certificate-next)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection system-last-anchor-present-p-of-store-certificate-next
  :short "Preservation of the invariant by @('store-certificate') events."
  :long
  (xdoc::topstring
   (xdoc::p
    "This kind of events does not modify any last committed round.
     It adds a certificate to the DAG of a validator,
     and leaves the other DAGs unchanged."))

  (defrule last-anchor-not-nil-of-store-certificate-next
    (implies (and (set::in val (correct-addresses systate))
                  (store-certificate-possiblep cert val1 systate)
                  (last-anchor (get-validator-state val systate)
                               (all-addresses systate)))
             (last-anchor (get-validator-state
                           val (store-certificate-next cert val1 systate))
                          (all-addresses systate)))
    :enable (last-anchor
             cert-with-author+round-of-insert-iff
             validator-state->dag-of-store-certificate-next
             validator-state->last-of-store-certificate-next))

  (defrule system-last-anchor-present-p-of-store-certificate-next
    (implies (and (system-last-anchor-present-p systate)
                  (store-certificate-possiblep cert val systate))
             (system-last-anchor-present-p
              (store-certificate-next cert val systate)))
    :expand (system-last-anchor-present-p
             (store-certificate-next cert val systate))
    :enable (system-last-anchor-present-p-necc
             validator-state->last-of-store-certificate-next)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection system-last-anchor-present-p-of-advance-round-next
  :short "Preservation of the invariant by @('advance-round') events."
  :long
  (xdoc::topstring
   (xdoc::p
    "This kind of events does not modify any last committed round or DAG."))

  (defrule last-anchor-not-nil-of-advance-round-next
    (implies (and (set::in val (correct-addresses systate))
                  (advance-round-possiblep val1 systate)
                  (last-anchor (get-validator-state val systate)
                               (all-addresses systate)))
             (last-anchor (get-validator-state
                           val (advance-round-next val1 systate))
                          (all-addresses systate)))
    :enable (last-anchor
             validator-state->dag-of-advance-round-next
             validator-state->last-of-advance-round-next))

  (defrule system-last-anchor-present-p-of-advance-round-next
    (implies (and (system-last-anchor-present-p systate)
                  (advance-round-possiblep val systate))
             (system-last-anchor-present-p
              (advance-round-next val systate)))
    :expand (system-last-anchor-present-p
             (advance-round-next val systate))
    :enable (system-last-anchor-present-p-necc
             validator-state->last-of-advance-round-next)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection system-last-anchor-present-p-of-commit-anchors-next
  :short "Preservation of the invariant by @('commit-anchors') events."
  :long
  (xdoc::topstring
   (xdoc::p
    "The validator that commits the anchors changes its last committed round,
     but it does so under @(tsee commit-anchors-possiblep),
     which guarantees that there is an anchor at that round.
     The other validators keep the same last committed rounds and DAGs."))

  (defrule last-anchor-not-nil-of-commit-anchors-next
    (implies (and (set::in val (correct-addresses systate))
                  (commit-anchors-possiblep val1 systate)
                  (or (equal val val1)
                      (last-anchor (get-validator-state val systate)
                                   (all-addresses systate))))
             (last-anchor (get-validator-state
                           val (commit-anchors-next val1 systate))
                          (all-addresses systate)))
    :enable (last-anchor
             commit-anchors-possiblep
             validator-state->dag-of-commit-anchors-next
             validator-state->last-of-commit-anchors-next))

  (defrule system-last-anchor-present-p-of-commit-anchors-next
    (implies (and (system-last-anchor-present-p systate)
                  (commit-anchors-possiblep val systate))
             (system-last-anchor-present-p
              (commit-anchors-next val systate)))
    :expand (system-last-anchor-present-p
             (commit-anchors-next val systate))
    :enable (system-last-anchor-present-p-necc
             validator-state->last-of-commit-anchors-next)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection system-last-anchor-present-p-of-timer-expires-next
  :short "Preservation of the invariant by @('timer-expires') events."
  :long
  (xdoc::topstring
   (xdoc::p
    "This kind of events does not modify any last committed round or DAG."))

  (defrule last-anchor-not-nil-of-timer-expires-next
    (implies (and (set::in val (correct-addresses systate))
                  (timer-expires-possiblep val1 systate)
                  (last-anchor (get-validator-state val systate)
                               (all-addresses systate)))
             (last-anchor (get-validator-state
                           val (timer-expires-next val1 systate))
                          (all-addresses systate)))
    :enable (last-anchor
             validator-state->dag-of-timer-expires-next
             validator-state->last-of-timer-expires-next))

  (defrule system-last-anchor-present-p-of-timer-expires-next
    (implies (and (system-last-anchor-present-p systate)
                  (timer-expires-possiblep val systate))
             (system-last-anchor-present-p
              (timer-expires-next val systate)))
    :expand (system-last-anchor-present-p
             (timer-expires-next val systate))
    :enable (system-last-anchor-present-p-necc
             validator-state->last-of-timer-expires-next)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule system-last-anchor-present-p-of-event-next
  :short "Preservation of the invariant by all events."
  :long
  (xdoc::topstring
   (xdoc::p
    "This follows from the theorems about the various kinds of events."))
  (implies (and (system-last-anchor-present-p systate)
                (event-possiblep event systate))
           (system-last-anchor-present-p
            (event-next event systate)))
  :enable (event-possiblep
           event-next))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled system-last-anchor-present-p-of-events-next
  :short "Preservation of the invariant by every sequence of events."
  (implies (and (system-statep systate)
                (system-last-anchor-present-p systate)
                (events-possiblep events systate))
           (system-last-anchor-present-p (events-next events systate)))
  :induct t
  :disable ((:e tau-system))
  :enable (events-next
           events-possiblep
           system-last-anchor-present-p-of-event-next))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled system-last-anchor-present-p-when-reachable
  :short "The invariant holds in every reachable state."
  :long
  (xdoc::topstring
   (xdoc::p
    "Reachable states are characterized by an initial state and
     a sequence of possible events from that initial state."))
  (implies (and (system-statep systate)
                (system-state-initp systate)
                (events-possiblep events systate))
           (system-last-anchor-present-p (events-next events systate)))
  :disable ((:e tau-system))
  :enable (system-last-anchor-present-p-when-system-state-initp
           system-last-anchor-present-p-of-events-next))
