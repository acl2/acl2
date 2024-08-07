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
     THe only kind of event that modifies the last committed round
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
              (not (set::emptyp (validator-addresses systate))))
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
                                           (validator-addresses systate))))))
  :guard-hints (("Goal" :in-theory (enable system-last-is-even-p-necc))))

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
                               (validator-addresses systate)))
             (last-anchor (get-validator-state
                           val (create-certificate-next cert systate))
                          (validator-addresses systate)))
    :enable last-anchor)

  (defrule system-last-anchor-present-p-of-create-certificate-next
    (implies (and (system-last-anchor-present-p systate)
                  (create-certificate-possiblep cert systate)
                  (certificatep cert))
             (system-last-anchor-present-p
              (create-certificate-next cert systate)))
    :expand (system-last-anchor-present-p
             (create-certificate-next cert systate))
    :enable system-last-anchor-present-p-necc))

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
                               (validator-addresses systate)))
             (last-anchor (get-validator-state
                           val (receive-certificate-next msg systate))
                          (validator-addresses systate)))
    :enable last-anchor)

  (defrule system-last-anchor-present-p-of-receive-certificate-next
    (implies (and (system-last-anchor-present-p systate)
                  (receive-certificate-possiblep msg systate))
             (system-last-anchor-present-p
              (receive-certificate-next msg systate)))
    :expand (system-last-anchor-present-p
             (receive-certificate-next msg systate))
    :enable system-last-anchor-present-p-necc))

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
                               (validator-addresses systate)))
             (last-anchor (get-validator-state
                           val (store-certificate-next cert val1 systate))
                          (validator-addresses systate)))
    :enable last-anchor)

  (defrule system-last-anchor-present-p-of-store-certificate-next
    (implies (and (system-last-anchor-present-p systate)
                  (store-certificate-possiblep cert val systate))
             (system-last-anchor-present-p
              (store-certificate-next cert val systate)))
    :expand (system-last-anchor-present-p
             (store-certificate-next cert val systate))
    :enable system-last-anchor-present-p-necc))

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
                               (validator-addresses systate)))
             (last-anchor (get-validator-state
                           val (advance-round-next val1 systate))
                          (validator-addresses systate)))
    :enable last-anchor)

  (defrule system-last-anchor-present-p-of-advance-round-next
    (implies (and (system-last-anchor-present-p systate)
                  (advance-round-possiblep val systate))
             (system-last-anchor-present-p
              (advance-round-next val systate)))
    :expand (system-last-anchor-present-p
             (advance-round-next val systate))
    :enable system-last-anchor-present-p-necc))

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
                                   (validator-addresses systate))))
             (last-anchor (get-validator-state
                           val (commit-anchors-next val1 systate))
                          (validator-addresses systate)))
    :enable (last-anchor
             commit-anchors-possiblep))

  (defrule system-last-anchor-present-p-of-commit-anchors-next
    (implies (and (system-last-anchor-present-p systate)
                  (commit-anchors-possiblep val systate))
             (system-last-anchor-present-p
              (commit-anchors-next val systate)))
    :expand (system-last-anchor-present-p
             (commit-anchors-next val systate))
    :enable system-last-anchor-present-p-necc))

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
                               (validator-addresses systate)))
             (last-anchor (get-validator-state
                           val (timer-expires-next val1 systate))
                          (validator-addresses systate)))
    :enable last-anchor)

  (defrule system-last-anchor-present-p-of-timer-expires-next
    (implies (and (system-last-anchor-present-p systate)
                  (timer-expires-possiblep val systate))
             (system-last-anchor-present-p
              (timer-expires-next val systate)))
    :expand (system-last-anchor-present-p
             (timer-expires-next val systate))
    :enable system-last-anchor-present-p-necc))

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
