; Aleo Library
;
; Copyright (C) 2024 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOBFT-STATIC")

(include-book "invariant-addresses")

(include-book "std/util/define-sk" :dir :system)

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ invariant-last-before-current
  :parents (correctness)
  :short "Invariant that the current round is always ahead of
          the last committed round."
  :long
  (xdoc::topstring
   (xdoc::p
    "Initially each validator is in round 1,
     while the last committed round is 0
     (meaning no anchors are committed yet),
     so the inequality holds.")
   (xdoc::p
    "The only kind of event that changes the last committed round number
     is @('commit-anchors'), which sets the last committed round
     to one less than the current round, so the inequality holds.")
   (xdoc::p
    "The only kinds of event that change the current round
     are @('store-certificate') and @('advance-round')
     (the former may not actually change it).
     Both kinds of events increase the current round,
     so if the inequality held before, it still holds."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk system-last-before-current-p ((systate system-statep))
  :returns (yes/no booleanp)
  :short "Definition of the invariant:
          the last committed round of each correct validator
          is less than the current round of the validator."
  (forall (val)
          (implies (set::in val (correct-addresses systate))
                   (b* (((validator-state vstate)
                         (get-validator-state val systate)))
                     (< vstate.last vstate.round)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule system-last-before-current-p-when-system-state-initp
  :short "Establishment of the invariant:
          the invariant holds on any initial state."
  :long
  (xdoc::topstring
   (xdoc::p
    "This reduces to the inequality @('0 < 1')."))
  (implies (system-state-initp systate)
           (system-last-before-current-p systate))
  :enable (system-last-before-current-p
           system-state-initp
           validator-init))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule system-last-before-current-p-of-create-certificate-next
  :short "Preservation of the invariant by @('create-certificate') events."
  :long
  (xdoc::topstring
   (xdoc::p
    "This kind of event does not change
     the current round or the last committed round,
     so the inequality is preserved from the previous state."))
  (implies (and (system-last-before-current-p systate)
                (create-certificate-possiblep cert systate)
                (certificatep cert))
           (system-last-before-current-p
            (create-certificate-next cert systate)))
  :expand (system-last-before-current-p
           (create-certificate-next cert systate))
  :enable system-last-before-current-p-necc)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule system-last-before-current-p-of-receive-certificate-next
  :short "Preservation of the invariant by @('receive-certificate') events."
  :long
  (xdoc::topstring
   (xdoc::p
    "This kind of event does not change
     the current round or the last committed round,
     so the inequality is preserved from the previous state."))
  (implies (and (system-last-before-current-p systate)
                (receive-certificate-possiblep msg systate))
           (system-last-before-current-p
            (receive-certificate-next msg systate)))
  :expand (system-last-before-current-p
           (receive-certificate-next msg systate))
  :enable system-last-before-current-p-necc)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule system-last-before-current-p-of-store-certificate-next
  :short "Preservation of the invariant by @('store-certificate') events."
  :long
  (xdoc::topstring
   (xdoc::p
    "This kind of event may increase the current round number,
     so it cannot violate the inequality if it held before."))
  (implies (and (system-last-before-current-p systate)
                (store-certificate-possiblep cert val systate))
           (system-last-before-current-p
            (store-certificate-next cert val systate)))
  :expand (system-last-before-current-p
           (store-certificate-next cert val systate))
  :use (:instance system-last-before-current-p-necc
                  (val (system-last-before-current-p-witness
                        (store-certificate-next cert val systate)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule system-last-before-current-p-of-advance-round-next
  :short "Preservation of the invariant by @('advance-round') events."
  :long
  (xdoc::topstring
   (xdoc::p
    "This kind of event increases the current round number,
     so it cannot violate the inequality if it held before."))
  (implies (and (system-last-before-current-p systate)
                (advance-round-possiblep val systate))
           (system-last-before-current-p
            (advance-round-next val systate)))
  :expand (system-last-before-current-p
           (advance-round-next val systate))
  :use (:instance system-last-before-current-p-necc
                  (val (system-last-before-current-p-witness
                        (advance-round-next val systate)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule system-last-before-current-p-of-commit-anchors-next
  :short "Preservation of the invariant by @('commit-anchors') events."
  :long
  (xdoc::topstring
   (xdoc::p
    "This kind of event modifies the last committed round number,
     but it sets it to one less than the current round,
     so the inequality holds."))
  (implies (and (system-last-before-current-p systate)
                (commit-anchors-possiblep val systate))
           (system-last-before-current-p
            (commit-anchors-next val systate)))
  :expand (system-last-before-current-p
           (commit-anchors-next val systate))
  :enable system-last-before-current-p-necc)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule system-last-before-current-p-of-timer-expires-next
  :short "Preservation of the invariant by @('timer-expires') events."
  :long
  (xdoc::topstring
   (xdoc::p
    "This kind of event does not change
     the current round or the last committed round,
     so the inequality is preserved from the previous state."))
  (implies (and (system-last-before-current-p systate)
                (timer-expires-possiblep val systate))
           (system-last-before-current-p
            (timer-expires-next val systate)))
  :expand (system-last-before-current-p
           (timer-expires-next val systate))
  :enable system-last-before-current-p-necc)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule system-last-before-current-p-of-event-next
  :short "Preservation of the invariant by all events."
  :long
  (xdoc::topstring
   (xdoc::p
    "This follows from the theorems about the various kinds of events."))
  (implies (and (system-last-before-current-p systate)
                (event-possiblep event systate))
           (system-last-before-current-p (event-next event systate)))
  :enable (event-possiblep
           event-next))
