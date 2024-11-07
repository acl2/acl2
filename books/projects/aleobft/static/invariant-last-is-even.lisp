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

(include-book "invariant-addresses")

(include-book "std/util/define-sk" :dir :system)

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ invariant-last-is-even
  :parents (correctness)
  :short "Invariant that the last committed round is always even."
  :long
  (xdoc::topstring
   (xdoc::p
    "Initially, this validator state component is 0, which is even.
     The only event that updates this state component is @('commit-anchors'),
     which sets this state component to one less than the current round,
     where the current round is odd (see @(tsee commit-anchors-possiblep))."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk system-last-is-even-p ((systate system-statep))
  :returns (yes/no booleanp)
  :short "Definition of the invariant:
          the last committed round in each correct validator state is even."
  (forall (val)
          (implies (set::in val (correct-addresses systate))
                   (evenp (validator-state->last
                           (get-validator-state val systate)))))
  :guard-hints
  (("Goal" :in-theory (enable in-all-addresses-when-in-correct-addresses))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule system-last-is-even-p-when-system-state-initp
  :short "Establishment of the invariant:
          the invariant holds on any initial state."
  :long
  (xdoc::topstring
   (xdoc::p
    "Initially the last committed round is 0, which is even.
     (In fact, 0 is not a valid round,
     so 0 indicates no actual rounds committed yet.)"))
  (implies (system-state-initp systate)
           (system-last-is-even-p systate))
  :enable (system-last-is-even-p
           system-state-initp
           validator-init-when-system-initp
           validator-init))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule system-last-is-even-p-of-create-certificate-next
  :short "Preservation of the invariant by @('create-certificate') events."
  :long
  (xdoc::topstring
   (xdoc::p
    "This kind of event does not change the last committed round,
     so it remains even if it was even before."))
  (implies (and (system-last-is-even-p systate)
                (create-certificate-possiblep cert systate))
           (system-last-is-even-p
            (create-certificate-next cert systate)))
  :expand (system-last-is-even-p
           (create-certificate-next cert systate))
  :enable (system-last-is-even-p-necc
           validator-state->last-of-create-certificate-next))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule system-last-is-even-p-of-receive-certificate-next
  :short "Preservation of the invariant by @('receive-certificate') events."
  :long
  (xdoc::topstring
   (xdoc::p
    "This kind of event does not change the last committed round,
     so it remains even if it was even before."))
  (implies (and (system-last-is-even-p systate)
                (receive-certificate-possiblep msg systate))
           (system-last-is-even-p
            (receive-certificate-next msg systate)))
  :expand (system-last-is-even-p
           (receive-certificate-next msg systate))
  :enable (system-last-is-even-p-necc
           validator-state->last-of-receive-certificate-next))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule system-last-is-even-p-of-store-certificate-next
  :short "Preservation of the invariant by @('store-certificate') events."
  :long
  (xdoc::topstring
   (xdoc::p
    "This kind of event does not change the last committed round,
     so it remains even if it was even before."))
  (implies (and (system-last-is-even-p systate)
                (store-certificate-possiblep cert val systate))
           (system-last-is-even-p
            (store-certificate-next cert val systate)))
  :expand (system-last-is-even-p
           (store-certificate-next cert val systate))
  :enable (system-last-is-even-p-necc
           validator-state->last-of-store-certificate-next))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule system-last-is-even-p-of-advance-round-next
  :short "Preservation of the invariant by @('advance-round') events."
  :long
  (xdoc::topstring
   (xdoc::p
    "This kind of event does not change the last committed round,
     so it remains even if it was even before."))
  (implies (and (system-last-is-even-p systate)
                (advance-round-possiblep val systate))
           (system-last-is-even-p
            (advance-round-next val systate)))
  :expand (system-last-is-even-p
           (advance-round-next val systate))
  :enable (system-last-is-even-p-necc
           validator-state->last-of-advance-round-next))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule system-last-is-even-p-of-commit-anchors-next
  :short "Preservation of the invariant by @('commit-anchors') events."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the only kind of events that changes
     the last committed round.
     It changes it to one less than the current-round,
     which @(tsee commit-anchors-possiblep) requires to be odd.
     So one minus the current round is even."))
  (implies (and (system-last-is-even-p systate)
                (commit-anchors-possiblep val systate))
           (system-last-is-even-p
            (commit-anchors-next val systate)))
  :expand (system-last-is-even-p
           (commit-anchors-next val systate))
  :enable (system-last-is-even-p-necc
           commit-anchors-possiblep
           validator-state->last-of-commit-anchors-next)
  :prep-lemmas
  ((defrule lemma
     (implies (and (natp x)
                   (not (evenp x)))
              (evenp (1- x)))
     :enable evenp
     :prep-books ((include-book "arithmetic-3/top" :dir :system)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule system-last-is-even-p-of-timer-expires-next
  :short "Preservation of the invariant by @('timer-expires') events."
  :long
  (xdoc::topstring
   (xdoc::p
    "This kind of event does not change the last committed round,
     so it remains even if it was even before."))
  (implies (and (system-last-is-even-p systate)
                (timer-expires-possiblep val systate))
           (system-last-is-even-p
            (timer-expires-next val systate)))
  :expand (system-last-is-even-p
           (timer-expires-next val systate))
  :enable (system-last-is-even-p-necc
           validator-state->last-of-timer-expires-next))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule system-last-is-even-p-of-event-next
  :short "Preservation of the invariant by all events."
  :long
  (xdoc::topstring
   (xdoc::p
    "This follows from the theorems about the various kinds of events."))
  (implies (and (system-last-is-even-p systate)
                (event-possiblep event systate))
           (system-last-is-even-p (event-next event systate)))
  :enable (event-possiblep
           event-next))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled system-last-is-even-p-of-events-next
  :short "Preservation of the invariant by every sequence of events."
  (implies (and (system-statep systate)
                (system-last-is-even-p systate)
                (events-possiblep events systate))
           (system-last-is-even-p (events-next events systate)))
  :induct t
  :disable ((:e tau-system))
  :enable (events-next
           events-possiblep
           system-last-is-even-p-of-event-next))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled system-last-is-even-p-when-reachable
  :short "The invariant holds in every reachable state."
  :long
  (xdoc::topstring
   (xdoc::p
    "Reachable states are characterized by an initial state and
     a sequence of possible events from that initial state."))
  (implies (and (system-statep systate)
                (system-state-initp systate)
                (events-possiblep events systate))
           (system-last-is-even-p (events-next events systate)))
  :disable ((:e tau-system))
  :enable (system-last-is-even-p-when-system-state-initp
           system-last-is-even-p-of-events-next))
