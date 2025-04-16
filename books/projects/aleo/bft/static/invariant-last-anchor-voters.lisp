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

(include-book "invariant-max-faulty")
(include-book "invariant-last-anchor-present")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ invariant-last-anchor-voters
  :parents (correctness)
  :short "Invariant that the last committed anchor
          has a certain number of voters in the subsequent round."
  :long
  (xdoc::topstring
   (xdoc::p
    "When the last committed round is not 0,
     there is always an anchor at that round:
     see @(see invariant-last-anchor-present).
     Furthermore, that anchor always has at least @($F + 1$) incoming edges
     from certificates in the immediately following rounds:
     those are the votes that are in fact necessary
     to commit that anchor.")
   (xdoc::p
    "Initially the last committed round is 0,
     so the invariant holds trivially.
     The only kind of events that changes the last committed round
     is @('commit-anchors'), whose preconditions establish the invariant.
     The only kinds of events that may change the voters
     are @('create-certificate') and @('store-certificate'),
     which add a certificate to the DAG:
     this certificate may or may not be a voter,
     but if it is, it can only increase the votes, never decrease them."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define validator-last-anchor-voters-p ((vstate validator-statep)
                                        (max-faulty natp)
                                        (vals address-setp))
  :guard (and (not (set::emptyp vals))
              (evenp (validator-state->last vstate))
              (or (equal (validator-state->last vstate) 0)
                  (last-anchor vstate vals)))
  :returns (yes/no booleanp)
  :short "Check if a validator state satisfies the invariant,
          at the validator state level."
  :long
  (xdoc::topstring
   (xdoc::p
    "Either the last committed round is 0,
     or the `yes' votes from the subsequent round
     are at least one more than the maximum number of faulty validators."))
  (b* (((validator-state vstate) vstate)
       ((when (equal vstate.last 0)) t)
       (voters (certs-with-round (1+ vstate.last) vstate.dag))
       ((mv yes &)
        (tally-leader-votes (leader-at-round vstate.last vals) voters)))
    (>= yes (1+ max-faulty))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk system-last-anchor-voters-p ((systate system-statep))
  :guard (and (not (set::emptyp (all-addresses systate)))
              (system-last-is-even-p systate)
              (system-last-anchor-present-p systate))
  :returns (yes/no booleanp)
  :short "Definition of the invariant:
          for each correct validator,
          if the last committed round is not 0,
          it has a sufficient number of votes for that anchor."
  (forall (val)
          (implies (set::in val (correct-addresses systate))
                   (validator-last-anchor-voters-p
                    (get-validator-state val systate)
                    (max-faulty systate)
                    (all-addresses systate))))
  :guard-hints
  (("Goal"
    :in-theory (enable system-last-is-even-p-necc
                       system-last-anchor-present-p-necc
                       in-all-addresses-when-in-correct-addresses))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule system-last-anchor-voters-p-when-system-state-initp
  :short "Establishment of the invariant:
          the invariant holds on any initial state."
  :long
  (xdoc::topstring
   (xdoc::p
    "The last committed round is initially 0, so the proof is trivial."))
  (implies (system-state-initp systate)
           (system-last-anchor-voters-p systate))
  :enable (system-last-anchor-voters-p
           validator-last-anchor-voters-p
           system-state-initp
           validator-init-when-system-initp
           validator-init))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection system-last-anchor-voters-p-of-create-certificate-next
  :short "Preservation of the invariant by @('create-certificate') events."
  :long
  (xdoc::topstring
   (xdoc::p
    "This kind of events leaves the last committed round unchanged,
     but it may add a certificate to the DAG.
     However, extending the DAG does not decrease any votes."))

  (defrule validator-last-anchor-voters-p-of-create-certificate-next
    (implies (and (set::in val (correct-addresses systate))
                  (certificatep cert)
                  (validator-last-anchor-voters-p
                   (get-validator-state val systate)
                   (max-faulty systate)
                   (all-addresses systate)))
             (validator-last-anchor-voters-p
              (get-validator-state val (create-certificate-next cert systate))
              (max-faulty systate)
              (all-addresses systate)))
    :enable (validator-last-anchor-voters-p
             certs-with-round-of-insert
             tally-leader-votes-of-insert
             validator-state->dag-of-create-certificate-next
             validator-state->last-of-create-certificate-next))

  (defrule system-last-anchor-voters-p-of-create-certificate-next
    (implies (and (system-last-anchor-voters-p systate)
                  (create-certificate-possiblep cert systate)
                  (certificatep cert))
             (system-last-anchor-voters-p
              (create-certificate-next cert systate)))
    :expand (system-last-anchor-voters-p
             (create-certificate-next cert systate))
    :enable system-last-anchor-voters-p-necc))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection system-last-anchor-voters-p-of-receive-certificate-next
  :short "Preservation of the invariant by @('receive-certificate') events."
  :long
  (xdoc::topstring
   (xdoc::p
    "This kind of events does not modify any last committed round or DAG."))

  (defrule validator-last-anchor-voters-p-of-receive-certificate-next
    (implies (and (set::in val (correct-addresses systate))
                  (receive-certificate-possiblep msg systate)
                  (validator-last-anchor-voters-p
                   (get-validator-state val systate)
                   (max-faulty systate)
                   (all-addresses systate)))
             (validator-last-anchor-voters-p
              (get-validator-state val (receive-certificate-next msg systate))
              (max-faulty systate)
              (all-addresses systate)))
    :enable (validator-last-anchor-voters-p
             validator-state->dag-of-receive-certificate-next
             validator-state->last-of-receive-certificate-next))

  (defrule system-last-anchor-voters-p-of-receive-certificate-next
    (implies (and (system-last-anchor-voters-p systate)
                  (receive-certificate-possiblep msg systate))
             (system-last-anchor-voters-p
              (receive-certificate-next msg systate)))
    :expand (system-last-anchor-voters-p
             (receive-certificate-next msg systate))
    :enable system-last-anchor-voters-p-necc))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection system-last-anchor-voters-p-of-store-certificate-next
  :short "Preservation of the invariant by @('store-certificate') events."
  :long
  (xdoc::topstring
   (xdoc::p
    "This kind of events leaves the last committed round unchanged,
     but it may add a certificate to the DAG.
     However, extending the DAG does not decrease any votes."))

  (defrule validator-last-anchor-voters-p-of-store-certificate-next
    (implies (and (set::in val (correct-addresses systate))
                  (store-certificate-possiblep cert val1 systate)
                  (certificatep cert)
                  (validator-last-anchor-voters-p
                   (get-validator-state val systate)
                   (max-faulty systate)
                   (all-addresses systate)))
             (validator-last-anchor-voters-p
              (get-validator-state val
                                   (store-certificate-next cert val1 systate))
              (max-faulty systate)
              (all-addresses systate)))
    :enable (validator-last-anchor-voters-p
             certs-with-round-of-insert
             tally-leader-votes-of-insert
             validator-state->dag-of-store-certificate-next
             validator-state->last-of-store-certificate-next))

  (defrule system-last-anchor-voters-p-of-store-certificate-next
    (implies (and (system-last-anchor-voters-p systate)
                  (store-certificate-possiblep cert val1 systate)
                  (certificatep cert))
             (system-last-anchor-voters-p
              (store-certificate-next cert val1 systate)))
    :expand (system-last-anchor-voters-p
             (store-certificate-next cert val1 systate))
    :enable system-last-anchor-voters-p-necc))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection system-last-anchor-voters-p-of-advance-round-next
  :short "Preservation of the invariant by @('advance-round') events."
  :long
  (xdoc::topstring
   (xdoc::p
    "This kind of events does not modify any last committed round or DAG."))

  (defrule validator-last-anchor-voters-p-of-advance-round-next
    (implies (and (set::in val (correct-addresses systate))
                  (advance-round-possiblep val1 systate)
                  (validator-last-anchor-voters-p
                   (get-validator-state val systate)
                   (max-faulty systate)
                   (all-addresses systate)))
             (validator-last-anchor-voters-p
              (get-validator-state val
                                   (advance-round-next val1 systate))
              (max-faulty systate)
              (all-addresses systate)))
    :enable (validator-last-anchor-voters-p
             validator-state->dag-of-advance-round-next
             validator-state->last-of-advance-round-next))

  (defrule system-last-anchor-voters-p-of-advance-round-next
    (implies (and (system-last-anchor-voters-p systate)
                  (advance-round-possiblep val1 systate))
             (system-last-anchor-voters-p
              (advance-round-next val1 systate)))
    :expand (system-last-anchor-voters-p
             (advance-round-next val1 systate))
    :enable system-last-anchor-voters-p-necc))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection system-last-anchor-voters-p-of-commit-anchors-next
  :short "Preservation of the invariant by @('commit-anchors') events."
  :long
  (xdoc::topstring
   (xdoc::p
    "The validator that commits the anchors changes its last committed round,
     but it does so under @(tsee commit-anchors-possiblep),
     which guarantees that there are enough `yes' votes.
     The other validators keep the same last committed rounds and DAGs."))

  (defrule validator-last-anchor-voters-p-of-commit-anchors-next
    (implies (and (set::in val (correct-addresses systate))
                  (commit-anchors-possiblep val1 systate)
                  (validator-last-anchor-voters-p
                   (get-validator-state val systate)
                   (max-faulty systate)
                   (all-addresses systate)))
             (validator-last-anchor-voters-p
              (get-validator-state val
                                   (commit-anchors-next val1 systate))
              (max-faulty systate)
              (all-addresses systate)))
    :enable (validator-last-anchor-voters-p
             fix
             commit-anchors-possiblep
             validator-state->dag-of-commit-anchors-next
             validator-state->last-of-commit-anchors-next))

  (defrule system-last-anchor-voters-p-of-commit-anchors-next
    (implies (and (system-last-anchor-voters-p systate)
                  (commit-anchors-possiblep val1 systate))
             (system-last-anchor-voters-p
              (commit-anchors-next val1 systate)))
    :expand (system-last-anchor-voters-p
             (commit-anchors-next val1 systate))
    :enable system-last-anchor-voters-p-necc))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection system-last-anchor-voters-p-of-timer-expires-next
  :short "Preservation of the invariant by @('timer-expires') events."
  :long
  (xdoc::topstring
   (xdoc::p
    "This kind of events does not modify any last committed round or DAG."))

  (defrule validator-last-anchor-voters-p-of-timer-expires-next
    (implies (and (set::in val (correct-addresses systate))
                  (timer-expires-possiblep val1 systate)
                  (validator-last-anchor-voters-p
                   (get-validator-state val systate)
                   (max-faulty systate)
                   (all-addresses systate)))
             (validator-last-anchor-voters-p
              (get-validator-state val
                                   (timer-expires-next val1 systate))
              (max-faulty systate)
              (all-addresses systate)))
    :enable (validator-last-anchor-voters-p
             validator-state->dag-of-timer-expires-next
             validator-state->last-of-timer-expires-next))

  (defrule system-last-anchor-voters-p-of-timer-expires-next
    (implies (and (system-last-anchor-voters-p systate)
                  (timer-expires-possiblep val1 systate))
             (system-last-anchor-voters-p
              (timer-expires-next val1 systate)))
    :expand (system-last-anchor-voters-p
             (timer-expires-next val1 systate))
    :enable system-last-anchor-voters-p-necc))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule system-last-anchor-voters-p-of-event-next
  :short "Preservation of the invariant by all events."
  :long
  (xdoc::topstring
   (xdoc::p
    "This follows from the theorems about the various kinds of events."))
  (implies (and (system-last-anchor-voters-p systate)
                (event-possiblep event systate))
           (system-last-anchor-voters-p
            (event-next event systate)))
  :enable (event-possiblep
           event-next))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled system-last-anchor-voters-p-of-events-next
  :short "Preservation of the invariant by every sequence of events."
  (implies (and (system-statep systate)
                (system-last-anchor-voters-p systate)
                (events-possiblep events systate))
           (system-last-anchor-voters-p (events-next events systate)))
  :induct t
  :disable ((:e tau-system))
  :enable (events-next
           events-possiblep
           system-last-anchor-voters-p-of-event-next))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled system-last-anchor-voters-p-when-reachable
  :short "The invariant holds in every reachable state."
  :long
  (xdoc::topstring
   (xdoc::p
    "Reachable states are characterized by an initial state and
     a sequence of possible events from that initial state."))
  (implies (and (system-statep systate)
                (system-state-initp systate)
                (events-possiblep events systate))
           (system-last-anchor-voters-p (events-next events systate)))
  :disable ((:e tau-system))
  :enable (system-last-anchor-voters-p-when-system-state-initp
           system-last-anchor-voters-p-of-events-next))
