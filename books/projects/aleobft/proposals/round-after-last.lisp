; AleoBFT Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOBFT-PROPOSALS")

(include-book "reachability")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ round-after-last
  :parents (correctness)
  :short "Invariant that the current round of each validator
          is always greater than the last committed round of the validator."
  :long
  (xdoc::topstring
   (xdoc::p
    "Initially, the current round is 1 and the last committed round is 0.
     The only event that changes the current round is @('advance'),
     which increments it by one, while not changing the last committed round;
     thus, this event preserves the invariant.
     The only event that changes the last committed round is @('commit'),
     but it sets it to the even number just before
     the odd current round number,
     so the invariant is re-established."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk round-after-last-p ((systate system-statep))
  :returns (yes/no booleanp)
  :short "Definition of the invariant."
  (forall (val)
          (implies (set::in val (correct-addresses systate))
                   (b* (((validator-state vstate)
                         (get-validator-state val systate)))
                     (> vstate.round vstate.last))))
  ///
  (fty::deffixequiv-sk round-after-last-p
    :args ((systate system-statep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled round-after-last-p-when-init
  :short "Establishment of the invariant in the initial states."
  (implies (system-initp systate)
           (round-after-last-p systate))
  :enable (round-after-last-p
           system-initp
           system-validators-initp-necc
           validator-init))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection round-after-last-p-of-next
  :short "Preservation of the invariant by single transitions."

  (defruled round-after-last-p-of-propose-next
    (implies (round-after-last-p systate)
             (round-after-last-p (propose-next prop dests systate)))
    :enable (round-after-last-p
             round-after-last-p-necc))

  (defruled round-after-last-p-of-endorse-next
    (implies (round-after-last-p systate)
             (round-after-last-p (endorse-next prop endor systate)))
    :enable (round-after-last-p
             round-after-last-p-necc))

  (defruled round-after-last-p-of-augment-next
    (implies (and (augment-possiblep prop endor systate)
                  (round-after-last-p systate))
             (round-after-last-p (augment-next prop endor systate)))
    :enable (round-after-last-p
             round-after-last-p-necc))

  (defruled round-after-last-p-of-certify-next
    (implies (and (certify-possiblep cert dests systate)
                  (round-after-last-p systate))
             (round-after-last-p (certify-next cert dests systate)))
    :enable (round-after-last-p
             round-after-last-p-necc))

  (defruled round-after-last-p-of-accept-next
    (implies (and (accept-possiblep val cert systate)
                  (round-after-last-p systate))
             (round-after-last-p (accept-next val cert systate)))
    :enable (round-after-last-p
             round-after-last-p-necc))

  (defruled round-after-last-p-of-advance-next
    (implies (and (advance-possiblep val systate)
                  (round-after-last-p systate))
             (round-after-last-p (advance-next val systate)))
    :use (:instance round-after-last-p-necc
                    (val (round-after-last-p-witness (advance-next val systate))))
    :enable (round-after-last-p
             validator-state->round-of-advance-next))

  (defruled round-after-last-p-of-commit-next
    (implies (and (commit-possiblep val systate)
                  (round-after-last-p systate))
             (round-after-last-p (commit-next val systate)))
    :enable (round-after-last-p
             round-after-last-p-necc
             validator-state->last-of-commit-next))

  (defruled round-after-last-p-of-event-next
    (implies (and (event-possiblep event systate)
                  (round-after-last-p systate))
             (round-after-last-p (event-next event systate)))
    :enable (event-possiblep
             event-next)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled round-after-last-p-of-events-next
  :short "Preservation of the invariant by multiple transitions."
  (implies (and (events-possiblep events systate)
                (round-after-last-p systate))
           (round-after-last-p (events-next events systate)))
  :induct t
  :enable (events-possiblep
           events-next))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled round-after-last-p-when-reachable
  :short "The invariant holds in every reachable state."
  (implies (system-state-reachablep systate)
           (round-after-last-p systate))
  :enable (system-state-reachablep
           round-after-last-p-when-init)
  :prep-lemmas
  ((defrule lemma
     (implies (and (system-state-reachable-from-p systate from)
                   (round-after-last-p from))
              (round-after-last-p systate))
     :use (:instance
           round-after-last-p-of-events-next
           (events (system-state-reachable-from-p-witness systate from))
           (systate from))
     :enable system-state-reachable-from-p)))
