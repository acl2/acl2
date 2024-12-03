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

(include-book "operations-anchors")
(include-book "properties-certificate-retrieval")
(include-book "invariant-certificate-retrieval")
(include-book "invariant-unequivocal-certificates")
(include-book "invariant-last-anchor-present")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ property-last-anchor-of-next-event
  :parents (correctness)
  :short "How @(tsee last-anchor) changes under each event."
  :long
  (xdoc::topstring
   (xdoc::p
    "The last committed anchor returned by @(tsee last-anchor) never changes,
     except under a @('commit-anchors') event,
     which updates the anchor for the validator indicated by the event."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled last-anchor-of-create-certificate-next
  :short "There is no change in @(tsee last-anchor)
          under a @('create-certificate') event."
  :long
  (xdoc::topstring
   (xdoc::p
    "The last committed round does not change, but the DAG changes.
     However, since the last committed anchor is already present,
     the newly added certificate does not affect it.
     We use the transition invariant on certificate retrieval here:
     see @(tsee invariant-certificate-with-author+round)."))
  (implies (and (system-signers-are-validators-p systate)
                (system-signers-are-quorum-p systate)
                (system-signers-have-author+round-p systate)
                (system-unequivocal-certificates-p systate)
                (system-last-anchor-present-p systate)
                (fault-tolerant-p systate)
                (set::in val (correct-addresses systate))
                (certificatep cert)
                (create-certificate-possiblep cert systate))
           (equal (last-anchor
                   (get-validator-state
                    val (create-certificate-next cert systate))
                   (all-addresses systate))
                  (last-anchor (get-validator-state val systate)
                               (all-addresses systate))))
  :enable (last-anchor
           validator-state->last-of-create-certificate-next)
  :disable validator-state->dag-of-create-certificate-next
  :use system-last-anchor-present-p-necc)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled last-anchor-of-receive-certificate-next
  :short "There is no change in @(tsee last-anchor)
          under a @('receive-certificate') event."
  :long
  (xdoc::topstring
   (xdoc::p
    "Neither the last committed round nor the DAG change,
     so the proof is trivial."))
  (implies (and (set::in val (correct-addresses systate))
                (receive-certificate-possiblep msg systate))
           (equal (last-anchor
                   (get-validator-state
                    val (receive-certificate-next msg systate))
                   (all-addresses systate))
                  (last-anchor (get-validator-state val systate)
                               (all-addresses systate))))
  :enable (last-anchor
           validator-state->last-of-receive-certificate-next))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled last-anchor-of-store-certificate-next
  :short "There is no change in @(tsee last-anchor)
          under a @('store-certificate') event."
  :long
  (xdoc::topstring
   (xdoc::p
    "The last committed round does not change, but the DAG changes.
     However, since the last committed anchor is already present,
     the newly added certificate does not affect it.
     We use the transition invariant on certificate retrieval here:
     see @(tsee invariant-certificate-with-author+round)."))
  (implies (and (system-signers-are-validators-p systate)
                (system-signers-are-quorum-p systate)
                (system-signers-have-author+round-p systate)
                (system-unequivocal-certificates-p systate)
                (system-last-anchor-present-p systate)
                (set::in val (correct-addresses systate))
                (store-certificate-possiblep cert val1 systate))
           (equal (last-anchor
                   (get-validator-state
                    val (store-certificate-next cert val1 systate))
                   (all-addresses systate))
                  (last-anchor (get-validator-state val systate)
                               (all-addresses systate))))
  :enable (last-anchor
           validator-state->last-of-store-certificate-next)
  :use system-last-anchor-present-p-necc)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled last-anchor-of-advance-round-next
  :short "There is no change in @(tsee last-anchor)
          under a @('advance-round') event."
  :long
  (xdoc::topstring
   (xdoc::p
    "Neither the last committed round nor the DAG change,
     so the proof is trivial."))
  (implies (and (set::in val (correct-addresses systate))
                (advance-round-possiblep val1 systate))
           (equal (last-anchor
                   (get-validator-state
                    val (advance-round-next val1 systate))
                   (all-addresses systate))
                  (last-anchor (get-validator-state val systate)
                               (all-addresses systate))))
  :enable (last-anchor
           validator-state->last-of-advance-round-next))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled last-anchor-of-commit-anchors-next
  :short "How the last committed anchor changes
          under a @('commit-anchors') event."
  :long
  (xdoc::topstring
   (xdoc::p
    "There is no change for the validators other than the one
     whose address is part of the event.
     For that validator, the DAG does not change,
     but the last committed round changes,
     to the even round just before the current round.
     Thus the new @(tsee last-anchor) is the certificate
     at that round authored by the leader at that round,
     which must be present in the DAG because the event is possible."))
  (implies (and (set::in val (correct-addresses systate))
                (commit-anchors-possiblep val1 systate))
           (equal (last-anchor
                   (get-validator-state
                    val (commit-anchors-next val1 systate))
                   (all-addresses systate))
                  (if (equal val1 val)
                      (b* ((round (1- (validator-state->round
                                       (get-validator-state val systate)))))
                        (certificate-with-author+round
                         (leader-at-round round (all-addresses systate))
                         round
                         (validator-state->dag
                          (get-validator-state val systate))))
                    (last-anchor (get-validator-state val systate)
                                 (all-addresses systate)))))
  :enable (last-anchor
           commit-anchors-next
           commit-anchors-next-val
           commit-anchors-possiblep
           nfix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled last-anchor-of-timer-expires-next
  :short "There is no change in @(tsee last-anchor)
          under a @('timer-expires') event."
  :long
  (xdoc::topstring
   (xdoc::p
    "Neither the last committed round nor the DAG change,
     so the proof is trivial."))
  (implies (and (set::in val (correct-addresses systate))
                (timer-expires-possiblep val1 systate))
           (equal (last-anchor
                   (get-validator-state
                    val (timer-expires-next val1 systate))
                   (all-addresses systate))
                  (last-anchor (get-validator-state val systate)
                               (all-addresses systate))))
  :enable (last-anchor
           validator-state->last-of-timer-expires-next))
