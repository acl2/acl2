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

(include-book "properties-anchors")
(include-book "properties-anchors-extension")
(include-book "invariant-paths-to-last-anchor")
(include-book "property-last-anchor-of-next-event")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ property-committed-anchors-of-next-event
  :parents (correctness)
  :short "How @(tsee committed-anchors) changes under each event."
  :long
  (xdoc::topstring
   (xdoc::p
    "The sequence of committed anchors returned by @(tsee committed-anchors)
     never changes,
     except under a @('commit-anchors') event,
     which updates extends the sequence with the new anchors."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled committed-anchors-of-create-certificate-next
  :short "There is no change in @(tsee committed-anchors)
          under a @('create-certificate') event."
  :long
  (xdoc::topstring
   (xdoc::p
    "The last committed anchor does not change, but the DAG changes.
     However, since the last committed anchor is already present,
     and the new DAG is a superset of the old one,
     we use @(tsee collect-all-anchors-of-unequivocal-dag-superset)
     to show that the collected anchors do not change."))
  (implies (and (system-signers-are-validators-p systate)
                (system-signers-are-quorum-p systate)
                (system-signers-have-author+round-p systate)
                (system-unequivocal-certificates-p systate)
                (system-last-anchor-present-p systate)
                (system-previous-in-dag-p systate)
                (fault-tolerant-p systate)
                (set::in val (correct-addresses systate))
                (certificatep cert)
                (create-certificate-possiblep cert systate))
           (equal (committed-anchors
                   (get-validator-state
                    val (create-certificate-next cert systate))
                   (all-addresses systate))
                  (committed-anchors (get-validator-state val systate)
                                     (all-addresses systate))))
  :enable (committed-anchors
           system-unequivocal-dag-p-necc
           system-unequivocal-dag-p-when-system-unequivocal-certificates-p
           system-previous-in-dag-p-necc
           validator-state->dag-subset-create-certificate-next
           validator-state->dag-of-create-certificate-next-same
           validator-state->last-of-create-certificate-next
           last-anchor-in-dag
           last-anchor-of-create-certificate-next
           system-unequivocal-certificates-p-of-create-certificate-next)
  :cases ((equal val (certificate->author cert)))
  :use ((:instance collect-all-anchors-of-unequivocal-dag-superset
                   (vals (all-addresses systate))
                   (last-anchor
                    (last-anchor
                     (get-validator-state (certificate->author cert) systate)
                     (all-addresses systate)))
                   (dag (validator-state->dag
                         (get-validator-state (certificate->author cert)
                                              systate)))
                   (dag2 (validator-state->dag
                          (get-validator-state
                           (certificate->author cert)
                           (create-certificate-next cert systate)))))
        (:instance system-last-anchor-present-p-necc
                   (val (certificate->author cert))))
  :disable validator-state->dag-of-create-certificate-next)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled committed-anchors-of-receive-certificate-next
  :short "There is no change in @(tsee last-anchor)
          under a @('receive-certificate') event."
  :long
  (xdoc::topstring
   (xdoc::p
    "Neither the last committed anchor nor the DAG change,
     so the proof is trivial."))
  (implies (and (set::in val (correct-addresses systate))
                (receive-certificate-possiblep msg systate))
           (equal (committed-anchors
                   (get-validator-state
                    val (receive-certificate-next msg systate))
                   (all-addresses systate))
                  (committed-anchors (get-validator-state val systate)
                                     (all-addresses systate))))
  :enable (committed-anchors
           validator-state->dag-of-receive-certificate-next
           validator-state->last-of-receive-certificate-next
           last-anchor-of-receive-certificate-next))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled committed-anchors-of-store-certificate-next
  :short "There is no change in @(tsee last-anchor)
          under a @('store-certificate') event."
  :long
  (xdoc::topstring
   (xdoc::p
    "The last committed anchor does not change, but the DAG changes.
     However, since the last committed anchor is already present,
     and the new DAG is a superset of the old one,
     we use @(tsee collect-all-anchors-of-unequivocal-dag-superset)
     to show that the collected anchors do not change."))
  (implies (and (system-signers-are-validators-p systate)
                (system-signers-are-quorum-p systate)
                (system-signers-have-author+round-p systate)
                (system-unequivocal-certificates-p systate)
                (system-last-anchor-present-p systate)
                (system-previous-in-dag-p systate)
                (fault-tolerant-p systate)
                (set::in val (correct-addresses systate))
                (store-certificate-possiblep cert val1 systate))
           (equal (committed-anchors
                   (get-validator-state
                    val (store-certificate-next cert val1 systate))
                   (all-addresses systate))
                  (committed-anchors (get-validator-state val systate)
                                     (all-addresses systate))))
  :enable (committed-anchors
           system-unequivocal-dag-p-necc
           system-unequivocal-dag-p-when-system-unequivocal-certificates-p
           system-previous-in-dag-p-necc
           system-last-anchor-present-p-necc
           validator-state->dag-subset-store-certificate-next
           validator-state->last-of-store-certificate-next
           last-anchor-in-dag
           last-anchor-of-store-certificate-next
           system-unequivocal-certificates-p-of-store-certificate-next)
  :use (:instance collect-all-anchors-of-unequivocal-dag-superset
                  (vals (all-addresses systate))
                  (last-anchor
                   (last-anchor
                    (get-validator-state val systate)
                    (all-addresses systate)))
                  (dag (validator-state->dag
                        (get-validator-state val systate)))
                  (dag2 (validator-state->dag
                         (get-validator-state
                          val
                          (store-certificate-next cert val1 systate))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled committed-anchors-of-advance-round-next
  :short "There is no change in @(tsee last-anchor)
          under a @('advance-round') event."
  :long
  (xdoc::topstring
   (xdoc::p
    "Neither the last committed anchor nor the DAG change,
     so the proof is trivial."))
  (implies (and (set::in val (correct-addresses systate))
                (advance-round-possiblep val1 systate))
           (equal (committed-anchors
                   (get-validator-state
                    val (advance-round-next val1 systate))
                   (all-addresses systate))
                  (committed-anchors (get-validator-state val systate)
                                     (all-addresses systate))))
  :enable (committed-anchors
           validator-state->dag-of-advance-round-next
           validator-state->last-of-advance-round-next
           last-anchor-of-advance-round-next))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled committed-anchors-of-commit-anchors
  :short "How the sequence of committed anchors changes
          under a @('commit-anchor') event."
  :long
  (xdoc::topstring
   (xdoc::p
    "There is no change for the validators other than the one
     whose address is part of the event.
     For that validator, the sequence of anchors is extended
     with one or more anchors,
     according to the definition of the transition."))
  (implies
   (and (system-last-anchor-present-p systate)
        (system-unequivocal-dag-p systate)
        (system-last-is-even-p systate)
        (system-paths-to-last-anchor-p systate)
        (set::in val (correct-addresses systate))
        (commit-anchors-possiblep val1 systate))
   (equal (committed-anchors
           (get-validator-state
            val (commit-anchors-next val1 systate))
           (all-addresses systate))
          (if (equal val val1)
              (b* (((validator-state vstate)
                    (get-validator-state val systate))
                   (commit-round (1- vstate.round))
                   (leader (leader-at-round commit-round
                                            (all-addresses systate)))
                   (anchor (certificate-with-author+round leader
                                                          commit-round
                                                          vstate.dag))
                   (anchors (collect-anchors anchor
                                             (- commit-round 2)
                                             vstate.last
                                             vstate.dag
                                             (all-addresses systate))))
                (append anchors
                        (committed-anchors (get-validator-state val systate)
                                           (all-addresses systate))))
            (committed-anchors (get-validator-state val systate)
                               (all-addresses systate)))))
  :enable (commit-anchors-possiblep
           committed-anchors
           collect-all-anchors
           system-last-anchor-present-p-necc
           system-unequivocal-dag-p-necc
           system-last-is-even-p-necc
           system-paths-to-last-anchor-p-necc
           anchorp
           certificate-with-author+round-element
           certificate->author-of-certificate-with-author+round
           certificate->round-of-certificate-with-author+round
           validator-state->dag-of-commit-anchors-next
           validator-state->last-of-commit-anchors-next
           certificate->author-of-last-anchor
           certificate->round-of-last-anchor
           last-anchor-in-dag
           last-anchor-of-commit-anchors-next)
  :use (:instance collect-all-anchors-to-append-of-collect-anchors
                  (anchor (last-anchor (get-validator-state val systate)
                                       (all-addresses systate)))
                  (anchor1 (certificate-with-author+round
                            (leader-at-round
                             (+ -1
                                (validator-state->round
                                 (get-validator-state val systate)))
                             (all-addresses systate))
                            (+ -1
                               (validator-state->round
                                (get-validator-state val systate)))
                            (validator-state->dag
                             (get-validator-state val systate))))
                  (dag (validator-state->dag
                        (get-validator-state val systate)))
                  (vals (all-addresses systate)))

  :prep-lemmas
  ((defrule lemma
     (implies (and (integerp x)
                   (not (evenp x)))
              (evenp (1- x)))
     :enable evenp
     :prep-books ((include-book "arithmetic-3/top" :dir :system)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled committed-anchors-of-timer-expires-next
  :short "There is no change in @(tsee last-anchor)
          under a @('timer-expires') event."
  :long
  (xdoc::topstring
   (xdoc::p
    "Neither the last committed anchor nor the DAG change,
     so the proof is trivial."))
  (implies (and (set::in val (correct-addresses systate))
                (timer-expires-possiblep val1 systate))
           (equal (committed-anchors
                   (get-validator-state
                    val (timer-expires-next val1 systate))
                   (all-addresses systate))
                  (committed-anchors (get-validator-state val systate)
                                     (all-addresses systate))))
  :enable (committed-anchors
           validator-state->dag-of-timer-expires-next
           validator-state->last-of-timer-expires-next
           last-anchor-of-timer-expires-next))
