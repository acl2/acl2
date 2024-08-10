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

(include-book "properties-anchors")
(include-book "properties-anchors-extension")
(include-book "invariant-paths-to-last-anchor")
(include-book "property-last-anchor-of-next-event")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ property-validator-anchors-of-next-event
  :parents (correctness)
  :short "How @(tsee validator-anchors) changes under each event."
  :long
  (xdoc::topstring
   (xdoc::p
    "The sequence of committed anchors returned by @(tsee validator-anchors)
     never changes,
     except under a @('commit-anchors') event,
     which updates extends the sequence with the new anchors."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule validator-anchors-of-create-certificate-next
  :short "There is no change in @(tsee validator-anchors)
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
           (equal (validator-anchors
                   (get-validator-state
                    val (create-certificate-next cert systate))
                   (all-addresses systate))
                  (validator-anchors (get-validator-state val systate)
                                     (all-addresses systate))))
  :enable (validator-anchors
           system-unequivocal-dag-p-necc
           system-unequivocal-dag-p-when-system-unequivocal-certificates-p
           system-previous-in-dag-p-necc)
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

(defrule validator-anchors-of-receive-certificate-next
  :short "There is no change in @(tsee last-anchor)
          under a @('receive-certificate') event."
  :long
  (xdoc::topstring
   (xdoc::p
    "Neither the last committed anchor nor the DAG change,
     so the proof is trivial."))
  (implies (and (set::in val (correct-addresses systate))
                (receive-certificate-possiblep msg systate))
           (equal (validator-anchors
                   (get-validator-state
                    val (receive-certificate-next msg systate))
                   (all-addresses systate))
                  (validator-anchors (get-validator-state val systate)
                                     (all-addresses systate))))
  :enable validator-anchors)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule validator-anchors-of-store-certificate-next
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
           (equal (validator-anchors
                   (get-validator-state
                    val (store-certificate-next cert val1 systate))
                   (all-addresses systate))
                  (validator-anchors (get-validator-state val systate)
                                     (all-addresses systate))))
  :enable (validator-anchors
           system-unequivocal-dag-p-necc
           system-unequivocal-dag-p-when-system-unequivocal-certificates-p
           system-previous-in-dag-p-necc
           system-last-anchor-present-p-necc)
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
                          (store-certificate-next cert val1 systate)))))
  :disable validator-state->dag-of-store-certificate-next)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule validator-anchors-of-advance-round-next
  :short "There is no change in @(tsee last-anchor)
          under a @('advance-round') event."
  :long
  (xdoc::topstring
   (xdoc::p
    "Neither the last committed anchor nor the DAG change,
     so the proof is trivial."))
  (implies (and (set::in val (correct-addresses systate))
                (advance-round-possiblep val1 systate))
           (equal (validator-anchors
                   (get-validator-state
                    val (advance-round-next val1 systate))
                   (all-addresses systate))
                  (validator-anchors (get-validator-state val systate)
                                     (all-addresses systate))))
  :enable validator-anchors)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule validator-anchors-of-commit-anchors
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
   (equal (validator-anchors
           (get-validator-state
            val (commit-anchors-next val1 systate))
           (all-addresses systate))
          (if (equal val val1)
              (b* (((validator-state vstate)
                    (get-validator-state val systate))
                   (commit-round (1- vstate.round))
                   (leader (leader-at-round commit-round
                                            (all-addresses systate)))
                   (anchor (get-certificate-with-author+round leader
                                                              commit-round
                                                              vstate.dag))
                   (anchors (collect-anchors anchor
                                             (- commit-round 2)
                                             vstate.last
                                             vstate.dag
                                             (all-addresses systate))))
                (append anchors
                        (validator-anchors (get-validator-state val systate)
                                           (all-addresses systate))))
            (validator-anchors (get-validator-state val systate)
                               (all-addresses systate)))))
  :enable (commit-anchors-possiblep
           validator-anchors
           collect-all-anchors
           system-last-anchor-present-p-necc
           system-unequivocal-dag-p-necc
           system-last-is-even-p-necc
           system-paths-to-last-anchor-p-necc
           anchorp
           get-certificate-with-author+round-element-when-not-nil)
  :use (:instance collect-all-anchors-to-append-of-collect-anchors
                  (anchor (last-anchor (get-validator-state val systate)
                                       (all-addresses systate)))
                  (anchor1 (get-certificate-with-author+round
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

(defrule validator-anchors-of-timer-expires-next
  :short "There is no change in @(tsee last-anchor)
          under a @('timer-expires') event."
  :long
  (xdoc::topstring
   (xdoc::p
    "Neither the last committed anchor nor the DAG change,
     so the proof is trivial."))
  (implies (and (set::in val (correct-addresses systate))
                (timer-expires-possiblep val1 systate))
           (equal (validator-anchors
                   (get-validator-state
                    val (timer-expires-next val1 systate))
                   (all-addresses systate))
                  (validator-anchors (get-validator-state val systate)
                                     (all-addresses systate))))
  :enable validator-anchors)
