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

(include-book "last-anchor-def")
(include-book "last-anchor-present")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ last-anchor-init-and-next
  :parents (correctness)
  :short "Last anchor committed by a validator:
          initial value, and how the value changed under the events."
  :long
  (xdoc::topstring
   (xdoc::p
    "Initially, @(tsee last-anchor) returns @('nil'),
     because no anchors have been committed yet.")
   (xdoc::p
    "The value of @(tsee last-anchor) is unchanged
     under all the events except @('commit'),
     which commits new anchors.")
   (xdoc::p
    "The proofs of preservation of @(tsee last-anchor)
     under @('certify') and @('accept'),
     both of which extend the DAG,
     rely on the fact that the last anchor is present
     unless the last committed round is 0:
     since the anchor was present,
     and since the new DAG is unequivocal (as previously proved),
     @(tsee cert-with-author+round)
     (which @(tsee last-anchor) is defined in terms of)
     retains its value;
     the proof is similar to the one for
     the preservation of @(tsee last-anchor-present-p)."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled last-anchor-when-init
  :short "Initial last anchor."
  (implies (and (system-initp systate)
                (set::in val (correct-addresses systate)))
           (equal (last-anchor (get-validator-state val systate))
                  nil))
  :enable (last-anchor
           system-initp
           system-validators-initp-necc
           validator-init))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule last-anchor-of-propose-next
  :short "How the last anchor changes under @('propose') events."
  :long
  (xdoc::topstring
   (xdoc::p
    "A @('propose') event does not modify
     any DAG, last committed round, or blockchain.
     Thus, @(tsee last-anchor) is unchanged (for all validators)."))
  (implies (set::in val (correct-addresses systate))
           (equal (last-anchor (get-validator-state
                                val (propose-next prop dests systate)))
                  (last-anchor (get-validator-state val systate))))
  :enable last-anchor)

(defrule last-anchor-of-endorse-next
  :short "How the last anchor changes under @('endorse') events."
  :long
  (xdoc::topstring
   (xdoc::p
    "An @('endorse') event does not modify
     any DAG, last committed round, or blockchain.
     Thus, @(tsee last-anchor) is unchanged (for all validators)."))
  (implies (set::in val (correct-addresses systate))
           (equal (last-anchor (get-validator-state
                                val (endorse-next prop endor systate)))
                  (last-anchor (get-validator-state val systate))))
  :enable last-anchor)

(defrule last-anchor-of-augment-next
  :short "How the last anchor changes under @('augment') events."
  :long
  (xdoc::topstring
   (xdoc::p
    "An @('augment') event does not modify
     any DAG, last committed round, or blockchain.
     Thus, @(tsee last-anchor) is unchanged (for all validators)."))
  (implies (set::in val (correct-addresses systate))
           (equal (last-anchor (get-validator-state
                                val (augment-next prop endor systate)))
                  (last-anchor (get-validator-state val systate))))
  :enable last-anchor)

(defrule last-anchor-of-certify-next
  :short "How the last anchor changes under @('certify') events."
  :long
  (xdoc::topstring
   (xdoc::p
    "A @('certify') event extends the DAG of the authoring validator,
     but in a way that does not affect
     the last committed anchor (or its absence).
     The proof is similar to one for
     the preservation of @(tsee last-anchor-present-p)
     under @('certify') events."))
  (implies (and (set::in val (correct-addresses systate))
                (certify-possiblep cert dests systate)
                (proposed-disjoint-dag-p systate)
                (unequiv-dag-p systate)
                (last-anchor-present-p systate))
           (equal (last-anchor (get-validator-state
                                val (certify-next cert dests systate)))
                  (last-anchor (get-validator-state val systate))))
  :use ((:instance last-anchor-present-p-necc
                   (val (certificate->author cert)))
        (:instance unequiv-dag-p-necc
                   (val (certificate->author cert))
                   (systate (certify-next cert dests systate)))
        (:instance cert-with-author+round-superset-when-unequiv
                   (certs0 (validator-state->dag
                            (get-validator-state
                             (certificate->author cert)
                             systate)))
                   (certs (validator-state->dag
                           (get-validator-state
                            (certificate->author cert)
                            (certify-next cert dests systate))))
                   (author (certificate->author
                            (last-anchor
                             (get-validator-state
                              (certificate->author cert)
                              systate))))
                   (round (certificate->round
                           (last-anchor
                            (get-validator-state
                             (certificate->author cert)
                             systate))))))
  :enable (last-anchor
           validator-state->dag-of-certify-next))

(defrule last-anchor-of-accept-next
  :short "How the last anchor changes under @('accept') events."
  :long
  (xdoc::topstring
   (xdoc::p
    "An @('accept') event extends the DAG of the accepting validator,
     but in a way that does not affect
     the last committed anchor (or its absence).
     The proof is similar to one for
     the preservation of @(tsee last-anchor-present-p)
     under @('accept') events."))
  (implies (and (set::in val1 (correct-addresses systate))
                (accept-possiblep val cert systate)
                (addressp val)
                (unequiv-dag-p systate)
                (last-anchor-present-p systate))
           (equal (last-anchor (get-validator-state
                                val1 (accept-next val cert systate)))
                  (last-anchor (get-validator-state val1 systate))))
  :use (last-anchor-present-p-necc
        (:instance unequiv-dag-p-necc
                   (systate (accept-next val cert systate)))
        (:instance cert-with-author+round-superset-when-unequiv
                   (certs0 (validator-state->dag
                            (get-validator-state val systate)))
                   (certs (validator-state->dag
                           (get-validator-state
                            val (accept-next val cert systate))))
                   (author (certificate->author
                            (last-anchor
                             (get-validator-state val systate))))
                   (round (certificate->round
                           (last-anchor
                            (get-validator-state val systate))))))
  :enable (last-anchor
           validator-state->dag-of-accept-next
           unequiv-dag-p-of-accept-next))

(defrule last-anchor-of-advance-next
  :short "How the last anchor changes under @('advance') events."
  :long
  (xdoc::topstring
   (xdoc::p
    "An @('advance') event does not modify
     any DAG, last committed round, or blockchain.
     Thus, @(tsee last-anchor) is unchanged (for all validators)."))
  (implies (and (set::in val1 (correct-addresses systate))
                (advance-possiblep val systate))
           (equal (last-anchor (get-validator-state
                                val1 (advance-next val systate)))
                  (last-anchor (get-validator-state val1 systate))))
  :enable last-anchor)

(defruled last-anchor-of-commit-next
  :short "How the last anchor changes under @('commit') events."
  :long
  (xdoc::topstring
   (xdoc::p
    "A @('commit') event modifies the last anchor
     according to the definition of @(tsee commit-next),
     for the target validator.
     The last anchor is unchanged for the other validators."))
  (implies (and (set::in val1 (correct-addresses systate))
                (commit-possiblep val systate)
                (last-blockchain-round-p systate)
                (ordered-blockchain-p systate))
           (equal (last-anchor (get-validator-state
                                val1 (commit-next val systate)))
                  (if (equal val1 (address-fix val))
                      (b* ((round (1- (validator-state->round
                                       (get-validator-state val systate))))
                           (commtt (active-committee-at-round
                                    round
                                    (validator-state->blockchain
                                     (get-validator-state val systate)))))
                        (cert-with-author+round
                         (leader-at-round round commtt)
                         round
                         (validator-state->dag
                          (get-validator-state val systate))))
                    (last-anchor (get-validator-state val1 systate)))))
  :use (:instance active-committee-at-round-of-commit-next
                  (round (1- (validator-state->round
                              (get-validator-state val systate))))
                  (val1 val))
  :enable (last-anchor
           validator-state->last-of-commit-next
           commit-possiblep
           commit-next
           nfix))
