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

(include-book "last-anchor-init-and-next")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ last-anchor-voters
  :parents (correctness)
  :short "Invariant that the last committed anchor
          has more than stake @($f$) of voters."
  :long
  (xdoc::topstring
   (xdoc::p
    "When the last committed round is not 0,
     there is always an anchor at that round:
     see @(see last-anchor-present).
     Furthermore, that anchor always has successors
     whose total stake is more than @($f$),
     where @($f$) is introduced in @(tsee max-faulty-for-total).
     This total stake provides the votes
     that are in fact necessary to commit that anchor.")
   (xdoc::p
    "Initially the last committed round is 0,
     so the invariant holds trivially.
     The only event that changes the last committed anchor is @('commit'),
     whose preconditions establish the required stake of successors.
     The only events that may change the successors
     are @('certify') and @('accept'),
     which may add a certificate to the DAG:
     the added certificate may or may not be a successor,
     but if it is, it can only increase the voting stake, never decrease it."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk last-anchor-voters-p ((systate system-statep))
  :guard (last-anchor-present-p systate)
  :returns (yes/no booleanp)
  :short "Definition of the invariant."
  :long
  (xdoc::topstring
   (xdoc::p
    "The guard serves to establish that,
     if the last committed round is not 0,
     there is a last comitted anchor
     of which we can take the successor certificates in the DAG.")
   (xdoc::p
    "We use @(tsee committee-validators-stake)
     instead of @(tsee committee-members-stake)
     because, in the body of this definition,
     we do not have available the fact that
     the successors of the last committed anchor
     are all in the active committee of the round just after the anchor.
     It is an invariant (proved elsewhere) that they are,
     but we do not have the invariant available here."))
  (forall (val)
          (implies (set::in val (correct-addresses systate))
                   (b* (((validator-state vstate)
                         (get-validator-state val systate)))
                     (implies (not (equal vstate.last 0))
                              (b* ((commtt (active-committee-at-round
                                            (1+ vstate.last)
                                            vstate.blockchain)))
                                (and commtt
                                     (> (committee-validators-stake
                                         (cert-set->author-set
                                          (successors (last-anchor vstate)
                                                      vstate.dag))
                                         commtt)
                                        (committee-max-faulty-stake
                                         commtt))))))))
  :guard-hints (("Goal" :in-theory (enable last-anchor-present-p-necc
                                           last-anchor-in-dag)))

  ///

  (fty::deffixequiv-sk last-anchor-voters-p
    :args ((systate system-statep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled last-anchor-voters-p-when-init
  :short "Establishment of the invariant in the initial states."
  (implies (system-initp systate)
           (last-anchor-voters-p systate))
  :enable (last-anchor-voters-p
           system-initp
           system-validators-initp-necc
           validator-init))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection last-anchor-voters-p-of-next
  :short "Preservation of the invariant by single transitions."
  :long
  (xdoc::topstring
   (xdoc::p
    "Since our invariant is phrased in terms of successors certificates,
     we need to relate the stake of successors
     to the voting stake returned by @(tsee leader-stake-votes),
     which is used in the definition of @('commit') transitions.
     This needs non-equivocation because @(tsee leader-stake-votes)
     would count the stake of equivocal certificates multiple times,
     while @(tsee cert-set->author-set) applied to @('successors-loop')
     counts the stake of each author only once.
     The theorems for @('commit') is preceded by two lemmas,
     one for @('successors-loop') and one for @(tsee successors).")
   (xdoc::p
    "The theorems for @('certify') and @('accept')
     are proved via some monotonicity theorems,
     but we need @(':use') hints to inject a key monotonicity theorem."))

  (defruled last-anchor-voters-p-of-propose-next
    (implies (last-anchor-voters-p systate)
             (last-anchor-voters-p (propose-next prop dests systate)))
    :enable (last-anchor-voters-p
             last-anchor-voters-p-necc))

  (defruled last-anchor-voters-p-of-endorse-next
    (implies (last-anchor-voters-p systate)
             (last-anchor-voters-p (endorse-next prop endor systate)))
    :enable (last-anchor-voters-p
             last-anchor-voters-p-necc))

  (defruled last-anchor-voters-p-of-augment-next
    (implies (and (augment-possiblep prop endor systate)
                  (last-anchor-voters-p systate))
             (last-anchor-voters-p (augment-next prop endor systate)))
    :enable (last-anchor-voters-p
             last-anchor-voters-p-necc))

  (defruled last-anchor-voters-p-of-certify-next
    (implies (and (certify-possiblep cert dests systate)
                  (proposed-disjoint-dag-p systate)
                  (unequiv-dag-p systate)
                  (last-anchor-present-p systate)
                  (last-anchor-voters-p systate))
             (last-anchor-voters-p (certify-next cert dests systate)))
    :use ((:instance last-anchor-voters-p-necc
                     (val (last-anchor-voters-p-witness
                           (certify-next cert dests systate))))
          (:instance last-anchor-voters-p-necc
                     (val (certificate->author cert)))
          (:instance committee-validators-stake-monotone
                     (vals1 (cert-set->author-set
                             (successors
                              (last-anchor (get-validator-state
                                            (certificate->author cert)
                                            systate))
                              (validator-state->dag
                               (get-validator-state (certificate->author cert)
                                                    systate)))))
                     (vals2 (cert-set->author-set
                             (successors
                              (last-anchor (get-validator-state
                                            (certificate->author cert)
                                            systate))
                              (validator-state->dag
                               (get-validator-state
                                (certificate->author cert)
                                (certify-next cert dests systate))))))
                     (commtt (active-committee-at-round
                              (+
                               1
                               (validator-state->last
                                (get-validator-state
                                 (last-anchor-voters-p-witness
                                  (certify-next cert dests systate))
                                 systate)))
                              (validator-state->blockchain
                               (get-validator-state
                                (last-anchor-voters-p-witness
                                 (certify-next cert dests systate))
                                systate))))))
    :enable (last-anchor-voters-p
             validator-state->dag-of-certify-next
             cert-set->author-set-monotone
             successors-monotone))

  (defruled last-anchor-voters-p-of-accept-next
    (implies (and (accept-possiblep val cert systate)
                  (addressp val)
                  (unequiv-dag-p systate)
                  (last-anchor-present-p systate)
                  (last-anchor-voters-p systate))
             (last-anchor-voters-p (accept-next val cert systate)))
    :use ((:instance last-anchor-voters-p-necc
                     (val (last-anchor-voters-p-witness
                           (accept-next val cert systate))))
          (:instance last-anchor-voters-p-necc
                     (val val))
          (:instance committee-validators-stake-monotone
                     (vals1 (cert-set->author-set
                             (successors
                              (last-anchor
                               (get-validator-state
                                (last-anchor-voters-p-witness
                                 (accept-next val cert systate))
                                systate))
                              (validator-state->dag
                               (get-validator-state
                                (last-anchor-voters-p-witness
                                 (accept-next val cert systate))
                                systate)))))
                     (vals2 (cert-set->author-set
                             (successors
                              (last-anchor
                               (get-validator-state
                                (last-anchor-voters-p-witness
                                 (accept-next val cert systate))
                                systate))
                              (validator-state->dag
                               (get-validator-state
                                (last-anchor-voters-p-witness
                                 (accept-next val cert systate))
                                (accept-next val cert systate))))))
                     (commtt (active-committee-at-round
                              (+
                               1
                               (validator-state->last
                                (get-validator-state
                                 (last-anchor-voters-p-witness
                                  (accept-next val cert systate))
                                 systate)))
                              (validator-state->blockchain
                               (get-validator-state
                                (last-anchor-voters-p-witness
                                 (accept-next val cert systate))
                                systate))))))
    :enable (last-anchor-voters-p
             validator-state->dag-of-accept-next
             cert-set->author-set-monotone
             successors-monotone))

  (defruled last-anchor-voters-p-of-advance-next
    (implies (and (advance-possiblep val systate)
                  (last-anchor-voters-p systate))
             (last-anchor-voters-p (advance-next val systate)))
    :enable (last-anchor-voters-p
             last-anchor-voters-p-necc))

  (defruled stake-of-successors-loop-to-leader-stake-votes
    (implies (and (certificate-setp certs)
                  (cert-set-unequivp certs)
                  (addressp prev)
                  (<= (set::cardinality (cert-set->round-set certs)) 1))
             (equal (committee-validators-stake
                     (cert-set->author-set (successors-loop certs prev))
                     commtt)
                    (leader-stake-votes prev certs commtt)))
    :induct t
    :enable (leader-stake-votes
             successors-loop
             cert-set-unequivp-when-subset
             cert-set->author-set-of-insert
             committee-validators-stake-of-insert
             in-of-cert-set->author-set
             in-of-successors-loop
             equal-cert-authors-when-unequivp-and-same-round)
    :hints ('(:use (:instance cert-set->round-set-monotone
                              (certs1 (set::tail certs))
                              (certs2 certs)))))

  (defruled stake-of-successors-to-leader-stake-votes
    (implies (and (certificate-setp dag)
                  (cert-set-unequivp dag))
             (equal (committee-validators-stake
                     (cert-set->author-set (successors cert dag))
                     commtt)
                    (leader-stake-votes
                     (certificate->author cert)
                     (certs-with-round
                      (1+ (certificate->round cert))
                      dag)
                     commtt)))
    :enable (successors
             stake-of-successors-loop-to-leader-stake-votes
             cert-set-unequivp-when-subset
             cardinality-of-round-set-of-certs-with-round-leq-1))

  (defruled last-anchor-voters-p-of-commit-next
    (implies (and (commit-possiblep val systate)
                  (addressp val)
                  (last-blockchain-round-p systate)
                  (ordered-blockchain-p systate)
                  (unequiv-dag-p systate)
                  (last-anchor-voters-p systate))
             (last-anchor-voters-p (commit-next val systate)))
    :use (:instance last-anchor-voters-p-necc
                    (val (last-anchor-voters-p-witness
                          (commit-next val systate))))
    :enable (last-anchor-voters-p
             validator-state->last-of-commit-next
             active-committee-at-round-of-commit-next
             commit-possiblep
             fix
             stake-of-successors-to-leader-stake-votes
             last-anchor-of-commit-next
             unequiv-dag-p-necc))

  (defruled last-anchor-voters-p-of-event-next
    (implies (and (event-possiblep event systate)
                  (last-blockchain-round-p systate)
                  (ordered-blockchain-p systate)
                  (proposed-disjoint-dag-p systate)
                  (unequiv-dag-p systate)
                  (last-anchor-present-p systate)
                  (last-anchor-voters-p systate))
             (last-anchor-voters-p (event-next event systate)))
    :enable (event-possiblep
             event-next)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled last-anchor-voters-p-of-events-next
  :short "Preservation of the invariant by multiple transitions."
  (implies (and (events-possiblep events systate)
                (last-blockchain-round-p systate)
                (ordered-blockchain-p systate)
                (certificate-to-other-p systate)
                (proposed-author-self-p systate)
                (unequiv-proposed-p systate)
                (proposed-disjoint-dag-p systate)
                (unequiv-dag-p systate)
                (last-anchor-present-p systate)
                (last-anchor-voters-p systate))
           (last-anchor-voters-p (events-next events systate)))
  :induct t
  :enable (events-possiblep
           events-next))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled last-anchor-voters-p-when-reachable
  :short "The invariant holds in every reachable state."
  (implies (system-state-reachablep systate)
           (last-anchor-voters-p systate))
  :enable (system-state-reachablep
           last-anchor-voters-p-when-init
           last-blockchain-round-p-when-init
           ordered-blockchain-p-when-init
           certificate-to-other-p-when-init
           proposed-author-self-p-when-init
           unequiv-proposed-p-when-init
           proposed-disjoint-dag-p-when-init
           unequiv-dag-p-when-init
           last-anchor-present-p-when-init)
  :prep-lemmas
  ((defrule lemma
     (implies (and (system-state-reachable-from-p systate from)
                   (last-blockchain-round-p from)
                   (ordered-blockchain-p from)
                   (certificate-to-other-p from)
                   (proposed-author-self-p from)
                   (unequiv-proposed-p from)
                   (proposed-disjoint-dag-p from)
                   (unequiv-dag-p from)
                   (last-anchor-present-p from)
                   (last-anchor-voters-p from))
              (last-anchor-voters-p systate))
     :use (:instance
           last-anchor-voters-p-of-events-next
           (events (system-state-reachable-from-p-witness systate from))
           (systate from))
     :enable system-state-reachable-from-p)))
