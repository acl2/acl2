; AleoBFT Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOBFT-STAKE")

(include-book "last-anchor-next")

(local (include-book "arithmetic-3/top" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ last-anchor-voters-def-and-init-and-next
  :parents (correctness)
  :short "Invariant that the last committed anchor
          has at least a certain stake of successors:
          definition, establishment, and preservation."
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
     The only kind of events that changes the last committed anchor
     is @('commit'), whose preconditions establish the invariant.
     The only kinds of events that may change the successors
     are @('create') and @('store'),
     which may add a certificate to the DAG:
     the added certificate may or may not be a successor,
     but if it is, it can only increase the voting stake, never decrease it.")
   (xdoc::p
    "Here we define the invariant,
     we prove that it holds in all initial states,
     and we prove that it is preserved by all transitions.
     Elsewhere we prove that
     the invariant holds in every reachable state."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define validator-last-anchor-voters-p ((vstate validator-statep))
  :guard (and (or (equal (validator-state->last vstate) 0)
                  (last-anchor vstate))
              (dag-has-committees-p (validator-state->dag vstate)
                                    (validator-state->blockchain vstate))
              (dag-in-committees-p (validator-state->dag vstate)
                                   (validator-state->blockchain vstate)))
  :returns (yes/no booleanp)
  :short "Check if a validator state satisfies the invariant."
  :long
  (xdoc::topstring
   (xdoc::p
    "Either the last committed round is 0,
     or the committee at the next round can be calculated
     and the total stake of the successors of the last anchor
     is more than @($f$),
     where @($f$) is the maximum stake of faulty validators in the committee.")
   (xdoc::p
    "The fact that the last anchor is present is in the guard,
     but in @(tsee last-anchor-voters-p) it is established
     from the previously proved invariant @(tsee last-anchor-present-p).
     The guard also includes conditions ensuring
     that the validator can calculate committees at all rounds with certificates
     (and in particular the comittee at the round just after the last committed,
     if the anchor has any successors),
     and that the authors of all the certificates in a round
     are members of the committee at that round
     (and in particular the successors of the anchor, if any,
     are members of the committee at their round);
     these guard conditions are established, in @(tsee last-anchor-voters-p),
     via previously proved invariants used as guards there."))
  (b* (((validator-state vstate) vstate)
       ((when (equal vstate.last 0)) t)
       (commtt (active-committee-at-round (1+ vstate.last) vstate.blockchain)))
    (and commtt
         (> (committee-members-stake (cert-set->author-set
                                      (successors (last-anchor vstate)
                                                  vstate.dag))
                                     commtt)
            (committee-max-faulty-stake commtt))))
  :guard-hints
  (("Goal"
    :use ((:instance successors-subset-of-next-round
                     (cert (last-anchor vstate))
                     (dag (validator-state->dag vstate)))
          (:instance set::subset-transitive
                     (x (cert-set->author-set
                         (successors (last-anchor vstate)
                                     (validator-state->dag vstate))))
                     (y (cert-set->author-set
                         (certs-with-round (1+ (validator-state->last vstate))
                                           (validator-state->dag vstate))))
                     (z (committee-members
                         (active-committee-at-round
                          (1+ (validator-state->last vstate))
                          (validator-state->blockchain vstate))))))
    :in-theory (e/d (last-anchor-in-dag
                     cert-set->author-set-monotone
                     certificate->round-of-last-anchor
                     round-in-committee-when-dag-in-committees-p)
                    (successors-subset-of-next-round))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk last-anchor-voters-p ((systate system-statep))
  :guard (and (last-anchor-present-p systate)
              (dag-committees-p systate))
  :returns (yes/no booleanp)
  :short "Definition of the invariant:
          for each correct validator,
          if the last committed round is not 0,
          the last committed anchor has at least @($f+1$) successors,
          where @($f$) is the maximum number of faulty validators
          in the committee active at
          the round just after the last committed one."
  (forall (val)
          (implies (set::in val (correct-addresses systate))
                   (validator-last-anchor-voters-p
                    (get-validator-state val systate))))
  :guard-hints (("Goal" :in-theory (enable last-anchor-present-p-necc
                                           dag-committees-p-necc)))
  ///
  (fty::deffixequiv-sk last-anchor-voters-p
    :args ((systate system-statep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled last-anchor-voters-p-when-init
  :short "Establishment of the invariant:
          the invariant holds in any initial state."
  :long
  (xdoc::topstring
   (xdoc::p
    "The last committed round is initially 0, so the proof is trivial."))
  (implies (system-initp systate)
           (last-anchor-voters-p systate))
  :enable (last-anchor-voters-p
           validator-last-anchor-voters-p
           system-initp
           system-validators-initp-necc
           validator-init))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection last-anchor-voters-p-of-next
  :short "Preservation of the invariant:
          if the invariant holds in a system state,
          it also holds in the next system state."
  :long
  (xdoc::topstring
   (xdoc::p
    "A @('create') or @('store') event
     does not modify the last committed anchor.
     It may add certificates to the DAG,
     which may be successors of the last committed anchor,
     but since @(tsee successors) is monotone,
     the inequality of more than @($f$) voting stake is preserved.")
   (xdoc::p
    "A @('commit') event changes the last committed anchor,
     but its preconditions include the fact that
     the new anchor has more than @($f$) voting stake.
     Since our invariant is phrased in terms of successors certificates,
     we need a lemma that relates the stake of successors
     to the voting stake returned by @(tsee tally-leader-stake-votes);
     this needs non-equivocation because @(tsee tally-leader-stake-votes)
     would count the stake of equivocal certificates multiple times,
     while @(tsee cert-set->author-set) applied to @('successors-loop')
     counts the stake of each author only once.
     Since the event also extends the blockchain,
     as in other proofs we need to show that the extension of the blockchain
     does not modify the committee active at the round of the successors.")
   (xdoc::p
    "The other three kinds of events do not change
     the last committed anchor or the DAG,
     and thus the successors of the anchor."))

  ;; create:

  (defruled validator-last-anchor-voters-p-of-create-next
    (implies (and (system-committees-fault-tolerant-p systate)
                  (same-associated-certs-p systate)
                  (no-self-endorsed-p systate)
                  (signer-records-p systate)
                  (dag-committees-p systate)
                  (signer-quorum-p systate)
                  (unequivocal-dags-p systate)
                  (same-committees-p systate)
                  (last-anchor-present-p systate)
                  (create-possiblep cert systate)
                  (set::in val (correct-addresses systate))
                  (validator-last-anchor-voters-p
                   (get-validator-state val systate)))
             (validator-last-anchor-voters-p
              (get-validator-state val (create-next cert systate))))
    :use (:instance
          committee-members-stake-monotone
          (members1
           (cert-set->author-set
            (successors
             (last-anchor
              (get-validator-state (certificate->author cert) systate))
             (validator-state->dag
              (get-validator-state (certificate->author cert) systate)))))
          (members2
           (cert-set->author-set
            (successors
             (last-anchor
              (get-validator-state (certificate->author cert)
                                   (create-next cert systate)))
             (validator-state->dag
              (get-validator-state (certificate->author cert)
                                   (create-next cert systate))))))
          (commtt (active-committee-at-round
                   (1+ (validator-state->last
                        (get-validator-state (certificate->author cert)
                                             systate)))
                   (validator-state->blockchain
                    (get-validator-state (certificate->author cert)
                                         systate)))))
    :enable (validator-last-anchor-voters-p
             validator-state->dag-of-create-next
             successors-monotone
             cert-set->author-set-monotone))

  (defruled last-anchor-voters-p-of-create-next
    (implies (and (last-anchor-voters-p systate)
                  (system-committees-fault-tolerant-p systate)
                  (same-associated-certs-p systate)
                  (no-self-endorsed-p systate)
                  (signer-records-p systate)
                  (dag-committees-p systate)
                  (signer-quorum-p systate)
                  (unequivocal-dags-p systate)
                  (same-committees-p systate)
                  (last-anchor-present-p systate)
                  (create-possiblep cert systate))
             (last-anchor-voters-p (create-next cert systate)))
    :enable (last-anchor-voters-p
             last-anchor-voters-p-necc
             validator-last-anchor-voters-p-of-create-next))

  ;; receive:

  (defruled validator-last-anchor-voters-p-of-receive-next
    (implies (and (receive-possiblep msg systate)
                  (set::in val (correct-addresses systate))
                  (validator-last-anchor-voters-p
                   (get-validator-state val systate)))
             (validator-last-anchor-voters-p
              (get-validator-state val (receive-next msg systate))))
    :enable validator-last-anchor-voters-p)

  (defruled last-anchor-voters-p-of-receive-next
    (implies (and (last-anchor-voters-p systate)
                  (receive-possiblep msg systate))
             (last-anchor-voters-p (receive-next msg systate)))
    :enable (last-anchor-voters-p
             last-anchor-voters-p-necc
             validator-last-anchor-voters-p-of-receive-next))

  ;; store:

  (defruled validator-last-anchor-voters-p-of-store-next
    (implies (and (system-committees-fault-tolerant-p systate)
                  (same-associated-certs-p systate)
                  (dag-committees-p systate)
                  (signer-quorum-p systate)
                  (unequivocal-signed-certs-p systate)
                  (unequivocal-dags-p systate)
                  (same-committees-p systate)
                  (last-anchor-present-p systate)
                  (store-possiblep val cert systate)
                  (addressp val)
                  (certificatep cert)
                  (set::in val1 (correct-addresses systate))
                  (validator-last-anchor-voters-p
                   (get-validator-state val1 systate)))
             (validator-last-anchor-voters-p
              (get-validator-state val1 (store-next val cert systate))))
    :use (:instance
          committee-members-stake-monotone
          (members1
           (cert-set->author-set
            (successors
             (last-anchor
              (get-validator-state val1 systate))
             (validator-state->dag
              (get-validator-state val1 systate)))))
          (members2
           (cert-set->author-set
            (successors
             (last-anchor
              (get-validator-state val1 (store-next val cert systate)))
             (validator-state->dag
              (get-validator-state val1 (store-next val cert systate))))))
          (commtt (active-committee-at-round
                   (1+ (validator-state->last
                        (get-validator-state val systate)))
                   (validator-state->blockchain
                    (get-validator-state val systate)))))
    :enable (validator-last-anchor-voters-p
             validator-state->dag-of-store-next
             successors-monotone
             cert-set->author-set-monotone))

  (defruled last-anchor-voters-p-of-store-next
    (implies (and (last-anchor-voters-p systate)
                  (system-committees-fault-tolerant-p systate)
                  (same-associated-certs-p systate)
                  (dag-committees-p systate)
                  (signer-quorum-p systate)
                  (unequivocal-signed-certs-p systate)
                  (unequivocal-dags-p systate)
                  (same-committees-p systate)
                  (last-anchor-present-p systate)
                  (store-possiblep val cert systate)
                  (addressp val)
                  (certificatep cert))
             (last-anchor-voters-p (store-next val cert systate)))
    :enable (last-anchor-voters-p
             last-anchor-voters-p-necc
             validator-last-anchor-voters-p-of-store-next))

  ;; advance:

  (defruled validator-last-anchor-voters-p-of-advance-next
    (implies (and (advance-possiblep val systate)
                  (set::in val1 (correct-addresses systate))
                  (validator-last-anchor-voters-p
                   (get-validator-state val1 systate)))
             (validator-last-anchor-voters-p
              (get-validator-state val1 (advance-next val systate))))
    :enable validator-last-anchor-voters-p)

  (defruled last-anchor-voters-p-of-advance-next
    (implies (and (last-anchor-voters-p systate)
                  (advance-possiblep val systate))
             (last-anchor-voters-p (advance-next val systate)))
    :enable (last-anchor-voters-p
             last-anchor-voters-p-necc
             validator-last-anchor-voters-p-of-advance-next))

  ;; commit

  (defruled stake-of-successors-loop-to-tally-leader-stake-votes
    (implies (and (certificate-setp certs)
                  (certificate-set-unequivocalp certs)
                  (addressp prev)
                  (<= (set::cardinality (cert-set->round-set certs)) 1))
             (equal (committee-members-stake
                     (cert-set->author-set
                      (successors-loop certs prev))
                     commtt)
                    (mv-nth 0 (tally-leader-stake-votes prev certs commtt))))
    :induct t
    :enable (tally-leader-stake-votes
             successors-loop
             in-of-successors-loop
             cert-set->author-set-of-insert
             committee-members-stake-of-insert
             certificate-set-unequivocalp-when-subset
             set::expensive-rules
             cert-set->author-set-monotone)
    :hints ('(:use
              (head-author-not-in-tail-authors-when-unequiv-and-all-same-round
               (:instance cert-set->round-set-monotone
                          (certs1 (set::tail certs))
                          (certs2 certs))))))

  (defruled stake-of-successors-to-tally-leader-stake-votes
    (implies (and (certificate-setp dag)
                  (certificate-set-unequivocalp dag))
             (equal (committee-members-stake
                     (cert-set->author-set (successors cert dag))
                     commtt)
                    (mv-nth 0 (tally-leader-stake-votes
                               (certificate->author cert)
                               (certs-with-round
                                (1+ (certificate->round cert))
                                dag)
                               commtt))))
    :enable (successors
             stake-of-successors-loop-to-tally-leader-stake-votes
             certificate-set-unequivocalp-when-subset
             cardinality-of-round-set-of-certs-with-round-leq-1))

  (defruled validator-last-anchor-voters-p-of-commit-next
    (implies (and (last-blockchain-round-p systate)
                  (ordered-even-p systate)
                  (unequivocal-dags-p systate)
                  (commit-possiblep val systate)
                  (addressp val)
                  (set::in val1 (correct-addresses systate))
                  (validator-last-anchor-voters-p
                   (get-validator-state val1 systate)))
             (validator-last-anchor-voters-p
              (get-validator-state val1 (commit-next val systate))))
    :enable (unequivocal-dags-p-necc-single
             active-committee-at-previous-round-when-at-round
             validator-last-anchor-voters-p
             commit-possiblep
             commit-next
             last-anchor
             get-validator-state-of-update-validator-state
             nfix
             active-committee-at-round-of-extend-blockchain-no-change
             blocks-ordered-even-p-of-extend-blockchain
             certificates-ordered-even-p-of-collect-anchors
             ordered-even-p-necc-fixing
             collect-anchors-above-last-committed-round
             last-blockchain-round-p-necc-fixing
             posp
             evenp
             stake-of-successors-to-tally-leader-stake-votes))

  (defruled last-anchor-voters-p-of-commit-next
    (implies (and (last-anchor-voters-p systate)
                  (last-blockchain-round-p systate)
                  (ordered-even-p systate)
                  (unequivocal-dags-p systate)
                  (commit-possiblep val systate)
                  (addressp val))
             (last-anchor-voters-p (commit-next val systate)))
    :enable (last-anchor-voters-p
             last-anchor-voters-p-necc
             validator-last-anchor-voters-p-of-commit-next))

  ;; timeout:

  (defruled validator-last-anchor-voters-p-of-timeout-next
    (implies (and (timeout-possiblep val systate)
                  (set::in val1 (correct-addresses systate))
                  (validator-last-anchor-voters-p
                   (get-validator-state val1 systate)))
             (validator-last-anchor-voters-p
              (get-validator-state val1 (timeout-next val systate))))
    :enable validator-last-anchor-voters-p)

  (defruled last-anchor-voters-p-of-timeout-next
    (implies (and (last-anchor-voters-p systate)
                  (timeout-possiblep val systate))
             (last-anchor-voters-p (timeout-next val systate)))
    :enable (last-anchor-voters-p
             last-anchor-voters-p-necc
             validator-last-anchor-voters-p-of-timeout-next))

  ;; all events:

  (defruled last-anchor-voters-p-of-event-next
    (implies (and (last-anchor-voters-p systate)
                  (system-committees-fault-tolerant-p systate)
                  (last-blockchain-round-p systate)
                  (ordered-even-p systate)
                  (same-associated-certs-p systate)
                  (no-self-endorsed-p systate)
                  (signer-records-p systate)
                  (dag-committees-p systate)
                  (signer-quorum-p systate)
                  (unequivocal-signed-certs-p systate)
                  (unequivocal-dags-p systate)
                  (same-committees-p systate)
                  (last-anchor-present-p systate)
                  (event-possiblep event systate))
             (last-anchor-voters-p (event-next event systate)))
    :enable (event-possiblep
             event-next)))
