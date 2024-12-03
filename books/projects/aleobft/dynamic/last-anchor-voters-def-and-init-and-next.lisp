; AleoBFT Library
;
; Copyright (C) 2024 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOBFT-DYNAMIC")

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
          has at least a certain number of successors:
          definition, establishment, and preservation."
  :long
  (xdoc::topstring
   (xdoc::p
    "When the last committed round is not 0,
     there is always an anchor at that round:
     see @(see last-anchor-present).
     Furthermore, that anchor always has at least @($f+1$) successors,
     where @($f$) is introduced in @(tsee max-faulty-for-total).
     Those are the votes that are in fact necessary
     to commit that anchor.")
   (xdoc::p
    "Initially the last committed round is 0,
     so the invariant holds trivially.
     The only kind of events that changes the last committed anchor
     is @('commit-anchors'), whose preconditions establish the invariant.
     The only kinds of events that may change the successors
     are @('create-certificate') and @('store-certificate'),
     which may add certificates to the DAG:
     this certificate may or may not be a successor,
     but if it is, it can only increase the votes, never decrease them.")
   (xdoc::p
    "Here we define the invariant,
     we prove that it holds in all initial states,
     and we prove that it is preserved by all transitions.
     In @(see last-anchor-voters) we prove that
     the invariant holds in every reachable state."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define validator-last-anchor-voters-p ((vstate validator-statep)
                                        (all-vals address-setp))
  :guard (or (equal (validator-state->last vstate) 0)
             (last-anchor vstate all-vals))
  :returns (yes/no booleanp)
  :short "Check if a validator state satisfies the invariant."
  :long
  (xdoc::topstring
   (xdoc::p
    "Either the last committed round is 0,
     or the committee at the next round can be calculated
     and the successors of the last anchor are at least @($f+1$),
     where @($f$) is the maximum number of faulty validators in the committee.
     The fact that the last anchor is present is in the guard,
     but in @(tsee last-anchor-voters-p) it is established
     from the previously proved invariant @(tsee last-anchor-present-p)."))
  (b* (((validator-state vstate) vstate)
       ((when (equal vstate.last 0)) t)
       (commtt (active-committee-at-round (1+ vstate.last)
                                          vstate.blockchain
                                          all-vals)))
    (and commtt
         (>= (set::cardinality (successors (last-anchor vstate all-vals)
                                           vstate.dag))
             (1+ (committee-max-faulty commtt)))))
  :guard-hints (("Goal" :in-theory (enable last-anchor-in-dag)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk last-anchor-voters-p ((systate system-statep))
  :guard (last-anchor-present-p systate)
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
                    (get-validator-state val systate)
                    (all-addresses systate))))
  :guard-hints (("Goal" :in-theory (enable last-anchor-present-p-necc)))
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
    "A @('create-certificate') or @('store-certificate') event
     does not modify the last committed anchor.
     It may add certificates to the DAG,
     which may be successors of the last committed anchor,
     but since @(tsee successors) is monotone,
     the inequality of at least @($f+1$) votes is preserved.")
   (xdoc::p
    "A @('commit-anchors') event changes the last committed anchor,
     but its preconditions include the fact that
     the new anchor has at least @($f+1$) votes.
     Since our invariant is phrased in terms of successors certificates,
     we need a lemma that relates the number of successors to the votes.
     Since the event also extends the blockchain,
     as in other proofs we need to show that the extension of the blockchain
     does not modify the committee active at the round of the successors.")
   (xdoc::p
    "The other three kinds of events do not change
     the last committed anchor or the DAG,
     and thus the successors of the anchor."))

  ;; create-certificate:

  (defruled validator-last-anchor-voters-p-of-create-certificate-next
    (implies (and (unequivocal-accepted-certificates-p systate)
                  (signer-records-p systate)
                  (committees-in-system-p systate)
                  (system-fault-tolerant-p systate)
                  (signer-quorum-p systate)
                  (same-committees-p systate)
                  (no-self-buffer-p systate)
                  (no-self-endorsed-p systate)
                  (same-owned-certificates-p systate)
                  (accepted-certificate-committee-p systate)
                  (last-anchor-present-p systate)
                  (create-certificate-possiblep cert systate)
                  (set::in val (correct-addresses systate))
                  (validator-last-anchor-voters-p
                   (get-validator-state val systate)
                   (all-addresses systate)))
             (validator-last-anchor-voters-p
              (get-validator-state val (create-certificate-next cert systate))
              (all-addresses systate)))
    :use (:instance
          set::subset-cardinality
          (x (successors
              (last-anchor
               (get-validator-state (certificate->author cert) systate)
               (all-addresses systate))
              (validator-state->dag
               (get-validator-state (certificate->author cert) systate))))
          (y (successors
              (last-anchor
               (get-validator-state (certificate->author cert) systate)
               (all-addresses systate))
              (validator-state->dag
               (get-validator-state (certificate->author cert)
                                    (create-certificate-next cert systate))))))
    :disable set::subset-cardinality
    :enable (validator-last-anchor-voters-p
             validator-state->last-of-create-certificate-next
             validator-state->blockchain-of-create-certificate-next
             validator-state->dag-of-create-certificate-next
             last-anchor-of-create-certificate-next
             successors-monotone))

  (defruled last-anchor-voters-p-of-create-certificate-next
    (implies (and (unequivocal-accepted-certificates-p systate)
                  (signer-records-p systate)
                  (committees-in-system-p systate)
                  (system-fault-tolerant-p systate)
                  (signer-quorum-p systate)
                  (same-committees-p systate)
                  (no-self-buffer-p systate)
                  (no-self-endorsed-p systate)
                  (same-owned-certificates-p systate)
                  (accepted-certificate-committee-p systate)
                  (last-anchor-present-p systate)
                  (create-certificate-possiblep cert systate)
                  (last-anchor-voters-p systate))
             (last-anchor-voters-p
              (create-certificate-next cert systate)))
    :enable (last-anchor-voters-p
             last-anchor-voters-p-necc
             validator-last-anchor-voters-p-of-create-certificate-next))

  ;; receive-certificate:

  (defruled validator-last-anchor-voters-p-of-receive-certificate-next
    (implies (and (last-anchor-present-p systate)
                  (receive-certificate-possiblep msg systate)
                  (set::in val (correct-addresses systate))
                  (validator-last-anchor-voters-p
                   (get-validator-state val systate)
                   (all-addresses systate)))
             (validator-last-anchor-voters-p
              (get-validator-state val (receive-certificate-next msg systate))
              (all-addresses systate)))
    :enable (validator-last-anchor-voters-p
             validator-state->last-of-receive-certificate-next
             validator-state->blockchain-of-receive-certificate-next
             validator-state->dag-of-receive-certificate-next
             last-anchor-of-receive-certificate-next))

  (defruled last-anchor-voters-p-of-receive-certificate-next
    (implies (and (last-anchor-present-p systate)
                  (receive-certificate-possiblep msg systate)
                  (last-anchor-voters-p systate))
             (last-anchor-voters-p
              (receive-certificate-next msg systate)))
    :enable (last-anchor-voters-p
             last-anchor-voters-p-necc
             validator-last-anchor-voters-p-of-receive-certificate-next))

  ;; store-certificate:

  (defruled validator-last-anchor-voters-p-of-store-certificate-next
    (implies (and (unequivocal-accepted-certificates-p systate)
                  (signer-records-p systate)
                  (committees-in-system-p systate)
                  (system-fault-tolerant-p systate)
                  (signer-quorum-p systate)
                  (same-committees-p systate)
                  (no-self-buffer-p systate)
                  (no-self-endorsed-p systate)
                  (same-owned-certificates-p systate)
                  (accepted-certificate-committee-p systate)
                  (last-anchor-present-p systate)
                  (store-certificate-possiblep val cert systate)
                  (set::in val1 (correct-addresses systate))
                  (validator-last-anchor-voters-p
                   (get-validator-state val1 systate)
                   (all-addresses systate)))
             (validator-last-anchor-voters-p
              (get-validator-state val1 (store-certificate-next val cert systate))
              (all-addresses systate)))
    :use (:instance
          set::subset-cardinality
          (x (successors
              (last-anchor
               (get-validator-state val1 systate)
               (all-addresses systate))
              (validator-state->dag
               (get-validator-state val1 systate))))
          (y (successors
              (last-anchor
               (get-validator-state val1 systate)
               (all-addresses systate))
              (validator-state->dag
               (get-validator-state val1
                                    (store-certificate-next val cert systate))))))
    :disable set::subset-cardinality
    :enable (validator-last-anchor-voters-p
             validator-state->last-of-store-certificate-next
             validator-state->blockchain-of-store-certificate-next
             validator-state->dag-of-store-certificate-next
             last-anchor-of-store-certificate-next
             successors-monotone))

  (defruled last-anchor-voters-p-of-store-certificate-next
    (implies (and (unequivocal-accepted-certificates-p systate)
                  (signer-records-p systate)
                  (committees-in-system-p systate)
                  (system-fault-tolerant-p systate)
                  (signer-quorum-p systate)
                  (same-committees-p systate)
                  (no-self-buffer-p systate)
                  (no-self-endorsed-p systate)
                  (same-owned-certificates-p systate)
                  (accepted-certificate-committee-p systate)
                  (last-anchor-present-p systate)
                  (store-certificate-possiblep val cert systate)
                  (last-anchor-voters-p systate))
             (last-anchor-voters-p
              (store-certificate-next val cert systate)))
    :enable (last-anchor-voters-p
             last-anchor-voters-p-necc
             validator-last-anchor-voters-p-of-store-certificate-next))

  ;; advance-round:

  (defruled validator-last-anchor-voters-p-of-advance-round-next
    (implies (and (last-anchor-present-p systate)
                  (advance-round-possiblep val systate)
                  (set::in val1 (correct-addresses systate))
                  (validator-last-anchor-voters-p
                   (get-validator-state val1 systate)
                   (all-addresses systate)))
             (validator-last-anchor-voters-p
              (get-validator-state val1 (advance-round-next val systate))
              (all-addresses systate)))
    :enable (validator-last-anchor-voters-p
             validator-state->last-of-advance-round-next
             validator-state->blockchain-of-advance-round-next
             validator-state->dag-of-advance-round-next
             last-anchor-of-advance-round-next))

  (defruled last-anchor-voters-p-of-advance-round-next
    (implies (and (last-anchor-present-p systate)
                  (advance-round-possiblep val systate)
                  (last-anchor-voters-p systate))
             (last-anchor-voters-p
              (advance-round-next val systate)))
    :enable (last-anchor-voters-p
             last-anchor-voters-p-necc
             validator-last-anchor-voters-p-of-advance-round-next))

  ;; commit-anchors

  (defruled cardinality-of-successors-loop-to-tally-leader-votes
    (implies (certificate-setp certs)
             (equal (set::cardinality (successors-loop certs prev))
                    (mv-nth 0 (tally-leader-votes prev certs))))
    :induct t
    :enable (tally-leader-votes
             successors-loop
             in-of-successors-loop
             set::expensive-rules))

  (defruled cardinality-of-successors-to-tally-leader-votes
    (equal (set::cardinality (successors cert dag))
           (mv-nth 0 (tally-leader-votes
                      (certificate->author cert)
                      (certificates-with-round
                       (1+ (certificate->round cert))
                       dag))))
    :enable (successors
             cardinality-of-successors-loop-to-tally-leader-votes))

  (defruled validator-last-anchor-voters-p-of-commit-anchors-next
    (implies (and (ordered-even-p systate)
                  (last-blockchain-round-p systate)
                  (accepted-certificate-committee-p systate)
                  (commit-anchors-possiblep val systate)
                  (set::in val1 (correct-addresses systate))
                  (validator-last-anchor-voters-p
                   (get-validator-state val1 systate)
                   (all-addresses systate)))
             (validator-last-anchor-voters-p
              (get-validator-state val1 (commit-anchors-next val systate))
              (all-addresses systate)))
    :enable (active-committee-at-previous-round-when-at-round
             validator-last-anchor-voters-p
             commit-anchors-possiblep
             commit-anchors-next
             last-anchor
             get-validator-state-of-update-validator-state
             nfix
             fix
             active-committee-at-round-of-extend-blockchain-no-change
             blocks-ordered-even-p-of-extend-blockchain
             certificates-ordered-even-p-of-collect-anchors
             ordered-even-p-necc-fixing
             collect-anchors-above-last-committed-round
             last-blockchain-round-p-necc-fixing
             posp
             pos-fix
             evenp
             certificate->round-of-certificate-with-author+round
             cardinality-of-successors-to-tally-leader-votes
             certificate->author-of-certificate-with-author+round))

  (defruled last-anchor-voters-p-of-commit-anchors-next
    (implies (and (ordered-even-p systate)
                  (last-blockchain-round-p systate)
                  (accepted-certificate-committee-p systate)
                  (last-anchor-present-p systate)
                  (commit-anchors-possiblep val systate)
                  (last-anchor-voters-p systate))
             (last-anchor-voters-p
              (commit-anchors-next val systate)))
    :enable (last-anchor-voters-p
             last-anchor-voters-p-necc
             validator-last-anchor-voters-p-of-commit-anchors-next))

  ;; timer-expires:

  (defruled validator-last-anchor-voters-p-of-timer-expires-next
    (implies (and (last-anchor-present-p systate)
                  (timer-expires-possiblep val systate)
                  (set::in val1 (correct-addresses systate))
                  (validator-last-anchor-voters-p
                   (get-validator-state val1 systate)
                   (all-addresses systate)))
             (validator-last-anchor-voters-p
              (get-validator-state val1 (timer-expires-next val systate))
              (all-addresses systate)))
    :enable (validator-last-anchor-voters-p
             validator-state->last-of-timer-expires-next
             validator-state->blockchain-of-timer-expires-next
             validator-state->dag-of-timer-expires-next
             last-anchor-of-timer-expires-next))

  (defruled last-anchor-voters-p-of-timer-expires-next
    (implies (and (last-anchor-present-p systate)
                  (timer-expires-possiblep val systate)
                  (last-anchor-voters-p systate))
             (last-anchor-voters-p
              (timer-expires-next val systate)))
    :enable (last-anchor-voters-p
             last-anchor-voters-p-necc
             validator-last-anchor-voters-p-of-timer-expires-next))

  ;; all events:

  (defruled last-anchor-voters-p-of-event-next
    (implies (and (unequivocal-accepted-certificates-p systate)
                  (signer-records-p systate)
                  (committees-in-system-p systate)
                  (system-fault-tolerant-p systate)
                  (signer-quorum-p systate)
                  (same-committees-p systate)
                  (no-self-buffer-p systate)
                  (no-self-endorsed-p systate)
                  (same-owned-certificates-p systate)
                  (accepted-certificate-committee-p systate)
                  (last-anchor-present-p systate)
                  (ordered-even-p systate)
                  (last-blockchain-round-p systate)
                  (last-anchor-voters-p systate)
                  (event-possiblep event systate))
             (last-anchor-voters-p (event-next event systate)))
    :enable (event-possiblep
             event-next)))
