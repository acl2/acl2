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

(include-book "system-states")
(include-book "operations-faults-and-quora")
(include-book "operations-voting")
(include-book "operations-blockchain")

(local (include-book "../library-extensions/oset-theorems"))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ transitions-commit-anchors
  :parents (transitions)
  :short "Transitions for anchor commitment."
  :long
  (xdoc::topstring
   (xdoc::p
    "Here we define the system state transitions
     caused by @('commit-anchors') events."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define commit-anchors-possiblep ((val addressp) (systate system-statep))
  :returns (yes/no booleanp)
  :short "Check if a @('commit-anchors') event is possible."
  :long
  (xdoc::topstring
   (xdoc::p
    "The validator must be at an odd round that is not 1.
     Thus, there is a preceding non-zero even round,
     which is the round with possibly the anchor to be committed
     (possibly along with previous anchors).
     The commit round must be ahead of the last committed round,
     otherwise it means that we have already committed the anchor.
     The anchor must be present in the commit round,
     i.e. there must be a certificate authored by the leader.
     Furthermore, the current odd round must have sufficient voters
     with edges to the anchor.
     If all of these conditions are met,
     the anchor can be committed,
     along with possibly some prceding ones,
     down to but not including the one at the last committed round;
     the committing is specified in @(tsee commit-anchors-next)."))
  (b* (((unless (set::in val (correct-addresses systate))) nil)
       (vstate (get-validator-state val systate))
       (current-round (validator-state->round vstate))
       ((when (evenp current-round)) nil)
       ((when (equal current-round 1)) nil)
       (commit-round (1- current-round))
       (last-committed-round (validator-state->last vstate))
       ((unless (> commit-round last-committed-round)) nil)
       (vals (all-addresses systate))
       (leader (leader-at-round commit-round vals))
       (dag (validator-state->dag vstate))
       (anchor? (cert-with-author+round leader commit-round dag))
       ((unless anchor?) nil)
       (voters (certs-with-round current-round dag))
       ((mv yes-votes &) (tally-leader-votes leader voters))
       ((unless (>= yes-votes (1+ (max-faulty systate)))) nil))
    t)
  :guard-hints
  (("Goal" :in-theory (enable evenp
                              posp
                              set::not-emptyp-when-in-of-subset
                              correct-addresses-subset-all-addresses
                              in-all-addresses-when-in-correct-addresses)))
  :prepwork ((local (include-book "arithmetic-3/top" :dir :system)))

  ///

  (fty::deffixequiv commit-anchors-possiblep
    :args ((systate system-statep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define commit-anchors-next ((val addressp) (systate system-statep))
  :guard (commit-anchors-possiblep val systate)
  :returns (new-systate system-statep)
  :short "New state resulting from a @('commit-anchors') event."
  :long
  (xdoc::topstring
   (xdoc::p
    "Because of @(tsee commit-anchors-possiblep),
     the validator is in an odd round greater than one,
     and the even round immediately before it
     has an anchor for the leader at that round.
     We retrieve that anchor,
     and we use @(tsee collect-anchors)
     to collect that anchor and all the preceding anchors
     that must be committed and have not already been committed.
     Then we use @(tsee extend-blockchain)
     to extend the blockchain, and the set of all committed certificates.
     We also update the last committed round
     to the one for the anchor at the even round."))
  (b* ((vstate (get-validator-state val systate))
       (vals (all-addresses systate))
       (new-vstate (commit-anchors-next-val vals vstate)))
    (update-validator-state val new-vstate systate))
  :guard-hints
  (("Goal" :in-theory (enable commit-anchors-possiblep
                              correct-addresses-subset-all-addresses
                              in-all-addresses-when-in-correct-addresses
                              set::not-emptyp-when-in-of-subset)))

  :prepwork
  ((define commit-anchors-next-val ((vals address-setp)
                                    (vstate validator-statep))
     :guard (and (not (set::emptyp vals))
                 (b* ((round (validator-state->round vstate)))
                   (and (oddp round)
                        (not (equal round 1))
                        (cert-with-author+round
                         (leader-at-round (1- round) vals)
                         (1- round)
                         (validator-state->dag vstate)))))
     :returns (new-vstate validator-statep)
     :parents nil
     (b* ((current-round (validator-state->round vstate))
          (commit-round (1- current-round))
          (leader (leader-at-round commit-round vals))
          (dag (validator-state->dag vstate))
          (anchor (cert-with-author+round leader commit-round dag))
          (last-committed-round (validator-state->last vstate))
          (anchors (collect-anchors anchor
                                    (- commit-round 2)
                                    last-committed-round
                                    dag
                                    vals))
          (blockchain (validator-state->blockchain vstate))
          (committed-certs (validator-state->committed vstate))
          ((mv new-blockchain new-committed-certs)
           (extend-blockchain anchors dag blockchain committed-certs)))
       (change-validator-state
        vstate
        :blockchain new-blockchain
        :last commit-round
        :committed new-committed-certs))
     :guard-hints
     (("Goal"
       :in-theory (enable posp
                          natp
                          evenp
                          oddp)))
     :prepwork ((local (include-book "arithmetic-3/top" :dir :system)))))

  ///

  (fty::deffixequiv commit-anchors-next
    :args ((systate system-statep)))

  (defruled validator-state->round-of-commit-anchors-next
    (implies (and (set::in val (correct-addresses systate))
                  (commit-anchors-possiblep val1 systate))
             (equal (validator-state->round
                     (get-validator-state val
                                          (commit-anchors-next val1 systate)))
                    (validator-state->round
                     (get-validator-state val systate))))
    :enable (commit-anchors-next-val
             commit-anchors-possiblep
             get-validator-state-of-update-validator-state))

  (defruled validator-state->dag-of-commit-anchors-next
    (implies (and (set::in val (correct-addresses systate))
                  (commit-anchors-possiblep val1 systate))
             (equal (validator-state->dag
                     (get-validator-state val
                                          (commit-anchors-next val1 systate)))
                    (validator-state->dag
                     (get-validator-state val systate))))
    :enable (commit-anchors-next-val
             commit-anchors-possiblep
             get-validator-state-of-update-validator-state))

  (defruled validator-state->last-of-commit-anchors-next
    (implies (and (set::in val (correct-addresses systate))
                  (commit-anchors-possiblep val1 systate))
             (equal (validator-state->last
                     (get-validator-state val
                                          (commit-anchors-next
                                           val1 systate)))
                    (if (equal val val1)
                        (1- (validator-state->round
                             (get-validator-state val systate)))
                      (validator-state->last
                       (get-validator-state val systate)))))
    :enable (commit-anchors-possiblep
             commit-anchors-next-val
             nfix))

  (defruled validator-state->blockchain-of-commit-anchors-next
    (implies
     (and (set::in val (correct-addresses systate))
          (commit-anchors-possiblep val1 systate))
     (equal (validator-state->blockchain
             (get-validator-state val
                                  (commit-anchors-next
                                   val1 systate)))
            (if (equal val val1)
                (b* (((validator-state vstate)
                      (get-validator-state val systate))
                     (commit-round (1- vstate.round))
                     (leader (leader-at-round commit-round
                                              (all-addresses systate)))
                     (anchor (cert-with-author+round leader
                                                                commit-round
                                                                vstate.dag))
                     (anchors (collect-anchors anchor
                                               (- commit-round 2)
                                               vstate.last
                                               vstate.dag
                                               (all-addresses systate))))
                  (mv-nth 0 (extend-blockchain anchors
                                               vstate.dag
                                               vstate.blockchain
                                               vstate.committed)))
              (validator-state->blockchain
               (get-validator-state val systate)))))
    :enable (commit-anchors-next-val
             commit-anchors-possiblep
             extend-blockchain)))
