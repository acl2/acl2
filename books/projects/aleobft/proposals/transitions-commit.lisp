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

(include-book "system-states")
(include-book "blockchains")

(local (include-book "../library-extensions/arithmetic-theorems"))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ transitions-commit
  :parents (transitions)
  :short "Transitions for anchor commitment."
  :long
  (xdoc::topstring
   (xdoc::p
    "Here we define the system state changes caused by @('commit') events.")
   (xdoc::p
    "This event involves a single validator.
     It can only happen in an odd round different from 1.
     The anchor at the preceding even round must be present,
     and it must have a sufficient stake of voters from the odd round.
     That anchor is committed, along with possibly more anchors
     that are reachable from that anchor and that have not been committed yet.
     Committing an anchor
     (the one in the even round voted from the odd round,
     or one reachable from it)
     amounts to generating a block, and adding it to the blockchain.
     Each block contains all the transactions
     from all the uncommitted certificates,
     linearized in some deterministic way."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define commit-possiblep ((val addressp) (systate system-statep))
  :returns (yes/no booleanp)
  :short "Check if a @('commit') event is possible."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('val') parameter of this function
     is the corresponding component of the @('commit') event.")
   (xdoc::p
    "The validator must be a correct one.
     We only model round advancement in correct validators.
     Faulty validators have no internal state in our model.")
   (xdoc::p
    "The validator must be at an odd round that is not 1.
     Thus, there is a preceding even round,
     which is the round with possibly the anchor to be committed
     (possibly along with other previous anchors).")
   (xdoc::p
    "The commit (i.e. even) round must be ahead of the last committed round,
     otherwise it means that we have already committed the anchor there.
     Note that the last committed round may be 0,
     in case no anchor has been committed yet.")
   (xdoc::p
    "The anchor must be present in the commit round,
     i.e. there must be a certificate authored by the leader.
     To calculate the leader,
     we need the active committee at the even round.
     The committee must be non-empty in order to calculate the leader.")
   (xdoc::p
    "The current odd round must have sufficient stake of
     voters with edges to the anchor.
     Note that we need to use the committee for the current odd round
     to calculate @($f$) (which is introduced in @(tsee max-faulty-for-total)).
     The stake must be strictly greater than @($f$),
     or equivalently greater than or equal to @($f+1$),
     but as also mentioned in @(tsee advance-possiblep),
     the latter is more common with numbers of validators,
     while the former seems more natural with stake.")
   (xdoc::p
    "The committees at both the odd and even round must be known;
     they may differ or not, as always.
     Since the odd round is ahead, if the committee is known there,
     it is also known for the even round, which is smaller.
     In order for the committee (at odd, and therefore also even, round)
     to be known, the validator's round must not have advanced
     further than the lookback amount from the latest block,
     otherwise the validator is effectively in a deadlocked state,
     ever unable to extend the blockchain.
     The latter aspect of AleoBFT may need some further study and analysis,
     in particular to establish a quantifiably adequate lookback amount.")
   (xdoc::p
    "If all of the above conditions are met, the anchor can be committed,
     along with possibly some prceding ones,
     down to, but not including, the one at the last committed round,
     or all of them is the last committed round is 0."))
  (b* (((unless (set::in (address-fix val) (correct-addresses systate))) nil)
       ((validator-state vstate) (get-validator-state val systate))
       ((when (evenp vstate.round)) nil)
       ((when (equal vstate.round 1)) nil)
       (commit-round (1- vstate.round))
       ((unless (> commit-round vstate.last)) nil)
       (commtt (active-committee-at-round vstate.round vstate.blockchain))
       ((unless commtt) nil)
       (prev-commtt (active-committee-at-round commit-round vstate.blockchain))
       ((unless (committee-nonemptyp prev-commtt)) nil)
       (leader (leader-at-round commit-round prev-commtt))
       (anchor? (cert-with-author+round leader commit-round vstate.dag))
       ((unless anchor?) nil)
       (voters (certs-with-round vstate.round vstate.dag))
       (yes-stake (leader-stake-votes leader voters commtt))
       ((unless (> yes-stake (committee-max-faulty-stake commtt))) nil))
    t)
  :guard-hints
  (("Goal"
    :in-theory (enable posp
                       active-committee-at-previous-round-when-at-round)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define commit-next ((val addressp) (systate system-statep))
  :guard (commit-possiblep val systate)
  :returns (new-systate system-statep)
  :short "New system state resulting from a @('commit') event."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('val') parameter of this function
     is the corresponding component of the @('commit') event.")
   (xdoc::p
    "Because of @(tsee commit-possiblep),
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
     to the one for the latest anchor we committed."))
  (b* (((validator-state vstate) (get-validator-state val systate))
       (commit-round (1- vstate.round))
       (commtt (active-committee-at-round commit-round vstate.blockchain))
       (leader (leader-at-round commit-round commtt))
       (anchor (cert-with-author+round leader commit-round vstate.dag))
       (anchors (collect-anchors anchor
                                 (- commit-round 2)
                                 vstate.last
                                 vstate.dag
                                 vstate.blockchain))
       ((mv new-blockchain new-committed)
        (extend-blockchain anchors
                           vstate.dag
                           vstate.blockchain
                           vstate.committed))
       (new-vstate
        (change-validator-state
         vstate
         :last commit-round
         :blockchain new-blockchain
         :committed new-committed))
       (systate (update-validator-state val new-vstate systate)))
    systate)
  :guard-hints
  (("Goal"
    :in-theory (enable commit-possiblep
                       natp
                       aleobft::evenp-of-1-less-when-not-evenp
                       aleobft::evenp-of-3-less-when-not-evenp
                       active-committee-at-previous-round-when-at-round
                       active-committee-at-previous3-round-when-at-round
                       certificate->round-of-cert-with-author+round)))
  :hooks (:fix)

  ///

  (defret correct-addresses-of-commit-next
    (equal (correct-addresses new-systate)
           (correct-addresses systate))
    :hyp (commit-possiblep val systate)
    :hints (("Goal" :in-theory (enable commit-possiblep))))

  (local (in-theory (enable get-validator-state-of-update-validator-state)))

  (defret validator-state->round-of-commit-next
    (equal (validator-state->round (get-validator-state val1 new-systate))
           (validator-state->round (get-validator-state val1 systate))))

  (defret validator-state->dag-of-commit-next
    (equal (validator-state->dag (get-validator-state val1 new-systate))
           (validator-state->dag (get-validator-state val1 systate))))

  (defret validator-state->proposed-of-commit-next
    (equal (validator-state->proposed (get-validator-state val1 new-systate))
           (validator-state->proposed (get-validator-state val1 systate))))

  (defret validator-state->endorsed-of-commit-next
    (equal (validator-state->endorsed (get-validator-state val1 new-systate))
           (validator-state->endorsed (get-validator-state val1 systate))))

  (defret validator-state->last-of-commit-next
    (equal (validator-state->last (get-validator-state val1 new-systate))
           (if (equal (address-fix val1) (address-fix val))
               (1- (validator-state->round (get-validator-state val1 systate)))
             (validator-state->last (get-validator-state val1 systate))))
    :hints (("Goal" :in-theory (enable nfix))))
  (in-theory (disable validator-state->last-of-commit-next))

  (defret validator-state->blockchain-of-commit-next
    (equal (validator-state->blockchain (get-validator-state val1 new-systate))
           (if (equal (address-fix val1) (address-fix val))
               (b* (((validator-state vstate)
                     (get-validator-state val1 systate))
                    (commit-round (1- vstate.round))
                    (commtt
                     (active-committee-at-round commit-round vstate.blockchain))
                    (leader (leader-at-round commit-round commtt))
                    (anchor
                     (cert-with-author+round leader commit-round vstate.dag))
                    (anchors (collect-anchors anchor
                                              (- commit-round 2)
                                              vstate.last
                                              vstate.dag
                                              vstate.blockchain)))
                 (mv-nth 0 (extend-blockchain anchors
                                              vstate.dag
                                              vstate.blockchain
                                              vstate.committed)))
             (validator-state->blockchain (get-validator-state val1 systate)))))
  (in-theory (disable validator-state->blockchain-of-commit-next))

  (defret validator-state->committed-of-commit-next
    (equal (validator-state->committed (get-validator-state val1 new-systate))
           (if (equal (address-fix val1) (address-fix val))
               (b* (((validator-state vstate)
                     (get-validator-state val1 systate))
                    (commit-round (1- vstate.round))
                    (commtt
                     (active-committee-at-round commit-round vstate.blockchain))
                    (leader (leader-at-round commit-round commtt))
                    (anchor
                     (cert-with-author+round leader commit-round vstate.dag))
                    (anchors (collect-anchors anchor
                                              (- commit-round 2)
                                              vstate.last
                                              vstate.dag
                                              vstate.blockchain)))
                 (mv-nth 1 (extend-blockchain anchors
                                              vstate.dag
                                              vstate.blockchain
                                              vstate.committed)))
             (validator-state->committed (get-validator-state val1 systate)))))
  (in-theory (disable validator-state->blockchain-of-commit-next))

  (defret get-network-state-of-commit-next
    (equal (get-network-state new-systate)
           (get-network-state systate))))
