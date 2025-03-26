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

(include-book "system-states")
(include-book "blockchains")

(local (include-book "arithmetic-3/top" :dir :system))

;; cert_param: (non-acl2r)

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
     caused by @('commit-anchors') events.")
   (xdoc::p
    "An anchor commitment event involves just one correct validator.
     Since we do not model the internal state of faulty validators,
     there is no point modeling events that change that internal state.")
   (xdoc::p
    "This event can only happen in an odd round different from 1.
     The anchor at the preceding even round must be present,
     and it must have a sufficient number of voters from the odd round.
     That anchor is committed, along with possibly more anchors
     that are reachable from that anchor and that have not been committed yet.
     Committing an anchor
     (the one in the even round voted from the odd round,
     or one reachable from it)
     amounts to generating a block, and adding it to the blockchain.
     Each block contains all the transactions
     from all the uncommitted certificates,
     linearized in some deterministic way.")
   (xdoc::p
    "An anchor commitment event does not involve the network."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define commit-anchors-possiblep ((val addressp) (systate system-statep))
  :returns (yes/no booleanp)
  :short "Check if a @('commit-anchors') event is possible."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('val') input of this function is
     the address in the @('commit-anchors') event;
     see @(tsee event).")
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
     otherwise it means that we have already committed the anchor.
     Note that the last committed round may be 0,
     in case no anchor has been committed yet.")
   (xdoc::p
    "The anchor must be present in the commit round,
     i.e. there must be a certificate authored by the leader.
     To calculate the leader,
     we need the active committee at the even round.")
   (xdoc::p
    "The current odd round must have sufficient voters
     with edges to the anchor.
     Note that we need to use the committee for the current odd round
     to calculate @($f + 1$)
     (where @($f$) is introduced in @(tsee max-faulty-for-total).")
   (xdoc::p
    "The committees at both the odd and even round must be known;
     they may differ or not.
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
     or all of them is the last committed round is 0.")
   (xdoc::p
    "Note that we instantiate the @('all-vals') parameter
     of @(tsee create-certificate-endorser-possiblep)
     with the set of all the addresses of all validators in the system;
     that is indeed the rols of @('all-vals'),
     as explained in @(tsee update-committee-with-transaction)."))
  (b* (((unless (set::in (address-fix val) (correct-addresses systate))) nil)
       ((validator-state vstate) (get-validator-state val systate))
       ((when (evenp vstate.round)) nil)
       ((when (equal vstate.round 1)) nil)
       (vstate.round-commtt
        (active-committee-at-round vstate.round
                                   vstate.blockchain
                                   (all-addresses systate)))
       ((unless vstate.round-commtt) nil)
       (commit-round (1- vstate.round))
       ((unless (> commit-round vstate.last)) nil)
       (commit-round-commtt
        (active-committee-at-round commit-round
                                   vstate.blockchain
                                   (all-addresses systate)))
       (leader (leader-at-round commit-round commit-round-commtt))
       (anchor?
        (certificate-with-author+round leader commit-round vstate.dag))
       ((unless anchor?) nil)
       (voters (certificates-with-round vstate.round vstate.dag))
       ((mv yes-votes &) (tally-leader-votes leader voters))
       ((unless (>= yes-votes
                    (1+ (committee-max-faulty vstate.round-commtt))))
        nil))
    t)
  :guard-hints
  (("Goal"
    :in-theory (enable posp
                       active-committee-at-previous-round-when-at-round)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define commit-anchors-next ((val addressp) (systate system-statep))
  :guard (commit-anchors-possiblep val systate)
  :returns (new-systate system-statep)
  :short "New state resulting from a @('commit-anchors') event."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('val') input of this function is
     the address in the @('commit-anchors') event;
     see @(tsee event).")
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
     to the one for the latest anchor we committed.")
   (xdoc::p
    "Note that we instantiate the @('all-vals') parameter
     of @(tsee create-certificate-endorser-possiblep)
     with the set of all the addresses of all validators in the system;
     that is indeed the rols of @('all-vals'),
     as explained in @(tsee update-committee-with-transaction)."))
  (b* (((validator-state vstate) (get-validator-state val systate))
       (commit-round (1- vstate.round))
       (commtt (active-committee-at-round commit-round
                                          vstate.blockchain
                                          (all-addresses systate)))
       (leader (leader-at-round commit-round commtt))
       (anchor
        (certificate-with-author+round leader commit-round vstate.dag))
       (anchors (collect-anchors anchor
                                 (- commit-round 2)
                                 vstate.last
                                 vstate.dag
                                 vstate.blockchain
                                 (all-addresses systate)))
       ((mv new-blockchain new-committed)
        (extend-blockchain anchors
                           vstate.dag
                           vstate.blockchain
                           vstate.committed))
       (new-vstate
        (change-validator-state
         vstate
         :blockchain new-blockchain
         :last commit-round
         :committed new-committed))
       (systate (update-validator-state val new-vstate systate)))
    systate)
  :guard-hints
  (("Goal"
    :in-theory (enable commit-anchors-possiblep
                       posp
                       natp
                       evenp
                       active-committee-at-previous-round-when-at-round
                       active-committee-at-previous3-round-when-at-round
                       certificate->round-of-certificate-with-author+round)))
  :hooks (:fix)

  ///

  (defret all-addresses-of-commit-anchors-next
    (equal (all-addresses new-systate)
           (all-addresses systate))
    :hyp (commit-anchors-possiblep val systate)
    :hints (("Goal" :in-theory (enable commit-anchors-possiblep))))

  (defret correct-addresses-of-commit-anchors-next
    (equal (correct-addresses new-systate)
           (correct-addresses systate))
    :hyp (commit-anchors-possiblep val systate)
    :hints (("Goal" :in-theory (enable commit-anchors-possiblep))))

  (defret faulty-addresses-of-commit-anchors-next
    (equal (faulty-addresses new-systate)
           (faulty-addresses systate))
    :hyp (commit-anchors-possiblep val systate)
    :hints (("Goal" :in-theory (enable commit-anchors-possiblep))))

  (defret validator-state->dag-of-commit-anchors-next
    (equal (validator-state->dag (get-validator-state val1 new-systate))
           (validator-state->dag (get-validator-state val1 systate)))
    :hyp (commit-anchors-possiblep val systate)
    :hints
    (("Goal"
      :in-theory (enable commit-anchors-possiblep
                         get-validator-state-of-update-validator-state))))

  (defret validator-state->buffer-of-commit-anchors-next
    (equal (validator-state->buffer (get-validator-state val1 new-systate))
           (validator-state->buffer (get-validator-state val1 systate)))
    :hyp (commit-anchors-possiblep val systate)
    :hints
    (("Goal"
      :in-theory (enable commit-anchors-possiblep
                         get-validator-state-of-update-validator-state))))

  (defret validator-state->endorsed-of-commit-anchors-next
    (equal (validator-state->endorsed
            (get-validator-state val1 new-systate))
           (validator-state->endorsed
            (get-validator-state val1 systate)))
    :hyp (commit-anchors-possiblep val systate)
    :hints
    (("Goal"
      :in-theory
      (enable commit-anchors-possiblep
              get-validator-state-of-update-validator-state))))

  (defret validator-state->last-of-commit-anchors-next
    (equal (validator-state->last
            (get-validator-state val1 new-systate))
           (if (equal (address-fix val1) (address-fix val))
               (1- (validator-state->round
                    (get-validator-state val systate)))
             (validator-state->last
              (get-validator-state val1 systate))))
    :hyp (commit-anchors-possiblep val systate)
    :hints
    (("Goal"
      :in-theory
      (enable commit-anchors-possiblep
              get-validator-state-of-update-validator-state
              nfix))))

  (defret validator-state->blockchain-of-commit-anchors-next
    (equal (validator-state->blockchain
            (get-validator-state val1 new-systate))
           (if (equal val1 (address-fix val))
               (b* (((validator-state vstate)
                     (get-validator-state val1 systate))
                    (commit-round (1- vstate.round))
                    (commtt (active-committee-at-round
                             commit-round
                             vstate.blockchain
                             (all-addresses systate)))
                    (leader (leader-at-round commit-round commtt))
                    (anchor (certificate-with-author+round
                             leader commit-round vstate.dag))
                    (anchors (collect-anchors anchor
                                              (- commit-round 2)
                                              vstate.last
                                              vstate.dag
                                              vstate.blockchain
                                              (all-addresses systate))))
                 (mv-nth 0 (extend-blockchain anchors
                                              vstate.dag
                                              vstate.blockchain
                                              vstate.committed)))
             (validator-state->blockchain
              (get-validator-state val1 systate))))
    :hyp (and (set::in val1 (correct-addresses systate))
              (commit-anchors-possiblep val systate))
    :hints
    (("Goal"
      :in-theory (enable commit-anchors-possiblep
                         get-validator-state-of-update-validator-state))))

  (defret validator-state->committed-of-commit-anchors-next
    (equal (validator-state->committed
            (get-validator-state val1 new-systate))
           (if (equal val1 (address-fix val))
               (b* (((validator-state vstate)
                     (get-validator-state val systate))
                    (commit-round (1- vstate.round))
                    (commtt (active-committee-at-round
                             commit-round
                             vstate.blockchain
                             (all-addresses systate)))
                    (leader (leader-at-round commit-round commtt))
                    (anchor (certificate-with-author+round
                             leader commit-round vstate.dag))
                    (anchors (collect-anchors anchor
                                              (- commit-round 2)
                                              vstate.last
                                              vstate.dag
                                              vstate.blockchain
                                              (all-addresses systate))))
                 (mv-nth 1 (extend-blockchain anchors
                                              vstate.dag
                                              vstate.blockchain
                                              vstate.committed)))
             (validator-state->committed
              (get-validator-state val1 systate))))
    :hyp (and (set::in val1 (correct-addresses systate))
              (commit-anchors-possiblep val systate))
    :hints
    (("Goal"
      :in-theory (enable commit-anchors-possiblep
                         get-validator-state-of-update-validator-state))))

  (defret get-network-state-of-commit-anchors-next
    (equal (get-network-state new-systate)
           (get-network-state systate)))

  (in-theory (disable validator-state->dag-of-commit-anchors-next
                      validator-state->buffer-of-commit-anchors-next
                      validator-state->endorsed-of-commit-anchors-next
                      validator-state->last-of-commit-anchors-next
                      validator-state->blockchain-of-commit-anchors-next
                      validator-state->committed-of-commit-anchors-next
                      get-network-state-of-commit-anchors-next)))
