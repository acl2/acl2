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
(include-book "elections")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ transitions-advance-round
  :parents (transitions)
  :short "Transitions for round advancement."
  :long
  (xdoc::topstring
   (xdoc::p
    "Here we define the system state transitions
     caused by @('advance-round') events.")
   (xdoc::p
    "A round advancement event involves just one correct validator.
     Since we do not model the internal state of faulty validators,
     there is no point modeling events that change that internal state.")
   (xdoc::p
    "This is not the only event that advances the round:
     see @(see transitions-store-certificate),
     where the round may advance to catch up a validator to others.
     However, @('advance-round') is the main event for round advancement.")
   (xdoc::p
    "Our current modeling of certificate creation as an atomic event
     interferes with properly modeling certain aspects of round advancement.
     For instance, it would be reasonable to allow a validator to advance round
     after it has created a proposal but before it creates the ceritifcate,
     if we had a more detailed model with explicit proposals and signatures;
     after the round has advanced, it would be possible for the validator
     to receive enough signatures and to create a certificate,
     which would be for the round of the proposal,
     and not the current round (which has advanced).
     Alternatively, we could relax the requirement that
     certificate creation must happen for the current round
     (in @(tsee create-certificate-possiblep)).
     But for now we do not worry about these aspects,
     because they do not affect the properties
     that we are proving in the short term, mainly blockchain non-forking.
     The exact details of round advancement need further study.")
   (xdoc::p
    "A round advancement event does not involve the network."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define advance-round-possiblep ((val addressp) (systate system-statep))
  :returns (yes/no booleanp)
  :short "Check if a round advancement event is possible."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('val') input of this function is
     the address in the @('advance-round') event;
     see @(tsee event).")
   (xdoc::p
    "The validator must be a correct one.
     We only model round advancement in correct validators.
     Faulty validators have no internal state in our model.")
   (xdoc::p
    "The committee at the current round must be known.
     Otherwise, we cannot check the appropriate conditions.")
   (xdoc::p
    "There are three cases to consider:
     round 1, even round, and odd round different from 1.
     The reason why even and odd rounds differ is that
     odd rounds vote for the leader at the preceding even round.
     The reason why round 1 is different from other odd rounds
     is that there is no round before round 1 and thus no leader to vote.")
   (xdoc::p
    "The following conditions for round advancement are based on
     our previous model of AleoBFT with static committee,
     which was in turn based on a probably now outdated snarkOS implementation.
     We will probably need to revise these conditions,
     but there is no urgency, because they do not affect
     the properties that we plan to prove in the short term:
     for those properties, we could simply define that
     round advancement is always possible.")
   (xdoc::p
    "In round 1, we always allow the round to advance.
     Note that this may lead to a quick deadlock,
     if all the validators in the genesis committee advance their round
     before generating a certificate for round 1,
     because when they are in round 2 they will never have
     enough certificates in round 1 to create a certificate for round 2.
     But again, this does not matter for now.
     Obviosuly, our model does not require that validators go into deadlock,
     it merely allows that.")
   (xdoc::p
    "In an even round, we advance if
     (1) we have the leader certificate (i.e. anchor) at this even round, or
     (2) the timer is expired and
     we have a quorum of certificates in this even round.
     The leader and quorum are calculated over
     the active committee at the current, even round.
     That committee must be non-empty.")
   (xdoc::p
    "In an odd round different from 1,
     there are four possible conditions for advancing:
     (1) there is no leader certificate (i.e. anchor)
     at the even round that immediately precedes this odd round;
     (2) there are at least @($f + 1$) certificates at this odd round
     that vote for the leader certificate at the preceding even round;
     (3) there are at least @($n - f$) certificates at this odd round
     that do not vote for the leader certificate at the preceding even round;
     (4) the timer is expired.
     Recall that @($f$) is introduced in @(tsee max-faulty-for-total).
     Note that the leader is calculated over
     the active committee at the previous, even round
     (which must be known because we have already checked that
     the active committee at the current, odd round is known),
     while the votes are calculated over
     the active committee at the current, odd round."))
  (b* (((unless (set::in (address-fix val) (correct-addresses systate))) nil)
       ((validator-state vstate) (get-validator-state val systate))
       (commtt (active-committee-at-round vstate.round vstate.blockchain))
       ((unless commtt) nil)
       ((when (= vstate.round 1)) t))
    (if (evenp vstate.round)
        (b* (((unless (committee-nonemptyp commtt)) nil)
             (leader (leader-at-round vstate.round commtt))
             (anchor? (get-certificate-with-author+round leader
                                                         vstate.round
                                                         vstate.dag)))
          (or (and anchor? t)
              (and (timer-case vstate.timer :expired)
                   (>= (set::cardinality
                        (get-certificates-with-round vstate.round vstate.dag))
                       (committee-quorum commtt)))))
      (b* ((prev-commtt
            (active-committee-at-round (1- vstate.round) vstate.blockchain))
           ((unless (committee-nonemptyp prev-commtt)) nil)
           (leader (leader-at-round (1- vstate.round) prev-commtt))
           (anchor? (get-certificate-with-author+round leader
                                                       (1- vstate.round)
                                                       vstate.dag))
           (voters (get-certificates-with-round vstate.round vstate.dag))
           ((mv yes-votes no-votes) (tally-leader-votes leader voters)))
        (or (not anchor?)
            (>= yes-votes
                (1+ (committee-max-faulty commtt)))
            (>= no-votes
                (committee-quorum commtt))
            (timer-case vstate.timer :expired)))))
  :guard-hints
  (("Goal" :in-theory (enable
                       posp
                       active-committee-at-earlier-round-when-at-later-round)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define advance-round-next ((val addressp) (systate system-statep))
  :guard (advance-round-possiblep val systate)
  :returns (new-systate system-statep)
  :short "New system state resulting from an @('advance-round') event."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('val') input of this function is
     the address in the @('advance-round') event;
     see @(tsee event).")
   (xdoc::p
    "We increment the validator' round by one.
     We also restart the timer, setting it to running
     (which is a no-op if the round has advanced not due to a timeout."))
  (b* (((validator-state vstate) (get-validator-state val systate))
       (new-round (1+ vstate.round))
       (new-timer (timer-running))
       (new-vstate (change-validator-state vstate
                                           :round new-round
                                           :timer new-timer))
       (systate (update-validator-state val new-vstate systate)))
    systate)
  :guard-hints (("Goal" :in-theory (enable advance-round-possiblep)))
  :hooks (:fix))
