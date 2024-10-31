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
(include-book "operations-leaders")
(include-book "operations-voting")

(local (include-book "../library-extensions/oset-theorems"))

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
     caused by @('advance-round') events."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define advance-round-possiblep ((val addressp) (systate system-statep))
  :returns (yes/no booleanp)
  :short "Check if an @('advance-round') event is possible."
  :long
  (xdoc::topstring
   (xdoc::p
    "The conditions for advancing to the next round
     are different for even and odd rounds.")
   (xdoc::p
    "In an even round, we advance if
     (1) we have the leader certificate (i.e. anchor) at this even round, or
     (2) the timer is expired and
     we have a quorum of certificates in this even round.")
   (xdoc::p
    "In an odd round that is not 1 (which is treated specially, see below),
     there are four possible conditions for advancing:
     (1) there is no leader certificate (i.e. anchor)
     at the even round that immediately precedes this odd round;
     (2) there are at least @($F + 1$) certificates at this odd round
     that vote for the leader certificate at the preceding even round,
     i.e. that have edges to that certificate;
     (3) there are at least @($n - F$) certificates at this odd round
     that do not vote for the leader certificate at the preceding even round,
     i.e. that have no edged to that certificate;
     (4) the timer is expired.
     Recall that @($F$) is introduced in @(tsee max-faulty-for-total).")
   (xdoc::p
    "For round 1, note that there is no preceding even round,
     so there is no notion of leader certificate for the preceding round.
     In this case, there is no leader certificate, and so we always advance."))
  (b* (((unless (set::in val (correct-addresses systate))) nil)
       (vstate (get-validator-state val systate))
       (round (validator-state->round vstate))
       (dag (validator-state->dag vstate))
       (timeout (timer-case (validator-state->timer vstate) :expired))
       (vals (all-addresses systate)))
    (if (evenp round)
        (b* ((leader (leader-at-round round vals))
             (anchor? (certificate-with-author+round leader round dag)))
          (or (and anchor? t)
              (and timeout
                   (>= (set::cardinality
                        (certificates-with-round round dag))
                       (quorum systate)))))
      (or (equal round 1)
          (b* ((leader (leader-at-round (1- round) vals))
               (anchor?
                (certificate-with-author+round leader (1- round) dag))
               (voters (certificates-with-round round dag))
               ((mv yes-votes no-votes) (tally-leader-votes leader voters)))
            (or (not anchor?)
                (>= yes-votes
                    (1+ (max-faulty systate)))
                (>= no-votes
                    (quorum systate))
                timeout)))))
  :guard-hints
  (("Goal" :in-theory (enable evenp
                              posp
                              correct-addresses-subset-all-addresses
                              in-all-addresses-when-in-correct-addresses
                              set::not-emptyp-when-in-of-subset)))
  :prepwork ((local (include-book "arithmetic-3/top" :dir :system)))

  ///

  (fty::deffixequiv advance-round-possiblep
    :args ((systate system-statep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define advance-round-next ((val addressp) (systate system-statep))
  :guard (advance-round-possiblep val systate)
  :returns (new-systate system-statep)
  :short "New state resulting from an @('advance-round') event."
  :long
  (xdoc::topstring
   (xdoc::p
    "The round number is incremented by 1.")
   (xdoc::p
    "The timer is restarted, i.e. it is set to running."))
  (b* ((vstate (get-validator-state val systate))
       (round (validator-state->round vstate))
       (new-vstate (advance-round-next-val round vstate)))
    (update-validator-state val new-vstate systate))
  :guard-hints
  (("Goal" :in-theory (enable advance-round-possiblep
                              in-all-addresses-when-in-correct-addresses)))

  :prepwork
  ((define advance-round-next-val ((round posp) (vstate validator-statep))
     :returns (new-vstate validator-statep)
     :parents nil
     (change-validator-state vstate
                             :round (1+ round)
                             :timer (timer-running))))

  ///

  (fty::deffixequiv advance-round-next
    :args ((systate system-statep)))

  (defruled validator-state->round-of-advance-round-next
    (implies (and (set::in val (correct-addresses systate))
                  (advance-round-possiblep val1 systate))
             (equal (validator-state->round
                     (get-validator-state val
                                          (advance-round-next val1 systate)))
                    (if (equal val val1)
                        (1+ (validator-state->round
                             (get-validator-state val systate)))
                      (validator-state->round
                       (get-validator-state val systate)))))
    :enable (advance-round-next-val
             advance-round-possiblep))

  (defruled validator-state->dag-of-advance-round-next
    (implies (and (set::in val (correct-addresses systate))
                  (advance-round-possiblep val1 systate))
             (equal (validator-state->dag
                     (get-validator-state val
                                          (advance-round-next val1 systate)))
                    (validator-state->dag
                     (get-validator-state val systate))))
    :enable (advance-round-next-val
             advance-round-possiblep
             get-validator-state-of-update-validator-state))

  (defruled validator-state->last-of-advance-round-next
    (implies (and (set::in val (correct-addresses systate))
                  (advance-round-possiblep val1 systate))
             (equal (validator-state->last
                     (get-validator-state val
                                          (advance-round-next
                                           val1 systate)))
                    (validator-state->last
                     (get-validator-state val systate))))
    :enable (advance-round-possiblep
             advance-round-next-val
             get-validator-state-of-update-validator-state
             nfix))

  (defruled validator-state->blockchain-of-advance-round-next
    (implies (and (set::in val (correct-addresses systate))
                  (advance-round-possiblep val1 systate))
             (equal (validator-state->blockchain
                     (get-validator-state val
                                          (advance-round-next
                                           val1 systate)))
                    (validator-state->blockchain
                     (get-validator-state val systate))))
    :enable (advance-round-possiblep
             advance-round-next-val
             get-validator-state-of-update-validator-state))

  (defruled validator-state->committed-of-advance-round-next
    (implies (and (set::in val (correct-addresses systate))
                  (advance-round-possiblep val1 systate))
             (equal (validator-state->committed
                     (get-validator-state val
                                          (advance-round-next
                                           val1 systate)))
                    (validator-state->committed
                     (get-validator-state val systate))))
    :enable (advance-round-possiblep
             advance-round-next-val
             get-validator-state-of-update-validator-state)))
