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

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ transitions-timer-expires
  :parents (transitions)
  :short "Transitions for timer expiration."
  :long
  (xdoc::topstring
   (xdoc::p
    "Here we define the system state transitions
     caused by @('timer-expires') events."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define timer-expires-possiblep ((val addressp) (systate system-statep))
  :returns (yes/no booleanp)
  :short "Check if a @('timer-expires') event is possible."
  :long
  (xdoc::topstring
   (xdoc::p
    "This event is possible when the timer is running.
     The address must be that of a correct validator;
     we do not model the internal state of faulty validators,
     and whether they have any timers at all."))
  (b* (((unless (set::in val (correct-addresses systate))) nil)
       (vstate (get-validator-state val systate)))
    (timer-case (validator-state->timer vstate) :running))
  :guard-hints
  (("Goal" :in-theory (enable in-all-addresses-when-in-correct-addresses)))

  ///

  (fty::deffixequiv timer-expires-possiblep
    :args ((systate system-statep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define timer-expires-next ((val addressp) (systate system-statep))
  :guard (timer-expires-possiblep val systate)
  :returns (new-systate system-statep)
  :short "New state resulting from a @('timer-expires') event."
  :long
  (xdoc::topstring
   (xdoc::p
    "The timer state is set to expired.
     Recall that we do not model real time here,
     just the sequences of events that may happen in the system."))
  (b* ((vstate (get-validator-state val systate))
       (new-vstate (timer-expires-next-val vstate)))
    (update-validator-state val new-vstate systate))
  :guard-hints
  (("Goal" :in-theory (enable timer-expires-possiblep
                              in-all-addresses-when-in-correct-addresses)))

  :prepwork
  ((define timer-expires-next-val ((vstate validator-statep))
     :returns (new-vstate validator-statep)
     :parents nil
     (change-validator-state vstate :timer (timer-expired))))

  ///

  (fty::deffixequiv timer-expires-next
    :args ((systate system-statep)))

  (defruled validator-state->round-of-timer-expires-next
    (implies (and (set::in val (correct-addresses systate))
                  (timer-expires-possiblep val1 systate))
             (equal (validator-state->round
                     (get-validator-state val
                                          (timer-expires-next val1 systate)))
                    (validator-state->round
                     (get-validator-state val systate))))
    :enable (timer-expires-next-val
             timer-expires-possiblep
             get-validator-state-of-update-validator-state))

  (defruled validator-state->dag-of-timer-expires-next
    (implies (and (set::in val (correct-addresses systate))
                  (timer-expires-possiblep val1 systate))
             (equal (validator-state->dag
                     (get-validator-state val
                                          (timer-expires-next val1 systate)))
                    (validator-state->dag
                     (get-validator-state val systate))))
    :enable (timer-expires-next-val
             timer-expires-possiblep
             get-validator-state-of-update-validator-state))

  (defruled validator-state->last-of-timer-expires-next
    (implies (and (set::in val (correct-addresses systate))
                  (timer-expires-possiblep val1 systate))
             (equal (validator-state->last
                     (get-validator-state val
                                          (timer-expires-next
                                           val1 systate)))
                    (validator-state->last
                     (get-validator-state val systate))))
    :enable (timer-expires-possiblep
             timer-expires-next-val
             get-validator-state-of-update-validator-state
             nfix))

  (defruled validator-state->blockchain-of-timer-expires-next
    (implies (and (set::in val (correct-addresses systate))
                  (timer-expires-possiblep val1 systate))
             (equal (validator-state->blockchain
                     (get-validator-state val
                                          (timer-expires-next
                                           val1 systate)))
                    (validator-state->blockchain
                     (get-validator-state val systate))))
    :enable (timer-expires-possiblep
             timer-expires-next-val
             get-validator-state-of-update-validator-state))

  (defruled validator-state->committed-of-timer-expires-next
    (implies (and (set::in val (correct-addresses systate))
                  (timer-expires-possiblep val1 systate))
             (equal (validator-state->committed
                     (get-validator-state val
                                          (timer-expires-next
                                           val1 systate)))
                    (validator-state->committed
                     (get-validator-state val systate))))
    :enable (timer-expires-possiblep
             timer-expires-next-val
             get-validator-state-of-update-validator-state)))
