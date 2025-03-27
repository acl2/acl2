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
     caused by @('timer-expires') events.")
   (xdoc::p
    "Each validator starts a timer when it advances its round.
     At some point, the timer may expire.
     We do not model real time currently,
     but we model the fact that a timer may change state,
     from running to expired."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define timer-expires-possiblep ((val addressp) (systate system-statep))
  :returns (yes/no booleanp)
  :short "Check if a @('timer-expires') event is possible."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('val') input of this function is
     the address in the @('timer-expires') event;
     see @(tsee event).")
   (xdoc::p
    "The validator must be a correct one.
     We only model round advancement in correct validators.
     Faulty validators have no internal state in our model.")
   (xdoc::p
    "The timer of the validator must be running."))
  (b* (((unless (set::in (address-fix val) (correct-addresses systate))) nil)
       ((validator-state vstate) (get-validator-state val systate)))
    (timer-case vstate.timer :running))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define timer-expires-next ((val addressp) (systate system-statep))
  :guard (timer-expires-possiblep val systate)
  :returns (new-systate system-statep)
  :short "New state resulting from a @('timer-expires') event."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('val') input of this function is
     the address in the @('timer-expires') event;
     see @(tsee event).")
   (xdoc::p
    "The timer state is set to expired."))
  (b* (((validator-state vstate) (get-validator-state val systate))
       (new-timer (timer-expired))
       (new-vstate (change-validator-state vstate :timer new-timer))
       (systate (update-validator-state val new-vstate systate)))
    systate)
  :guard-hints (("Goal" :in-theory (enable timer-expires-possiblep)))
  :hooks (:fix)

  ///

  (defret all-addresses-of-timer-expires-next
    (equal (all-addresses new-systate)
           (all-addresses systate))
    :hyp (timer-expires-possiblep val systate)
    :hints (("Goal" :in-theory (enable timer-expires-possiblep))))

  (defret correct-addresses-of-timer-expires-next
    (equal (correct-addresses new-systate)
           (correct-addresses systate))
    :hyp (timer-expires-possiblep val systate)
    :hints (("Goal" :in-theory (enable timer-expires-possiblep))))

  (defret faulty-addresses-of-timer-expires-next
    (equal (faulty-addresses new-systate)
           (faulty-addresses systate))
    :hyp (timer-expires-possiblep val systate)
    :hints (("Goal" :in-theory (enable timer-expires-possiblep))))

  (defret validator-state->dag-of-timer-expires-next
    (equal (validator-state->dag (get-validator-state val1 new-systate))
           (validator-state->dag (get-validator-state val1 systate)))
    :hyp (timer-expires-possiblep val systate)
    :hints
    (("Goal"
      :in-theory (enable timer-expires-possiblep
                         get-validator-state-of-update-validator-state))))

  (defret validator-state->buffer-of-timer-expires-next
    (equal (validator-state->buffer (get-validator-state val1 new-systate))
           (validator-state->buffer (get-validator-state val1 systate)))
    :hyp (timer-expires-possiblep val systate)
    :hints
    (("Goal"
      :in-theory (enable timer-expires-possiblep
                         get-validator-state-of-update-validator-state))))

  (defret validator-state->endorsed-of-timer-expires-next
    (equal (validator-state->endorsed
            (get-validator-state val1 new-systate))
           (validator-state->endorsed
            (get-validator-state val1 systate)))
    :hyp (timer-expires-possiblep val systate)
    :hints
    (("Goal"
      :in-theory
      (enable timer-expires-possiblep
              get-validator-state-of-update-validator-state))))

  (defret validator-state->last-of-timer-expires-next
    (equal (validator-state->last
            (get-validator-state val1 new-systate))
           (validator-state->last
            (get-validator-state val1 systate)))
    :hyp (timer-expires-possiblep val systate)
    :hints
    (("Goal"
      :in-theory
      (enable timer-expires-possiblep
              get-validator-state-of-update-validator-state
              nfix))))

  (defret validator-state->blockchain-of-timer-expires-next
    (equal (validator-state->blockchain
            (get-validator-state val1 new-systate))
           (validator-state->blockchain
            (get-validator-state val1 systate)))
    :hyp (timer-expires-possiblep val systate)
    :hints
    (("Goal"
      :in-theory
      (enable timer-expires-possiblep
              get-validator-state-of-update-validator-state))))

  (defret validator-state->committed-of-timer-expires-next
    (equal (validator-state->committed
            (get-validator-state val1 new-systate))
           (validator-state->committed
            (get-validator-state val1 systate)))
    :hyp (timer-expires-possiblep val systate)
    :hints
    (("Goal"
      :in-theory
      (enable timer-expires-possiblep
              get-validator-state-of-update-validator-state))))

  (defret get-network-state-of-timer-expires-next
    (equal (get-network-state new-systate)
           (get-network-state systate)))

  (in-theory (disable validator-state->dag-of-timer-expires-next
                      validator-state->buffer-of-timer-expires-next
                      validator-state->endorsed-of-timer-expires-next
                      validator-state->last-of-timer-expires-next
                      validator-state->blockchain-of-timer-expires-next
                      validator-state->committed-of-timer-expires-next
                      get-network-state-of-timer-expires-next)))
