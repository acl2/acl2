; AleoBFT Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOBFT-STAKE2")

(include-book "system-states")

;; cert_param: (non-acl2r)

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ transitions-advance
  :parents (transitions)
  :short "Transitions for round advancement."
  :long
  (xdoc::topstring
   (xdoc::p
    "Here we define the system state transitions
     caused by @('advance') events.")
   (xdoc::p
    "A round advancement event involves just one correct validator.")
   (xdoc::p
    "This just increments the round number of the validator by one.
     The round advancement logic in AleoBFT is more complex,
     but our simple model suffices for many properties of interest,
     which, if proved for our model with the simpler round advancement logic,
     also hold in a model with a more complex round advancement logic,
     whose possible behaviors are a subset of
     the ones of this model with simple round advancement logic.")
   (xdoc::p
    "A round advancement event does not involve the network."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define advance-possiblep ((val addressp) (systate system-statep))
  :returns (yes/no booleanp)
  :short "Check if a round advancement event is possible."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('val') input of this function is
     the address in the @('advance') event;
     see @(tsee event).")
   (xdoc::p
    "The validator must be a correct one.
     This is the only condition,
     since our round advancement logic is so simple."))
  (set::in (address-fix val) (correct-addresses systate))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define advance-next ((val addressp) (systate system-statep))
  :guard (advance-possiblep val systate)
  :returns (new-systate system-statep)
  :short "New system state resulting from an @('advance') event."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('val') input of this function is
     the address in the @('advance') event;
     see @(tsee event).")
   (xdoc::p
    "We increment the validator's round by one."))
  (b* (((validator-state vstate) (get-validator-state val systate))
       (new-round (1+ vstate.round))
       (new-vstate (change-validator-state vstate :round new-round))
       (systate (update-validator-state val new-vstate systate)))
    systate)
  :guard-hints (("Goal" :in-theory (enable advance-possiblep)))
  :hooks (:fix)

  ///

  (defret correct-addresses-of-advance-next
    (equal (correct-addresses new-systate)
           (correct-addresses systate))
    :hyp (advance-possiblep val systate)
    :hints (("Goal" :in-theory (enable advance-possiblep))))

  (defret validator-state->round-of-advance-next
    (equal (validator-state->round (get-validator-state val1 new-systate))
           (if (equal (address-fix val1) (address-fix val))
               (1+ (validator-state->round (get-validator-state val1 systate)))
             (validator-state->round (get-validator-state val1 systate))))
    :hyp (advance-possiblep val systate)
    :hints
    (("Goal"
      :in-theory (enable advance-possiblep
                         get-validator-state-of-update-validator-state))))
  (in-theory (disable validator-state->round-of-advance-next))

  (defret validator-state->dag-of-advance-next
    (equal (validator-state->dag (get-validator-state val1 new-systate))
           (validator-state->dag (get-validator-state val1 systate)))
    :hyp (advance-possiblep val systate)
    :hints
    (("Goal"
      :in-theory (enable advance-possiblep
                         get-validator-state-of-update-validator-state))))

  (defret validator-state->endorsed-of-advance-next
    (equal (validator-state->endorsed (get-validator-state val1 new-systate))
           (validator-state->endorsed (get-validator-state val1 systate)))
    :hyp (advance-possiblep val systate)
    :hints
    (("Goal"
      :in-theory
      (enable advance-possiblep
              get-validator-state-of-update-validator-state))))

  (defret validator-state->last-of-advance-next
    (equal (validator-state->last (get-validator-state val1 new-systate))
           (validator-state->last (get-validator-state val1 systate)))
    :hyp (advance-possiblep val systate)
    :hints
    (("Goal"
      :in-theory (enable advance-possiblep
                         get-validator-state-of-update-validator-state
                         nfix))))

  (defret validator-state->blockchain-of-advance-next
    (equal (validator-state->blockchain (get-validator-state val1 new-systate))
           (validator-state->blockchain (get-validator-state val1 systate)))
    :hyp (advance-possiblep val systate)
    :hints
    (("Goal"
      :in-theory (enable advance-possiblep
                         get-validator-state-of-update-validator-state))))

  (defret validator-state->committed-of-advance-next
    (equal (validator-state->committed (get-validator-state val1 new-systate))
           (validator-state->committed (get-validator-state val1 systate)))
    :hyp (advance-possiblep val systate)
    :hints
    (("Goal"
      :in-theory (enable advance-possiblep
                         get-validator-state-of-update-validator-state))))

  (defret get-network-state-of-advance-next
    (equal (get-network-state new-systate)
           (get-network-state systate))))
