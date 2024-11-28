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

(include-book "initialization")
(include-book "transitions")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ last-blockchain-round
  :parents (correctness)
  :short "Invariant that the last round in the blockchain of a validator
          is the last committed round of the validator."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('last') component of a "
    (xdoc::seetopic "validator-state" "validator state")
    " stores the last committed round number,
     or 0 if no block has been committed yet.")
   (xdoc::p
    "Initially, there are no blocks and @('last') is 0.")
   (xdoc::p
    "When new blocks are committed,
     which only happens with @('commit-anchors') events,
     @('last') gets updated with the round number of
     the last (i.e. newest) block added to the blockchain."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk last-blockchain-round-p ((systate system-statep))
  :returns (yes/no booleanp)
  :short "Definition of the invariant:
          for each correct validator in the system,
          the last committed round is 0 if the blockchain is empty,
          or the round of the newest block in the blockchain otherwise."
  (forall (val)
          (implies (set::in val (correct-addresses systate))
                   (b* (((validator-state vstate)
                         (get-validator-state val systate))
                        (blockchain (validator-state->blockchain vstate)))
                     (equal (validator-state->last vstate)
                            (blocks-last-round blockchain)))))

  ///

  (fty::deffixequiv-sk last-blockchain-round-p
    :args ((systate system-statep)))

  (defruled last-blockchain-round-p-necc-fixing
    (implies (and (last-blockchain-round-p systate)
                  (set::in (address-fix val) (correct-addresses systate)))
             (b* (((validator-state vstate)
                   (get-validator-state val systate))
                  (blockchain (validator-state->blockchain vstate)))
               (equal (validator-state->last vstate)
                      (blocks-last-round blockchain))))
    :use (:instance last-blockchain-round-p-necc (val (address-fix val)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled last-blockchain-round-p-when-init
  :short "Establishment of the invariant:
          the invariant holds in any initial system state."
  :long
  (xdoc::topstring
   (xdoc::p
    "Initially, blockchains are empty and
     the last committed rounds are all 0,
     so the relation holds."))
  (implies (system-initp systate)
           (last-blockchain-round-p systate))
  :enable (last-blockchain-round-p
           system-initp
           system-validators-initp-necc
           validator-init))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection last-blockchain-round-p-of-next
  :short "Preservation of the invariant:
          if the invariant holds in a system state,
          it also holds in the next system state."
  :long
  (xdoc::topstring
   (xdoc::p
    "The only kind of event that changes
     (both) the blockchain and the last committed round
     is @('commit-anchors').
     All the other events do not change either,
     and thus it is easy to show the preservation.")
   (xdoc::p
    "For @('commit-anchors'),
     one or more anchors are committed,
     generating a block for each anchor.
     The newest block is the one added last,
     i.e. the @(tsee car) of the new blockchain,
     whose round number is the same as
     the first anchor in the list of collected anchors;
     by definition of @(tsee commit-anchors-next),
     this is exactly the commit round,
     which also becomes the last committed round,
     and so the invariant is established in the new system state."))

  (defruled last-blockchain-round-p-of-create-certificate-next
    (implies (last-blockchain-round-p systate)
             (last-blockchain-round-p
              (create-certificate-next cert systate)))
    :enable (last-blockchain-round-p
             last-blockchain-round-p-necc
             validator-state->blockchain-of-create-certificate-next
             validator-state->last-of-create-certificate-next
             certificate->round-of-certificate-with-author+round))

  (defruled last-blockchain-round-p-of-receive-certificate-next
    (implies (and (last-blockchain-round-p systate)
                  (receive-certificate-possiblep msg systate))
             (last-blockchain-round-p
              (receive-certificate-next msg systate)))
    :enable (last-blockchain-round-p
             last-blockchain-round-p-necc
             validator-state->blockchain-of-receive-certificate-next
             validator-state->last-of-receive-certificate-next))

  (defruled last-blockchain-round-p-of-store-certificate-next
    (implies (and (last-blockchain-round-p systate)
                  (store-certificate-possiblep val cert systate))
             (last-blockchain-round-p
              (store-certificate-next val cert systate)))
    :enable (last-blockchain-round-p
             last-blockchain-round-p-necc
             validator-state->blockchain-of-store-certificate-next
             validator-state->last-of-store-certificate-next))

  (defruled last-blockchain-round-p-of-advance-round-next
    (implies (and (last-blockchain-round-p systate)
                  (advance-round-possiblep val systate))
             (last-blockchain-round-p
              (advance-round-next val systate)))
    :enable (last-blockchain-round-p
             last-blockchain-round-p-necc
             validator-state->blockchain-of-advance-round-next
             validator-state->last-of-advance-round-next))

  (defruled last-blockchain-round-p-of-commit-anchors-next
    (implies (and (last-blockchain-round-p systate)
                  (commit-anchors-possiblep val systate))
             (last-blockchain-round-p
              (commit-anchors-next val systate)))
    :enable (last-blockchain-round-p
             last-blockchain-round-p-necc
             validator-state->blockchain-of-commit-anchors-next
             validator-state->last-of-commit-anchors-next
             commit-anchors-possiblep
             consp-of-extend-blockchain
             car-of-collect-anchors
             blocks-last-round-of-extend-blockchain
             certificate->round-of-certificate-with-author+round))

  (defruled last-blockchain-round-p-of-timer-expires-next
    (implies (and (last-blockchain-round-p systate)
                  (timer-expires-possiblep val systate))
             (last-blockchain-round-p
              (timer-expires-next val systate)))
    :enable (last-blockchain-round-p
             last-blockchain-round-p-necc
             validator-state->blockchain-of-timer-expires-next
             validator-state->last-of-timer-expires-next))

  (defruled last-blockchain-round-p-of-event-next
    (implies (and (last-blockchain-round-p systate)
                  (event-possiblep event systate))
             (last-blockchain-round-p (event-next event systate)))
    :enable (event-possiblep
             event-next)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection last-blockchain-round-p-always
  :short "The invariant holds in every state
          reachable from an initial state via a sequence of events."

  (defruled last-blockchain-round-p-of-events-next
    (implies (and (last-blockchain-round-p systate)
                  (events-possiblep events systate))
             (last-blockchain-round-p (events-next events systate)))
    :induct t
    :disable ((:e tau-system))
    :enable (events-possiblep
             events-next
             last-blockchain-round-p-of-event-next))

  (defruled last-blockchain-round-p-when-reachable
    (implies (and (system-initp systate)
                  (events-possiblep events systate))
             (last-blockchain-round-p (events-next events systate)))
    :disable ((:e tau-system))
    :enable (last-blockchain-round-p-when-init
             last-blockchain-round-p-of-events-next)))
