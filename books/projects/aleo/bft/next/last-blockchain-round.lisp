; AleoBFT Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOBFT")

(include-book "reachability")

(local (include-book "../library-extensions/arithmetic-theorems"))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ last-blockchain-round
  :parents (correctness)
  :short "Invariant that the last round in the blockchain of each validator
          is always the last committed round of the validator."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('last') component of a "
    (xdoc::seetopic "validator-state" "validator state")
    " stores the last committed round number,
     or 0 if no block has been committed yet.
     Initially, there are no blocks and @('last') is 0.
     When new blocks are generated,
     which only happens with @('commit') events,
     @('last') gets updated with the round number of
     the last (i.e. newest) block added to the blockchain."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk last-blockchain-round-p ((systate system-statep))
  :returns (yes/no booleanp)
  :short "Definition of the invariant."
  (forall (val)
          (implies (set::in val (correct-addresses systate))
                   (b* (((validator-state vstate)
                         (get-validator-state val systate)))
                     (equal vstate.last
                            (blocks-last-round vstate.blockchain)))))

  ///

  (fty::deffixequiv-sk last-blockchain-round-p
    :args ((systate system-statep)))

  (defruled last-blockchain-round-p-necc-with-address-fix
    (implies (and (last-blockchain-round-p systate)
                  (set::in (address-fix val) (correct-addresses systate)))
             (equal (validator-state->last (get-validator-state val systate))
                    (blocks-last-round (validator-state->blockchain
                                        (get-validator-state val systate)))))
    :use (:instance last-blockchain-round-p-necc (val (address-fix val)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled last-blockchain-round-p-when-init
  :short "Establishment of the invariant in the initial states."
  (implies (system-initp systate)
           (last-blockchain-round-p systate))
  :enable (last-blockchain-round-p
           system-initp
           system-validators-initp-necc
           validator-init))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection last-blockchain-round-p-of-next
  :short "Preservation of the invariant by single transitions."
  :long
  (xdoc::topstring
   (xdoc::p
    "The only kind of event that changes
     (both) the blockchain and the last committed round
     is @('commit').
     All the other events do not change either,
     and thus it is easy to show the preservation.")
   (xdoc::p
    "For @('commit'),
     one or more anchors are committed,
     generating a block for each anchor.
     The newest block is the one added last,
     i.e. the @(tsee car) of the new blockchain,
     whose round number is the same as
     the first anchor in the list of collected anchors;
     by definition of @(tsee commit-next),
     this is exactly the commit round,
     which also becomes the last committed round,
     and so the invariant is established in the new system state."))

  (defruled last-blockchain-round-p-of-propose-next
    (implies (last-blockchain-round-p systate)
             (last-blockchain-round-p (propose-next prop dests systate)))
    :enable (last-blockchain-round-p
             last-blockchain-round-p-necc))

  (defruled last-blockchain-round-p-of-endorse-next
    (implies (last-blockchain-round-p systate)
             (last-blockchain-round-p (endorse-next prop endor systate)))
    :enable (last-blockchain-round-p
             last-blockchain-round-p-necc))

  (defruled last-blockchain-round-p-of-augment-next
    (implies (and (augment-possiblep prop endor systate)
                  (last-blockchain-round-p systate))
             (last-blockchain-round-p (augment-next prop endor systate)))
    :enable (last-blockchain-round-p
             last-blockchain-round-p-necc))

  (defruled last-blockchain-round-p-of-certify-next
    (implies (and (certify-possiblep cert dests systate)
                  (last-blockchain-round-p systate))
             (last-blockchain-round-p (certify-next cert dests systate)))
    :enable (last-blockchain-round-p
             last-blockchain-round-p-necc))

  (defruled last-blockchain-round-p-of-accept-next
    (implies (and (accept-possiblep val cert systate)
                  (last-blockchain-round-p systate))
             (last-blockchain-round-p (accept-next val cert systate)))
    :enable (last-blockchain-round-p
             last-blockchain-round-p-necc))

  (defruled last-blockchain-round-p-of-advance-next
    (implies (and (advance-possiblep val systate)
                  (last-blockchain-round-p systate))
             (last-blockchain-round-p (advance-next val systate)))
    :enable (last-blockchain-round-p
             last-blockchain-round-p-necc))

  (defruled last-blockchain-round-p-of-commit-next
    (implies (and (commit-possiblep val systate)
                  (last-blockchain-round-p systate))
             (last-blockchain-round-p (commit-next val systate)))
    :enable (last-blockchain-round-p
             last-blockchain-round-p-necc
             validator-state->last-of-commit-next
             validator-state->blockchain-of-commit-next
             commit-possiblep
             blocks-last-round-of-extend-blockchain
             car-of-collect-anchors
             evenp-of-1-less-when-not-evenp
             evenp-of-3-less-when-not-evenp))

  (defruled last-blockchain-round-p-of-event-next
    (implies (and (last-blockchain-round-p systate)
                  (event-possiblep event systate))
             (last-blockchain-round-p (event-next event systate)))
    :enable (event-possiblep
             event-next)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled last-blockchain-round-p-of-events-next
  :short "Preservation of the invariant by multiple transitions."
  (implies (and (events-possiblep events systate)
                (last-blockchain-round-p systate))
           (last-blockchain-round-p (events-next events systate)))
  :induct t
  :enable (events-possiblep
           events-next))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled last-blockchain-round-p-when-reachable
  :short "The invariant holds in every reachable state."
  (implies (system-state-reachablep systate)
           (last-blockchain-round-p systate))
  :enable (system-state-reachablep
           last-blockchain-round-p-when-init)
  :prep-lemmas
  ((defrule lemma
     (implies (and (system-state-reachable-from-p systate from)
                   (last-blockchain-round-p from))
              (last-blockchain-round-p systate))
     :use (:instance
           last-blockchain-round-p-of-events-next
           (events (system-state-reachable-from-p-witness systate from))
           (systate from))
     :enable system-state-reachable-from-p)))
