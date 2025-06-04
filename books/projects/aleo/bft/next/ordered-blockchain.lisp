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

(include-book "last-blockchain-round")

(local (include-book "../library-extensions/arithmetic-theorems"))

(local (include-book "kestrel/utilities/nfix" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ ordered-blockchain
  :parents (correctness)
  :short "Invariant that the blocks in the blockchain of each validator
          have strictly increasing round numbers."
  :long
  (xdoc::topstring
   (xdoc::p
    "Initially, validators have no blocks.
     Blocks are generated as rounds increase,
     so blocks have strictly increasing round numbers."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk ordered-blockchain-p ((systate system-statep))
  :returns (yes/no booleanp)
  :short "Definition of the invariant."
  (forall (val)
          (implies (set::in val (correct-addresses systate))
                   (blocks-orderedp
                    (validator-state->blockchain
                     (get-validator-state val systate)))))

  ///

  (fty::deffixequiv-sk ordered-blockchain-p
    :args ((systate system-statep)))

  (defruled ordered-blockchain-p-necc-with-address-fix
    (implies (and (ordered-blockchain-p systate)
                  (set::in (address-fix val) (correct-addresses systate)))
             (blocks-orderedp (validator-state->blockchain
                               (get-validator-state val systate))))
    :use (:instance ordered-blockchain-p-necc (val (address-fix val)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled ordered-blockchain-p-when-init
  :short "Establishment of the invariant in the initial states."
  (implies (system-initp systate)
           (ordered-blockchain-p systate))
  :enable (ordered-blockchain-p
           system-initp
           system-validators-initp-necc
           validator-init))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection ordered-blockchain-p-of-next
  :short "Preservation of the invariant by single transitions."
  :long
  (xdoc::topstring
   (xdoc::p
    "The only kind of event that modifies the blockchain is @('commit').
     All the other events leave the blockchain unchanged,
     and it is thus easy to prove that they preserve the invariant.")
   (xdoc::p
    "For @('commit') event,
     we need to assume a previously proved invariant,
     namely @(see last-blockchain-round).
     We use previously proved theorems about
     @(tsee extend-blockchain) and @(tsee collect-anchors).
     We also need to open up @(tsee commit-possiblep),
     to expose certain needed constraints on the involved round numbers.
     The @(tsee last-blockchain-round-p) assumption
     serves to tie the last committed round in the validator state
     to the round of the newest block of the blockchain
     prior to the addition of the new blocks,
     to complete the relieving of the hypotheses
     of the aforementioned theorems
     about @(tsee extend-blockchain) and @(tsee collect-anchors)."))

  (defruled ordered-blockchain-p-of-propose-next
    (implies (ordered-blockchain-p systate)
             (ordered-blockchain-p (propose-next prop dests systate)))
    :enable (ordered-blockchain-p
             ordered-blockchain-p-necc))

  (defruled ordered-blockchain-p-of-endorse-next
    (implies (ordered-blockchain-p systate)
             (ordered-blockchain-p (endorse-next prop endor systate)))
    :enable (ordered-blockchain-p
             ordered-blockchain-p-necc))

  (defruled ordered-blockchain-p-of-augment-next
    (implies (and (augment-possiblep prop endor systate)
                  (ordered-blockchain-p systate))
             (ordered-blockchain-p (augment-next prop endor systate)))
    :enable (ordered-blockchain-p
             ordered-blockchain-p-necc))

  (defruled ordered-blockchain-p-of-certify-next
    (implies (ordered-blockchain-p systate)
             (ordered-blockchain-p (certify-next cert dests systate)))
    :enable (ordered-blockchain-p
             ordered-blockchain-p-necc))

  (defruled ordered-blockchain-p-of-accept-next
    (implies (and (accept-possiblep val cert systate)
                  (ordered-blockchain-p systate))
             (ordered-blockchain-p (accept-next val cert systate)))
    :enable (ordered-blockchain-p
             ordered-blockchain-p-necc))

  (defruled ordered-blockchain-p-of-advance-next
    (implies (and (advance-possiblep val systate)
                  (ordered-blockchain-p systate))
             (ordered-blockchain-p (advance-next val systate)))
    :enable (ordered-blockchain-p
             ordered-blockchain-p-necc))

  (defruled ordered-blockchain-p-of-commit-next
    (implies (and (commit-possiblep val systate)
                  (last-blockchain-round-p systate)
                  (ordered-blockchain-p systate))
             (ordered-blockchain-p (commit-next val systate)))
    :enable (ordered-blockchain-p
             ordered-blockchain-p-necc-with-address-fix
             validator-state->blockchain-of-commit-next
             commit-possiblep
             blocks-orderedp-of-extend-blockchain
             cert-list-orderedp-of-collect-anchors
             cert-list-evenp-of-collect-anchors
             evenp-of-1-less-when-not-evenp
             evenp-of-3-less-when-not-evenp
             last-blockchain-round-p-necc-with-address-fix
             collect-anchors-above-last-committed-round))

  (defruled ordered-blockchain-p-of-event-next
    (implies (and (event-possiblep event systate)
                  (last-blockchain-round-p systate)
                  (ordered-blockchain-p systate))
             (ordered-blockchain-p (event-next event systate)))
    :enable (event-possiblep
             event-next)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled ordered-blockchain-p-of-events-next
  :short "Preservation of the invariant by multiple transitions."
  (implies (and (events-possiblep events systate)
                (last-blockchain-round-p systate)
                (ordered-blockchain-p systate))
           (ordered-blockchain-p (events-next events systate)))
  :induct t
  :enable (events-possiblep
           events-next))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled ordered-blockchain-p-when-reachable
  :short "The invariant holds in every reachable state."
  (implies (system-state-reachablep systate)
           (ordered-blockchain-p systate))
  :enable (system-state-reachablep
           ordered-blockchain-p-when-init
           last-blockchain-round-p-when-init)
  :prep-lemmas
  ((defrule lemma
     (implies (and (system-state-reachable-from-p systate from)
                   (last-blockchain-round-p from)
                   (ordered-blockchain-p from))
              (ordered-blockchain-p systate))
     :use (:instance
           ordered-blockchain-p-of-events-next
           (events (system-state-reachable-from-p-witness systate from))
           (systate from))
     :enable system-state-reachable-from-p)))
