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

(include-book "active-committees-after-commit")

(local (include-book "../library-extensions/omap-theorems"))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ proposed-endorser-in-committee
  :parents (correctness)
  :short "Invariant that the endorsers of a pending proposal are
          in the active committee at the round of the proposal."
  :long
  (xdoc::topstring
   (xdoc::p
    "Endorsers are added to the pending proposal map by @('augment') events.
     This happens only if the endorsers are
     in the active committee at the round of the proposal;
     the validator that holds the pending proposal map checks that.")
   (xdoc::p
    "The other kinds of events do not change the values
     of the pending proposal map."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk proposed-endorser-in-committee-p ((systate system-statep))
  :returns (yes/no booleanp)
  :short "Definition of the invariant."
  (forall (val prop)
          (implies (set::in val (correct-addresses systate))
                   (b* (((validator-state vstate)
                         (get-validator-state val systate)))
                     (implies (set::in prop (omap::keys vstate.proposed))
                              (b* ((commtt (active-committee-at-round
                                            (proposal->round prop)
                                            vstate.blockchain)))
                                (and commtt
                                     (set::subset
                                      (omap::lookup prop vstate.proposed)
                                      (committee-members commtt))))))))
  :guard-hints
  (("Goal"
    :in-theory (enable omap::assoc-to-in-of-keys
                       proposal-setp-of-keys-when-proposal-address-set-mapp)))

  ///

  (fty::deffixequiv-sk proposed-endorser-in-committee-p
    :args ((systate system-statep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled proposed-endorser-in-committee-p-when-init
  :short "Establishment of the invariant in the initial states."
  (implies (system-initp systate)
           (proposed-endorser-in-committee-p systate))
  :enable (proposed-endorser-in-committee-p
           system-initp
           system-validators-initp-necc
           validator-init))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection proposed-endorser-in-committee-p-of-next
  :short "Preservation of the invariant by single transitions."
  :long
  (xdoc::topstring
   (xdoc::p
    "The proof for @('augment') events
     comes directly from @(tsee augment-possiblep).")
   (xdoc::p
    "Since @('commit') extends the blockchain,
     we need @(tsee active-committee-at-round-of-commit-next),
     which needs two previously proved invariants."))

  (defruled proposed-endorser-in-committee-p-of-propose-next
    (implies (and (propose-possiblep prop dests systate)
                  (proposed-endorser-in-committee-p systate))
             (proposed-endorser-in-committee-p
              (propose-next prop dests systate)))
    :enable (propose-possiblep
             proposed-endorser-in-committee-p
             proposed-endorser-in-committee-p-necc
             validator-state->proposed-of-propose-next))

  (defruled proposed-endorser-in-committee-p-of-endorse-next
    (implies (proposed-endorser-in-committee-p systate)
             (proposed-endorser-in-committee-p
              (endorse-next prop endor systate)))
    :enable (proposed-endorser-in-committee-p
             proposed-endorser-in-committee-p-necc))

  (defruled proposed-endorser-in-committee-p-of-augment-next
    (implies (and (augment-possiblep prop endor systate)
                  (proposed-endorser-in-committee-p systate))
             (proposed-endorser-in-committee-p
              (augment-next prop endor systate)))
    :use (:instance proposed-endorser-in-committee-p-necc
                    (prop (proposal-fix prop))
                    (val (mv-nth 0 (proposed-endorser-in-committee-p-witness
                                    (augment-next prop endor systate)))))
    :enable (proposed-endorser-in-committee-p
             augment-possiblep
             proposed-endorser-in-committee-p-necc
             validator-state->proposed-of-augment-next
             omap::assoc-to-in-of-keys))

  (defruled proposed-endorser-in-committee-p-of-certify-next
    (implies (proposed-endorser-in-committee-p systate)
             (proposed-endorser-in-committee-p
              (certify-next cert dests systate)))
    :enable (proposed-endorser-in-committee-p
             proposed-endorser-in-committee-p-necc
             validator-state->proposed-of-certify-next
             omap::keys-of-delete))

  (defruled proposed-endorser-in-committee-p-of-accept-next
    (implies (and (accept-possiblep val cert systate)
                  (proposed-endorser-in-committee-p systate))
             (proposed-endorser-in-committee-p
              (accept-next val cert systate)))
    :enable (proposed-endorser-in-committee-p
             proposed-endorser-in-committee-p-necc))

  (defruled proposed-endorser-in-committee-p-of-advance-next
    (implies (and (advance-possiblep val systate)
                  (proposed-endorser-in-committee-p systate))
             (proposed-endorser-in-committee-p
              (advance-next val systate)))
    :enable (proposed-endorser-in-committee-p
             proposed-endorser-in-committee-p-necc))

  (defruled proposed-endorser-in-committee-p-of-commit-next
    (implies (and (commit-possiblep val systate)
                  (last-blockchain-round-p systate)
                  (ordered-blockchain-p systate)
                  (proposed-endorser-in-committee-p systate))
             (proposed-endorser-in-committee-p
              (commit-next val systate)))
    :enable (proposed-endorser-in-committee-p
             proposed-endorser-in-committee-p-necc
             active-committee-at-round-of-commit-next))

  (defruled proposed-endorser-in-committee-p-of-event-next
    (implies (and (event-possiblep event systate)
                  (last-blockchain-round-p systate)
                  (ordered-blockchain-p systate)
                  (proposed-endorser-in-committee-p systate))
             (proposed-endorser-in-committee-p (event-next event systate)))
    :enable (event-possiblep
             event-next)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled proposed-endorser-in-committee-p-of-events-next
  :short "Preservation of the invariant by multiple transitions."
  (implies (and (events-possiblep events systate)
                (last-blockchain-round-p systate)
                (ordered-blockchain-p systate)
                (proposed-endorser-in-committee-p systate))
           (proposed-endorser-in-committee-p (events-next events systate)))
  :induct t
  :enable (events-possiblep
           events-next))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled proposed-endorser-in-committee-p-when-reachable
  :short "The invariant holds in every reachable state."
  (implies (system-state-reachablep systate)
           (proposed-endorser-in-committee-p systate))
  :enable (system-state-reachablep
           proposed-endorser-in-committee-p-when-init
           last-blockchain-round-p-when-init
           ordered-blockchain-p-when-init)
  :prep-lemmas
  ((defrule lemma
     (implies (and (system-state-reachable-from-p systate from)
                   (last-blockchain-round-p from)
                   (ordered-blockchain-p from)
                   (proposed-endorser-in-committee-p from))
              (proposed-endorser-in-committee-p systate))
     :use (:instance
           proposed-endorser-in-committee-p-of-events-next
           (events (system-state-reachable-from-p-witness systate from))
           (systate from))
     :enable system-state-reachable-from-p)))
