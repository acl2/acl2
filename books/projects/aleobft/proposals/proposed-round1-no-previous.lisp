; AleoBFT Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOBFT-PROPOSALS")

(include-book "reachability")

(local (include-book "../library-extensions/omap-theorems"))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ proposed-round1-no-previous
  :parents (correctness)
  :short "Invariant that each proposal in round 1
          in the pending proposals of a correct validator
          has no references to previous certificates."
  :long
  (xdoc::topstring
   (xdoc::p
    "When a correct validator creates a proposal for round 1,
     it puts no references to previous certificates in it,
     because there is no round 0."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk proposed-round1-no-previous-p ((systate system-statep))
  :returns (yes/no booleanp)
  :short "Definition of the invariant."
  (forall (val prop)
          (implies (set::in val (correct-addresses systate))
                   (b* (((validator-state vstate)
                         (get-validator-state val systate)))
                     (implies (set::in prop (omap::keys vstate.proposed))
                              (b* (((proposal prop) prop))
                                (implies (equal prop.round 1)
                                         (set::emptyp prop.previous)))))))
  :guard-hints
  (("Goal"
    :in-theory
    (enable proposal-setp-of-keys-when-proposal-address-set-mapp)))
  ///
  (fty::deffixequiv-sk proposed-round1-no-previous-p
    :args ((systate system-statep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled proposed-round1-no-previous-p-when-init
  :short "Establishment of the invariant in the initial states."
  (implies (system-initp systate)
           (proposed-round1-no-previous-p systate))
  :enable (proposed-round1-no-previous-p
           system-initp
           system-validators-initp-necc
           validator-init))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection proposed-round1-no-previous-p-of-next
  :short "Preservation of the invariant by single transitions."

  (defruled proposed-round1-no-previous-p-of-propose-next
    (implies (and (propose-possiblep prop dests systate)
                  (proposed-round1-no-previous-p systate))
             (proposed-round1-no-previous-p (propose-next prop dests systate)))
    :expand (proposed-round1-no-previous-p (propose-next prop dests systate))
    :enable (proposed-round1-no-previous-p-necc
             validator-state->proposed-of-propose-next
             propose-possiblep))

  (defruled proposed-round1-no-previous-p-of-endorse-next
    (implies (proposed-round1-no-previous-p systate)
             (proposed-round1-no-previous-p (endorse-next prop endor systate)))
    :expand (proposed-round1-no-previous-p (endorse-next prop endor systate))
    :enable proposed-round1-no-previous-p-necc)

  (defruled proposed-round1-no-previous-p-of-augment-next
    (implies (and (augment-possiblep prop endor systate)
                  (proposed-round1-no-previous-p systate))
             (proposed-round1-no-previous-p (augment-next prop endor systate)))
    :expand (proposed-round1-no-previous-p (augment-next prop endor systate))
    :enable (proposed-round1-no-previous-p-necc
             validator-state->proposed-of-augment-next
             augment-possiblep
             omap::assoc-to-in-of-keys))

  (defruled proposed-round1-no-previous-p-of-certify-next
    (implies (proposed-round1-no-previous-p systate)
             (proposed-round1-no-previous-p (certify-next cert dests systate)))
    :expand (proposed-round1-no-previous-p (certify-next cert dests systate))
    :enable (proposed-round1-no-previous-p-necc
             validator-state->proposed-of-certify-next
             omap::keys-of-delete))

  (defruled proposed-round1-no-previous-p-of-accept-next
    (implies (and (accept-possiblep val cert systate)
                  (proposed-round1-no-previous-p systate))
             (proposed-round1-no-previous-p (accept-next val cert systate)))
    :expand (proposed-round1-no-previous-p (accept-next val cert systate))
    :enable proposed-round1-no-previous-p-necc)

  (defruled proposed-round1-no-previous-p-of-advance-next
    (implies (and (advance-possiblep val systate)
                  (proposed-round1-no-previous-p systate))
             (proposed-round1-no-previous-p (advance-next val systate)))
    :expand (proposed-round1-no-previous-p (advance-next val systate))
    :enable proposed-round1-no-previous-p-necc)

  (defruled proposed-round1-no-previous-p-of-commit-next
    (implies (and (commit-possiblep val systate)
                  (proposed-round1-no-previous-p systate))
             (proposed-round1-no-previous-p (commit-next val systate)))
    :expand (proposed-round1-no-previous-p (commit-next val systate))
    :enable proposed-round1-no-previous-p-necc)

  (defruled proposed-round1-no-previous-p-of-event-next
    (implies (and (event-possiblep event systate)
                  (proposed-round1-no-previous-p systate))
             (proposed-round1-no-previous-p (event-next event systate)))
    :enable (event-possiblep
             event-next)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled proposed-round1-no-previous-p-of-events-next
  :short "Preservation of the invariant by multiple transitions."
  (implies (and (events-possiblep events systate)
                (proposed-round1-no-previous-p systate))
           (proposed-round1-no-previous-p (events-next events systate)))
  :induct t
  :enable (events-possiblep
           events-next))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled proposed-round1-no-previous-p-when-reachable
  :short "The invariant holds in every reachable state."
  (implies (system-state-reachablep systate)
           (proposed-round1-no-previous-p systate))
  :enable (system-state-reachablep
           proposed-round1-no-previous-p-when-init)
  :prep-lemmas
  ((defrule lemma
     (implies (and (system-state-reachable-from-p systate from)
                   (proposed-round1-no-previous-p from))
              (proposed-round1-no-previous-p systate))
     :use (:instance
           proposed-round1-no-previous-p-of-events-next
           (events (system-state-reachable-from-p-witness systate from))
           (systate from))
     :enable system-state-reachable-from-p)))
