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
(include-book "signed-proposals")

(local (include-book "../library-extensions/omap-theorems"))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ signed-in-signer
  :parents (correctness)
  :short "Invariant that each correct signer of each proposal
          has the proposal in its state."
  :long
  (xdoc::topstring
   (xdoc::p
    "The proposal is in (a certificate in) the DAG,
     or in the pending proposal map,
     or in the endorsed proposal set.")
   (xdoc::p
    "Initially there are no proposals in the system.
     As proved in the @('signed-props-of-...-next') theorems
     in @(see signed-proposals),
     new proposals may be added only by @('propose') and @('endorse') events
     (@('certify') events may only add proposals signed by faulty validators).
     In a @('propose') event,
     the proposal is added to the map of pending proposals of the author;
     in an @('endorse') event,
     the proposal is added to the endorsed set of the endorser.
     In a @('certify') event,
     a proposal is removed from the pending proposal map,
     but a certificate with the proposal is added to the DAG,
     so the proposal remains in the state.
     In an @('accept') event,
     a proposal may be removed from the endorsed proposals,
     but a certificate with the same proposal is added to the DAG,
     so the proposal remains in the state."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk signed-in-signer-p ((systate system-statep))
  :returns (yes/no booleanp)
  :short "Definition of the invariant."
  (forall (signer prop)
          (implies (and (set::in signer (correct-addresses systate))
                        (set::in prop (signed-props signer systate)))
                   (b* (((validator-state vstate)
                         (get-validator-state signer systate))
                        ((proposal prop) prop))
                     (or (set::in prop (cert-set->prop-set vstate.dag))
                         (set::in prop (omap::keys vstate.proposed))
                         (set::in prop vstate.endorsed)))))

  ///

  (fty::deffixequiv-sk signed-in-signer-p
    :args ((systate system-statep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled signed-in-signer-p-when-init
  :short "Establishment of the invariant in the initial states."
  (implies (system-initp systate)
           (signed-in-signer-p systate))
  :enable (signed-in-signer-p
           signed-props-when-init))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection signed-in-signer-p-of-next
  :short "Preservation of the invariant by single transitions."

  (defruled signed-in-signer-p-of-propose-next
    (implies (and (propose-possiblep prop dests systate)
                  (signed-in-signer-p systate))
             (signed-in-signer-p (propose-next prop dests systate)))
    :use (:instance signed-in-signer-p-necc
                    (signer (mv-nth 0 (signed-in-signer-p-witness
                                       (propose-next prop dests systate))))
                    (prop (mv-nth 1 (signed-in-signer-p-witness
                                     (propose-next prop dests systate)))))
    :enable (signed-in-signer-p
             signed-props-of-propose-next
             validator-state->proposed-of-propose-next))

  (defruled signed-in-signer-p-of-endorse-next
    (implies (and (endorse-possiblep prop endor systate)
                  (signed-in-signer-p systate))
             (signed-in-signer-p (endorse-next prop endor systate)))
    :use (:instance signed-in-signer-p-necc
                    (signer (mv-nth 0 (signed-in-signer-p-witness
                                       (endorse-next prop endor systate))))
                    (prop (mv-nth 1 (signed-in-signer-p-witness
                                     (endorse-next prop endor systate)))))
    :enable (signed-in-signer-p
             signed-props-of-endorse-next
             validator-state->endorsed-of-endorse-next))

  (defruled signed-in-signer-p-of-augment-next
    (implies (and (augment-possiblep prop endor systate)
                  (signed-in-signer-p systate))
             (signed-in-signer-p (augment-next prop endor systate)))
    :use (:instance signed-in-signer-p-necc
                    (signer (mv-nth 0 (signed-in-signer-p-witness
                                       (augment-next prop endor systate))))
                    (prop (mv-nth 1 (signed-in-signer-p-witness
                                     (augment-next prop endor systate)))))
    :enable (signed-in-signer-p
             signed-props-of-augment-next
             validator-state->proposed-of-augment-next))

  (defruled signed-in-signer-p-of-certify-next
    (implies (and (certify-possiblep cert dests systate)
                  (signed-in-signer-p systate))
             (signed-in-signer-p (certify-next cert dests systate)))
    :use (:instance signed-in-signer-p-necc
                    (signer (mv-nth 0 (signed-in-signer-p-witness
                                       (certify-next cert dests systate))))
                    (prop (mv-nth 1 (signed-in-signer-p-witness
                                     (certify-next cert dests systate)))))
    :enable (signed-in-signer-p
             signed-props-of-certify-next
             validator-state->dag-of-certify-next
             validator-state->proposed-of-certify-next
             cert-set->prop-set-of-insert
             omap::keys-of-delete))

  (defruled signed-in-signer-p-of-accept-next
    (implies (and (accept-possiblep val cert systate)
                  (signed-in-signer-p systate))
             (signed-in-signer-p (accept-next val cert systate)))
    :use (:instance signed-in-signer-p-necc
                    (signer (mv-nth 0 (signed-in-signer-p-witness
                                       (accept-next val cert systate))))
                    (prop (mv-nth 1 (signed-in-signer-p-witness
                                     (accept-next val cert systate)))))
    :enable (signed-in-signer-p
             signed-props-of-accept-next
             validator-state->dag-of-accept-next
             validator-state->endorsed-of-accept-next
             cert-set->prop-set-of-insert))

  (defruled signed-in-signer-p-of-advance-next
    (implies (and (advance-possiblep val systate)
                  (signed-in-signer-p systate))
             (signed-in-signer-p (advance-next val systate)))
    :use (:instance signed-in-signer-p-necc
                    (signer (mv-nth 0 (signed-in-signer-p-witness
                                       (advance-next val systate))))
                    (prop (mv-nth 1 (signed-in-signer-p-witness
                                     (advance-next val systate)))))
    :enable (signed-in-signer-p
             signed-props-of-advance-next))

  (defruled signed-in-signer-p-of-commit-next
    (implies (and (commit-possiblep val systate)
                  (signed-in-signer-p systate))
             (signed-in-signer-p (commit-next val systate)))
    :use (:instance signed-in-signer-p-necc
                    (signer (mv-nth 0 (signed-in-signer-p-witness
                                       (commit-next val systate))))
                    (prop (mv-nth 1 (signed-in-signer-p-witness
                                     (commit-next val systate)))))
    :enable (signed-in-signer-p
             signed-props-of-commit-next))

  (defruled signed-in-signer-p-of-event-next
    (implies (and (event-possiblep event systate)
                  (signed-in-signer-p systate))
             (signed-in-signer-p (event-next event systate)))
    :enable (event-possiblep
             event-next)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled signed-in-signer-p-of-events-next
  :short "Preservation of the invariant by multiple transitions."
  (implies (and (events-possiblep events systate)
                (signed-in-signer-p systate))
           (signed-in-signer-p (events-next events systate)))
  :induct t
  :enable (events-possiblep
           events-next))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled signed-in-signer-p-when-reachable
  :short "The invariant holds in every reachable state."
  (implies (system-state-reachablep systate)
           (signed-in-signer-p systate))
  :enable (system-state-reachablep
           signed-in-signer-p-when-init)
  :prep-lemmas
  ((defrule lemma
     (implies (and (system-state-reachable-from-p systate from)
                   (signed-in-signer-p from))
              (signed-in-signer-p systate))
     :use (:instance
           signed-in-signer-p-of-events-next
           (events (system-state-reachable-from-p-witness systate from))
           (systate from))
     :enable system-state-reachable-from-p)))
