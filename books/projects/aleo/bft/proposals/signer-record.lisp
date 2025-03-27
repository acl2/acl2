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
(include-book "signed-proposals")

(local (include-book "../library-extensions/omap-theorems"))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ signer-record
  :parents (correctness)
  :short "Invariant that each correct signer of each proposal
          has a record of the proposal in its state."
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

(define-sk signer-record-p ((systate system-statep))
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
  (fty::deffixequiv-sk signer-record-p
    :args ((systate system-statep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled signer-record-p-when-init
  :short "Establishment of the invariant in the initial states."
  (implies (system-initp systate)
           (signer-record-p systate))
  :enable (signer-record-p
           signed-props-when-init))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection signed-record-p-of-next
  :short "Preservation of the invariant by single transitions."

  (defruled signer-record-p-of-propose-next
    (implies (and (propose-possiblep prop dests systate)
                  (signer-record-p systate))
             (signer-record-p (propose-next prop dests systate)))
    :use (:instance signer-record-p-necc
                    (signer (mv-nth 0 (signer-record-p-witness
                                       (propose-next prop dests systate))))
                    (prop (mv-nth 1 (signer-record-p-witness
                                     (propose-next prop dests systate)))))
    :enable (signer-record-p
             signed-props-of-propose-next
             validator-state->proposed-of-propose-next))

  (defruled signer-record-p-of-endorse-next
    (implies (and (endorse-possiblep prop endor systate)
                  (signer-record-p systate))
             (signer-record-p (endorse-next prop endor systate)))
    :use (:instance signer-record-p-necc
                    (signer (mv-nth 0 (signer-record-p-witness
                                       (endorse-next prop endor systate))))
                    (prop (mv-nth 1 (signer-record-p-witness
                                     (endorse-next prop endor systate)))))
    :enable (signer-record-p
             signed-props-of-endorse-next
             validator-state->endorsed-of-endorse-next))

  (defruled signer-record-p-of-augment-next
    (implies (and (augment-possiblep prop endor systate)
                  (signer-record-p systate))
             (signer-record-p (augment-next prop endor systate)))
    :use (:instance signer-record-p-necc
                    (signer (mv-nth 0 (signer-record-p-witness
                                       (augment-next prop endor systate))))
                    (prop (mv-nth 1 (signer-record-p-witness
                                     (augment-next prop endor systate)))))
    :enable (signer-record-p
             signed-props-of-augment-next
             validator-state->proposed-of-augment-next))

  (defruled signer-record-p-of-certify-next
    (implies (and (certify-possiblep cert dests systate)
                  (signer-record-p systate))
             (signer-record-p (certify-next cert dests systate)))
    :use (:instance signer-record-p-necc
                    (signer (mv-nth 0 (signer-record-p-witness
                                       (certify-next cert dests systate))))
                    (prop (mv-nth 1 (signer-record-p-witness
                                     (certify-next cert dests systate)))))
    :enable (signer-record-p
             signed-props-of-certify-next
             validator-state->dag-of-certify-next
             validator-state->proposed-of-certify-next
             cert-set->prop-set-of-insert
             omap::keys-of-delete))

  (defruled signer-record-p-of-accept-next
    (implies (and (accept-possiblep val cert systate)
                  (signer-record-p systate))
             (signer-record-p (accept-next val cert systate)))
    :use (:instance signer-record-p-necc
                    (signer (mv-nth 0 (signer-record-p-witness
                                       (accept-next val cert systate))))
                    (prop (mv-nth 1 (signer-record-p-witness
                                     (accept-next val cert systate)))))
    :enable (signer-record-p
             signed-props-of-accept-next
             validator-state->dag-of-accept-next
             validator-state->endorsed-of-accept-next
             cert-set->prop-set-of-insert))

  (defruled signer-record-p-of-advance-next
    (implies (and (advance-possiblep val systate)
                  (signer-record-p systate))
             (signer-record-p (advance-next val systate)))
    :use (:instance signer-record-p-necc
                    (signer (mv-nth 0 (signer-record-p-witness
                                       (advance-next val systate))))
                    (prop (mv-nth 1 (signer-record-p-witness
                                     (advance-next val systate)))))
    :enable (signer-record-p
             signed-props-of-advance-next))

  (defruled signer-record-p-of-commit-next
    (implies (and (commit-possiblep val systate)
                  (signer-record-p systate))
             (signer-record-p (commit-next val systate)))
    :use (:instance signer-record-p-necc
                    (signer (mv-nth 0 (signer-record-p-witness
                                       (commit-next val systate))))
                    (prop (mv-nth 1 (signer-record-p-witness
                                     (commit-next val systate)))))
    :enable (signer-record-p
             signed-props-of-commit-next))

  (defruled signer-record-p-of-event-next
    (implies (and (event-possiblep event systate)
                  (signer-record-p systate))
             (signer-record-p (event-next event systate)))
    :enable (event-possiblep
             event-next)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled signer-record-p-of-events-next
  :short "Preservation of the invariant by multiple transitions."
  (implies (and (events-possiblep events systate)
                (signer-record-p systate))
           (signer-record-p (events-next events systate)))
  :induct t
  :enable (events-possiblep
           events-next))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled signer-record-p-when-reachable
  :short "The invariant holds in every reachable state."
  (implies (system-state-reachablep systate)
           (signer-record-p systate))
  :enable (system-state-reachablep
           signer-record-p-when-init)
  :prep-lemmas
  ((defrule lemma
     (implies (and (system-state-reachable-from-p systate from)
                   (signer-record-p from))
              (signer-record-p systate))
     :use (:instance
           signer-record-p-of-events-next
           (events (system-state-reachable-from-p-witness systate from))
           (systate from))
     :enable system-state-reachable-from-p)))
