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

(defxdoc+ proposed-has-previous
  :parents (correctness)
  :short "Invariant that each validator's DAG has the previous certificates
          referenced by each of its pending proposals,
          if the round of the proposal is not 1;
          if the round is 1,
          the proposal has no references to previous certificates."
  :long
  (xdoc::topstring
   (xdoc::p
    "A validator creates a proposal only if its DAG contains
     all the previous certificates referenced in the proposal.
     That is the case if the round of the proposal is not 1.
     If the round is 1, the validator creates a proposal
     with no references to previous certificates."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk proposed-has-previous-p ((systate system-statep))
  :returns (yes/no booleanp)
  :short "Definition of the invariant."
  (forall (val prop)
          (implies (set::in val (correct-addresses systate))
                   (b* (((validator-state vstate)
                         (get-validator-state val systate)))
                     (implies (set::in prop (omap::keys vstate.proposed))
                              (b* (((proposal prop) prop))
                                (if (equal prop.round 1)
                                    (set::emptyp prop.previous)
                                  (set::subset prop.previous
                                               (cert-set->author-set
                                                (certs-with-round
                                                 (1- prop.round)
                                                 vstate.dag)))))))))
  :guard-hints
  (("Goal"
    :in-theory
    (enable proposal-setp-of-keys-when-proposal-address-set-mapp
            posp)))
  ///
  (fty::deffixequiv-sk proposed-has-previous-p
    :args ((systate system-statep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled proposed-has-previous-p-when-init
  :short "Establishment of the invariant in the initial states."
  (implies (system-initp systate)
           (proposed-has-previous-p systate))
  :enable (proposed-has-previous-p
           system-initp
           system-validators-initp-necc
           validator-init))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection proposed-has-previous-p-of-next
  :short "Preservation of the invariant by single transitions."

  (defruled proposed-has-previous-p-of-propose-next
    (implies (and (propose-possiblep prop dests systate)
                  (proposed-has-previous-p systate))
             (proposed-has-previous-p (propose-next prop dests systate)))
    :use (:instance proposed-has-previous-p-necc
                    (val (mv-nth 0 (proposed-has-previous-p-witness
                                    (propose-next prop dests systate))))
                    (prop (mv-nth 1 (proposed-has-previous-p-witness
                                     (propose-next prop dests systate)))))
    :enable (proposed-has-previous-p
             validator-state->dag-of-propose-next
             validator-state->proposed-of-propose-next
             propose-possiblep ))

  (defruled proposed-has-previous-p-of-endorse-next
    (implies (proposed-has-previous-p systate)
             (proposed-has-previous-p (endorse-next prop endor systate)))
    :use (:instance proposed-has-previous-p-necc
                    (val (mv-nth 0 (proposed-has-previous-p-witness
                                    (endorse-next prop endor systate))))
                    (prop (mv-nth 1 (proposed-has-previous-p-witness
                                     (endorse-next prop endor systate)))))
    :enable proposed-has-previous-p)

  (defruled proposed-has-previous-p-of-augment-next
    (implies (and (augment-possiblep prop endor systate)
                  (proposed-has-previous-p systate))
             (proposed-has-previous-p (augment-next prop endor systate)))
    :use (:instance proposed-has-previous-p-necc
                    (val (mv-nth 0 (proposed-has-previous-p-witness
                                    (augment-next prop endor systate))))
                    (prop (mv-nth 1 (proposed-has-previous-p-witness
                                     (augment-next prop endor systate)))))
    :enable (proposed-has-previous-p
             validator-state->proposed-of-augment-next
             augment-possiblep
             omap::assoc-to-in-of-keys))

  (defruled proposed-has-previous-p-of-certify-next
    (implies (proposed-has-previous-p systate)
             (proposed-has-previous-p (certify-next cert dests systate)))
    :use (:instance proposed-has-previous-p-necc
                    (val (mv-nth 0 (proposed-has-previous-p-witness
                                    (certify-next cert dests systate))))
                    (prop (mv-nth 1 (proposed-has-previous-p-witness
                                     (certify-next cert dests systate)))))
    :enable (proposed-has-previous-p
             validator-state->dag-of-certify-next
             validator-state->proposed-of-certify-next
             omap::keys-of-delete
             certs-with-round-of-insert
             cert-set->author-set-of-insert
             set::expensive-rules))

  (defruled proposed-has-previous-p-of-accept-next
    (implies (and (accept-possiblep val cert systate)
                  (proposed-has-previous-p systate))
             (proposed-has-previous-p (accept-next val cert systate)))
    :use (:instance proposed-has-previous-p-necc
                    (val (mv-nth 0 (proposed-has-previous-p-witness
                                    (accept-next val cert systate))))
                    (prop (mv-nth 1 (proposed-has-previous-p-witness
                                     (accept-next val cert systate)))))
    :enable (proposed-has-previous-p
             validator-state->dag-of-accept-next
             certs-with-round-of-insert
             cert-set->author-set-of-insert
             set::expensive-rules))

  (defruled proposed-has-previous-p-of-advance-next
    (implies (and (advance-possiblep val systate)
                  (proposed-has-previous-p systate))
             (proposed-has-previous-p (advance-next val systate)))
    :use (:instance proposed-has-previous-p-necc
                    (val (mv-nth 0 (proposed-has-previous-p-witness
                                    (advance-next val systate))))
                    (prop (mv-nth 1 (proposed-has-previous-p-witness
                                     (advance-next val systate)))))
    :enable proposed-has-previous-p)

  (defruled proposed-has-previous-p-of-commit-next
    (implies (and (commit-possiblep val systate)
                  (proposed-has-previous-p systate))
             (proposed-has-previous-p (commit-next val systate)))
    :use (:instance proposed-has-previous-p-necc
                    (val (mv-nth 0 (proposed-has-previous-p-witness
                                    (commit-next val systate))))
                    (prop (mv-nth 1 (proposed-has-previous-p-witness
                                     (commit-next val systate)))))
    :enable proposed-has-previous-p)

  (defruled proposed-has-previous-p-of-event-next
    (implies (and (event-possiblep event systate)
                  (proposed-has-previous-p systate))
             (proposed-has-previous-p (event-next event systate)))
    :enable (event-possiblep
             event-next)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled proposed-has-previous-p-of-events-next
  :short "Preservation of the invariant by multiple transitions."
  (implies (and (events-possiblep events systate)
                (proposed-has-previous-p systate))
           (proposed-has-previous-p (events-next events systate)))
  :induct t
  :enable (events-possiblep
           events-next))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled proposed-has-previous-p-when-reachable
  :short "The invariant holds in every reachable state."
  (implies (system-state-reachablep systate)
           (proposed-has-previous-p systate))
  :enable (system-state-reachablep
           proposed-has-previous-p-when-init)
  :prep-lemmas
  ((defrule lemma
     (implies (and (system-state-reachable-from-p systate from)
                   (proposed-has-previous-p from))
              (proposed-has-previous-p systate))
     :use (:instance
           proposed-has-previous-p-of-events-next
           (events (system-state-reachable-from-p-witness systate from))
           (systate from))
     :enable system-state-reachable-from-p)))
