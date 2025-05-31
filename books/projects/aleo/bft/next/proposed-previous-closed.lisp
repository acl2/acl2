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

(local (include-book "../library-extensions/omap-theorems"))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ proposed-previous-closed
  :parents (correctness)
  :short "Invariant that each validator's DAG has the previous certificates
          referenced by each of its pending proposals
          at rounds greater than 1."
  :long
  (xdoc::topstring
   (xdoc::p
    "A validator creates a proposal only if its DAG contains
     all the previous certificates referenced in the proposal,
     when the round of the proposal is not 1."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk proposed-previous-closed-p ((systate system-statep))
  :returns (yes/no booleanp)
  :short "Definition of the invariant."
  (forall (val prop)
          (implies (set::in val (correct-addresses systate))
                   (b* (((validator-state vstate)
                         (get-validator-state val systate)))
                     (implies (set::in prop (omap::keys vstate.proposed))
                              (b* (((proposal prop) prop))
                                (implies (not (equal prop.round 1))
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
  (fty::deffixequiv-sk proposed-previous-closed-p
    :args ((systate system-statep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled proposed-previous-closed-p-when-init
  :short "Establishment of the invariant in the initial states."
  (implies (system-initp systate)
           (proposed-previous-closed-p systate))
  :enable (proposed-previous-closed-p
           system-initp
           system-validators-initp-necc
           validator-init))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection proposed-previous-closed-p-of-next
  :short "Preservation of the invariant by single transitions."

  (defruled proposed-previous-closed-p-of-propose-next
    (implies (and (propose-possiblep prop dests systate)
                  (proposed-previous-closed-p systate))
             (proposed-previous-closed-p (propose-next prop dests systate)))
    :enable (proposed-previous-closed-p
             proposed-previous-closed-p-necc
             validator-state->proposed-of-propose-next
             propose-possiblep))

  (defruled proposed-previous-closed-p-of-endorse-next
    (implies (proposed-previous-closed-p systate)
             (proposed-previous-closed-p (endorse-next prop endor systate)))
    :enable (proposed-previous-closed-p
             proposed-previous-closed-p-necc))

  (defruled proposed-previous-closed-p-of-augment-next
    (implies (and (augment-possiblep prop endor systate)
                  (proposed-previous-closed-p systate))
             (proposed-previous-closed-p (augment-next prop endor systate)))
    :enable (proposed-previous-closed-p
             proposed-previous-closed-p-necc
             validator-state->proposed-of-augment-next
             augment-possiblep
             omap::assoc-to-in-of-keys))

  (defruled proposed-previous-closed-p-of-certify-next
    (implies (proposed-previous-closed-p systate)
             (proposed-previous-closed-p (certify-next cert dests systate)))
    :enable (proposed-previous-closed-p
             proposed-previous-closed-p-necc
             validator-state->dag-of-certify-next
             validator-state->proposed-of-certify-next
             omap::keys-of-delete
             certs-with-round-of-insert
             cert-set->author-set-of-insert
             set::expensive-rules))

  (defruled proposed-previous-closed-p-of-accept-next
    (implies (and (accept-possiblep val cert systate)
                  (proposed-previous-closed-p systate))
             (proposed-previous-closed-p (accept-next val cert systate)))
    :use (:instance proposed-previous-closed-p-necc
                    (val (mv-nth 0 (proposed-previous-closed-p-witness
                                    (accept-next val cert systate))))
                    (prop (mv-nth 1 (proposed-previous-closed-p-witness
                                     (accept-next val cert systate)))))
    :enable (proposed-previous-closed-p
             validator-state->dag-of-accept-next
             certs-with-round-of-insert
             cert-set->author-set-of-insert
             set::expensive-rules))

  (defruled proposed-previous-closed-p-of-advance-next
    (implies (and (advance-possiblep val systate)
                  (proposed-previous-closed-p systate))
             (proposed-previous-closed-p (advance-next val systate)))
    :enable (proposed-previous-closed-p
             proposed-previous-closed-p-necc))

  (defruled proposed-previous-closed-p-of-commit-next
    (implies (and (commit-possiblep val systate)
                  (proposed-previous-closed-p systate))
             (proposed-previous-closed-p (commit-next val systate)))
    :enable (proposed-previous-closed-p
             proposed-previous-closed-p-necc))

  (defruled proposed-previous-closed-p-of-event-next
    (implies (and (event-possiblep event systate)
                  (proposed-previous-closed-p systate))
             (proposed-previous-closed-p (event-next event systate)))
    :enable (event-possiblep
             event-next)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled proposed-previous-closed-p-of-events-next
  :short "Preservation of the invariant by multiple transitions."
  (implies (and (events-possiblep events systate)
                (proposed-previous-closed-p systate))
           (proposed-previous-closed-p (events-next events systate)))
  :induct t
  :enable (events-possiblep
           events-next))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled proposed-previous-closed-p-when-reachable
  :short "The invariant holds in every reachable state."
  (implies (system-state-reachablep systate)
           (proposed-previous-closed-p systate))
  :enable (system-state-reachablep
           proposed-previous-closed-p-when-init)
  :prep-lemmas
  ((defrule lemma
     (implies (and (system-state-reachable-from-p systate from)
                   (proposed-previous-closed-p from))
              (proposed-previous-closed-p systate))
     :use (:instance
           proposed-previous-closed-p-of-events-next
           (events (system-state-reachable-from-p-witness systate from))
           (systate from))
     :enable system-state-reachable-from-p)))
