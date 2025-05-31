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

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ endorsed-previous-closed
  :parents (correctness)
  :short "Invariant that each validator's DAG has the previous certificates
          referenced by each of its endorsed proposals,
          at rounds greater than 1."
  :long
  (xdoc::topstring
   (xdoc::p
    "A validator endorses a proposal only if its DAG contains
     all the previous certificates referenced in the proposal,
     when the round of the proposal is not 1."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk endorsed-previous-closed-p ((systate system-statep))
  :returns (yes/no booleanp)
  :short "Definition of the invariant."
  (forall (val prop)
          (implies (set::in val (correct-addresses systate))
                   (b* (((validator-state vstate)
                         (get-validator-state val systate)))
                     (implies (set::in prop vstate.endorsed)
                              (b* (((proposal prop) prop))
                                (implies (not (equal prop.round 1))
                                         (set::subset prop.previous
                                                      (cert-set->author-set
                                                       (certs-with-round
                                                        (1- prop.round)
                                                        vstate.dag)))))))))
  :guard-hints (("Goal" :in-theory (enable posp)))
  ///
  (fty::deffixequiv-sk endorsed-previous-closed-p
    :args ((systate system-statep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled endorsed-previous-closed-p-when-init
  :short "Establishment of the invariant in the initial states."
  (implies (system-initp systate)
           (endorsed-previous-closed-p systate))
  :enable (endorsed-previous-closed-p
           system-initp
           system-validators-initp-necc
           validator-init))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection endorsed-previous-closed-p-of-next
  :short "Preservation of the invariant by single transitions."

  (defruled endorsed-previous-closed-p-of-propose-next
    (implies (endorsed-previous-closed-p systate)
             (endorsed-previous-closed-p (propose-next prop dests systate)))
    :enable (endorsed-previous-closed-p
             endorsed-previous-closed-p-necc))

  (defruled endorsed-previous-closed-p-of-endorse-next
    (implies (and (endorse-possiblep prop endor systate)
                  (endorsed-previous-closed-p systate))
             (endorsed-previous-closed-p (endorse-next prop endor systate)))
    :use (:instance endorsed-previous-closed-p-necc
                    (val (mv-nth 0 (endorsed-previous-closed-p-witness
                                    (endorse-next prop endor systate))))
                    (prop (mv-nth 1 (endorsed-previous-closed-p-witness
                                     (endorse-next prop endor systate)))))
    :enable (endorsed-previous-closed-p
             validator-state->endorsed-of-endorse-next
             endorse-possiblep))

  (defruled endorsed-previous-closed-p-of-augment-next
    (implies (and (augment-possiblep prop endor systate)
                  (endorsed-previous-closed-p systate))
             (endorsed-previous-closed-p (augment-next prop endor systate)))
    :enable (endorsed-previous-closed-p
             endorsed-previous-closed-p-necc))

  (defruled endorsed-previous-closed-p-of-certify-next
    (implies (endorsed-previous-closed-p systate)
             (endorsed-previous-closed-p (certify-next cert dests systate)))
    :enable (endorsed-previous-closed-p
             endorsed-previous-closed-p-necc
             validator-state->dag-of-certify-next
             certs-with-round-of-insert
             cert-set->author-set-of-insert
             set::expensive-rules))

  (defruled endorsed-previous-closed-p-of-accept-next
    (implies (and (accept-possiblep val cert systate)
                  (endorsed-previous-closed-p systate))
             (endorsed-previous-closed-p (accept-next val cert systate)))
    :use (:instance endorsed-previous-closed-p-necc
                    (val (mv-nth 0 (endorsed-previous-closed-p-witness
                                    (accept-next val cert systate))))
                    (prop (mv-nth 1 (endorsed-previous-closed-p-witness
                                     (accept-next val cert systate)))))
    :enable (endorsed-previous-closed-p
             validator-state->dag-of-accept-next
             validator-state->endorsed-of-accept-next
             certs-with-round-of-insert
             cert-set->author-set-of-insert
             set::expensive-rules))

  (defruled endorsed-previous-closed-p-of-advance-next
    (implies (and (advance-possiblep val systate)
                  (endorsed-previous-closed-p systate))
             (endorsed-previous-closed-p (advance-next val systate)))
    :enable (endorsed-previous-closed-p
             endorsed-previous-closed-p-necc))

  (defruled endorsed-previous-closed-p-of-commit-next
    (implies (and (commit-possiblep val systate)
                  (endorsed-previous-closed-p systate))
             (endorsed-previous-closed-p (commit-next val systate)))
    :enable (endorsed-previous-closed-p
             endorsed-previous-closed-p-necc))

  (defruled endorsed-previous-closed-p-of-event-next
    (implies (and (event-possiblep event systate)
                  (endorsed-previous-closed-p systate))
             (endorsed-previous-closed-p (event-next event systate)))
    :enable (event-possiblep
             event-next)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled endorsed-previous-closed-p-of-events-next
  :short "Preservation of the invariant by multiple transitions."
  (implies (and (events-possiblep events systate)
                (endorsed-previous-closed-p systate))
           (endorsed-previous-closed-p (events-next events systate)))
  :induct t
  :enable (events-possiblep
           events-next))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled endorsed-previous-closed-p-when-reachable
  :short "The invariant holds in every reachable state."
  (implies (system-state-reachablep systate)
           (endorsed-previous-closed-p systate))
  :enable (system-state-reachablep
           endorsed-previous-closed-p-when-init)
  :prep-lemmas
  ((defrule lemma
     (implies (and (system-state-reachable-from-p systate from)
                   (endorsed-previous-closed-p from))
              (endorsed-previous-closed-p systate))
     :use (:instance
           endorsed-previous-closed-p-of-events-next
           (events (system-state-reachable-from-p-witness systate from))
           (systate from))
     :enable system-state-reachable-from-p)))
