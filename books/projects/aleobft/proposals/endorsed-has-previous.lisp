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

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ endorsed-has-previous
  :parents (correctness)
  :short "Invariant that each validator's DAG has the previous certificates
          referenced by each of its endorsed proposals,
          if the round of the proposal is not 1;
          if the round is 1,
          the proposal has no references to previous certificates."
  :long
  (xdoc::topstring
   (xdoc::p
    "A validator endorses a proposal only if its DAG contains
     all the previous certificates referenced in the proposal.
     That is the case if the round of the proposal is not 1.
     If the round is 1, the validator endorses a proposal
     only if it has no references to previous certificates."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk endorsed-has-previous-p ((systate system-statep))
  :returns (yes/no booleanp)
  :short "Definition of the invariant."
  (forall (val prop)
          (implies (set::in val (correct-addresses systate))
                   (b* (((validator-state vstate)
                         (get-validator-state val systate)))
                     (implies (set::in prop vstate.endorsed)
                              (b* (((proposal prop) prop))
                                (if (equal prop.round 1)
                                    (set::emptyp prop.previous)
                                  (set::subset prop.previous
                                               (cert-set->author-set
                                                (certs-with-round
                                                 (1- prop.round)
                                                 vstate.dag)))))))))
  :guard-hints (("Goal" :in-theory (enable posp)))
  ///
  (fty::deffixequiv-sk endorsed-has-previous-p
    :args ((systate system-statep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled endorsed-has-previous-p-when-init
  :short "Establishment of the invariant in the initial states."
  (implies (system-initp systate)
           (endorsed-has-previous-p systate))
  :enable (endorsed-has-previous-p
           system-initp
           system-validators-initp-necc
           validator-init))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection endorsed-has-previous-p-of-next
  :short "Preservation of the invariant by single transitions."

  (defruled endorsed-has-previous-p-of-propose-next
    (implies (endorsed-has-previous-p systate)
             (endorsed-has-previous-p (propose-next prop dests systate)))
    :use (:instance endorsed-has-previous-p-necc
                    (val (mv-nth 0 (endorsed-has-previous-p-witness
                                    (propose-next prop dests systate))))
                    (prop (mv-nth 1 (endorsed-has-previous-p-witness
                                     (propose-next prop dests systate)))))
    :enable endorsed-has-previous-p)

  (defruled endorsed-has-previous-p-of-endorse-next
    (implies (and (endorse-possiblep prop endor systate)
                  (endorsed-has-previous-p systate))
             (endorsed-has-previous-p (endorse-next prop endor systate)))
    :use (:instance endorsed-has-previous-p-necc
                    (val (mv-nth 0 (endorsed-has-previous-p-witness
                                    (endorse-next prop endor systate))))
                    (prop (mv-nth 1 (endorsed-has-previous-p-witness
                                     (endorse-next prop endor systate)))))
    :enable (endorsed-has-previous-p
             validator-state->endorsed-of-endorse-next
             endorse-possiblep))

  (defruled endorsed-has-previous-p-of-augment-next
    (implies (and (augment-possiblep prop endor systate)
                  (endorsed-has-previous-p systate))
             (endorsed-has-previous-p (augment-next prop endor systate)))
    :use (:instance endorsed-has-previous-p-necc
                    (val (mv-nth 0 (endorsed-has-previous-p-witness
                                    (augment-next prop endor systate))))
                    (prop (mv-nth 1 (endorsed-has-previous-p-witness
                                     (augment-next prop endor systate)))))
    :enable (endorsed-has-previous-p))

  (defruled endorsed-has-previous-p-of-certify-next
    (implies (endorsed-has-previous-p systate)
             (endorsed-has-previous-p (certify-next cert dests systate)))
    :use (:instance endorsed-has-previous-p-necc
                    (val (mv-nth 0 (endorsed-has-previous-p-witness
                                    (certify-next cert dests systate))))
                    (prop (mv-nth 1 (endorsed-has-previous-p-witness
                                     (certify-next cert dests systate)))))
    :enable (endorsed-has-previous-p
             validator-state->dag-of-certify-next
             certs-with-round-of-insert
             cert-set->author-set-of-insert
             set::expensive-rules))

  (defruled endorsed-has-previous-p-of-accept-next
    (implies (and (accept-possiblep val cert systate)
                  (endorsed-has-previous-p systate))
             (endorsed-has-previous-p (accept-next val cert systate)))
    :use (:instance endorsed-has-previous-p-necc
                    (val (mv-nth 0 (endorsed-has-previous-p-witness
                                    (accept-next val cert systate))))
                    (prop (mv-nth 1 (endorsed-has-previous-p-witness
                                     (accept-next val cert systate)))))
    :enable (endorsed-has-previous-p
             validator-state->dag-of-accept-next
             validator-state->endorsed-of-accept-next
             certs-with-round-of-insert
             cert-set->author-set-of-insert
             set::expensive-rules))

  (defruled endorsed-has-previous-p-of-advance-next
    (implies (and (advance-possiblep val systate)
                  (endorsed-has-previous-p systate))
             (endorsed-has-previous-p (advance-next val systate)))
    :use (:instance endorsed-has-previous-p-necc
                    (val (mv-nth 0 (endorsed-has-previous-p-witness
                                    (advance-next val systate))))
                    (prop (mv-nth 1 (endorsed-has-previous-p-witness
                                     (advance-next val systate)))))
    :enable endorsed-has-previous-p)

  (defruled endorsed-has-previous-p-of-commit-next
    (implies (and (commit-possiblep val systate)
                  (endorsed-has-previous-p systate))
             (endorsed-has-previous-p (commit-next val systate)))
    :use (:instance endorsed-has-previous-p-necc
                    (val (mv-nth 0 (endorsed-has-previous-p-witness
                                    (commit-next val systate))))
                    (prop (mv-nth 1 (endorsed-has-previous-p-witness
                                     (commit-next val systate)))))
    :enable endorsed-has-previous-p)

  (defruled endorsed-has-previous-p-of-event-next
    (implies (and (event-possiblep event systate)
                  (endorsed-has-previous-p systate))
             (endorsed-has-previous-p (event-next event systate)))
    :enable (event-possiblep
             event-next)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled endorsed-has-previous-p-of-events-next
  :short "Preservation of the invariant by multiple transitions."
  (implies (and (events-possiblep events systate)
                (endorsed-has-previous-p systate))
           (endorsed-has-previous-p (events-next events systate)))
  :induct t
  :enable (events-possiblep
           events-next))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled endorsed-has-previous-p-when-reachable
  :short "The invariant holds in every reachable state."
  (implies (system-state-reachablep systate)
           (endorsed-has-previous-p systate))
  :enable (system-state-reachablep
           endorsed-has-previous-p-when-init)
  :prep-lemmas
  ((defrule lemma
     (implies (and (system-state-reachable-from-p systate from)
                   (endorsed-has-previous-p from))
              (endorsed-has-previous-p systate))
     :use (:instance
           endorsed-has-previous-p-of-events-next
           (events (system-state-reachable-from-p-witness systate from))
           (systate from))
     :enable system-state-reachable-from-p)))
