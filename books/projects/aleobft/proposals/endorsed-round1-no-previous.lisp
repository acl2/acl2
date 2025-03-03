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

(include-book "proposed-round1-no-previous")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ endorsed-round1-no-previous
  :parents (correctness)
  :short "Invariant that each proposal in round 1
          in the endorsed proposals of a correct validator
          has no references to previous certificates."
  :long
  (xdoc::topstring
   (xdoc::p
    "When a correct validator endorses a proposal for round 1,
     it ensures that there are no references to previous certificates in it,
     because there is no round 0."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk endorsed-round1-no-previous-p ((systate system-statep))
  :returns (yes/no booleanp)
  :short "Definition of the invariant."
  (forall (val prop)
          (implies (set::in val (correct-addresses systate))
                   (b* (((validator-state vstate)
                         (get-validator-state val systate)))
                     (implies (set::in prop vstate.endorsed)
                              (b* (((proposal prop) prop))
                                (implies (equal prop.round 1)
                                         (set::emptyp prop.previous)))))))
  ///
  (fty::deffixequiv-sk endorsed-round1-no-previous-p
    :args ((systate system-statep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled endorsed-round1-no-previous-p-when-init
  :short "Establishment of the invariant in the initial states."
  (implies (system-initp systate)
           (endorsed-round1-no-previous-p systate))
  :enable (endorsed-round1-no-previous-p
           system-initp
           system-validators-initp-necc
           validator-init))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection endorsed-round1-no-previous-p-of-next
  :short "Preservation of the invariant by single transitions."

  (defruled endorsed-round1-no-previous-p-of-propose-next
    (implies (endorsed-round1-no-previous-p systate)
             (endorsed-round1-no-previous-p (propose-next prop dests systate)))
    :expand (endorsed-round1-no-previous-p (propose-next prop dests systate))
    :enable endorsed-round1-no-previous-p-necc)

  (defruled endorsed-round1-no-previous-p-of-endorse-next
    (implies (and (endorse-possiblep prop endor systate)
                  (endorsed-round1-no-previous-p systate))
             (endorsed-round1-no-previous-p (endorse-next prop endor systate)))
    :expand (endorsed-round1-no-previous-p (endorse-next prop endor systate))
    :enable (endorsed-round1-no-previous-p-necc
             validator-state->endorsed-of-endorse-next
             endorse-possiblep))

  (defruled endorsed-round1-no-previous-p-of-augment-next
    (implies (and (augment-possiblep prop endor systate)
                  (endorsed-round1-no-previous-p systate))
             (endorsed-round1-no-previous-p (augment-next prop endor systate)))
    :expand (endorsed-round1-no-previous-p (augment-next prop endor systate))
    :enable (endorsed-round1-no-previous-p-necc
             validator-state->proposed-of-augment-next
             augment-possiblep
             omap::assoc-to-in-of-keys))

  (defruled endorsed-round1-no-previous-p-of-certify-next
    (implies (endorsed-round1-no-previous-p systate)
             (endorsed-round1-no-previous-p (certify-next cert dests systate)))
    :expand (endorsed-round1-no-previous-p (certify-next cert dests systate))
    :enable endorsed-round1-no-previous-p-necc)

  (defruled endorsed-round1-no-previous-p-of-accept-next
    (implies (and (accept-possiblep val cert systate)
                  (endorsed-round1-no-previous-p systate))
             (endorsed-round1-no-previous-p (accept-next val cert systate)))
    :expand (endorsed-round1-no-previous-p (accept-next val cert systate))
    :enable (endorsed-round1-no-previous-p-necc
             validator-state->endorsed-of-accept-next))

  (defruled endorsed-round1-no-previous-p-of-advance-next
    (implies (and (advance-possiblep val systate)
                  (endorsed-round1-no-previous-p systate))
             (endorsed-round1-no-previous-p (advance-next val systate)))
    :expand (endorsed-round1-no-previous-p (advance-next val systate))
    :enable endorsed-round1-no-previous-p-necc)

  (defruled endorsed-round1-no-previous-p-of-commit-next
    (implies (and (commit-possiblep val systate)
                  (endorsed-round1-no-previous-p systate))
             (endorsed-round1-no-previous-p (commit-next val systate)))
    :expand (endorsed-round1-no-previous-p (commit-next val systate))
    :enable endorsed-round1-no-previous-p-necc)

  (defruled endorsed-round1-no-previous-p-of-event-next
    (implies (and (event-possiblep event systate)
                  (endorsed-round1-no-previous-p systate))
             (endorsed-round1-no-previous-p (event-next event systate)))
    :enable (event-possiblep
             event-next)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled endorsed-round1-no-previous-p-of-events-next
  :short "Preservation of the invariant by multiple transitions."
  (implies (and (events-possiblep events systate)
                (endorsed-round1-no-previous-p systate))
           (endorsed-round1-no-previous-p (events-next events systate)))
  :induct t
  :enable (events-possiblep
           events-next))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled endorsed-round1-no-previous-p-when-reachable
  :short "The invariant holds in every reachable state."
  (implies (system-state-reachablep systate)
           (endorsed-round1-no-previous-p systate))
  :enable (system-state-reachablep
           endorsed-round1-no-previous-p-when-init)
  :prep-lemmas
  ((defrule lemma
     (implies (and (system-state-reachable-from-p systate from)
                   (endorsed-round1-no-previous-p from))
              (endorsed-round1-no-previous-p systate))
     :use (:instance
           endorsed-round1-no-previous-p-of-events-next
           (events (system-state-reachable-from-p-witness systate from))
           (systate from))
     :enable system-state-reachable-from-p)))
