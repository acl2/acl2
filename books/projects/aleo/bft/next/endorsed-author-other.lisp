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

(include-book "proposal-to-other")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ endorsed-author-other
  :parents (correctness)
  :short "Invariant that the author of each endorsed proposal
          in each validator state
          is never the validator itself."
  :long
  (xdoc::topstring
   (xdoc::p
    "Each validator state has an @('endorsed') component
     that keeps track of the proposals endorsed by the validator.
     Proposals are added to this state component only by @('endorse') events,
     and the proposals are taken from the received proposal messages,
     which, as proved in @(see proposal-to-other),
     are always addressed to validators different from the author:
     thus, the endorser who adds the proposal to its @('endorsed') component,
     is never the proposal author."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk endorsed-author-other-p ((systate system-statep))
  :returns (yes/no booleanp)
  :short "Definition of the invariant."
  (forall (val prop)
          (implies (set::in val (correct-addresses systate))
                   (b* (((validator-state vstate)
                         (get-validator-state val systate)))
                     (implies (set::in prop vstate.endorsed)
                              (not (equal (proposal->author prop)
                                          val))))))

  ///

  (fty::deffixequiv-sk endorsed-author-other-p
    :args ((systate system-statep)))

  (defruled prop-set-none-author-p-when-endorsed-author-other-p
    (implies (and (endorsed-author-other-p systate)
                  (set::in val (correct-addresses systate)))
             (prop-set-none-author-p
              val (validator-state->endorsed
                   (get-validator-state val systate))))
    :disable (endorsed-author-other-p
              endorsed-author-other-p-necc)
    :enable prop-set-none-author-p
    :use (:instance endorsed-author-other-p-necc
                    (prop (prop-set-none-author-p-witness
                           val
                           (validator-state->endorsed
                            (get-validator-state val systate)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled endorsed-author-other-p-when-init
  :short "Establishment of the invariant in the initial states."
  (implies (system-initp systate)
           (endorsed-author-other-p systate))
  :enable (endorsed-author-other-p
           system-initp
           system-validators-initp-necc
           validator-init))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection endorsed-author-other-p-of-next
  :short "Preservation of the invariant by single transitions."
  :long
  (xdoc::topstring
   (xdoc::p
    "The reason why use the @(':expand') hint,
     instead of just enabling @(tsee endorsed-author-other-p),
     is that, if we do the latter,
     the @('endorsed-author-other-p-necc') rule does not fire,
     because it cannot instantiate the free variable @('systate').
     With the @(':expand') hint,
     only the call of @(tsee endorsed-author-other-p)
     in the conclusion of the theorems is expanded,
     leaving the call in the hypothesis unexpanded,
     so it can be used to provide an instantiation for
     the free variable @('systate') in @('endorsed-author-other-p-necc')."))

  (defruled endorsed-author-other-p-of-propose-next
    (implies (endorsed-author-other-p systate)
             (endorsed-author-other-p (propose-next prop dests systate)))
    :expand (endorsed-author-other-p (propose-next prop dests systate))
    :enable endorsed-author-other-p-necc)

  (defruled endorsed-author-other-p-of-endorse-next
    (implies (and (endorse-possiblep prop endor systate)
                  (proposal-to-other-p systate)
                  (endorsed-author-other-p systate))
             (endorsed-author-other-p (endorse-next prop endor systate)))
    :expand (endorsed-author-other-p (endorse-next prop endor systate))
    :use (:instance proposal-to-other-p-necc
                    (prop (proposal-fix prop))
                    (dest (address-fix endor)))
    :enable (endorsed-author-other-p-necc
             validator-state->endorsed-of-endorse-next
             endorse-possiblep))

  (defruled endorsed-author-other-p-of-augment-next
    (implies (and (augment-possiblep prop endor systate)
                  (endorsed-author-other-p systate))
             (endorsed-author-other-p (augment-next prop endor systate)))
    :expand (endorsed-author-other-p (augment-next prop endor systate))
    :enable endorsed-author-other-p-necc)

  (defruled endorsed-author-other-p-of-certify-next
    (implies (endorsed-author-other-p systate)
             (endorsed-author-other-p (certify-next cert dests systate)))
    :expand (endorsed-author-other-p (certify-next cert dests systate))
    :enable endorsed-author-other-p-necc)

  (defruled endorsed-author-other-p-of-accept-next
    (implies (and (accept-possiblep val cert systate)
                  (endorsed-author-other-p systate))
             (endorsed-author-other-p (accept-next val cert systate)))
    :expand (endorsed-author-other-p (accept-next val cert systate))
    :enable (endorsed-author-other-p-necc
             validator-state->endorsed-of-accept-next))

  (defruled endorsed-author-other-p-of-advance-next
    (implies (and (advance-possiblep val systate)
                  (endorsed-author-other-p systate))
             (endorsed-author-other-p (advance-next val systate)))
    :expand (endorsed-author-other-p (advance-next val systate))
    :enable endorsed-author-other-p-necc)

  (defruled endorsed-author-other-p-of-commit-next
    (implies (and (commit-possiblep val systate)
                  (endorsed-author-other-p systate))
             (endorsed-author-other-p (commit-next val systate)))
    :expand (endorsed-author-other-p (commit-next val systate))
    :enable endorsed-author-other-p-necc)

  (defruled endorsed-author-other-p-of-event-next
    (implies (and (event-possiblep event systate)
                  (proposal-to-other-p systate)
                  (endorsed-author-other-p systate))
             (endorsed-author-other-p (event-next event systate)))
    :enable (event-possiblep
             event-next)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled endorsed-author-other-p-of-events-next
  :short "Preservation of the invariant by multiple transitions."
  (implies (and (events-possiblep events systate)
                (proposal-to-other-p systate)
                (endorsed-author-other-p systate))
           (endorsed-author-other-p (events-next events systate)))
  :induct t
  :enable (events-possiblep
           events-next))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled endorsed-author-other-p-when-reachable
  :short "The invariant holds in every reachable state."
  (implies (system-state-reachablep systate)
           (endorsed-author-other-p systate))
  :enable (system-state-reachablep
           endorsed-author-other-p-when-init
           proposal-to-other-p-when-init)
  :prep-lemmas
  ((defrule lemma
     (implies (and (system-state-reachable-from-p systate from)
                   (proposal-to-other-p from)
                   (endorsed-author-other-p from))
              (endorsed-author-other-p systate))
     :use (:instance
           endorsed-author-other-p-of-events-next
           (events (system-state-reachable-from-p-witness systate from))
           (systate from))
     :enable system-state-reachable-from-p)))
