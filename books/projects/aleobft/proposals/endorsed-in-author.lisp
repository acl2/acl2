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

(include-book "proposal-in-author")

(local (include-book "../library-extensions/omap-theorems"))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ endorsed-in-author
  :parents (correctness)
  :short "Invariant that each proposal endorsed by each correct validator
          is in the state of the proposal author if correct."
  :long
  (xdoc::topstring
   (xdoc::p
    "Each validator state has an @('endorsed') component
     that keeps track of the proposals endorsed by the validator.
     Proposals are added to this state component only by @('endorse') events,
     and the proposals are taken from the received proposal messages,
     which, as proved in @(see proposal-in-author),
     are in the state of the proposer if the latter is a correct validator;
     precisely, they are in the pending proposals or in the DAG."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk endorsed-in-author-p ((systate system-statep))
  :returns (yes/no booleanp)
  :short "Definition of the invariant."
  (forall (endor prop)
          (implies (and (set::in endor (correct-addresses systate))
                        (set::in prop (validator-state->endorsed
                                       (get-validator-state endor systate)))
                        (set::in (proposal->author prop)
                                 (correct-addresses systate)))
                   (b* (((validator-state vstate)
                         (get-validator-state (proposal->author prop) systate)))
                     (or (set::in prop (omap::keys vstate.proposed))
                         (set::in prop (cert-set->prop-set vstate.dag))))))
  ///
  (fty::deffixequiv-sk endorsed-in-author-p
    :args ((systate system-statep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled endorsed-in-author-p-when-init
  :short "Establishment of the invariant in the initial states."
  (implies (system-initp systate)
           (endorsed-in-author-p systate))
  :enable (endorsed-in-author-p
           system-initp
           system-validators-initp-necc
           validator-init))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection endorsed-in-author-p-of-next
  :short "Preservation of the invariant by single transitions."

  (defruled endorsed-in-author-p-of-propose-next
    (implies (endorsed-in-author-p systate)
             (endorsed-in-author-p (propose-next prop dests systate)))
    :use (:instance endorsed-in-author-p-necc
                    (endor (mv-nth 0 (endorsed-in-author-p-witness
                                      (propose-next prop dests systate))))
                    (prop (mv-nth 1 (endorsed-in-author-p-witness
                                     (propose-next prop dests systate)))))
    :enable (endorsed-in-author-p
             validator-state->proposed-of-propose-next))

  (defruled endorsed-in-author-p-of-endorse-next
    (implies (and (endorse-possiblep prop endor systate)
                  (proposal-in-author-p systate)
                  (endorsed-in-author-p systate))
             (endorsed-in-author-p (endorse-next prop endor systate)))
    :use ((:instance endorsed-in-author-p-necc
                     (endor (mv-nth 0 (endorsed-in-author-p-witness
                                       (endorse-next prop endor systate))))
                     (prop (mv-nth 1 (endorsed-in-author-p-witness
                                      (endorse-next prop endor systate)))))
          (:instance proposal-in-author-p-necc
                     (msg (message-proposal prop endor))))
    :enable (endorsed-in-author-p
             validator-state->endorsed-of-endorse-next
             endorse-possiblep))

  (defruled endorsed-in-author-p-of-augment-next
    (implies (and (augment-possiblep prop endor systate)
                  (endorsed-in-author-p systate))
             (endorsed-in-author-p (augment-next prop endor systate)))
    :use (:instance endorsed-in-author-p-necc
                    (endor (mv-nth 0 (endorsed-in-author-p-witness
                                      (augment-next prop endor systate))))
                    (prop (mv-nth 1 (endorsed-in-author-p-witness
                                     (augment-next prop endor systate)))))
    :enable (endorsed-in-author-p
             validator-state->proposed-of-augment-next))

  (defruled endorsed-in-author-p-of-certify-next
    (implies (endorsed-in-author-p systate)
             (endorsed-in-author-p (certify-next cert dests systate)))
    :use (:instance endorsed-in-author-p-necc
                    (endor (mv-nth 0 (endorsed-in-author-p-witness
                                      (certify-next cert dests systate))))
                    (prop (mv-nth 1 (endorsed-in-author-p-witness
                                     (certify-next cert dests systate)))))
    :enable (endorsed-in-author-p
             validator-state->dag-of-certify-next
             validator-state->proposed-of-certify-next
             cert-set->prop-set-of-insert
             omap::keys-of-delete))

  (defruled endorsed-in-author-p-of-accept-next
    (implies (and (accept-possiblep val cert systate)
                  (endorsed-in-author-p systate))
             (endorsed-in-author-p (accept-next val cert systate)))
    :use (:instance endorsed-in-author-p-necc
                    (endor (mv-nth 0 (endorsed-in-author-p-witness
                                      (accept-next val cert systate))))
                    (prop (mv-nth 1 (endorsed-in-author-p-witness
                                     (accept-next val cert systate)))))
    :enable (endorsed-in-author-p
             validator-state->dag-of-accept-next
             validator-state->endorsed-of-accept-next
             cert-set->prop-set-of-insert))

  (defruled endorsed-in-author-p-of-advance-next
    (implies (and (advance-possiblep val systate)
                  (endorsed-in-author-p systate))
             (endorsed-in-author-p (advance-next val systate)))
    :use (:instance endorsed-in-author-p-necc
                    (endor (mv-nth 0 (endorsed-in-author-p-witness
                                      (advance-next val systate))))
                    (prop (mv-nth 1 (endorsed-in-author-p-witness
                                     (advance-next val systate)))))
    :enable endorsed-in-author-p)

  (defruled endorsed-in-author-p-of-commit-next
    (implies (and (commit-possiblep val systate)
                  (endorsed-in-author-p systate))
             (endorsed-in-author-p (commit-next val systate)))
    :use (:instance endorsed-in-author-p-necc
                    (endor (mv-nth 0 (endorsed-in-author-p-witness
                                      (commit-next val systate))))
                    (prop (mv-nth 1 (endorsed-in-author-p-witness
                                     (commit-next val systate)))))
    :enable endorsed-in-author-p)

  (defruled endorsed-in-author-p-of-event-next
    (implies (and (event-possiblep event systate)
                  (proposal-in-author-p systate)
                  (endorsed-in-author-p systate))
             (endorsed-in-author-p (event-next event systate)))
    :enable (event-possiblep
             event-next)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled endorsed-in-author-p-of-events-next
  :short "Preservation of the invariant by multiple transitions."
  (implies (and (events-possiblep events systate)
                (proposal-in-author-p systate)
                (endorsed-in-author-p systate))
           (endorsed-in-author-p (events-next events systate)))
  :induct t
  :enable (events-possiblep
           events-next))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled endorsed-in-author-p-when-reachable
  :short "The invariant holds in every reachable state."
  (implies (system-state-reachablep systate)
           (endorsed-in-author-p systate))
  :enable (system-state-reachablep
           endorsed-in-author-p-when-init
           proposal-in-author-p-when-init)
  :prep-lemmas
  ((defrule lemma
     (implies (and (system-state-reachable-from-p systate from)
                   (proposal-in-author-p from)
                   (endorsed-in-author-p from))
              (endorsed-in-author-p systate))
     :use (:instance
           endorsed-in-author-p-of-events-next
           (events (system-state-reachable-from-p-witness systate from))
           (systate from))
     :enable system-state-reachable-from-p)))
