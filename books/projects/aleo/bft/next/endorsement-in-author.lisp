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

(include-book "proposal-in-author")

(local (include-book "../library-extensions/omap-theorems"))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ endorsement-in-author
  :parents (correctness)
  :short "Invariant that the proposal in every endorsement message
          is in the state of the proposal author if correct."
  :long
  (xdoc::topstring
   (xdoc::p
    "Initially there are no messages.
     When an endorsement message is created
     for a proposal authored by a correct validator,
     the proposal comes from a proposal message,
     which, by the invariant @(see proposal-in-author),
     is in the author's pending proposals or DAG."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk endorsement-in-author-p ((systate system-statep))
  :returns (yes/no booleanp)
  :short "Definition of the invariant."
  (forall (msg)
          (implies (and (set::in msg (get-network-state systate))
                        (message-case msg :endorsement))
                   (b* (((proposal prop) (message-endorsement->proposal msg)))
                     (implies (set::in prop.author
                                       (correct-addresses systate))
                              (b* (((validator-state vstate)
                                    (get-validator-state prop.author systate)))
                                (or (set::in prop (omap::keys vstate.proposed))
                                    (set::in prop (cert-set->prop-set
                                                   vstate.dag))))))))
  ///
  (fty::deffixequiv-sk endorsement-in-author-p
    :args ((systate system-statep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled endorsement-in-author-p-when-init
  :short "Establishment of the invariant in the initial states."
  (implies (system-initp systate)
           (endorsement-in-author-p systate))
  :enable (endorsement-in-author-p
           system-initp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection endorsement-in-author-p-of-next
  :short "Preservation of the invariant by single transitions."

  (defruled endorsement-in-author-p-of-propose-next
    (implies (endorsement-in-author-p systate)
             (endorsement-in-author-p (propose-next prop dests systate)))
    :use (:instance endorsement-in-author-p-necc
                    (msg (endorsement-in-author-p-witness
                          (propose-next prop dests systate))))
    :enable (endorsement-in-author-p
             validator-state->proposed-of-propose-next
             get-network-state-of-propose-next
             in-of-make-proposal-messages))

  (defruled endorsement-in-author-p-of-endorse-next
    (implies (and (endorse-possiblep prop endor systate)
                  (proposal-in-author-p systate)
                  (endorsement-in-author-p systate))
             (endorsement-in-author-p (endorse-next prop endor systate)))
    :use ((:instance endorsement-in-author-p-necc
                     (msg (endorsement-in-author-p-witness
                           (endorse-next prop endor systate))))
          (:instance proposal-in-author-p-necc
                     (msg (message-proposal prop endor))))
    :enable (endorsement-in-author-p
             get-network-state-of-endorse-next
             endorse-possiblep))

  (defruled endorsement-in-author-p-of-augment-next
    (implies (and (augment-possiblep prop endor systate)
                  (endorsement-in-author-p systate))
             (endorsement-in-author-p (augment-next prop endor systate)))
    :use (:instance endorsement-in-author-p-necc
                    (msg (endorsement-in-author-p-witness
                          (augment-next prop endor systate))))
    :enable (endorsement-in-author-p
             validator-state->proposed-of-augment-next
             get-network-state-of-augment-next))

  (defruled endorsement-in-author-p-of-certify-next
    (implies (endorsement-in-author-p systate)
             (endorsement-in-author-p (certify-next cert dests systate)))
    :use (:instance endorsement-in-author-p-necc
                    (msg (endorsement-in-author-p-witness
                          (certify-next cert dests systate))))
    :enable (endorsement-in-author-p
             validator-state->dag-of-certify-next
             validator-state->proposed-of-certify-next
             get-network-state-of-certify-next
             in-of-make-certificate-messages
             cert-set->prop-set-of-insert
             omap::keys-of-delete))

  (defruled endorsement-in-author-p-of-accept-next
    (implies (and (accept-possiblep val cert systate)
                  (endorsement-in-author-p systate))
             (endorsement-in-author-p (accept-next val cert systate)))
    :use (:instance endorsement-in-author-p-necc
                    (msg (endorsement-in-author-p-witness
                          (accept-next val cert systate))))
    :enable (endorsement-in-author-p
             validator-state->dag-of-accept-next
             get-network-state-of-accept-next
             cert-set->prop-set-of-insert))

  (defruled endorsement-in-author-p-of-advance-next
    (implies (and (advance-possiblep val systate)
                  (endorsement-in-author-p systate))
             (endorsement-in-author-p (advance-next val systate)))
    :use (:instance endorsement-in-author-p-necc
                    (msg (endorsement-in-author-p-witness
                          (advance-next val systate))))
    :enable endorsement-in-author-p)

  (defruled endorsement-in-author-p-of-commit-next
    (implies (and (commit-possiblep val systate)
                  (endorsement-in-author-p systate))
             (endorsement-in-author-p (commit-next val systate)))
    :use (:instance endorsement-in-author-p-necc
                    (msg (endorsement-in-author-p-witness
                          (commit-next val systate))))
    :enable endorsement-in-author-p)

  (defruled endorsement-in-author-p-of-event-next
    (implies (and (event-possiblep event systate)
                  (proposal-in-author-p systate)
                  (endorsement-in-author-p systate))
             (endorsement-in-author-p (event-next event systate)))
    :enable (event-possiblep
             event-next)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled endorsement-in-author-p-of-events-next
  :short "Preservation of the invariant by multiple transitions."
  (implies (and (events-possiblep events systate)
                (proposal-in-author-p systate)
                (endorsement-in-author-p systate))
           (endorsement-in-author-p (events-next events systate)))
  :induct t
  :enable (events-possiblep
           events-next))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled endorsement-in-author-p-when-reachable
  :short "The invariant holds in every reachable state."
  (implies (system-state-reachablep systate)
           (endorsement-in-author-p systate))
  :enable (system-state-reachablep
           endorsement-in-author-p-when-init
           proposal-in-author-p-when-init)
  :prep-lemmas
  ((defrule lemma
     (implies (and (system-state-reachable-from-p systate from)
                   (proposal-in-author-p from)
                   (endorsement-in-author-p from))
              (endorsement-in-author-p systate))
     :use (:instance
           endorsement-in-author-p-of-events-next
           (events (system-state-reachable-from-p-witness systate from))
           (systate from))
     :enable system-state-reachable-from-p)))
