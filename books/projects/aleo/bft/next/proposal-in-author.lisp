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

(defxdoc+ proposal-in-author
  :parents (correctness)
  :short "Invariant that the proposal in every proposal message
          is in the state of the proposal author if correct."
  :long
  (xdoc::topstring
   (xdoc::p
    "Initially there are no messages.
     When a proposal message is created by a correct validator,
     it is added to its map @('proposed') of pending proposals.
     The proposal is removed from the map only when the validator
     creates a certificate with the proposal,
     but in that case it also adds the certificate to its DAG."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk proposal-in-author-p ((systate system-statep))
  :returns (yes/no booleanp)
  :short "Definition of the invariant."
  (forall (msg)
          (implies (and (set::in msg (get-network-state systate))
                        (message-case msg :proposal))
                   (b* (((proposal prop) (message-proposal->proposal msg)))
                     (implies (set::in prop.author
                                       (correct-addresses systate))
                              (b* (((validator-state vstate)
                                    (get-validator-state prop.author systate)))
                                (or (set::in prop (omap::keys vstate.proposed))
                                    (set::in prop (cert-set->prop-set
                                                   vstate.dag))))))))
  ///
  (fty::deffixequiv-sk proposal-in-author-p
    :args ((systate system-statep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled proposal-in-author-p-when-init
  :short "Establishment of the invariant in the initial states."
  (implies (system-initp systate)
           (proposal-in-author-p systate))
  :enable (proposal-in-author-p
           system-initp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection proposal-in-author-p-of-next
  :short "Preservation of the invariant by single transitions."

  (defruled proposal-in-author-p-of-propose-next
    (implies (proposal-in-author-p systate)
             (proposal-in-author-p (propose-next prop dests systate)))
    :use (:instance proposal-in-author-p-necc
                    (msg (proposal-in-author-p-witness
                          (propose-next prop dests systate))))
    :enable (proposal-in-author-p
             validator-state->proposed-of-propose-next
             get-network-state-of-propose-next
             in-of-make-proposal-messages))

  (defruled proposal-in-author-p-of-endorse-next
    (implies (proposal-in-author-p systate)
             (proposal-in-author-p (endorse-next prop endor systate)))
    :use (:instance proposal-in-author-p-necc
                    (msg (proposal-in-author-p-witness
                          (endorse-next prop endor systate))))
    :enable (proposal-in-author-p
             get-network-state-of-endorse-next))

  (defruled proposal-in-author-p-of-augment-next
    (implies (and (augment-possiblep prop endor systate)
                  (proposal-in-author-p systate))
             (proposal-in-author-p (augment-next prop endor systate)))
    :use (:instance proposal-in-author-p-necc
                    (msg (proposal-in-author-p-witness
                          (augment-next prop endor systate))))
    :enable (proposal-in-author-p
             validator-state->proposed-of-augment-next
             get-network-state-of-augment-next))

  (defruled proposal-in-author-p-of-certify-next
    (implies (proposal-in-author-p systate)
             (proposal-in-author-p (certify-next cert dests systate)))
    :use (:instance proposal-in-author-p-necc
                    (msg (proposal-in-author-p-witness
                          (certify-next cert dests systate))))
    :enable (proposal-in-author-p
             validator-state->dag-of-certify-next
             validator-state->proposed-of-certify-next
             get-network-state-of-certify-next
             in-of-make-certificate-messages
             cert-set->prop-set-of-insert
             omap::keys-of-delete))

  (defruled proposal-in-author-p-of-accept-next
    (implies (and (accept-possiblep val cert systate)
                  (proposal-in-author-p systate))
             (proposal-in-author-p (accept-next val cert systate)))
    :use (:instance proposal-in-author-p-necc
                    (msg (proposal-in-author-p-witness
                          (accept-next val cert systate))))
    :enable (proposal-in-author-p
             validator-state->dag-of-accept-next
             get-network-state-of-accept-next
             cert-set->prop-set-of-insert))

  (defruled proposal-in-author-p-of-advance-next
    (implies (and (advance-possiblep val systate)
                  (proposal-in-author-p systate))
             (proposal-in-author-p (advance-next val systate)))
    :use (:instance proposal-in-author-p-necc
                    (msg (proposal-in-author-p-witness
                          (advance-next val systate))))
    :enable proposal-in-author-p)

  (defruled proposal-in-author-p-of-commit-next
    (implies (and (commit-possiblep val systate)
                  (proposal-in-author-p systate))
             (proposal-in-author-p (commit-next val systate)))
    :use (:instance proposal-in-author-p-necc
                    (msg (proposal-in-author-p-witness
                          (commit-next val systate))))
    :enable proposal-in-author-p)

  (defruled proposal-in-author-p-of-event-next
    (implies (and (event-possiblep event systate)
                  (proposal-in-author-p systate))
             (proposal-in-author-p (event-next event systate)))
    :enable (event-possiblep event-next)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled proposal-in-author-p-of-events-next
  :short "Preservation of the invariant by multiple transitions."
  (implies (and (events-possiblep events systate)
                (proposal-in-author-p systate))
           (proposal-in-author-p (events-next events systate)))
  :induct t
  :enable (events-possiblep
           events-next))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled proposal-in-author-p-when-reachable
  :short "The invariant holds in every reachable state."
  (implies (system-state-reachablep systate)
           (proposal-in-author-p systate))
  :enable (system-state-reachablep
           proposal-in-author-p-when-init)
  :prep-lemmas
  ((defrule lemma
     (implies (and (system-state-reachable-from-p systate from)
                   (proposal-in-author-p from))
              (proposal-in-author-p systate))
     :use (:instance
           proposal-in-author-p-of-events-next
           (events (system-state-reachable-from-p-witness systate from))
           (systate from))
     :enable system-state-reachable-from-p)))
