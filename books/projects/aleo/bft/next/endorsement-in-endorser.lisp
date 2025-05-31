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

(defxdoc+ endorsement-in-endorser
  :parents (correctness)
  :short "Invariant that the proposal in every endorsement message
          is in the state of the endorser if correct."
  :long
  (xdoc::topstring
   (xdoc::p
    "Initially there are no messages.
     When an endorsement message is created by a correct validator,
     the proposal is stored into the @('endorsed') component
     of the state of the validator.
     The proposal is removed from there only when the validator
     accepts a certificate with that proposal into the DAG;
     thus, it remains in the state of the validator."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk endorsement-in-endorser-p ((systate system-statep))
  :returns (yes/no booleanp)
  :short "Definition of the invariant."
  (forall (msg)
          (implies (and (set::in msg (get-network-state systate))
                        (message-case msg :endorsement))
                   (b* (((proposal prop) (message-endorsement->proposal msg))
                        (endor (message-endorsement->endorser msg)))
                     (implies (set::in endor (correct-addresses systate))
                              (b* (((validator-state vstate)
                                    (get-validator-state endor systate)))
                                (or (set::in prop vstate.endorsed)
                                    (set::in prop (cert-set->prop-set
                                                   vstate.dag))))))))
  ///
  (fty::deffixequiv-sk endorsement-in-endorser-p
    :args ((systate system-statep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled endorsement-in-endorser-p-when-init
  :short "Establishment of the invariant in the initial states."
  (implies (system-initp systate)
           (endorsement-in-endorser-p systate))
  :enable (endorsement-in-endorser-p
           system-initp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection endorsement-in-endorser-p-of-next
  :short "Preservation of the invariant by single transitions."

  (defruled endorsement-in-endorser-p-of-propose-next
    (implies (endorsement-in-endorser-p systate)
             (endorsement-in-endorser-p (propose-next prop dests systate)))
    :use (:instance endorsement-in-endorser-p-necc
                    (msg (endorsement-in-endorser-p-witness
                          (propose-next prop dests systate))))
    :enable (endorsement-in-endorser-p
             get-network-state-of-propose-next
             in-of-make-proposal-messages))

  (defruled endorsement-in-endorser-p-of-endorse-next
    (implies (endorsement-in-endorser-p systate)
             (endorsement-in-endorser-p (endorse-next prop endor systate)))
    :use (:instance endorsement-in-endorser-p-necc
                    (msg (endorsement-in-endorser-p-witness
                          (endorse-next prop endor systate))))
    :enable (endorsement-in-endorser-p
             validator-state->endorsed-of-endorse-next
             get-network-state-of-endorse-next))

  (defruled endorsement-in-endorser-p-of-augment-next
    (implies (and (augment-possiblep prop endor systate)
                  (endorsement-in-endorser-p systate))
             (endorsement-in-endorser-p (augment-next prop endor systate)))
    :use (:instance endorsement-in-endorser-p-necc
                    (msg (endorsement-in-endorser-p-witness
                          (augment-next prop endor systate))))
    :enable (endorsement-in-endorser-p
             get-network-state-of-augment-next))

  (defruled endorsement-in-endorser-p-of-certify-next
    (implies (endorsement-in-endorser-p systate)
             (endorsement-in-endorser-p (certify-next cert dests systate)))
    :use (:instance endorsement-in-endorser-p-necc
                    (msg (endorsement-in-endorser-p-witness
                          (certify-next cert dests systate))))
    :enable (endorsement-in-endorser-p
             validator-state->dag-of-certify-next
             get-network-state-of-certify-next
             in-of-make-certificate-messages
             cert-set->prop-set-of-insert))

  (defruled endorsement-in-endorser-p-of-accept-next
    (implies (and (accept-possiblep val cert systate)
                  (endorsement-in-endorser-p systate))
             (endorsement-in-endorser-p (accept-next val cert systate)))
    :use (:instance endorsement-in-endorser-p-necc
                    (msg (endorsement-in-endorser-p-witness
                          (accept-next val cert systate))))
    :enable (endorsement-in-endorser-p
             validator-state->endorsed-of-accept-next
             validator-state->dag-of-accept-next
             get-network-state-of-accept-next
             cert-set->prop-set-of-insert))

  (defruled endorsement-in-endorser-p-of-advance-next
    (implies (and (advance-possiblep val systate)
                  (endorsement-in-endorser-p systate))
             (endorsement-in-endorser-p (advance-next val systate)))
    :use (:instance endorsement-in-endorser-p-necc
                    (msg (endorsement-in-endorser-p-witness
                          (advance-next val systate))))
    :enable endorsement-in-endorser-p)

  (defruled endorsement-in-endorser-p-of-commit-next
    (implies (and (commit-possiblep val systate)
                  (endorsement-in-endorser-p systate))
             (endorsement-in-endorser-p (commit-next val systate)))
    :use (:instance endorsement-in-endorser-p-necc
                    (msg (endorsement-in-endorser-p-witness
                          (commit-next val systate))))
    :enable endorsement-in-endorser-p)

  (defruled endorsement-in-endorser-p-of-event-next
    (implies (and (event-possiblep event systate)
                  (endorsement-in-endorser-p systate))
             (endorsement-in-endorser-p (event-next event systate)))
    :enable (event-possiblep
             event-next)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled endorsement-in-endorser-p-of-events-next
  :short "Preservation of the invariant by multiple transitions."
  (implies (and (events-possiblep events systate)
                (endorsement-in-endorser-p systate))
           (endorsement-in-endorser-p (events-next events systate)))
  :induct t
  :enable (events-possiblep
           events-next))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled endorsement-in-endorser-p-when-reachable
  :short "The invariant holds in every reachable state."
  (implies (system-state-reachablep systate)
           (endorsement-in-endorser-p systate))
  :enable (system-state-reachablep
           endorsement-in-endorser-p-when-init)
  :prep-lemmas
  ((defrule lemma
     (implies (and (system-state-reachable-from-p systate from)
                   (endorsement-in-endorser-p from))
              (endorsement-in-endorser-p systate))
     :use (:instance
           endorsement-in-endorser-p-of-events-next
           (events (system-state-reachable-from-p-witness systate from))
           (systate from))
     :enable system-state-reachable-from-p)))
