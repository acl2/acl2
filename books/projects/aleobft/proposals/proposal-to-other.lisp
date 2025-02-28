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

(defxdoc+ proposal-to-other
  :parents (correctness)
  :short "Invariant that every proposal message from a correct validator
          is addressed to a different validator than the proposal author."
  :long
  (xdoc::topstring
   (xdoc::p
    "Initially there is no (proposal or other kind of) message in the network.
     Proposal messages are only created when proposals are created.
     When a correct validator creates a proposal,
     it does not send the proposal messages to itself.
     Faulty validators may send proposal messages to themselves,
     but this invariant only concerns proposals from correct validators."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk proposal-to-other-p ((systate system-statep))
  :returns (yes/no booleanp)
  :short "Definition of the invariant."
  (forall (prop dest)
          (implies (and (proposalp prop)
                        (addressp dest)
                        (set::in (message-proposal prop dest)
                                 (get-network-state systate))
                        (set::in (proposal->author prop)
                                 (correct-addresses systate)))
                   (not (equal (proposal->author prop) dest))))
  ///
  (fty::deffixequiv-sk proposal-to-other-p
    :args ((systate system-statep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled proposal-to-other-p-when-init
  :short "Establishment of the invariant in the initial states."
  (implies (system-initp systate)
           (proposal-to-other-p systate))
  :enable (proposal-to-other-p
           system-initp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection proposal-to-other-p-of-next
  :short "Preservation of the invariant by single transitions."
  :long
  (xdoc::topstring
   (xdoc::p
    "The reason why use the @(':expand') hint in some of the proofs,
     instead of just enabling @(tsee proposal-to-other-p),
     is that, if we do the latter,
     the @('proposal-to-other-p-necc') rule does not fire,
     because it cannot instantiate the free variable @('systate').
     With the @(':expand') hint,
     only the call of @(tsee proposal-to-other-p)
     in the conclusion of the theorems is expanded,
     leaving the call in the hypothesis unexpanded,
     so it can be used to provide an instantiation for
     the free variable @('systate') in @('proposal-to-other-p-necc').
     This is only the case for some of the theorems;
     others need a @(':use') hint for @('proposal-to-other-p-necc'),
     and so in that case we just enable @(tsee proposal-to-other-p)."))

  (defruled proposal-to-other-p-of-propose-next
    (implies (and (propose-possiblep prop dests systate)
                  (proposal-to-other-p systate))
             (proposal-to-other-p (propose-next prop dests systate)))
    :use (:instance proposal-to-other-p-necc
                    (prop (mv-nth 0 (proposal-to-other-p-witness
                                     (propose-next prop dests systate))))
                    (dest (mv-nth 1 (proposal-to-other-p-witness
                                     (propose-next prop dests systate)))))
    :enable (proposal-to-other-p
             get-network-state-of-propose-next
             in-of-make-proposal-messages
             propose-possiblep))

  (defruled proposal-to-other-p-of-endorse-next
    (implies (proposal-to-other-p systate)
             (proposal-to-other-p (endorse-next prop endor systate)))
    :use (:instance proposal-to-other-p-necc
                    (prop (mv-nth 0 (proposal-to-other-p-witness
                                     (endorse-next prop endor systate))))
                    (dest (mv-nth 1 (proposal-to-other-p-witness
                                     (endorse-next prop endor systate)))))
    :enable (proposal-to-other-p
             get-network-state-of-endorse-next))

  (defruled proposal-to-other-p-of-augment-next
    (implies (and (augment-possiblep prop endor systate)
                  (proposal-to-other-p systate))
             (proposal-to-other-p (augment-next prop endor systate)))
    :expand (proposal-to-other-p (augment-next prop endor systate))
    :enable (proposal-to-other-p-necc
             get-network-state-of-augment-next))

  (defruled proposal-to-other-p-of-certify-next
    (implies (proposal-to-other-p systate)
             (proposal-to-other-p (certify-next cert dests systate)))
    :use (:instance proposal-to-other-p-necc
                    (prop (mv-nth 0 (proposal-to-other-p-witness
                                     (certify-next cert dests systate))))
                    (dest (mv-nth 1 (proposal-to-other-p-witness
                                     (certify-next cert dests systate)))))
    :enable (proposal-to-other-p
             get-network-state-of-certify-next
             in-of-make-certificate-messages))

  (defruled proposal-to-other-p-of-accept-next
    (implies (and (accept-possiblep val cert systate)
                  (proposal-to-other-p systate))
             (proposal-to-other-p (accept-next val cert systate)))
    :expand (proposal-to-other-p (accept-next val cert systate))
    :enable (proposal-to-other-p-necc
             get-network-state-of-accept-next))

  (defruled proposal-to-other-p-of-advance-next
    (implies (and (advance-possiblep val systate)
                  (proposal-to-other-p systate))
             (proposal-to-other-p (advance-next val systate)))
    :expand (proposal-to-other-p (advance-next val systate))
    :enable proposal-to-other-p-necc)

  (defruled proposal-to-other-p-of-commit-next
    (implies (and (commit-possiblep val systate)
                  (proposal-to-other-p systate))
             (proposal-to-other-p (commit-next val systate)))
    :expand (proposal-to-other-p (commit-next val systate))
    :enable proposal-to-other-p-necc)

  (defruled proposal-to-other-p-of-event-next
    (implies (and (event-possiblep event systate)
                  (proposal-to-other-p systate))
             (proposal-to-other-p (event-next event systate)))
    :enable (event-possiblep
             event-next)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled proposal-to-other-p-of-events-next
  :short "Preservation of the invariant by multiple transitions."
  (implies (and (events-possiblep events systate)
                (proposal-to-other-p systate))
           (proposal-to-other-p (events-next events systate)))
  :induct t
  :enable (events-possiblep
           events-next))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled proposal-to-other-p-when-reachable
  :short "The invariant holds in every reachable state."
  (implies (system-state-reachablep systate)
           (proposal-to-other-p systate))
  :enable (system-state-reachablep
           proposal-to-other-p-when-init)
  :prep-lemmas
  ((defrule lemma
     (implies (and (system-state-reachable-from-p systate from)
                   (proposal-to-other-p from))
              (proposal-to-other-p systate))
     :use (:instance
           proposal-to-other-p-of-events-next
           (events (system-state-reachable-from-p-witness systate from))
           (systate from))
     :enable system-state-reachable-from-p)))
