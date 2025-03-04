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

(include-book "proposal-to-other")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ endorsement-from-other
  :parents (correctness)
  :short "Invariant that every endorsement message to a correct validator
          comes from a different validator than the proposal author."
  :long
  (xdoc::topstring
   (xdoc::p
    "Initially there is no (endorsement or other kind of) message
     in the network.
     Endorsement messages are only created from proposal messages,
     which, as proved in @(see proposal-to-other),
     have different source (proposal author) and destination
     when the proposal author is a correct validator:
     thus, the endorsement message resulting from such a proposal message
     also has different source (endorser) and destination (proposal author).
     On the other hand, endorsement messages to faulty validators,
     i.e. whose proposal author is a faulty validator,
     come from proposal messages that do not satisfy that restriction;
     but this invariant, like @(see proposal-to-other),
     only concerns proposals authored by correct validators."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk endorsement-from-other-p ((systate system-statep))
  :returns (yes/no booleanp)
  :short "Definition of the invariant."
  (forall (prop endor)
          (implies (and (proposalp prop)
                        (addressp endor)
                        (set::in (message-endorsement prop endor)
                                 (get-network-state systate))
                        (set::in (proposal->author prop)
                                 (correct-addresses systate)))
                   (not (equal (proposal->author prop) endor))))
  ///
  (fty::deffixequiv-sk endorsement-from-other-p
    :args ((systate system-statep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled endorsement-from-other-p-when-init
  :short "Establishment of the invariant in the initial states."
  (implies (system-initp systate)
           (endorsement-from-other-p systate))
  :enable (endorsement-from-other-p
           system-initp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection endorsement-from-other-p-of-next
  :short "Preservation of the invariant by single transitions."
  :long
  (xdoc::topstring
   (xdoc::p
    "The reason why use the @(':expand') hint in some of the proofs,
     instead of just enabling @(tsee endorsement-from-other-p),
     is that, if we do the latter,
     the @('endorsement-from-other-p-necc') rule does not fire,
     because it cannot instantiate the free variable @('systate').
     With the @(':expand') hint,
     only the call of @(tsee endorsement-from-other-p)
     in the conclusion of the theorems is expanded,
     leaving the call in the hypothesis unexpanded,
     so it can be used to provide an instantiation for
     the free variable @('systate') in @('endorsement-from-other-p-necc').
     This is only the case for some of the theorems;
     others need a @(':use') hint for @('endorsement-from-other-p-necc'),
     and so in that case we just enable @(tsee endorsement-from-other-p)."))

  (defruled endorsement-from-other-p-of-propose-next
    (implies (endorsement-from-other-p systate)
             (endorsement-from-other-p (propose-next prop dests systate)))
    :use (:instance endorsement-from-other-p-necc
                    (prop (mv-nth 0 (endorsement-from-other-p-witness
                                     (propose-next prop dests systate))))
                    (endor (mv-nth 1 (endorsement-from-other-p-witness
                                      (propose-next prop dests systate)))))
    :enable (endorsement-from-other-p
             get-network-state-of-propose-next
             in-of-make-proposal-messages))

  (defruled endorsement-from-other-p-of-endorse-next
    (implies (and (endorse-possiblep prop endor systate)
                  (proposal-to-other-p systate)
                  (endorsement-from-other-p systate))
             (endorsement-from-other-p (endorse-next prop endor systate)))
    :use ((:instance endorsement-from-other-p-necc
                     (prop (mv-nth 0 (endorsement-from-other-p-witness
                                      (endorse-next prop endor systate))))
                     (endor (mv-nth 1 (endorsement-from-other-p-witness
                                       (endorse-next prop endor systate)))))
          (:instance proposal-to-other-p-necc
                     (prop (mv-nth 0 (endorsement-from-other-p-witness
                                      (endorse-next prop endor systate))))
                     (dest (mv-nth 1 (endorsement-from-other-p-witness
                                      (endorse-next prop endor systate))))))
    :enable (endorsement-from-other-p
             get-network-state-of-endorse-next
             endorse-possiblep))

  (defruled endorsement-from-other-p-of-augment-next
    (implies (and (augment-possiblep prop endor systate)
                  (endorsement-from-other-p systate))
             (endorsement-from-other-p (augment-next prop endor systate)))
    :expand (endorsement-from-other-p (augment-next prop endor systate))
    :enable (endorsement-from-other-p-necc
             get-network-state-of-augment-next))

  (defruled endorsement-from-other-p-of-certify-next
    (implies (endorsement-from-other-p systate)
             (endorsement-from-other-p (certify-next cert dests systate)))
    :use (:instance endorsement-from-other-p-necc
                    (prop (mv-nth 0 (endorsement-from-other-p-witness
                                     (certify-next cert dests systate))))
                    (endor (mv-nth 1 (endorsement-from-other-p-witness
                                      (certify-next cert dests systate)))))
    :enable (endorsement-from-other-p
             get-network-state-of-certify-next
             in-of-make-certificate-messages))

  (defruled endorsement-from-other-p-of-accept-next
    (implies (and (accept-possiblep val cert systate)
                  (endorsement-from-other-p systate))
             (endorsement-from-other-p (accept-next val cert systate)))
    :expand (endorsement-from-other-p (accept-next val cert systate))
    :enable (endorsement-from-other-p-necc
             get-network-state-of-accept-next))

  (defruled endorsement-from-other-p-of-advance-next
    (implies (and (advance-possiblep val systate)
                  (endorsement-from-other-p systate))
             (endorsement-from-other-p (advance-next val systate)))
    :expand (endorsement-from-other-p (advance-next val systate))
    :enable endorsement-from-other-p-necc)

  (defruled endorsement-from-other-p-of-commit-next
    (implies (and (commit-possiblep val systate)
                  (endorsement-from-other-p systate))
             (endorsement-from-other-p (commit-next val systate)))
    :expand (endorsement-from-other-p (commit-next val systate))
    :enable endorsement-from-other-p-necc)

  (defruled endorsement-from-other-p-of-event-next
    (implies (and (event-possiblep event systate)
                  (proposal-to-other-p systate)
                  (endorsement-from-other-p systate))
             (endorsement-from-other-p (event-next event systate)))
    :enable (event-possiblep
             event-next)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled endorsement-from-other-p-of-events-next
  :short "Preservation of the invariant by multiple transitions."
  (implies (and (events-possiblep events systate)
                (proposal-to-other-p systate)
                (endorsement-from-other-p systate))
           (endorsement-from-other-p (events-next events systate)))
  :induct t
  :enable (events-possiblep
           events-next))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled endorsement-from-other-p-when-reachable
  :short "The invariant holds in every reachable state."
  (implies (system-state-reachablep systate)
           (endorsement-from-other-p systate))
  :enable (system-state-reachablep
           endorsement-from-other-p-when-init
           proposal-to-other-p-when-init)
  :prep-lemmas
  ((defrule lemma
     (implies (and (system-state-reachable-from-p systate from)
                   (proposal-to-other-p from)
                   (endorsement-from-other-p from))
              (endorsement-from-other-p systate))
     :use (:instance
           endorsement-from-other-p-of-events-next
           (events (system-state-reachable-from-p-witness systate from))
           (systate from))
     :enable system-state-reachable-from-p)))
