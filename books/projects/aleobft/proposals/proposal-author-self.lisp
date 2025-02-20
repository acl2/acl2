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

(local (include-book "../library-extensions/omap-theorems"))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ proposal-author-self
  :parents (correctness)
  :short "Invariant that the author of a pending proposal
          in each validator state
          is always the validator itself."
  :long
  (xdoc::topstring
   (xdoc::p
    "Each validator keeps track of its own pending proposals,
     in the @('proposed') map of @(tse validator-state).
     The map is initially empty,
     and is extended only by @('propose') events,
     by the validator itself, with its own authored proposal."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk proposal-author-self-p ((systate system-statep))
  :returns (yes/no booleanp)
  :short "Definition of the invariant."
  (forall (val prop)
          (implies (set::in val (correct-addresses systate))
                   (b* (((validator-state vstate)
                         (get-validator-state val systate)))
                     (implies (set::in prop (omap::keys vstate.proposed))
                              (equal (proposal->author prop)
                                     val)))))
  :guard-hints
  (("Goal"
    :in-theory (enable proposal-setp-of-keys-when-proposal-address-set-mapp)))
  ///
  (fty::deffixequiv-sk proposal-author-self-p
    :args ((systate system-statep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled proposal-author-self-p-when-init
  :short "Establishment of the invariant in the initial states."
  (implies (system-initp systate)
           (proposal-author-self-p systate))
  :enable (proposal-author-self-p
           system-initp
           system-validators-initp-necc
           validator-init))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection proposal-author-self-p-of-next
  :short "Preservation of the invariant by single transitions."
  :long
  (xdoc::topstring
   (xdoc::p
    "The reason why use the @(':expand') hint,
     instead of just enabling @(tsee proposal-author-self-p),
     is that, if we do the latter,
     the @('proposal-author-self-p-necc') rule does not fire,
     because it cannot instantiate the free variable @('systate').
     With the @(':expand') hint,
     only the call of @(tsee proposal-author-self-p)
     in the conclusion of the theorems is expanded,
     leaving the call in the hypothesis unexpanded,
     so it can be used to provide an instantiation for
     the free variable @('systate') in @('proposal-author-self-p-necc')."))

  (defruled proposal-author-self-p-of-propose-next
    (implies (proposal-author-self-p systate)
             (proposal-author-self-p (propose-next prop dests systate)))
    :expand (proposal-author-self-p (propose-next prop dests systate))
    :enable (proposal-author-self-p-necc
             validator-state->proposed-of-propose-next))

  (defruled proposal-author-self-p-of-endorse-next
    (implies (proposal-author-self-p systate)
             (proposal-author-self-p (endorse-next prop endor systate)))
    :expand (proposal-author-self-p (endorse-next prop endor systate))
    :enable proposal-author-self-p-necc)

  (defruled proposal-author-self-p-of-augment-next
    (implies (and (augment-possiblep prop endor systate)
                  (proposal-author-self-p systate))
             (proposal-author-self-p (augment-next prop endor systate)))
    :expand (proposal-author-self-p (augment-next prop endor systate))
    :enable (proposal-author-self-p-necc
             validator-state->proposed-of-augment-next))

  (defruled proposal-author-self-p-of-certify-next
    (implies (proposal-author-self-p systate)
             (proposal-author-self-p (certify-next cert dests systate)))
    :expand (proposal-author-self-p (certify-next cert dests systate))
    :enable (proposal-author-self-p-necc
             validator-state->proposed-of-certify-next
             omap::keys-of-delete))

  (defruled proposal-author-self-p-of-accept-next
    (implies (and (accept-possiblep val cert systate)
                  (proposal-author-self-p systate))
             (proposal-author-self-p (accept-next val cert systate)))
    :expand (proposal-author-self-p (accept-next val cert systate))
    :enable proposal-author-self-p-necc)

  (defruled proposal-author-self-p-of-advance-next
    (implies (and (advance-possiblep val systate)
                  (proposal-author-self-p systate))
             (proposal-author-self-p (advance-next val systate)))
    :expand (proposal-author-self-p (advance-next val systate))
    :enable (proposal-author-self-p-necc))

  (defruled proposal-author-self-p-of-commit-next
    (implies (and (commit-possiblep val systate)
                  (proposal-author-self-p systate))
             (proposal-author-self-p (commit-next val systate)))
    :expand (proposal-author-self-p (commit-next val systate))
    :enable proposal-author-self-p-necc)

  (defruled proposal-author-self-p-of-event-next
    (implies (and (event-possiblep event systate)
                  (proposal-author-self-p systate))
             (proposal-author-self-p (event-next event systate)))
    :enable (event-possiblep event-next)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled proposal-author-self-p-of-events-next
  :short "Preservation of the invariant by multiple transitions."
  (implies (and (events-possiblep events systate)
                (proposal-author-self-p systate))
           (proposal-author-self-p (events-next events systate)))
  :induct t
  :enable (events-possiblep
           events-next))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled proposal-author-self-p-when-reachable
  :short "The invariant holds in every reachable state."
  (implies (system-state-reachablep systate)
           (proposal-author-self-p systate))
  :enable (system-state-reachablep
           proposal-author-self-p-when-init)
  :prep-lemmas
  ((defrule lemma
     (implies (and (system-state-reachable-from-p systate from)
                   (proposal-author-self-p from))
              (proposal-author-self-p systate))
     :use (:instance
           proposal-author-self-p-of-events-next
           (events (system-state-reachable-from-p-witness systate from))
           (systate from))
     :enable system-state-reachable-from-p)))
