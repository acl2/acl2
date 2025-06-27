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

(include-book "endorsement-from-other")

(local (include-book "../library-extensions/omap-theorems"))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ proposed-endorser-other
  :parents (correctness)
  :short "Invariant that each endorser of each pending proposal
          in each validator state
          is never the validator itself."
  :long
  (xdoc::topstring
   (xdoc::p
    "Each validator keeps track of its own pending proposals,
     in the @('proposed') map of @(tsee validator-state);
     the map associates endorsers to proposals,
     obtained from endorsement messages.
     Since, as proved in @(see endorsement-from-other),
     the endorsers are always different from the proposal authors,
     it follows that the endorsers in the map always differ from
     the authors of the associated proposals.
     The map is initially empty.
     This invariant only concerns correct validators,
     which are the ones with the maps."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk proposed-endorser-other-p ((systate system-statep))
  :returns (yes/no booleanp)
  :short "Definition of the invariant."
  (forall (val prop)
          (implies (set::in val (correct-addresses systate))
                   (b* (((validator-state vstate)
                         (get-validator-state val systate)))
                     (implies (set::in prop (omap::keys vstate.proposed))
                              (not (set::in (proposal->author prop)
                                            (omap::lookup prop
                                                          vstate.proposed)))))))
  :guard-hints
  (("Goal"
    :in-theory (enable proposal-setp-of-keys-when-proposal-address-set-mapp
                       omap::assoc-to-in-of-keys)))
  ///
  (fty::deffixequiv-sk proposed-endorser-other-p
    :args ((systate system-statep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled proposed-endorser-other-p-when-init
  :short "Establishment of the invariant in the initial states."
  (implies (system-initp systate)
           (proposed-endorser-other-p systate))
  :enable (proposed-endorser-other-p
           system-initp
           system-validators-initp-necc
           validator-init))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection proposed-endorser-other-p-of-next
  :short "Preservation of the invariant by single transitions."

  (defruled proposed-endorser-other-p-of-propose-next
    (implies (proposed-endorser-other-p systate)
             (proposed-endorser-other-p (propose-next prop dests systate)))
    :enable (proposed-endorser-other-p
             proposed-endorser-other-p-necc
             validator-state->proposed-of-propose-next
             omap::lookup-of-update))

  (defruled proposed-endorser-other-p-of-endorse-next
    (implies (proposed-endorser-other-p systate)
             (proposed-endorser-other-p (endorse-next prop endor systate)))
    :enable (proposed-endorser-other-p
             proposed-endorser-other-p-necc))

  (defruled proposed-endorser-other-p-of-augment-next
    (implies (and (augment-possiblep prop endor systate)
                  (endorsement-from-other-p systate)
                  (proposed-endorser-other-p systate))
             (proposed-endorser-other-p (augment-next prop endor systate)))
    :use ((:instance proposed-endorser-other-p-necc
                     (val (mv-nth 0 (proposed-endorser-other-p-witness
                                     (augment-next prop endor systate))))
                     (prop (mv-nth 1 (proposed-endorser-other-p-witness
                                      (augment-next prop endor systate)))))
          (:instance endorsement-from-other-p-necc
                     (prop (proposal-fix prop))
                     (endor (address-fix endor))))
    :enable (proposed-endorser-other-p
             validator-state->proposed-of-augment-next
             augment-possiblep
             omap::assoc-to-in-of-keys
             omap::lookup-of-update))

  (defruled proposed-endorser-other-p-of-certify-next
    (implies (proposed-endorser-other-p systate)
             (proposed-endorser-other-p (certify-next cert dests systate)))
    :enable (proposed-endorser-other-p
             proposed-endorser-other-p-necc
             validator-state->proposed-of-certify-next
             omap::keys-of-delete))

  (defruled proposed-endorser-other-p-of-accept-next
    (implies (and (accept-possiblep val cert systate)
                  (proposed-endorser-other-p systate))
             (proposed-endorser-other-p (accept-next val cert systate)))
    :enable (proposed-endorser-other-p
             proposed-endorser-other-p-necc))

  (defruled proposed-endorser-other-p-of-advance-next
    (implies (and (advance-possiblep val systate)
                  (proposed-endorser-other-p systate))
             (proposed-endorser-other-p (advance-next val systate)))
    :enable (proposed-endorser-other-p
             proposed-endorser-other-p-necc))

  (defruled proposed-endorser-other-p-of-commit-next
    (implies (and (commit-possiblep val systate)
                  (proposed-endorser-other-p systate))
             (proposed-endorser-other-p (commit-next val systate)))
    :enable (proposed-endorser-other-p
             proposed-endorser-other-p-necc))

  (defruled proposed-endorser-other-p-of-event-next
    (implies (and (event-possiblep event systate)
                  (endorsement-from-other-p systate)
                  (proposed-endorser-other-p systate))
             (proposed-endorser-other-p (event-next event systate)))
    :enable (event-possiblep
             event-next)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled proposed-endorser-other-p-of-events-next
  :short "Preservation of the invariant by multiple transitions."
  :long
  (xdoc::topstring
   (xdoc::p
    "Note that, besides @(tsee endorsement-from-other-p),
     we also need @(tsee proposal-to-other-p) as hypothesis,
     which @(tsee endorsement-from-other-p) depends on.
     We do not need to explicitly enable rules,
     because ACL2's tau apparently takes care of that."))
  (implies (and (events-possiblep events systate)
                (proposal-to-other-p systate)
                (endorsement-from-other-p systate)
                (proposed-endorser-other-p systate))
           (proposed-endorser-other-p (events-next events systate)))
  :induct t
  :enable (events-possiblep
           events-next))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled proposed-endorser-other-p-when-reachable
  :short "The invariant holds in every reachable state."
  (implies (system-state-reachablep systate)
           (proposed-endorser-other-p systate))
  :enable (system-state-reachablep
           proposed-endorser-other-p-when-init
           endorsement-from-other-p-when-init
           proposal-to-other-p-when-init)
  :prep-lemmas
  ((defrule lemma
     (implies (and (system-state-reachable-from-p systate from)
                   (proposal-to-other-p from)
                   (endorsement-from-other-p from)
                   (proposed-endorser-other-p from))
              (proposed-endorser-other-p systate))
     :use (:instance
           proposed-endorser-other-p-of-events-next
           (events (system-state-reachable-from-p-witness systate from))
           (systate from))
     :enable system-state-reachable-from-p)))
