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

(include-book "proposed-author-self")

(local (include-book "../library-extensions/omap-theorems"))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ unequivocal-proposed
  :parents (correctness)
  :short "Invariant that the pending proposals are unequivocal,
          i.e. have unique author and round combinations."
  :long
  (xdoc::topstring
   (xdoc::p
    "This invariant concerns the keys of the pending proposal map.
     The only events that modify the keys are @('propose') and @('certify').")
   (xdoc::p
    "A @('propose') event adds a pending proposal only if
     there is not already one for the same round.
     Under the previously proved invariant @(see proposed-author-self),
     the pending proposals are all authored by the validator,
     and so is the new one being added.
     Thus, the fact that the rounds are unique
     implies that the author-round combinations are unique.")
   (xdoc::p
    "A @('certify') event removes a pending proposal,
     which preserves nonequivocation for the remaining ones."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk unequivocal-proposed-p ((systate system-statep))
  :returns (yes/no booleanp)
  :short "Definition of the invariant."
  (forall (val)
          (implies (set::in val (correct-addresses systate))
                   (b* (((validator-state vstate)
                         (get-validator-state val systate)))
                     (prop-set-unequivp (omap::keys vstate.proposed)))))

  ///

  (fty::deffixequiv-sk unequivocal-proposed-p
    :args ((systate system-statep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled unequivocal-proposed-p-when-init
  :short "Establishment of the invariant in the initial states."
  (implies (system-initp systate)
           (unequivocal-proposed-p systate))
  :enable (unequivocal-proposed-p
           system-initp
           system-validators-initp-necc
           validator-init))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection unequivocal-proposed-p-of-next
  :short "Preservation of the invariant by single transitions."

  (defruled unequivocal-proposed-p-of-propose-next
    (implies (and (propose-possiblep prop dests systate)
                  (proposed-author-self-p systate)
                  (unequivocal-proposed-p systate))
             (unequivocal-proposed-p (propose-next prop dests systate)))
    :enable (unequivocal-proposed-p
             unequivocal-proposed-p-necc
             validator-state->proposed-of-propose-next
             prop-set-unequivp-of-insert
             proposal-setp-of-keys-when-proposal-address-set-mapp
             props-with-author+round-to-props-with-round
             prop-set-all-author-p-when-proposed-author-self-p
             propose-possiblep))

  (defruled unequivocal-proposed-p-of-endorse-next
    (implies (unequivocal-proposed-p systate)
             (unequivocal-proposed-p (endorse-next prop endor systate)))
    :enable (unequivocal-proposed-p
             unequivocal-proposed-p-necc))

  (defruled unequivocal-proposed-p-of-augment-next
    (implies (and (augment-possiblep prop endor systate)
                  (unequivocal-proposed-p systate))
             (unequivocal-proposed-p (augment-next prop endor systate)))
    :enable (unequivocal-proposed-p
             unequivocal-proposed-p-necc
             validator-state->proposed-of-augment-next
             augment-possiblep
             omap::assoc-to-in-of-keys))

  (defruled unequivocal-proposed-p-of-certify-next
    (implies (unequivocal-proposed-p systate)
             (unequivocal-proposed-p (certify-next cert dests systate)))
    :enable (unequivocal-proposed-p
             unequivocal-proposed-p-necc
             validator-state->proposed-of-certify-next
             omap::keys-of-delete
             prop-set-unequivp-of-delete
             proposal-setp-of-keys-when-proposal-address-set-mapp))

  (defruled unequivocal-proposed-p-of-accept-next
    (implies (and (accept-possiblep val cert systate)
                  (unequivocal-proposed-p systate))
             (unequivocal-proposed-p (accept-next val cert systate)))
    :enable (unequivocal-proposed-p
             unequivocal-proposed-p-necc))

  (defruled unequivocal-proposed-p-of-advance-next
    (implies (and (advance-possiblep val systate)
                  (unequivocal-proposed-p systate))
             (unequivocal-proposed-p (advance-next val systate)))
    :enable (unequivocal-proposed-p
             unequivocal-proposed-p-necc))

  (defruled unequivocal-proposed-p-of-commit-next
    (implies (and (commit-possiblep val systate)
                  (unequivocal-proposed-p systate))
             (unequivocal-proposed-p (commit-next val systate)))
    :enable (unequivocal-proposed-p
             unequivocal-proposed-p-necc))

  (defruled unequivocal-proposed-p-of-event-next
    (implies (and (event-possiblep event systate)
                  (proposed-author-self-p systate)
                  (unequivocal-proposed-p systate))
             (unequivocal-proposed-p (event-next event systate)))
    :enable (event-possiblep
             event-next)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled unequivocal-proposed-p-of-events-next
  :short "Preservation of the invariant by multiple transitions."
  (implies (and (events-possiblep events systate)
                (proposed-author-self-p systate)
                (unequivocal-proposed-p systate))
           (unequivocal-proposed-p (events-next events systate)))
  :induct t
  :enable (events-possiblep
           events-next))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled unequivocal-proposed-p-when-reachable
  :short "The invariant holds in every reachable state."
  (implies (system-state-reachablep systate)
           (unequivocal-proposed-p systate))
  :enable (system-state-reachablep
           unequivocal-proposed-p-when-init
           proposed-author-self-p-when-init)
  :prep-lemmas
  ((defrule lemma
     (implies (and (system-state-reachable-from-p systate from)
                   (proposed-author-self-p from)
                   (unequivocal-proposed-p from))
              (unequivocal-proposed-p systate))
     :use (:instance
           unequivocal-proposed-p-of-events-next
           (events (system-state-reachable-from-p-witness systate from))
           (systate from))
     :enable system-state-reachable-from-p)))
