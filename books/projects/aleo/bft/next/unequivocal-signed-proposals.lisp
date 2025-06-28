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

(include-book "signed-in-signer")
(include-book "author-round-pairs-in-validators")
(include-book "proposed-author-self")
(include-book "endorsed-author-other")

(local (include-book "../library-extensions/oset-theorems"))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ unequivocal-signed-proposals
  :parents (correctness)
  :short "Invariant that all the proposals signed by each correct validator
          are unequivocal, i.e. have unique author and round combinations."
  :long
  (xdoc::topstring
   (xdoc::p
    "The set of proposals signed by a validator
     is the set returned by @(tsee signed-props).
     As proved in @(see signed-proposals),
     the only events that extend that set are
     @('propose'), @('endorse'), and @('certify').
     The latter does so only if the signer is faulty,
     but the invariant discussed here only concerns correct validators;
     so the only events of interest are @('propose') and @('endorse').")
   (xdoc::p
    "Before proposing or endorsing a proposal,
     a correct validator ensures that the proposal does not have
     the same author and round as
     all the other proposals it has signed (proposed or endorsed):
     these are critical checks performed by validators.
     The validators do not actually perform checks on
     the full set set @(tsee signed-props),
     because, under some already proved invariants,
     weaker checks suffice.
     This is explained in more detail in the proofs below."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk unequiv-signed-props-p ((systate system-statep))
  :returns (yes/no booleanp)
  :short "Definition of the invariant."
  (forall (signer)
          (implies (set::in signer (correct-addresses systate))
                   (prop-set-unequivp (signed-props signer systate))))

  ///

  (fty::deffixequiv-sk unequiv-signed-props-p
    :args ((systate system-statep)))

  (defruled unequiv-signed-props-p-necc-with-address-fix
    (implies (and (unequiv-signed-props-p systate)
                  (set::in (address-fix signer)
                           (correct-addresses systate)))
             (prop-set-unequivp (signed-props signer systate)))
    :disable (unequiv-signed-props-p
              unequiv-signed-props-p-necc)
    :use (:instance unequiv-signed-props-p-necc
                    (signer (address-fix signer)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled unequiv-signed-props-p-when-init
  :short "Establishment of the invariant in the initial states."
  (implies (system-initp systate)
           (unequiv-signed-props-p systate))
  :enable (unequiv-signed-props-p
           signed-props-when-init))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection unequiv-signed-props-p-of-next
  :short "Preservation of the invariant by single transitions."
  :long
  (xdoc::topstring
   (xdoc::p
    "As explained in @(see unequivocal-signed-proposals),
     the only events that can modify
     the set of proposals signed by a correct validator
     are @('propose') and @('endorse').
     These two events add a proposal to the set.")
   (xdoc::p
    "A key rule used here is @('prop-set-unequivp-of-insert')
     in @(tsee prop-set-unequivp),
     which reduces the unequivocation of
     a set with an added proposal to
     (i) the unequivocation of the original set and
     (ii) the inability to retrieve, from the original set,
     any proposal with the added proposal's author and round.
     Part (i) follows from the assumption of the invariant in the old state.
     Part (ii) is proved by contradition:
     assuming that a proposal can be retrieved from the original set
     (i.e. the witness of @(tsee set::nonemptyp)),
     then by the invariant @(see signed-in-signer)
     the proposing or endorsing validator
     must have, in its state, the author-round pair of the proposal,
     as proved in @(tsee validator-has-author+round-p-when-signed-in-signer-p).
     However, as proved in
     @(tsee not-validator-has-author+round-p-when-propose-possiblep) and
     @(tsee not-validator-has-author+round-p-when-endorse-possiblep),
     it is also the case that the proposer or endorse
     does not have, in its state, the author-round pair of the proposal.")
   (xdoc::p
    "The preservation of the invariant for the other events is proved easily,
     because there is no change to the sets of signed proposals
     (of correct validators)."))

  (defruled unequiv-signed-props-p-of-propose-next
    (implies (and (propose-possiblep prop dests systate)
                  (proposed-author-self-p systate)
                  (endorsed-author-other-p systate)
                  (signed-in-signer-p systate)
                  (unequiv-signed-props-p systate))
             (unequiv-signed-props-p (propose-next prop dests systate)))
    :expand (unequiv-signed-props-p (propose-next prop dests systate))
    :enable (signed-props-of-propose-next
             prop-set-unequivp-of-insert
             set::emptyp-to-not-nonemptyp
             set::nonemptyp
             in-of-props-with-author+round
             not-validator-has-author+round-p-when-propose-possiblep)
    :use (:instance validator-has-author+round-p-when-signed-in-signer-p
                    (signer (proposal->author prop))
                    (prop (set::nonemptyp-witness
                           (props-with-author+round
                            (proposal->author prop)
                            (proposal->round prop)
                            (signed-props (proposal->author prop) systate))))))

  (defruled unequiv-signed-props-p-of-endorse-next
    (implies (and (endorse-possiblep prop endor systate)
                  (proposed-author-self-p systate)
                  (proposal-to-other-p systate)
                  (signed-in-signer-p systate)
                  (unequiv-signed-props-p systate))
             (unequiv-signed-props-p (endorse-next prop endor systate)))
    :expand (unequiv-signed-props-p (endorse-next prop endor systate))
    :enable (signed-props-of-endorse-next
             prop-set-unequivp-of-insert
             unequiv-signed-props-p-necc-with-address-fix
             set::emptyp-to-not-nonemptyp
             set::nonemptyp
             in-of-props-with-author+round)
    :use ((:instance validator-has-author+round-p-when-signed-in-signer-p
                     (signer (address-fix endor))
                     (prop (set::nonemptyp-witness
                            (props-with-author+round
                             (proposal->author prop)
                             (proposal->round prop)
                             (signed-props endor systate)))))
          (:instance not-validator-has-author+round-p-when-endorse-possiblep
                     (endor (address-fix endor)))))

  (defruled unequiv-signed-props-p-of-augment-possiblep
    (implies (and (augment-possiblep prop endor systate)
                  (unequiv-signed-props-p systate))
             (unequiv-signed-props-p (augment-next prop endor systate)))
    :expand (unequiv-signed-props-p (augment-next prop endor systate))
    :enable signed-props-of-augment-next)

  (defruled unequiv-signed-props-p-of-certify-possiblep
    (implies (and (certify-possiblep cert dests systate)
                  (unequiv-signed-props-p systate))
             (unequiv-signed-props-p (certify-next cert dests systate)))
    :expand (unequiv-signed-props-p (certify-next cert dests systate))
    :enable signed-props-of-certify-next)

  (defruled unequiv-signed-props-p-of-accept-possiblep
    (implies (and (accept-possiblep val cert systate)
                  (unequiv-signed-props-p systate))
             (unequiv-signed-props-p (accept-next val cert systate)))
    :expand (unequiv-signed-props-p (accept-next val cert systate))
    :enable signed-props-of-accept-next)

  (defruled unequiv-signed-props-p-of-advance-possiblep
    (implies (and (advance-possiblep val systate)
                  (unequiv-signed-props-p systate))
             (unequiv-signed-props-p (advance-next val systate)))
    :expand (unequiv-signed-props-p (advance-next val systate))
    :enable signed-props-of-advance-next)

  (defruled unequiv-signed-props-p-of-commit-possiblep
    (implies (and (commit-possiblep val systate)
                  (unequiv-signed-props-p systate))
             (unequiv-signed-props-p (commit-next val systate)))
    :expand (unequiv-signed-props-p (commit-next val systate))
    :enable signed-props-of-commit-next)

  (defruled unequiv-signed-props-p-of-event-next
    (implies (and (event-possiblep event systate)
                  (proposed-author-self-p systate)
                  (proposal-to-other-p systate)
                  (endorsed-author-other-p systate)
                  (signed-in-signer-p systate)
                  (unequiv-signed-props-p systate))
             (unequiv-signed-props-p (event-next event systate)))
    :enable (event-possiblep
             event-next)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled unequiv-signed-props-p-of-events-next
  :short "Preservation of the invariant by multiple transitions."
  (implies (and (events-possiblep events systate)
                (proposed-author-self-p systate)
                (proposal-to-other-p systate)
                (endorsed-author-other-p systate)
                (signed-in-signer-p systate)
                (unequiv-signed-props-p systate))
           (unequiv-signed-props-p (events-next events systate)))
  :induct t
  :enable (events-possiblep
           events-next))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled unequiv-signed-props-p-when-reachable
  :short "The invariant holds in every reachable state."
  (implies (system-state-reachablep systate)
           (unequiv-signed-props-p systate))
  :enable (system-state-reachablep
           unequiv-signed-props-p-when-init
           proposed-author-self-p-when-init
           proposal-to-other-p-when-init
           endorsed-author-other-p-when-init
           signed-in-signer-p-when-init)
  :prep-lemmas
  ((defrule lemma
     (implies (and (system-state-reachable-from-p systate from)
                   (proposed-author-self-p from)
                   (proposal-to-other-p from)
                   (endorsed-author-other-p from)
                   (signed-in-signer-p from)
                   (unequiv-signed-props-p from))
              (unequiv-signed-props-p systate))
     :use (:instance
           unequiv-signed-props-p-of-events-next
           (events (system-state-reachable-from-p-witness systate from))
           (systate from))
     :enable system-state-reachable-from-p)))
