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

(include-book "last-anchor-def")
(include-book "unequivocal-dag")
(include-book "active-committees-after-commit")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ last-anchor-present
  :parents (correctness)
  :short "Invariant that if the last committed round is not 0
          then the validator has a last anchor."
  :long
  (xdoc::topstring
   (xdoc::p
    "Initially the last committed round is 0,
     so the invariant trivially holds.")
   (xdoc::p
    "The only event that modifies the last committed round is @('commit'),
     which can happen only if
     there is a certificate anchor for the new last committed round;
     this is explicitly checked by  @(tsee commit-possiblep).")
   (xdoc::p
    "A @('certify') or @('accept') event may extend the DAG,
     which could potentially turn @(tsee last-anchor) into @('nil')
     if the newly added certificate had
     the same author and round as the last anchor.
     However, this cannot happen
     under the already proved in @(see unequivocal-dag),
     which, if true in a state, it preserved in the next:
     so the next state after @('certify') or @('accept')
     still satisfies that invariant,
     and cannot turn @(tsee last-anchor) into @('nil')."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk last-anchor-present-p ((systate system-statep))
  :returns (yes/no booleanp)
  :short "Definition of the invariant."
  (forall (val)
          (implies (set::in val (correct-addresses systate))
                   (b* ((vstate (get-validator-state val systate)))
                     (implies (not (equal (validator-state->last vstate) 0))
                              (last-anchor vstate)))))

  ///

  (fty::deffixequiv-sk last-anchor-present-p
    :args ((systate system-statep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule last-anchor-present-p-when-init
  :short "Establishment of the invariant in the initial states."
  (implies (system-initp systate)
           (last-anchor-present-p systate))
  :enable (last-anchor-present-p
           system-initp
           system-validators-initp-necc
           validator-init))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection last-anchor-present-p-of-next
  :short "Preservation of the invariant by single transitions."
  :long
  (xdoc::topstring
   (xdoc::p
    "For @('certify'), we need the previosuly proved invariants
     @(see proposed-disjoint-dag) and @(see unequivocal-dag)
     in order to relieve the hypotheses of @('unequiv-dag-p-of-certify-next').")
   (xdoc::p
    "For @('accept'), we just need @(see unequivocal-dag)
     for an analogous reason.")
   (xdoc::p
    "For @('commit'), we need @(tsee active-committee-at-round-of-commit-next)
     to show that the extension of the blockchain
     does not modify the relevant committee.
     This rule needs other previously proved invariants."))

  (defruled last-anchor-present-p-of-propose-next
    (implies (last-anchor-present-p systate)
             (last-anchor-present-p (propose-next prop dests systate)))
    :use (:instance last-anchor-present-p-necc
                    (val (last-anchor-present-p-witness
                          (propose-next prop dests systate))))
    :enable (last-anchor-present-p
             last-anchor))

  (defruled last-anchor-present-p-of-endorse-next
    (implies (last-anchor-present-p systate)
             (last-anchor-present-p (endorse-next prop endor systate)))
    :use (:instance last-anchor-present-p-necc
                    (val (last-anchor-present-p-witness
                          (endorse-next prop endor systate))))
    :enable (last-anchor-present-p
             last-anchor))

  (defruled last-anchor-present-p-of-augment-next
    (implies (and (augment-possiblep prop endor systate)
                  (last-anchor-present-p systate))
             (last-anchor-present-p (augment-next prop endor systate)))
    :use (:instance last-anchor-present-p-necc
                    (val (last-anchor-present-p-witness
                          (augment-next prop endor systate))))
    :enable (last-anchor-present-p
             last-anchor))

  (defruled last-anchor-present-p-of-certify-next
    (implies (and (certify-possiblep cert dests systate)
                  (proposed-disjoint-dag-p systate)
                  (unequiv-dag-p systate)
                  (last-anchor-present-p systate))
             (last-anchor-present-p (certify-next cert dests systate)))
    :use ((:instance last-anchor-present-p-necc
                     (val (last-anchor-present-p-witness
                           (certify-next cert dests systate))))
          (:instance unequiv-dag-p-necc
                     (val (certificate->author cert))
                     (systate (certify-next cert dests systate)))
          (:instance cert-with-author+round-superset-when-unequiv
                     (certs0 (validator-state->dag
                              (get-validator-state
                               (certificate->author cert)
                               systate)))
                     (certs (validator-state->dag
                             (get-validator-state
                              (certificate->author cert)
                              (certify-next cert dests systate))))
                     (author (certificate->author
                              (last-anchor
                               (get-validator-state
                                (certificate->author cert)
                                systate))))
                     (round (certificate->round
                             (last-anchor
                              (get-validator-state
                               (certificate->author cert)
                               systate))))))
    :enable (last-anchor-present-p
             last-anchor
             validator-state->dag-of-certify-next
             unequiv-dag-p-of-certify-next))

  (defruled last-anchor-present-p-of-accept-next
    (implies (and (accept-possiblep val cert systate)
                  (addressp val)
                  (unequiv-dag-p systate)
                  (last-anchor-present-p systate))
             (last-anchor-present-p (accept-next val cert systate)))
    :use ((:instance last-anchor-present-p-necc
                     (val (last-anchor-present-p-witness
                           (accept-next val cert systate))))
          (:instance unequiv-dag-p-necc
                     (systate (accept-next val cert systate)))
          (:instance cert-with-author+round-superset-when-unequiv
                     (certs0 (validator-state->dag
                              (get-validator-state val systate)))
                     (certs (validator-state->dag
                             (get-validator-state
                              val (accept-next val cert systate))))
                     (author (certificate->author
                              (last-anchor
                               (get-validator-state val systate))))
                     (round (certificate->round
                             (last-anchor
                              (get-validator-state val systate))))))
    :enable (last-anchor-present-p
             last-anchor
             validator-state->dag-of-accept-next
             unequiv-dag-p-of-accept-next))

  (defruled last-anchor-present-p-of-advance-next
    (implies (and (advance-possiblep val systate)
                  (last-anchor-present-p systate))
             (last-anchor-present-p (advance-next val systate)))
    :use (:instance last-anchor-present-p-necc
                    (val (last-anchor-present-p-witness
                          (advance-next val systate))))
    :enable (last-anchor-present-p
             last-anchor))

  (defruled last-anchor-present-p-of-commit-next
    (implies (and (commit-possiblep val systate)
                  (last-blockchain-round-p systate)
                  (ordered-blockchain-p systate)
                  (last-anchor-present-p systate))
             (last-anchor-present-p (commit-next val systate)))
    :use (:instance last-anchor-present-p-necc
                    (val (last-anchor-present-p-witness
                          (commit-next val systate))))
    :enable (last-anchor-present-p
             last-anchor
             commit-possiblep
             validator-state->last-of-commit-next
             active-committee-at-round-of-commit-next
             active-committee-at-earlier-round-when-at-later-round))

  (defruled last-anchor-present-p-of-event-next
    (implies (and (event-possiblep event systate)
                  (last-blockchain-round-p systate)
                  (ordered-blockchain-p systate)
                  (proposed-disjoint-dag-p systate)
                  (unequiv-dag-p systate)
                  (last-anchor-present-p systate))
             (last-anchor-present-p (event-next event systate)))
    :enable (event-possiblep
             event-next)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled last-anchor-present-p-of-events-next
  :short "Preservation of the invariant by multiple transitions."
  (implies (and (events-possiblep events systate)
                (last-blockchain-round-p systate)
                (ordered-blockchain-p systate)
                (certificate-to-other-p systate)
                (proposed-author-self-p systate)
                (unequiv-proposed-p systate)
                (proposed-disjoint-dag-p systate)
                (unequiv-dag-p systate)
                (last-anchor-present-p systate))
           (last-anchor-present-p (events-next events systate)))
  :induct t
  :enable (events-possiblep
           events-next))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled last-anchor-present-p-when-reachable
  :short "The invariant holds in every reachable state."
  (implies (system-state-reachablep systate)
           (last-anchor-present-p systate))
  :enable (system-state-reachablep
           last-anchor-present-p-when-init
           last-blockchain-round-p-when-init
           ordered-blockchain-p-when-init
           certificate-to-other-p-when-init
           proposed-author-self-p-when-init
           unequiv-proposed-p-when-init
           proposed-disjoint-dag-p-when-init
           unequiv-dag-p-when-init)
  :prep-lemmas
  ((defrule lemma
     (implies (and (system-state-reachable-from-p systate from)
                   (last-blockchain-round-p from)
                   (ordered-blockchain-p from)
                   (certificate-to-other-p from)
                   (proposed-author-self-p from)
                   (unequiv-proposed-p from)
                   (proposed-disjoint-dag-p from)
                   (unequiv-dag-p from)
                   (last-anchor-present-p from))
              (last-anchor-present-p systate))
     :use (:instance
           last-anchor-present-p-of-events-next
           (events (system-state-reachable-from-p-witness systate from))
           (systate from))
     :enable system-state-reachable-from-p)))
