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

(include-book "unequivocal-proposed")
(include-book "certificate-to-other")

(local (include-book "../library-extensions/omap-theorems"))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ proposed-disjoint-dag
  :parents (correctness)
  :short "Invariant that the author-round pairs of the pending proposals
          are disjoint from the author-round pairs of the DAG."
  :long
  (xdoc::topstring
   (xdoc::p
    "Pending proposals and DAGs are modified only by
     @('propose'), @('certify'), and @('accept') events.")
   (xdoc::p
    "A @('propose') event can happen only if
     the new proposal's author and round combination
     is not in any certificate in the DAG:
     this is checked explicitly by @(tsee propose-possiblep).")
   (xdoc::p
    "A @('certify') event adds a certificate to the DAG
     from a pending proposal, which it removes from the map.
     Because of the previously proved invariant @(see unequivocal-proposed),
     once that proposal is removed from the pending map,
     the pending map cannot have any other proposal
     with that author and round,
     and thus the disjointness with the DAG is preserved.")
   (xdoc::p
    "An @('accept') event adds a certificate to the DAG,
     but the certificate can only be authored by a different validator
     (as proved in @(see certificate-to-other)),
     while the pending proposals are all authored by the validator
     (as proved in @(see proposed-author-self)),
     and therefore the accepted certificate's author-round pair
     cannot occur in any pending proposal."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk proposed-disjoint-dag-p ((systate system-statep))
  :returns (yes/no booleanp)
  :short "Definition of the invariant."
  (forall (val prop)
          (implies (set::in val (correct-addresses systate))
                   (b* (((validator-state vstate)
                         (get-validator-state val systate)))
                     (implies (set::in prop (omap::keys vstate.proposed))
                              (set::emptyp
                               (certs-with-author+round (proposal->author prop)
                                                        (proposal->round prop)
                                                        vstate.dag))))))
  :guard-hints
  (("Goal"
    :in-theory (enable proposal-setp-of-keys-when-proposal-address-set-mapp)))

  ///

  (fty::deffixequiv-sk proposed-disjoint-dag-p
    :args ((systate system-statep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled proposed-disjoint-dag-p-when-init
  :short "Establishment of the invariant in the initial states."
  (implies (system-initp systate)
           (proposed-disjoint-dag-p systate))
  :enable (proposed-disjoint-dag-p
           system-initp
           system-validators-initp-necc
           validator-init))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection proposed-disjoint-dag-p-of-next
  :short "Preservation of the invariant by single transitions."

  (defruled proposed-disjoint-dag-p-of-propose-next
    (implies (and (propose-possiblep prop dests systate)
                  (proposed-disjoint-dag-p systate))
             (proposed-disjoint-dag-p (propose-next prop dests systate)))
    :enable (proposed-disjoint-dag-p
             proposed-disjoint-dag-p-necc
             validator-state->proposed-of-propose-next
             propose-possiblep))

  (defruled proposed-disjoint-dag-p-of-endorse-next
    (implies (proposed-disjoint-dag-p systate)
             (proposed-disjoint-dag-p (endorse-next prop endor systate)))
    :enable (proposed-disjoint-dag-p
             proposed-disjoint-dag-p-necc))

  (defruled proposed-disjoint-dag-p-of-augment-next
    (implies (and (augment-possiblep prop endor systate)
                  (proposed-disjoint-dag-p systate))
             (proposed-disjoint-dag-p (augment-next prop endor systate)))
    :enable (proposed-disjoint-dag-p
             proposed-disjoint-dag-p-necc
             validator-state->proposed-of-augment-next
             augment-possiblep
             omap::assoc-to-in-of-keys))

  (defruled proposed-disjoint-dag-p-of-certify-next
    (implies (and (certify-possiblep cert dests systate)
                  (unequiv-proposed-p systate)
                  (proposed-disjoint-dag-p systate))
             (proposed-disjoint-dag-p (certify-next cert dests systate)))
    :use (:instance prop-set-unequivp-necc
                    (props (omap::keys
                            (validator-state->proposed
                             (get-validator-state (certificate->author cert)
                                                  systate))))
                    (prop1 (certificate->proposal cert))
                    (prop2 (mv-nth 1 (proposed-disjoint-dag-p-witness
                                      (certify-next cert dests systate)))))
    :enable (proposed-disjoint-dag-p
             proposed-disjoint-dag-p-necc
             unequiv-proposed-p-necc
             validator-state->proposed-of-certify-next
             validator-state->dag-of-certify-next
             certify-possiblep
             certs-with-author+round-of-insert
             omap::keys-of-delete
             certificate->author
             certificate->round
             omap::assoc-to-in-of-keys
             proposal-setp-of-keys-when-proposal-address-set-mapp))

  (defruled proposed-disjoint-dag-p-of-accept-next
    (implies (and (accept-possiblep val cert systate)
                  (addressp val)
                  (certificatep cert)
                  (proposed-author-self-p systate)
                  (certificate-to-other-p systate)
                  (proposed-disjoint-dag-p systate))
             (proposed-disjoint-dag-p (accept-next val cert systate)))
    :use ((:instance certificate-to-other-p-necc
                     (dest val))
          (:instance proposed-disjoint-dag-p-necc
                     (val (mv-nth 0 (proposed-disjoint-dag-p-witness
                                     (accept-next val cert systate))))
                     (prop (mv-nth 1 (proposed-disjoint-dag-p-witness
                                      (accept-next val cert systate)))))
          (:instance proposed-disjoint-dag-p-necc
                     (prop (mv-nth 1 (proposed-disjoint-dag-p-witness
                                      (accept-next val cert systate))))))
    :enable (proposed-disjoint-dag-p
             accept-possiblep
             certificate->author
             certificate->round
             validator-state->dag-of-accept-next
             certs-with-author+round-of-insert
             proposed-author-self-p-necc))

  (defruled proposed-disjoint-dag-p-of-advance-next
    (implies (and (advance-possiblep val systate)
                  (proposed-disjoint-dag-p systate))
             (proposed-disjoint-dag-p (advance-next val systate)))
    :enable (proposed-disjoint-dag-p
             proposed-disjoint-dag-p-necc))

  (defruled proposed-disjoint-dag-p-of-commit-next
    (implies (and (commit-possiblep val systate)
                  (proposed-disjoint-dag-p systate))
             (proposed-disjoint-dag-p (commit-next val systate)))
    :enable (proposed-disjoint-dag-p
             proposed-disjoint-dag-p-necc))

  (defruled proposed-disjoint-dag-p-of-event-next
    (implies (and (event-possiblep event systate)
                  (unequiv-proposed-p systate)
                  (proposed-author-self-p systate)
                  (certificate-to-other-p systate)
                  (proposed-disjoint-dag-p systate))
             (proposed-disjoint-dag-p (event-next event systate)))
    :enable (event-possiblep
             event-next)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled proposed-disjoint-dag-p-of-events-next
  :short "Preservation of the invariant by multiple transitions."
  (implies (and (events-possiblep events systate)
                (unequiv-proposed-p systate)
                (proposed-author-self-p systate)
                (certificate-to-other-p systate)
                (proposed-disjoint-dag-p systate))
           (proposed-disjoint-dag-p (events-next events systate)))
  :induct t
  :enable (events-possiblep
           events-next))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled proposed-disjoint-dag-p-when-reachable
  :short "The invariant holds in every reachable state."
  (implies (system-state-reachablep systate)
           (proposed-disjoint-dag-p systate))
  :enable (system-state-reachablep
           proposed-disjoint-dag-p-when-init
           unequiv-proposed-p-when-init
           proposed-author-self-p-when-init
           certificate-to-other-p-when-init)
  :prep-lemmas
  ((defrule lemma
     (implies (and (system-state-reachable-from-p systate from)
                   (unequiv-proposed-p from)
                   (proposed-author-self-p from)
                   (certificate-to-other-p from)
                   (proposed-disjoint-dag-p from))
              (proposed-disjoint-dag-p systate))
     :use (:instance
           proposed-disjoint-dag-p-of-events-next
           (events (system-state-reachable-from-p-witness systate from))
           (systate from))
     :enable system-state-reachable-from-p)))
