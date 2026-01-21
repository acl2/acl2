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

(include-book "proposed-disjoint-dag")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ unequivocal-dag
  :parents (correctness)
  :short "Invariant that the DAG of each correct validator is unequivocal,
          i.e. its certificates have unique author and round combinations."
  :long
  (xdoc::topstring
   (xdoc::p
    "Initially the DAG is empty, and thus trivially unequivocal.")
   (xdoc::p
    "The only events that add certificates to the DAG
     are @('certify') and @('accept').")
   (xdoc::p
    "A @('certify') event adds a certificate
     whose proposal is from the pending proposal map,
     which, as proved in @(see proposed-disjoint-dag),
     has different author and round combination
     from all the certificates already in the DAG.
     So the addition of the certificate cannot cause equivocation.")
   (xdoc::p
    "An @('accept') event adds the received certificate
     only if its author and round combination
     is not already in the DAG:
     this is explicitly checked by @(tsee accept-possiblep)."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk unequiv-dag-p ((systate system-statep))
  :returns (yes/no booleanp)
  :short "Definition of the invariant."
  (forall (val)
          (implies (set::in val (correct-addresses systate))
                   (cert-set-unequivp (validator-state->dag
                                       (get-validator-state val systate)))))

  ///

  (fty::deffixequiv-sk unequiv-dag-p
    :args ((systate system-statep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled unequiv-dag-p-when-init
  :short "Establishment of the invariant in the initial states."
  (implies (system-initp systate)
           (unequiv-dag-p systate))
  :enable (unequiv-dag-p
           system-initp
           system-validators-initp-necc
           validator-init))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection unequiv-dag-p-of-next
  :short "Preservation of the invariant by single transitions."

  (defruled unequiv-dag-p-of-propose-next
    (implies (unequiv-dag-p systate)
             (unequiv-dag-p (propose-next prop dests systate)))
    :enable (unequiv-dag-p
             unequiv-dag-p-necc))

  (defruled unequiv-dag-p-of-endorse-next
    (implies (unequiv-dag-p systate)
             (unequiv-dag-p (endorse-next prop endor systate)))
    :enable (unequiv-dag-p
             unequiv-dag-p-necc))

  (defruled unequiv-dag-p-of-augment-next
    (implies (and (augment-possiblep prop endor systate)
                  (unequiv-dag-p systate))
             (unequiv-dag-p (augment-next prop endor systate)))
    :enable (unequiv-dag-p
             unequiv-dag-p-necc))

  (defruled unequiv-dag-p-of-certify-next
    (implies (and (certify-possiblep cert dests systate)
                  (proposed-disjoint-dag-p systate)
                  (unequiv-dag-p systate))
             (unequiv-dag-p (certify-next cert dests systate)))
    :enable (unequiv-dag-p
             unequiv-dag-p-necc
             validator-state->dag-of-certify-next
             proposed-disjoint-dag-p-necc
             cert-set-unequivp-of-insert
             certify-possiblep
             certificate->author
             certificate->round
             omap::assoc-to-in-of-keys))

  (defruled unequiv-dag-p-of-accept-next
    (implies (and (accept-possiblep val cert systate)
                  (addressp val)
                  (unequiv-dag-p systate))
             (unequiv-dag-p (accept-next val cert systate)))
    :enable (unequiv-dag-p
             unequiv-dag-p-necc
             validator-state->dag-of-accept-next
             accept-possiblep
             cert-set-unequivp-of-insert
             certificate->author
             certificate->round))

  (defruled unequiv-dag-p-of-advance-next
    (implies (and (advance-possiblep val systate)
                  (unequiv-dag-p systate))
             (unequiv-dag-p (advance-next val systate)))
    :enable (unequiv-dag-p
             unequiv-dag-p-necc))

  (defruled unequiv-dag-p-of-commit-next
    (implies (and (commit-possiblep val systate)
                  (unequiv-dag-p systate))
             (unequiv-dag-p (commit-next val systate)))
    :enable (unequiv-dag-p
             unequiv-dag-p-necc))

  (defruled unequiv-dag-p-of-event-next
    (implies (and (event-possiblep event systate)
                  (proposed-disjoint-dag-p systate)
                  (unequiv-dag-p systate))
             (unequiv-dag-p (event-next event systate)))
    :enable (event-possiblep
             event-next)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled unequiv-dag-p-of-events-next
  :short "Preservation of the invariant by multiple transitions."
  (implies (and (events-possiblep events systate)
                (certificate-to-other-p systate)
                (proposed-author-self-p systate)
                (unequiv-proposed-p systate)
                (proposed-disjoint-dag-p systate)
                (unequiv-dag-p systate))
           (unequiv-dag-p (events-next events systate)))
  :induct t
  :enable (events-possiblep
           events-next))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled unequiv-dag-p-when-reachable
  :short "The invariant holds in every reachable state."
  (implies (system-state-reachablep systate)
           (unequiv-dag-p systate))
  :enable (system-state-reachablep
           certificate-to-other-p-when-init
           proposed-author-self-p-when-init
           unequiv-proposed-p-when-init
           proposed-disjoint-dag-p-when-init
           unequiv-dag-p-when-init)
  :prep-lemmas
  ((defrule lemma
     (implies (and (system-state-reachable-from-p systate from)
                   (certificate-to-other-p from)
                   (proposed-author-self-p from)
                   (unequiv-proposed-p from)
                   (proposed-disjoint-dag-p from)
                   (unequiv-dag-p from))
              (unequiv-dag-p systate))
     :use (:instance
           unequiv-dag-p-of-events-next
           (events (system-state-reachable-from-p-witness systate from))
           (systate from))
     :enable system-state-reachable-from-p)))
