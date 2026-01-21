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

(include-book "proposed-previous-closed")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ dag-previous-closed
  :parents (correctness)
  :short "Invariant that DAGs are backward-closed."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, there are no dangling edges:
     for each reference to a previous certificate,
     the certificate is present in the DAG.
     This only applied to certificates at rounds different from 1.")
   (xdoc::p
    "A validator's DAG is extended when the validator
     creates or accepts a certificate.")
   (xdoc::p
    "A (correct) validator creates a certificate from a pending proposal,
     which, as proved in @(see proposed-previous-closed),
     references previous certificates that are in the validator's DAG.")
   (xdoc::p
    "A validator accepts a certificate from the network
     only if it already has, in its DAG, all the previous certificates
     referenced by the certificate."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk dag-previous-closed-p ((systate system-statep))
  :returns (yes/no booleanp)
  :short "Definition of the invariant."
  (forall (val)
          (implies (set::in val (correct-addresses systate))
                   (dag-closedp
                    (validator-state->dag
                     (get-validator-state val systate)))))
  ///
  (fty::deffixequiv-sk dag-previous-closed-p
    :args ((systate system-statep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule dag-previous-closed-p-when-init
  :short "Establishment of the invariant in the initial states."
  (implies (system-initp systate)
           (dag-previous-closed-p systate))
  :enable (dag-previous-closed-p
           system-initp
           system-validators-initp-necc
           validator-init))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection dag-previous-closed-p-of-next
  :short "Preservation of the invariant by single transitions."
  :long
  (xdoc::topstring
   (xdoc::p
    "For each of @('certify') and @('accept') events,
     we first prove a theorem about @(tsee cert-previous-in-dag-p),
     and then the main one about involving @(tsee dag-closedp)."))

  (defruled dag-previous-closed-p-of-propose-next
    (implies (dag-previous-closed-p systate)
             (dag-previous-closed-p (propose-next prop dests systate)))
    :enable (dag-previous-closed-p
             dag-previous-closed-p-necc))

  (defruled dag-previous-closed-p-of-endorse-next
    (implies (dag-previous-closed-p systate)
             (dag-previous-closed-p (endorse-next prop endor systate)))
    :enable (dag-previous-closed-p
             dag-previous-closed-p-necc))

  (defruled dag-previous-closed-p-of-augment-next
    (implies (and (augment-possiblep prop endor systate)
                  (dag-previous-closed-p systate))
             (dag-previous-closed-p (augment-next prop endor systate)))
    :enable (dag-previous-closed-p
             dag-previous-closed-p-necc))

  (defruled cert-previous-in-dag-p-of-certify-next
    (implies (and (certify-possiblep cert dests systate)
                  (proposed-previous-closed-p systate)
                  (set::in (certificate->author cert)
                           (correct-addresses systate)))
             (cert-previous-in-dag-p
              cert
              (validator-state->dag
               (get-validator-state (certificate->author cert) systate))))
    :enable (cert-previous-in-dag-p
             certify-possiblep
             proposed-previous-closed-p-necc
             certificate->author
             certificate->round
             certificate->previous
             omap::assoc-to-in-of-keys))

  (defruled dag-previous-closed-p-of-certify-next
    (implies (and (certify-possiblep cert dests systate)
                  (proposed-previous-closed-p systate)
                  (dag-previous-closed-p systate))
             (dag-previous-closed-p (certify-next cert dests systate)))
    :enable (dag-previous-closed-p
             dag-previous-closed-p-necc
             validator-state->dag-of-certify-next
             dag-closedp-of-insert
             cert-previous-in-dag-p-of-certify-next))

  (defruled cert-previous-in-dag-p-of-accept-next
    (implies (and (accept-possiblep val cert systate)
                  (set::in val (correct-addresses systate)))
             (cert-previous-in-dag-p
              cert
              (validator-state->dag
               (get-validator-state val systate))))
    :enable (cert-previous-in-dag-p
             accept-possiblep
             certificate->round
             certificate->previous))

  (defruled dag-previous-closed-p-of-accept-next
    (implies (and (accept-possiblep val cert systate)
                  (addressp val)
                  (dag-previous-closed-p systate))
             (dag-previous-closed-p (accept-next val cert systate)))
    :enable (dag-previous-closed-p
             dag-previous-closed-p-necc
             accept-possiblep
             validator-state->dag-of-accept-next
             dag-closedp-of-insert
             cert-previous-in-dag-p-of-accept-next))

  (defruled dag-previous-closed-p-of-advance-next
    (implies (and (advance-possiblep val systate)
                  (dag-previous-closed-p systate))
             (dag-previous-closed-p (advance-next val systate)))
    :enable (dag-previous-closed-p
             dag-previous-closed-p-necc))

  (defruled dag-previous-closed-p-of-commit-next
    (implies (and (commit-possiblep val systate)
                  (dag-previous-closed-p systate))
             (dag-previous-closed-p (commit-next val systate)))
    :enable (dag-previous-closed-p
             dag-previous-closed-p-necc))

  (defruled dag-previous-closed-p-of-event-next
    (implies (and (event-possiblep event systate)
                  (proposed-previous-closed-p systate)
                  (dag-previous-closed-p systate))
             (dag-previous-closed-p (event-next event systate)))
    :enable (event-possiblep
             event-next)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled dag-previous-closed-p-of-events-next
  :short "Preservation of the invariant by multiple transitions."
  (implies (and (events-possiblep events systate)
                (proposed-previous-closed-p systate)
                (dag-previous-closed-p systate))
           (dag-previous-closed-p (events-next events systate)))
  :induct t
  :enable (events-possiblep
           events-next))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled dag-previous-closed-p-when-reachable
  :short "The invariant holds in every reachable state."
  (implies (system-state-reachablep systate)
           (dag-previous-closed-p systate))
  :enable (system-state-reachablep
           dag-previous-closed-p-when-init
           proposed-previous-closed-p-when-init)
  :prep-lemmas
  ((defrule lemma
     (implies (and (system-state-reachable-from-p systate from)
                   (proposed-previous-closed-p from)
                   (dag-previous-closed-p from))
              (dag-previous-closed-p systate))
     :use (:instance
           dag-previous-closed-p-of-events-next
           (events (system-state-reachable-from-p-witness systate from))
           (systate from))
     :enable system-state-reachable-from-p)))
