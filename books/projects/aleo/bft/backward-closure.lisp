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

(include-book "reachability")
(include-book "dags")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ backward-closure
  :parents (correctness)
  :short "Invariant that DAGs are backward-closed."
  :long
  (xdoc::topstring
   (xdoc::p
    "A validator's DAG is extended via two kinds of events,
     namely @('create') and @('accept').")
   (xdoc::p
    "A @('create') event may only occur if
     the certificate's author has all the previous certificates in its DAG.")
   (xdoc::p
    "An @('accept') event may only occur if
     the DAG has all the previous certificates as well.")
   (xdoc::p
    "This means that DAGs are always backward-closed:
     there are no dangling edges.
     Recall that edges always point backwards
     (from a round to the round just before it),
     which justifies the `backward' in `backward-closed'."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk backward-closed-p ((systate system-statep))
  :returns (yes/no booleanp)
  :short "Definition of the invariant:
          the DAG of each correct validator is backward-closed."
  (forall (val)
          (implies (set::in val (correct-addresses systate))
                   (dag-closedp
                    (validator-state->dag
                     (get-validator-state val systate)))))
  ///
  (fty::deffixequiv-sk backward-closed-p
    :args ((systate system-statep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule backward-closed-p-when-init
  :short "Establishment of the invariant:
          the invariant holds in any initial system state."
  :long
  (xdoc::topstring
   (xdoc::p
    "Initially, DAGs are empty, and so they are trivially backward-closed."))
  (implies (system-initp systate)
           (backward-closed-p systate))
  :enable (backward-closed-p
           system-initp
           system-validators-initp-necc
           validator-init))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection backward-closed-p-of-next
  :short "Preservation of the invariant:
          if the invariant holds in a system state,
          it also holds in the next system state."
  :long
  (xdoc::topstring
   (xdoc::p
    "The only two kinds of events that extend DAGs are
     @('create') and @('accept').
     For these two kinds of events,
     first we prove theorems saying that the added certificate
     has all the predecessors in the DAG,
     which is ensured by
     @(tsee create-possiblep) and @(tsee accept-possiblep).
     Then we prove the main theorems,
     using rule @('dag-closedp-of-insert')
     to handle the addition of the certificate.")
   (xdoc::p
    "For the other four kinds of events,
     the proof is easy."))

  ;; create:

  (defruled certificate-previous-in-dag-p-when-create-possiblep
    (implies (and (create-possiblep cert systate)
                  (set::in (certificate->author cert)
                           (correct-addresses systate)))
             (certificate-previous-in-dag-p
              cert
              (validator-state->dag
               (get-validator-state (certificate->author cert) systate))))
    :enable (certificate-previous-in-dag-p
             create-possiblep
             create-author-possiblep
             create-signer-possiblep))

  (defruled backward-closed-p-of-create-next
    (implies (and (backward-closed-p systate)
                  (create-possiblep cert systate)
                  (certificatep cert))
             (backward-closed-p (create-next cert systate)))
    :enable (backward-closed-p
             backward-closed-p-necc
             validator-state->dag-of-create-next
             dag-closedp-of-insert
             certificate-previous-in-dag-p-when-create-possiblep))

  ;; accept:

  (defruled certificate-previous-in-dag-p-when-accept-possiblep
    (implies (accept-possiblep msg systate)
             (certificate-previous-in-dag-p
              (message->certificate msg)
              (validator-state->dag
               (get-validator-state (message->destination msg) systate))))
    :enable (certificate-previous-in-dag-p
             accept-possiblep))

  (defruled backward-closed-p-of-accept-next
    (implies (and (backward-closed-p systate)
                  (accept-possiblep msg systate))
             (backward-closed-p (accept-next msg systate)))
    :enable (backward-closed-p
             backward-closed-p-necc
             validator-state->dag-of-accept-next
             dag-closedp-of-insert
             certificate-previous-in-dag-p-when-accept-possiblep))

  ;; advance:

  (defruled backward-closed-p-of-advance-next
    (implies (and (backward-closed-p systate)
                  (advance-possiblep val systate))
             (backward-closed-p (advance-next val systate)))
    :enable (backward-closed-p
             backward-closed-p-necc))

  ;; commit:

  (defruled backward-closed-p-of-commit-next
    (implies (and (backward-closed-p systate)
                  (commit-possiblep val systate))
             (backward-closed-p (commit-next val systate)))
    :enable (backward-closed-p
             backward-closed-p-necc))

  ;; all events:

  (defruled backward-closed-p-of-event-next
    (implies (and (backward-closed-p systate)
                  (event-possiblep event systate))
             (backward-closed-p (event-next event systate)))
    :enable (event-possiblep event-next)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled backward-closed-p-of-events-next
  :short "Preservation of the invariant by multiple transitions."
  (implies (and (events-possiblep events systate)
                (backward-closed-p systate))
           (backward-closed-p (events-next events systate)))
  :induct t
  :enable (events-possiblep
           events-next))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled backward-closed-p-when-reachable
  :short "The invariant holds in every reachable state."
  (implies (system-state-reachablep systate)
           (backward-closed-p systate))
  :enable (system-state-reachablep
           backward-closed-p-when-init)
  :prep-lemmas
  ((defrule lemma
     (implies (and (system-state-reachable-from-p systate from)
                   (backward-closed-p from))
              (backward-closed-p systate))
     :use (:instance
           backward-closed-p-of-events-next
           (events (system-state-reachable-from-p-witness systate from))
           (systate from))
     :enable system-state-reachable-from-p)))
