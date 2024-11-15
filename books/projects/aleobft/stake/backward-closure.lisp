; AleoBFT Library
;
; Copyright (C) 2024 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOBFT-STAKE")

(include-book "initialization")
(include-book "transitions")
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
     namely @('create') and @('store').")
   (xdoc::p
    "A @('create') event may only occur if
     the certificate's author has all the previous certificates in its DAG.")
   (xdoc::p
    "A @('store') event may only occur if
     the DAG has all the previous certificates as well.
     Under that condition, the certificate is moved from the buffer to the DAG.
     In fact, the purpose of the buffer is to wait
     until all the previous certificates are in the DAG,
     since they may be coming out of order with respect to round numbers.")
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
     @('create') and @('store').
     For these two kinds of events,
     first we prove theorems saying that the added certificate
     has all the predecessors in the DAG,
     which is ensured by
     @(tsee create-possiblep) and @(tsee store-possiblep).
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

  ;; receive:

  (defruled backward-closed-p-of-receive-next
    (implies (and (backward-closed-p systate)
                  (receive-possiblep msg systate))
             (backward-closed-p (receive-next msg systate)))
    :enable (backward-closed-p
             backward-closed-p-necc))

  ;; store:

  (defruled certificate-previous-in-dag-p-when-store-possiblep
    (implies (and (store-possiblep val cert systate)
                  (set::in val (correct-addresses systate)))
             (certificate-previous-in-dag-p
              cert
              (validator-state->dag
               (get-validator-state val systate))))
    :enable (certificate-previous-in-dag-p
             store-possiblep))

  (defruled backward-closed-p-of-store-next
    (implies (and (backward-closed-p systate)
                  (store-possiblep val cert systate)
                  (addressp val))
             (backward-closed-p (store-next val cert systate)))
    :enable (backward-closed-p
             backward-closed-p-necc
             validator-state->dag-of-store-next
             dag-closedp-of-insert
             certificate-previous-in-dag-p-when-store-possiblep))

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

  ;; timeout:

  (defruled backward-closed-p-of-timeout-next
    (implies (and (backward-closed-p systate)
                  (timeout-possiblep val systate))
             (backward-closed-p (timeout-next val systate)))
    :enable (backward-closed-p
             backward-closed-p-necc))

  ;; all events:

  (defruled backward-closed-p-of-event-next
    (implies (and (backward-closed-p systate)
                  (event-possiblep event systate))
             (backward-closed-p (event-next event systate)))
    :enable (event-possiblep event-next)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection backward-closed-p-always
  :short "The invariant holds in every state
          reachable from an initial state via a sequence of events."

  (defruled backward-closed-p-of-events-next
    (implies (and (backward-closed-p systate)
                  (events-possiblep events systate))
             (backward-closed-p (events-next events systate)))
    :induct t
    :enable (events-possiblep
             events-next))

  (defruled backward-closed-p-when-reachable
    (implies (and (system-initp systate)
                  (events-possiblep events systate))
             (backward-closed-p (events-next events systate)))))
