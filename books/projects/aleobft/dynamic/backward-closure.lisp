; AleoBFT Library
;
; Copyright (C) 2024 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOBFT-DYNAMIC")

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
     namely @('create-certificate') and @('store-certificate').")
   (xdoc::p
    "The first kind of event may only occur if
     the certificate's author has all the previous certificates in its DAG.")
   (xdoc::p
    "The second kind of event may only occur if
     the DAG has all the previous certificates.
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

(defruled backward-closed-p-when-init
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
           validator-init
           dag-closedp-when-emptyp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection backward-closed-p-of-next
  :short "Preservation of the invariant:
          if the invariant holds in a system state,
          it also holds in the next system state."
  :long
  (xdoc::topstring
   (xdoc::p
    "The only two kinds of events that extend DAGs are
     @('create-certificate') and @('store-certificate').
     For these two kinds of events,
     first we prove theorems saying that the added certificate
     has all the predecessors in the DAG,
     which is ensured by @(tsee create-certificate-possiblep)
     and @(tsee store-certificate-possiblep).
     Then we prove the main theorems,
     using rule @('dag-closedp-of-insert')
     to handle the addition of the certificate.")
   (xdoc::p
    "For the other four kinds of events,
     the proof is easy."))

  ;; create-certificate:

  (defruled certificate-previous-in-dag-p-when-create-certificate-possiblep
    (implies (and (create-certificate-possiblep cert systate)
                  (set::in (certificate->author cert)
                           (correct-addresses systate)))
             (certificate-previous-in-dag-p
              cert
              (validator-state->dag
               (get-validator-state (certificate->author cert) systate))))
    :enable (certificate-previous-in-dag-p
             create-certificate-possiblep
             create-certificate-author-possiblep
             create-certificate-signer-possiblep))

  (defruled backward-closed-p-of-create-certificate-next
    (implies (and (backward-closed-p systate)
                  (create-certificate-possiblep cert systate))
             (backward-closed-p
              (create-certificate-next cert systate)))
    :use (:instance lemma (cert (certificate-fix cert)))
    :prep-lemmas
    ((defruled lemma
       (implies (and (backward-closed-p systate)
                     (create-certificate-possiblep cert systate)
                     (certificatep cert))
                (backward-closed-p
                 (create-certificate-next cert systate)))
       :enable
       (backward-closed-p
        backward-closed-p-necc
        validator-state->dag-of-create-certificate-next
        dag-closedp-of-insert
        certificate-previous-in-dag-p-when-create-certificate-possiblep))))

  ;; receive-certificate:

  (defruled backward-closed-p-of-receive-certificate-next
    (implies (and (backward-closed-p systate)
                  (receive-certificate-possiblep msg systate))
             (backward-closed-p
              (receive-certificate-next msg systate)))
    :enable (backward-closed-p
             backward-closed-p-necc
             validator-state->dag-of-receive-certificate-next))

  ;; store-certificate:

  (defruled certificate-previous-in-dag-p-when-store-certificate-possiblep
    (implies (and (store-certificate-possiblep val cert systate)
                  (set::in val (correct-addresses systate)))
             (certificate-previous-in-dag-p
              cert
              (validator-state->dag
               (get-validator-state val systate))))
    :enable (certificate-previous-in-dag-p
             store-certificate-possiblep))

  (defruled backward-closed-p-of-store-certificate-next
    (implies (and (backward-closed-p systate)
                  (store-certificate-possiblep val cert systate))
             (backward-closed-p
              (store-certificate-next val cert systate)))
    :use (:instance lemma (val (address-fix val)))
    :prep-lemmas
    ((defruled lemma
       (implies (and (backward-closed-p systate)
                     (store-certificate-possiblep val cert systate)
                     (addressp val))
                (backward-closed-p
                 (store-certificate-next val cert systate)))
       :enable (backward-closed-p
                backward-closed-p-necc
                validator-state->dag-of-store-certificate-next
                dag-closedp-of-insert
                certificate-previous-in-dag-p-when-store-certificate-possiblep))))

  ;; advance-round:

  (defruled backward-closed-p-of-advance-round-next
    (implies (and (backward-closed-p systate)
                  (advance-round-possiblep val systate))
             (backward-closed-p
              (advance-round-next val systate)))
    :enable (backward-closed-p
             backward-closed-p-necc
             validator-state->dag-of-advance-round-next))

  ;; commit-anchors:

  (defruled backward-closed-p-of-commit-anchors-next
    (implies (and (backward-closed-p systate)
                  (commit-anchors-possiblep val systate))
             (backward-closed-p
              (commit-anchors-next val systate)))
    :enable (backward-closed-p
             backward-closed-p-necc
             validator-state->dag-of-commit-anchors-next))

  ;; timer-expires:

  (defruled backward-closed-p-of-timer-expires-next
    (implies (and (backward-closed-p systate)
                  (timer-expires-possiblep val systate))
             (backward-closed-p
              (timer-expires-next val systate)))
    :enable (backward-closed-p
             backward-closed-p-necc
             validator-state->dag-of-timer-expires-next))

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
    :disable ((:e tau-system))
    :enable (events-possiblep
             events-next
             backward-closed-p-of-event-next))

  (defruled backward-closed-p-when-reachable
    (implies (and (system-initp systate)
                  (events-possiblep events systate))
             (backward-closed-p (events-next events systate)))
    :disable ((:e tau-system))
    :enable (backward-closed-p-when-init
             backward-closed-p-of-events-next)))
