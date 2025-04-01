; AleoBFT Library
;
; Copyright (C) 2024 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOBFT-STATIC")

(include-book "invariant-addresses")
(include-book "operations-certificates-for-validators")

(include-book "std/util/define-sk" :dir :system)

(local (include-book "../library-extensions/oset-theorems"))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ invariant-same-certificates
  :parents (correctness)
  :short "Invariant that correct validators have the same set of certificates,
          if messages in the network are taken into account."
  :long
  (xdoc::topstring
   (xdoc::p
    "Validators have certificates in their DAGs and buffers,
     which may differ across validators.
     However, if we also take into account the messages in the network
     that are addressed to the validators,
     then validators have the same set of certificates.")
   (xdoc::p
    "Initially, DAGs, buffers, and the network are all empty,
     so the equality is trivial (it is the empty set for every validator).
     When a new certificate is created, there are two cases.
     If the author is a correct validator,
     the certificate is added to that validator's DAG,
     and messages with that certificate are created in the network
     for all the other correct validators:
     so all correct validators now have that certificate,
     in the DAG or in the network.
     If the author is a faulty validator,
     messages with that certificate are created in the network
     for all the correct validators:
     so again all correct validators now have that certificate,
     in the network.")
   (xdoc::p
    "This is an important invariant towards showing suitable agreement
     among (correct) validators in the protocol.
     It says that there is in fact one set of certificates,
     shared by all the correct validators.
     That can simplify some other proofs about the system,
     because one can pick any of these equivalent sets."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk same-certificates-p ((systate system-statep))
  :returns (yes/no booleanp)
  :short "Definition of the invariant:
          any two correct validators in the system have the same certificates."
  (forall (val1 val2)
          (implies (and (set::in val1 (correct-addresses systate))
                        (set::in val2 (correct-addresses systate)))
                   (equal (certificates-for-validator val1 systate)
                          (certificates-for-validator val2 systate)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled same-certificates-p-when-system-state-initp
  :short "Establishment of the invariant:
          the invariant holds on any initial system state."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is easy to prove, because DAGs, buffer, and network
     are initially empty.
     The set of certificate of every validator is thus the empty set."))
  (implies (system-state-initp systate)
           (same-certificates-p systate))
  :enable (system-state-initp
           same-certificates-p
           certificates-for-validator
           message-certificates-for-validator
           get-network-state
           correct-addresses
           validator-init-when-system-initp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled same-certificates-p-of-create-certificate-next
  :short "Preservation of the invariants by @('create-certificate') events."
  :long
  (xdoc::topstring
   (xdoc::p
    "This follows easily from
     @(tsee certificates-for-validator-of-create-certificate-next),
     which asserts the the only change in every validator
     is to add the same certificate,
     so if the sets were the same before, they stay the same."))
  (implies (and (same-certificates-p systate)
                (create-certificate-possiblep cert systate)
                (certificatep cert))
           (same-certificates-p (create-certificate-next cert systate)))
  :expand (same-certificates-p (create-certificate-next cert systate))
  :enable certificates-for-validator-of-create-certificate-next
  :use (:instance same-certificates-p-necc
                  (val1 (mv-nth
                         0
                         (same-certificates-p-witness
                          (create-certificate-next cert systate))))
                  (val2 (mv-nth
                         1
                         (same-certificates-p-witness
                          (create-certificate-next cert systate))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled same-certificates-p-of-receive-certificate-next
  :short "Preservation of the invariants by @('receive-certificate') events."
  :long
  (xdoc::topstring
   (xdoc::p
    "This follows easily from
     @(tsee certificates-for-validator-of-receive-certificate-next),
     which asserts the the only change in every validator
     is to add the same certificate,
     so if the sets were the same before, they stay the same."))
  (implies (and (same-certificates-p systate)
                (receive-certificate-possiblep msg systate))
           (same-certificates-p (receive-certificate-next msg systate)))
  :expand (same-certificates-p (receive-certificate-next msg systate))
  :enable certificates-for-validator-of-receive-certificate-next
  :use (:instance same-certificates-p-necc
                  (val1 (mv-nth
                         0
                         (same-certificates-p-witness
                          (receive-certificate-next msg systate))))
                  (val2 (mv-nth
                         1
                         (same-certificates-p-witness
                          (receive-certificate-next msg systate))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled same-certificates-p-of-store-certificate-next
  :short "Preservation of the invariants by @('store-certificate') events."
  :long
  (xdoc::topstring
   (xdoc::p
    "This follows easily from
     @(tsee certificates-for-validator-of-store-certificate-next),
     which asserts the the only change in every validator
     is to add the same certificate,
     so if the sets were the same before, they stay the same."))
  (implies (and (same-certificates-p systate)
                (store-certificate-possiblep cert val systate))
           (same-certificates-p (store-certificate-next cert val systate)))
  :expand (same-certificates-p (store-certificate-next cert val systate))
  :enable certificates-for-validator-of-store-certificate-next
  :use (:instance same-certificates-p-necc
                  (val1 (mv-nth
                         0
                         (same-certificates-p-witness
                          (store-certificate-next cert val systate))))
                  (val2 (mv-nth
                         1
                         (same-certificates-p-witness
                          (store-certificate-next cert val systate))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled same-certificates-p-of-advance-round-next
  :short "Preservation of the invariants by @('advance-round') events."
  :long
  (xdoc::topstring
   (xdoc::p
    "This follows easily from
     @(tsee certificates-for-validator-of-advance-round-next),
     which asserts the the only change in every validator
     is to add the same certificate,
     so if the sets were the same before, they stay the same."))
  (implies (and (same-certificates-p systate)
                (advance-round-possiblep val systate))
           (same-certificates-p (advance-round-next val systate)))
  :expand (same-certificates-p (advance-round-next val systate))
  :enable certificates-for-validator-of-advance-round-next
  :use (:instance same-certificates-p-necc
                  (val1 (mv-nth
                         0
                         (same-certificates-p-witness
                          (advance-round-next val systate))))
                  (val2 (mv-nth
                         1
                         (same-certificates-p-witness
                          (advance-round-next val systate))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled same-certificates-p-of-commit-anchors-next
  :short "Preservation of the invariants by @('commit-anchors') events."
  :long
  (xdoc::topstring
   (xdoc::p
    "This follows easily from
     @(tsee certificates-for-validator-of-commit-anchors-next),
     which asserts the the only change in every validator
     is to add the same certificate,
     so if the sets were the same before, they stay the same."))
  (implies (and (same-certificates-p systate)
                (commit-anchors-possiblep val systate))
           (same-certificates-p (commit-anchors-next val systate)))
  :expand (same-certificates-p (commit-anchors-next val systate))
  :enable certificates-for-validator-of-commit-anchors-next
  :use (:instance same-certificates-p-necc
                  (val1 (mv-nth
                         0
                         (same-certificates-p-witness
                          (commit-anchors-next val systate))))
                  (val2 (mv-nth
                         1
                         (same-certificates-p-witness
                          (commit-anchors-next val systate))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled same-certificates-p-of-timer-expires-next
  :short "Preservation of the invariants by @('timer-expires') events."
  :long
  (xdoc::topstring
   (xdoc::p
    "This follows easily from
     @(tsee certificates-for-validator-of-timer-expires-next),
     which asserts the the only change in every validator
     is to add the same certificate,
     so if the sets were the same before, they stay the same."))
  (implies (and (same-certificates-p systate)
                (timer-expires-possiblep val systate))
           (same-certificates-p (timer-expires-next val systate)))
  :expand (same-certificates-p (timer-expires-next val systate))
  :enable certificates-for-validator-of-timer-expires-next
  :use (:instance same-certificates-p-necc
                  (val1 (mv-nth
                         0
                         (same-certificates-p-witness
                          (timer-expires-next val systate))))
                  (val2 (mv-nth
                         1
                         (same-certificates-p-witness
                          (timer-expires-next val systate))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled same-certificates-p-of-event-next
  :short "Preservation of the invariant by all events."
  :long
  (xdoc::topstring
   (xdoc::p
    "This follows from the theorems about the various kinds of events."))
  (implies (and (same-certificates-p systate)
                (event-possiblep event systate))
           (same-certificates-p (event-next event systate)))
  :enable (event-possiblep
           event-next))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled same-certificates-p-of-events-next
  :short "Preservation of the invariant by every sequence of events."
  (implies (and (system-statep systate)
                (same-certificates-p systate)
                (events-possiblep events systate))
           (same-certificates-p (events-next events systate)))
  :induct t
  :disable ((:e tau-system))
  :enable (events-next
           events-possiblep
           same-certificates-p-of-event-next))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled same-certificates-p-when-reachable
  :short "The invariant holds in every reachable state."
  :long
  (xdoc::topstring
   (xdoc::p
    "Reachable states are characterized by an initial state and
     a sequence of possible events from that initial state."))
  (implies (and (system-statep systate)
                (system-state-initp systate)
                (events-possiblep events systate))
           (same-certificates-p (events-next events systate)))
  :disable ((:e tau-system))
  :enable (same-certificates-p-when-system-state-initp
           same-certificates-p-of-events-next))
