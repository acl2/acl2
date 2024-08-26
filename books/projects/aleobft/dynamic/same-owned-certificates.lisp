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

(include-book "owned-certificates")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ same-owned-certificates
  :parents (correctness)
  :short "Invariant that correct validators own the same certificates."
  :long
  (xdoc::topstring
   (xdoc::p
    "The notion of `owned certificates'
     is formalized in @(see owned-certificates).
     Each validator has certificates in its DAG and buffer,
     but there may be also messages in the network addresses to the validator,
     which can therefore be eventually received by the validator:
     all of these certificates are (actually or potentially) owned
     by the validator.")
   (xdoc::p
    "An important invariant of the protocol is that
     validators always have the same set of owned certificates.
     Their DAGs and buffers may have (together) different certificates,
     but there will be messages in transit that ``fill the gap''.
     This is a consequence of our reliable broadcast model,
     in which a certificate's author broadcasts the certificate
     to all correct validators, except possibly itself if correct
     (because in that case the certificate is immediately added to the DAG).")
   (xdoc::p
    "Initially there are no certificates,
     so every validator owns the empty set.
     The only kind of event that changes the set is @('create-certificate'),
     but as already discussed the certificate is added
     to every validator's set of owned certificates.
     Other events only move certificates
     (from network to buffer, or from buffer to DAG),
     or do not touch them at all."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk same-owned-certificates-p ((systate system-statep))
  :returns (yes/no booleanp)
  :short "Definition of the invariant:
          any two correct validators in the system own the same certificates."
  (forall (val1 val2)
          (implies (and (set::in val1 (correct-addresses systate))
                        (set::in val2 (correct-addresses systate)))
                   (equal (certificates-owned-by val1 systate)
                          (certificates-owned-by val2 systate)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled same-owned-certificates-p-when-init
  :short "Establishment of the invariant:
          the invariant holds on any initial system state."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is easy to prove, because DAGs, buffer, and network
     are initially empty.
     The set of certificate of every validator is thus the empty set.")
   (xdoc::p
    "Since we already proved in @(tsee certificates-owned-by-when-init)
     that the set is empty in the initial state,
     that rule suffices to prove this theorem."))
  (implies (system-initp systate)
           (same-owned-certificates-p systate))
  :enable (same-owned-certificates-p
           certificates-owned-by-when-init))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection same-owned-certificates-p-of-next
  :short "Preservation of the invariant:
          if the invariant holds in a system state,
          it also holds in the next system state."
  :long
  (xdoc::topstring
   (xdoc::p
    "We prove this for every kind of event,
     and then for a generic event.")
   (xdoc::p
    "The proofs of these theorems are easy,
     given the proofs in @(tsee certificates-owned-by-of-next).
     In particular, the theorem
     @('certificates-owned-by-of-create-certificate-next')
     tells us that the new set of owned certificates
     is the old one plus the new certificate for every validator,
     not just the author:
     so all sets change in the same way.
     The other theorems there say that the sets do not change."))

  (defruled same-owned-certificates-p-of-create-certificate-next
    (implies (same-owned-certificates-p systate)
             (same-owned-certificates-p
              (create-certificate-next cert systate)))
    :enable certificates-owned-by-of-create-certificate-next
    :expand (same-owned-certificates-p (create-certificate-next cert systate))
    :use (:instance same-owned-certificates-p-necc
                    (val1 (mv-nth
                           0
                           (same-owned-certificates-p-witness
                            (create-certificate-next cert systate))))
                    (val2 (mv-nth
                           1
                           (same-owned-certificates-p-witness
                            (create-certificate-next cert systate))))))

  (defruled same-owned-certificates-p-of-receive-certificate-next
    (implies (and (same-owned-certificates-p systate)
                  (receive-certificate-possiblep msg systate))
             (same-owned-certificates-p
              (receive-certificate-next msg systate)))
    :enable certificates-owned-by-of-receive-certificate-next
    :expand (same-owned-certificates-p (receive-certificate-next msg systate))
    :use (:instance same-owned-certificates-p-necc
                    (val1 (mv-nth
                           0
                           (same-owned-certificates-p-witness
                            (receive-certificate-next msg systate))))
                    (val2 (mv-nth
                           1
                           (same-owned-certificates-p-witness
                            (receive-certificate-next msg systate))))))

  (defruled same-owned-certificates-p-of-store-certificate-next
    (implies (and (same-owned-certificates-p systate)
                  (store-certificate-possiblep cert val systate))
             (same-owned-certificates-p
              (store-certificate-next cert val systate)))
    :enable certificates-owned-by-of-store-certificate-next
    :expand (same-owned-certificates-p (store-certificate-next cert val systate))
    :use (:instance same-owned-certificates-p-necc
                    (val1 (mv-nth
                           0
                           (same-owned-certificates-p-witness
                            (store-certificate-next cert val systate))))
                    (val2 (mv-nth
                           1
                           (same-owned-certificates-p-witness
                            (store-certificate-next cert val systate))))))

  (defruled same-owned-certificates-p-of-advance-round-next
    (implies (and (same-owned-certificates-p systate)
                  (advance-round-possiblep val systate))
             (same-owned-certificates-p
              (advance-round-next val systate)))
    :enable certificates-owned-by-of-advance-round-next
    :expand (same-owned-certificates-p (advance-round-next val systate))
    :use (:instance same-owned-certificates-p-necc
                    (val1 (mv-nth
                           0
                           (same-owned-certificates-p-witness
                            (advance-round-next val systate))))
                    (val2 (mv-nth
                           1
                           (same-owned-certificates-p-witness
                            (advance-round-next val systate))))))

  (defruled same-owned-certificates-p-of-commit-anchors-next
    (implies (and (same-owned-certificates-p systate)
                  (commit-anchors-possiblep val systate))
             (same-owned-certificates-p
              (commit-anchors-next val systate)))
    :enable certificates-owned-by-of-commit-anchors-next
    :expand (same-owned-certificates-p (commit-anchors-next val systate))
    :use (:instance same-owned-certificates-p-necc
                    (val1 (mv-nth
                           0
                           (same-owned-certificates-p-witness
                            (commit-anchors-next val systate))))
                    (val2 (mv-nth
                           1
                           (same-owned-certificates-p-witness
                            (commit-anchors-next val systate))))))

  (defruled same-owned-certificates-p-of-timer-expires-next
    (implies (and (same-owned-certificates-p systate)
                  (timer-expires-possiblep val systate))
             (same-owned-certificates-p
              (timer-expires-next val systate)))
    :enable certificates-owned-by-of-timer-expires-next
    :expand (same-owned-certificates-p (timer-expires-next val systate))
    :use (:instance same-owned-certificates-p-necc
                    (val1 (mv-nth
                           0
                           (same-owned-certificates-p-witness
                            (timer-expires-next val systate))))
                    (val2 (mv-nth
                           1
                           (same-owned-certificates-p-witness
                            (timer-expires-next val systate))))))

  (defruled same-owned-certificates-p-of-event-next
    (implies (and (same-owned-certificates-p systate)
                  (event-possiblep event systate))
             (same-owned-certificates-p (event-next event systate)))
    :enable (event-possiblep
             event-next)))
