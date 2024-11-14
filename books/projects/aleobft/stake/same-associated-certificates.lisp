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

(include-book "associated-certificates")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ same-associated-certificates
  :parents (correctness)
  :short "Invariant that correct validators have
          the same associated certificates."
  :long
  (xdoc::topstring
   (xdoc::p
    "The notion of associated certificates
     is formalized in @(see associated-certificates).
     Each validator has certificates in its DAG and buffer,
     but there may be also messages in the network addresses to the validator,
     which can therefore be eventually received by the validator:
     all of these certificates are (actually or potentially)
     associated to the validator.")
   (xdoc::p
    "An invariant of the protocol is that
     validators always have the same set of associated certificates.
     Their DAGs and buffers may have (together) different certificates,
     but there will be messages in transit that ``fill the gap''.
     This is a consequence of our reliable broadcast model,
     in which a certificate's author broadcasts the certificate
     to all correct validators, except possibly itself if correct
     (because in that case the certificate is immediately added to the DAG).
     DAGs and buffers may also individually differ across validators,
     but their union, together with the messages in the network,
     are always the same.")
   (xdoc::p
    "Initially there are no certificates,
     so every validator has the empty set associated to it.
     The only kind of event that changes the set is @('create'),
     but as already discussed the certificate is added
     to every validator's set of associated certificates.
     Other events only move certificates
     (from network to buffer, or from buffer to DAG),
     or do not touch them at all."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk same-associated-certs-p ((systate system-statep))
  :returns (yes/no booleanp)
  :short "Definition of the invariant:
          any two correct validators in the system have
          the same set of associated certificates."
  (forall (val1 val2)
          (implies (and (set::in val1 (correct-addresses systate))
                        (set::in val2 (correct-addresses systate)))
                   (equal (associated-certs val1 systate)
                          (associated-certs val2 systate))))

  ///

  (fty::deffixequiv-sk same-associated-certs-p
    :args ((systate system-statep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled same-associated-certs-p-when-init
  :short "Establishment of the invariant:
          the invariant holds in any initial system state."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is easy to prove,
     because DAGs, buffer, and network are initially empty.
     The set of associated certificates of every validator is the empty set.")
   (xdoc::p
    "Since we already proved in @(tsee associated-certs-when-init)
     that the set is empty in the initial state,
     that rule suffices to prove this theorem."))
  (implies (system-initp systate)
           (same-associated-certs-p systate))
  :enable (same-associated-certs-p
           associated-certs-when-init))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection same-associated-certs-p-of-next
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
     given the proofs in @(tsee associated-certs-of-next).
     In particular, the theorem
     @('associated-certs-of-create-next')
     tells us that the new set of associated certificates
     is the old one plus the new certificate for every validator,
     not just the author:
     so all sets change in the same way.
     The other theorems there say that the sets do not change."))

  (defruled same-associated-certs-p-of-create-next
    (implies (same-associated-certs-p systate)
             (same-associated-certs-p (create-next cert systate)))
    :enable (associated-certs-of-create-next
             same-associated-certs-p)
    :use (:instance same-associated-certs-p-necc
                    (val1 (mv-nth 0 (same-associated-certs-p-witness
                                     (create-next cert systate))))
                    (val2 (mv-nth 1 (same-associated-certs-p-witness
                                     (create-next cert systate))))))

  (defruled same-associated-certs-p-of-receive-next
    (implies (and (same-associated-certs-p systate)
                  (receive-possiblep msg systate))
             (same-associated-certs-p (receive-next msg systate)))
    :enable (associated-certs-of-receive-next
             same-associated-certs-p)
    :use (:instance same-associated-certs-p-necc
                    (val1 (mv-nth 0 (same-associated-certs-p-witness
                                     (receive-next msg systate))))
                    (val2 (mv-nth 1 (same-associated-certs-p-witness
                                     (receive-next msg systate))))))

  (defruled same-associated-certs-p-of-store-next
    (implies (and (same-associated-certs-p systate)
                  (store-possiblep cert val systate))
             (same-associated-certs-p (store-next cert val systate)))
    :enable (associated-certs-of-store-next
             same-associated-certs-p)
    :use (:instance same-associated-certs-p-necc
                    (val1 (mv-nth 0 (same-associated-certs-p-witness
                                     (store-next cert val systate))))
                    (val2 (mv-nth 1 (same-associated-certs-p-witness
                                     (store-next cert val systate))))))

  (defruled same-associated-certs-p-of-advance-next
    (implies (and (same-associated-certs-p systate)
                  (advance-possiblep val systate))
             (same-associated-certs-p (advance-next val systate)))
    :enable (associated-certs-of-advance-next
             same-associated-certs-p)
    :use (:instance same-associated-certs-p-necc
                    (val1 (mv-nth 0 (same-associated-certs-p-witness
                                     (advance-next val systate))))
                    (val2 (mv-nth 1 (same-associated-certs-p-witness
                                     (advance-next val systate))))))

  (defruled same-associated-certs-p-of-commit-next
    (implies (and (same-associated-certs-p systate)
                  (commit-possiblep val systate))
             (same-associated-certs-p (commit-next val systate)))
    :enable (associated-certs-of-commit-next
             same-associated-certs-p)
    :use (:instance same-associated-certs-p-necc
                    (val1 (mv-nth 0 (same-associated-certs-p-witness
                                     (commit-next val systate))))
                    (val2 (mv-nth 1 (same-associated-certs-p-witness
                                     (commit-next val systate))))))

  (defruled same-associated-certs-p-of-timeout-next
    (implies (and (same-associated-certs-p systate)
                  (timeout-possiblep val systate))
             (same-associated-certs-p (timeout-next val systate)))
    :enable (associated-certs-of-timeout-next
             same-associated-certs-p)
    :use (:instance same-associated-certs-p-necc
                    (val1 (mv-nth 0 (same-associated-certs-p-witness
                                     (timeout-next val systate))))
                    (val2 (mv-nth 1 (same-associated-certs-p-witness
                                     (timeout-next val systate))))))

  (defruled same-associated-certs-p-of-event-next
    (implies (and (same-associated-certs-p systate)
                  (event-possiblep event systate))
             (same-associated-certs-p (event-next event systate)))
    :enable (event-possiblep
             event-next)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection same-associated-certs-p-always
  :short "The invariant holds in every state
          reachable from an initial state via a sequence of events."

  (defruled same-associated-certs-p-of-events-next
    (implies (and (same-associated-certs-p systate)
                  (events-possiblep events systate))
             (same-associated-certs-p (events-next events systate)))
    :induct t
    :enable (events-possiblep
             events-next))

  (defruled same-associated-certs-p-when-reachable
    (implies (and (system-initp systate)
                  (events-possiblep events systate))
             (same-associated-certs-p (events-next events systate)))))
