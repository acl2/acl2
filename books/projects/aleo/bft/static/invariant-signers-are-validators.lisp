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

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ invariant-signers-are-validators
  :parents (correctness)
  :short "Invariant that the signers of every certificate
          are validators in the system."
  :long
  (xdoc::topstring
   (xdoc::p
    "This follows from the conditions checked
     by @(tsee create-certificate-possiblep);
     the @('create-certificate') events are the only ones
     that generate new certificates,
     and that could thus possibly break the invariant
     (which they do not break).")
   (xdoc::p
    "This builds upon the "
    (xdoc::seetopic "invariant-same-certificates"
                    "invariant that all validators have the same certificates")
    ", which establishes that @(tsee certificates-for-validator)
     returns the same set for all (correct) validators."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define certificate-signers-are-validators-p ((cert certificatep)
                                              (systate system-statep))
  :short "Check that the signers of a certificate
          are validators in the system."
  :long
  (xdoc::topstring
   (xdoc::p
    "The signers are both the author and the endorsers.
     These are not necessarily correct validators;
     they could be faulty ones."))
  :returns (yes/no booleanp)
  (set::subset (certificate->signers cert)
               (all-addresses systate)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk system-signers-are-validators-p ((systate system-statep))
  :returns (yes/no booleanp)
  :short "Definition of the invariant:
          the signers of every certificate of every validator
          are validators in the system."
  (forall (val cert)
          (implies (and (set::in val
                                 (correct-addresses systate))
                        (set::in cert
                                 (certificates-for-validator val systate)))
                   (certificate-signers-are-validators-p cert systate))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled system-signers-are-validators-p-when-system-state-initp
  :short "Establishment of the invariant:
          the invariant holds on any initial system state."
  :long
  (xdoc::topstring
   (xdoc::p
    "Initially, the set of certificates of validators is empty."))
  (implies (system-state-initp systate)
           (system-signers-are-validators-p systate))
  :enable (system-state-initp
           system-signers-are-validators-p
           certificates-for-validator
           get-network-state
           validator-init-when-system-initp
           validator-init
           in-of-message-certificates-for-validator))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled system-signers-are-validators-p-of-create-certificate-next
  :short "Preservation of the invariant by @('create-certificate') events."
  :long
  (xdoc::topstring
   (xdoc::p
    "This relies on
     @(tsee certificates-for-validator-of-create-certificate-next),
     which says how this kind of events modifies the set of certificates.
     The new certificate is checked in @(tsee create-certificate-possiblep)
     to have author and endorsers be validators in the system."))
  (implies (and (system-signers-are-validators-p systate)
                (create-certificate-possiblep cert systate)
                (certificatep cert))
           (system-signers-are-validators-p
            (create-certificate-next cert systate)))
  :expand (system-signers-are-validators-p
           (create-certificate-next cert systate))
  :enable (certificate-signers-are-validators-p
           create-certificate-possiblep
           certificate->signers
           certificates-for-validator-of-create-certificate-next)
  :use (:instance system-signers-are-validators-p-necc
                  (val (mv-nth 0
                               (system-signers-are-validators-p-witness
                                (create-certificate-next cert systate))))
                  (cert (mv-nth 1
                                (system-signers-are-validators-p-witness
                                 (create-certificate-next cert systate))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled system-signers-are-validators-p-of-receive-certificate-next
  :short "Preservation of the invariant by @('receive-certificate') events."
  :long
  (xdoc::topstring
   (xdoc::p
    "This relies on
     @(tsee certificates-for-validator-of-receive-certificate-next),
     which says that this kind of events
     does not modify the set of certificates."))
  (implies (and (system-signers-are-validators-p systate)
                (receive-certificate-possiblep msg systate))
           (system-signers-are-validators-p
            (receive-certificate-next msg systate)))
  :expand (system-signers-are-validators-p
           (receive-certificate-next msg systate))
  :enable (certificate-signers-are-validators-p
           certificates-for-validator-of-receive-certificate-next)
  :use (:instance system-signers-are-validators-p-necc
                  (val (mv-nth 0
                               (system-signers-are-validators-p-witness
                                (receive-certificate-next msg systate))))
                  (cert (mv-nth 1
                                (system-signers-are-validators-p-witness
                                 (receive-certificate-next msg systate))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled system-signers-are-validators-p-of-store-certificate-next
  :short "Preservation of the invariant by @('store-certificate') events."
  :long
  (xdoc::topstring
   (xdoc::p
    "This relies on
     @(tsee certificates-for-validator-of-store-certificate-next),
     which says that this kind of events
     does not modify the set of certificates."))
  (implies (and (system-signers-are-validators-p systate)
                (store-certificate-possiblep cert val systate))
           (system-signers-are-validators-p
            (store-certificate-next cert val systate)))
  :expand (system-signers-are-validators-p
           (store-certificate-next cert val systate))
  :enable (certificate-signers-are-validators-p
           certificates-for-validator-of-store-certificate-next)
  :use (:instance system-signers-are-validators-p-necc
                  (val (mv-nth 0
                               (system-signers-are-validators-p-witness
                                (store-certificate-next cert val systate))))
                  (cert (mv-nth 1
                                (system-signers-are-validators-p-witness
                                 (store-certificate-next cert val systate))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled system-signers-are-validators-p-of-advance-round-next
  :short "Preservation of the invariant by @('advance-round') events."
  :long
  (xdoc::topstring
   (xdoc::p
    "This relies on
     @(tsee certificates-for-validator-of-advance-round-next),
     which says that this kind of events
     does not modify the set of certificates."))
  (implies (and (system-signers-are-validators-p systate)
                (advance-round-possiblep val systate))
           (system-signers-are-validators-p
            (advance-round-next val systate)))
  :expand (system-signers-are-validators-p
           (advance-round-next val systate))
  :enable (certificate-signers-are-validators-p
           certificates-for-validator-of-advance-round-next)
  :use (:instance system-signers-are-validators-p-necc
                  (val (mv-nth 0
                               (system-signers-are-validators-p-witness
                                (advance-round-next val systate))))
                  (cert (mv-nth 1
                                (system-signers-are-validators-p-witness
                                 (advance-round-next val systate))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled system-signers-are-validators-p-of-commit-anchors-next
  :short "Preservation of the invariant by @('commit-anchors') events."
  :long
  (xdoc::topstring
   (xdoc::p
    "This relies on
     @(tsee certificates-for-validator-of-commit-anchors-next),
     which says that this kind of events
     does not modify the set of certificates."))
  (implies (and (system-signers-are-validators-p systate)
                (commit-anchors-possiblep val systate))
           (system-signers-are-validators-p
            (commit-anchors-next val systate)))
  :expand (system-signers-are-validators-p
           (commit-anchors-next val systate))
  :enable (certificate-signers-are-validators-p
           certificates-for-validator-of-commit-anchors-next)
  :use (:instance system-signers-are-validators-p-necc
                  (val (mv-nth 0
                               (system-signers-are-validators-p-witness
                                (commit-anchors-next val systate))))
                  (cert (mv-nth 1
                                (system-signers-are-validators-p-witness
                                 (commit-anchors-next val systate))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled system-signers-are-validators-p-of-timer-expires-next
  :short "Preservation of the invariant by @('timer-expires') events."
  :long
  (xdoc::topstring
   (xdoc::p
    "This relies on
     @(tsee certificates-for-validator-of-timer-expires-next),
     which says that this kind of events
     does not modify the set of certificates."))
  (implies (and (system-signers-are-validators-p systate)
                (timer-expires-possiblep val systate))
           (system-signers-are-validators-p
            (timer-expires-next val systate)))
  :expand (system-signers-are-validators-p
           (timer-expires-next val systate))
  :enable (certificate-signers-are-validators-p
           certificates-for-validator-of-timer-expires-next)
  :use (:instance system-signers-are-validators-p-necc
                  (val (mv-nth 0
                               (system-signers-are-validators-p-witness
                                (timer-expires-next val systate))))
                  (cert (mv-nth 1
                                (system-signers-are-validators-p-witness
                                 (timer-expires-next val systate))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled system-signers-are-validators-p-of-event-next
  :short "Preservation of the invariant by all events."
  :long
  (xdoc::topstring
   (xdoc::p
    "This follows from the theorems about the various kinds of events."))
  (implies (and (system-signers-are-validators-p systate)
                (event-possiblep event systate))
           (system-signers-are-validators-p (event-next event systate)))
  :enable (event-possiblep
           event-next))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled system-signers-are-validators-p-of-events-next
  :short "Preservation of the invariant by every sequence of events."
  (implies (and (system-statep systate)
                (system-signers-are-validators-p systate)
                (events-possiblep events systate))
           (system-signers-are-validators-p (events-next events systate)))
  :induct t
  :disable ((:e tau-system))
  :enable (events-next
           events-possiblep
           system-signers-are-validators-p-of-event-next))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled system-signers-are-validators-p-when-reachable
  :short "The invariant holds in every reachable state."
  :long
  (xdoc::topstring
   (xdoc::p
    "Reachable states are characterized by an initial state and
     a sequence of possible events from that initial state."))
  (implies (and (system-statep systate)
                (system-state-initp systate)
                (events-possiblep events systate))
           (system-signers-are-validators-p (events-next events systate)))
  :disable ((:e tau-system))
  :enable (system-signers-are-validators-p-when-system-state-initp
           system-signers-are-validators-p-of-events-next))
