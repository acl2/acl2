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

(include-book "invariant-quorum")
(include-book "invariant-same-certificates")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ invariant-signers-are-quorum
  :parents (correctness)
  :short "Invariant that the signers of every certificate form a quorum."
  :long
  (xdoc::topstring
   (xdoc::p
    "New certificates are created via @('create-certificate') events,
     whose preconditions require that
     the number of signers of the certificate
     is equal to the quorum number."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk system-signers-are-quorum-p ((systate system-statep))
  :returns (yes/no booleanp)
  :short "Definition of the invariant:
          the number of signers of every certificate of every validator
          is equal to the quorum number."
  (forall (val cert)
          (implies (and (set::in val
                                 (correct-addresses systate))
                        (set::in cert
                                 (certificates-for-validator val systate)))
                   (equal (set::cardinality (certificate->signers cert))
                          (quorum systate)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule system-signers-are-quorum-p-when-system-state-initp
  :short "Establishment of the invariant:
          the invariant holds on any initial system state."
  :long
  (xdoc::topstring
   (xdoc::p
    "Initially, the set of certificates of validators is empty."))
  (implies (system-state-initp systate)
           (system-signers-are-quorum-p systate))
  :enable (system-state-initp
           system-signers-are-quorum-p
           certificates-for-validator
           get-network-state
           validator-init))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection system-signers-are-quorum-p-of-create-certificate-next
  :short "Preservation of the invariant by @('create-certificate') event."
  :long
  (xdoc::topstring
   (xdoc::p
    "The key point is that if @(tsee create-certificate-possiblep) holds,
     the endorsers must be one less than the quorum,
     and the author is not endorser.
     Thus, putting together author and endorser, which are the signers,
     we get a quorum.
     We prove this as a separate theorem,
     used in the proof of the theorem about the event,
     which involves considering all certificates, old and new
     (which the prover handles automatically)."))

  (defrule signers-are-quorum-when-create-certificate-possiblep
    (implies (create-certificate-possiblep cert systate)
             (equal (set::cardinality (certificate->signers cert))
                    (quorum systate)))
    :enable (create-certificate-possiblep
             certificate->signers
             set::expensive-rules))

  (defrule system-signers-are-quorum-p-of-create-certificate-next
    (implies (and (system-signers-are-quorum-p systate)
                  (create-certificate-possiblep cert systate)
                  (certificatep cert))
             (system-signers-are-quorum-p
              (create-certificate-next cert systate)))
    :expand (system-signers-are-quorum-p
             (create-certificate-next cert systate))
    :enable system-signers-are-quorum-p-necc))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule system-signers-are-quorum-p-of-receive-certificate-next
  :short "Preservation of the invariant by @('receive-certificate') events."
  :long
  (xdoc::topstring
   (xdoc::p
    "This kind of event does not introduce new certificates,
     so the proof is easy."))
  (implies (and (system-signers-are-quorum-p systate)
                (receive-certificate-possiblep msg systate))
           (system-signers-are-quorum-p
            (receive-certificate-next msg systate)))
  :expand (system-signers-are-quorum-p
           (receive-certificate-next msg systate))
  :enable system-signers-are-quorum-p-necc)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule system-signers-are-quorum-p-of-store-certificate-next
  :short "Preservation of the invariant by @('store-certificate') events."
  :long
  (xdoc::topstring
   (xdoc::p
    "This kind of event does not introduce new certificates,
     so the proof is easy."))
  (implies (and (system-signers-are-quorum-p systate)
                (store-certificate-possiblep cert val systate))
           (system-signers-are-quorum-p
            (store-certificate-next cert val systate)))
  :expand (system-signers-are-quorum-p
           (store-certificate-next cert val systate))
  :enable system-signers-are-quorum-p-necc)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule system-signers-are-quorum-p-of-advance-round-next
  :short "Preservation of the invariant by @('advance-round') events."
  :long
  (xdoc::topstring
   (xdoc::p
    "This kind of event does not introduce new certificate,s
     so the proof is easy."))
  (implies (and (system-signers-are-quorum-p systate)
                (advance-round-possiblep val systate))
           (system-signers-are-quorum-p
            (advance-round-next val systate)))
  :expand (system-signers-are-quorum-p
           (advance-round-next val systate))
  :enable system-signers-are-quorum-p-necc)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule system-signers-are-quorum-p-of-commit-anchors-next
  :short "Preservation of the invariant by @('commit-anchors') events."
  :long
  (xdoc::topstring
   (xdoc::p
    "This kind of event does not introduce new certificates,
     so the proof is easy."))
  (implies (and (system-signers-are-quorum-p systate)
                (commit-anchors-possiblep val systate))
           (system-signers-are-quorum-p
            (commit-anchors-next val systate)))
  :expand (system-signers-are-quorum-p
           (commit-anchors-next val systate))
  :enable system-signers-are-quorum-p-necc)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule system-signers-are-quorum-p-of-timer-expires-next
  :short "Preservation of the invariant by @('timer-expires') events."
  :long
  (xdoc::topstring
   (xdoc::p
    "This kind of event does not introduce new certificates,
     so the proof is easy."))
  (implies (and (system-signers-are-quorum-p systate)
                (timer-expires-possiblep val systate))
           (system-signers-are-quorum-p
            (timer-expires-next val systate)))
  :expand (system-signers-are-quorum-p
           (timer-expires-next val systate))
  :enable system-signers-are-quorum-p-necc)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule system-signers-are-quorum-p-of-event-next
  :short "Preservation of the invariant by all events."
  :long
  (xdoc::topstring
   (xdoc::p
    "This follows from the theorems about the various kinds of events."))
  (implies (and (system-signers-are-quorum-p systate)
                (event-possiblep val systate))
           (system-signers-are-quorum-p
            (event-next val systate)))
  :enable (event-possiblep
           event-next))
