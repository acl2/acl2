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

(defxdoc+ invariant-previous-are-quorum
  :parents (correctness)
  :short "Invariant that the previous certificates of every certificate
          form a quorum if the round is not 1, and there are none in round 1."
  :long
  (xdoc::topstring
   (xdoc::p
    "When a new certificate is created via a @('create-certificate') event,
     that event's preconditions require that the certificate includes
     a quorum of references to certificates in the previous round,
     unless the certificate round is 1,
     in which case there must be no references.")
   (xdoc::p
    "The names for this invariant,
     namely this XDOC topic,
     as well as the function and theorem names,
     just mention the quorum requirement, for brevity,
     and because that is the ``normal'' requirement.
     The requirement for round 1 is a special case,
     but it is part of this invariant."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk system-previous-are-quorum-p ((systate system-statep))
  :returns (yes/no booleanp)
  :short "Definition of the invariant:
          the number of previous certificate references
          of every certificate of every validator
          is equal to the quorum number if the round number is not 1,
          or to 0 if the round number is 1."
  (forall (val cert)
          (implies (and (set::in val
                                 (correct-addresses systate))
                        (set::in cert
                                 (certificates-for-validator val systate)))
                   (equal (set::cardinality (certificate->previous cert))
                          (if (equal (certificate->round cert) 1)
                              0
                            (quorum systate))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled system-previous-are-quorum-p-when-system-state-initp
  :short "Establishment of the invariant:
          the invariant holds on any initial system state."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is easy to prove, because initially there are no certificates."))
  (implies (system-state-initp systate)
           (system-previous-are-quorum-p systate))
  :enable (system-state-initp
           system-previous-are-quorum-p
           certificates-for-validator
           get-network-state
           validator-init-when-system-initp
           validator-init
           in-of-message-certificates-for-validator))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection system-previous-are-quorum-p-of-create-certificate-next
  :short "Preservation of the invariant by @('create-certificate') events."
  :long
  (xdoc::topstring
   (xdoc::p
    "The key point is that if @(tsee create-certificate-possiblep) holds,
     the previous certificate references
     must be exactly in the number required by the invariant.
     We prove this as a separate theorem,
     used in the proof of the theorem about the event,
     which involves considering all certificates, old and new
     (which the prover handles automatically)."))

  (defruled previous-are-quorum-when-create-certificate-possiblep
    (implies (create-certificate-possiblep cert systate)
             (equal (set::cardinality (certificate->previous cert))
                    (if (equal (certificate->round cert) 1)
                        0
                      (quorum systate))))
    :enable (create-certificate-possiblep
             set::expensive-rules))

  (defruled system-previous-are-quorum-p-of-create-certificate-next
    (implies (and (system-previous-are-quorum-p systate)
                  (create-certificate-possiblep cert systate)
                  (certificatep cert))
             (system-previous-are-quorum-p
              (create-certificate-next cert systate)))
    :expand (system-previous-are-quorum-p
             (create-certificate-next cert systate))
    :enable (system-previous-are-quorum-p-necc
             certificates-for-validator-of-create-certificate-next
             previous-are-quorum-when-create-certificate-possiblep)
    :disable set::cardinality-zero-emptyp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled system-previous-are-quorum-p-of-receive-certificate-next
  :short "Preservation of the invariant by @('receive-certificate') events."
  :long
  (xdoc::topstring
   (xdoc::p
    "This kind of event does not introduce new certificates,
     so the proof is easy."))
  (implies (and (system-previous-are-quorum-p systate)
                (receive-certificate-possiblep msg systate))
           (system-previous-are-quorum-p
            (receive-certificate-next msg systate)))
  :expand (system-previous-are-quorum-p
           (receive-certificate-next msg systate))
  :enable (system-previous-are-quorum-p-necc
           certificates-for-validator-of-receive-certificate-next))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled system-previous-are-quorum-p-of-store-certificate-next
  :short "Preservation of the invariant by @('store-certificate') events."
  :long
  (xdoc::topstring
   (xdoc::p
    "This kind of event does not introduce new certificates,
     so the proof is easy."))
  (implies (and (system-previous-are-quorum-p systate)
                (store-certificate-possiblep cert val systate))
           (system-previous-are-quorum-p
            (store-certificate-next cert val systate)))
  :expand (system-previous-are-quorum-p
           (store-certificate-next cert val systate))
  :enable (system-previous-are-quorum-p-necc
           certificates-for-validator-of-store-certificate-next))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled system-previous-are-quorum-p-of-advance-round-next
  :short "Preservation of the invariant by @('advance-round') events."
  :long
  (xdoc::topstring
   (xdoc::p
    "This kind of event does not introduce new certificate,s
     so the proof is easy."))
  (implies (and (system-previous-are-quorum-p systate)
                (advance-round-possiblep val systate))
           (system-previous-are-quorum-p
            (advance-round-next val systate)))
  :expand (system-previous-are-quorum-p
           (advance-round-next val systate))
  :enable (system-previous-are-quorum-p-necc
           certificates-for-validator-of-advance-round-next))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled system-previous-are-quorum-p-of-commit-anchors-next
  :short "Preservation of the invariant by @('commit-anchors') events."
  :long
  (xdoc::topstring
   (xdoc::p
    "This kind of event does not introduce new certificates,
     so the proof is easy."))
  (implies (and (system-previous-are-quorum-p systate)
                (commit-anchors-possiblep val systate))
           (system-previous-are-quorum-p
            (commit-anchors-next val systate)))
  :expand (system-previous-are-quorum-p
           (commit-anchors-next val systate))
  :enable (system-previous-are-quorum-p-necc
           certificates-for-validator-of-commit-anchors-next))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled system-previous-are-quorum-p-of-timer-expires-next
  :short "Preservation of the invariant by @('timer-expires') events."
  :long
  (xdoc::topstring
   (xdoc::p
    "This kind of event does not introduce new certificates,
     so the proof is easy."))
  (implies (and (system-previous-are-quorum-p systate)
                (timer-expires-possiblep val systate))
           (system-previous-are-quorum-p
            (timer-expires-next val systate)))
  :expand (system-previous-are-quorum-p
           (timer-expires-next val systate))
  :enable (system-previous-are-quorum-p-necc
           certificates-for-validator-of-timer-expires-next))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled system-previous-are-quorum-p-of-event-next
  :short "Preservation of the invariant by all events."
  :long
  (xdoc::topstring
   (xdoc::p
    "This follows from the theorems about the various kinds of events."))
  (implies (and (system-previous-are-quorum-p systate)
                (event-possiblep event systate))
           (system-previous-are-quorum-p
            (event-next event systate)))
  :enable (event-possiblep
           event-next))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled system-previous-are-quorum-p-of-events-next
  :short "Preservation of the invariant by every sequence of events."
  (implies (and (system-statep systate)
                (system-previous-are-quorum-p systate)
                (events-possiblep events systate))
           (system-previous-are-quorum-p (events-next events systate)))
  :induct t
  :disable ((:e tau-system))
  :enable (events-next
           events-possiblep
           system-previous-are-quorum-p-of-event-next))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled system-previous-are-quorum-p-when-reachable
  :short "The invariant holds in every reachable state."
  :long
  (xdoc::topstring
   (xdoc::p
    "Reachable states are characterized by an initial state and
     a sequence of possible events from that initial state."))
  (implies (and (system-statep systate)
                (system-state-initp systate)
                (events-possiblep events systate))
           (system-previous-are-quorum-p (events-next events systate)))
  :disable ((:e tau-system))
  :enable (system-previous-are-quorum-p-when-system-state-initp
           system-previous-are-quorum-p-of-events-next))
