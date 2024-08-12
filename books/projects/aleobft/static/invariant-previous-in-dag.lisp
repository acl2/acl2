; Aleo Library
;
; Copyright (C) 2024 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOBFT-STATIC")

(include-book "operations-dags-additional")
(include-book "invariant-addresses")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ invariant-previous-in-dag
  :parents (correctness)
  :short "Invariant that the previous certificates
          referenced by a certificate in a DAG
          are also in the DAG."
  :long
  (xdoc::topstring
   (xdoc::p
    "A validator's DAG is extended via two kinds of events,
     namely @('create-certificate') and @('store-certificate').")
   (xdoc::p
    "The first kind of event may only occur if
     the certificate's author has all the previous certificates in its DAG.")
   (xdoc::p
    "The second kind of event may only ocur if
     the DAG has all the previous certificates.
     Under that condition, the certificate is moved from the buffer to the DAG.
     In fact, the purpose of the buffer is to wait
     until all the previous certificates are in the DAG,
     since they may be coming out of order with respect to round numbers."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk system-previous-in-dag-p ((systate system-statep))
  :returns (yes/no booleanp)
  :short "Definition of the invariant:
          the previous certificates
          of each certificate in the DAG of a correct validator
          are also in that validator's DAG."
  (forall (val)
          (implies (set::in val (correct-addresses systate))
                   (dag-previous-in-dag-p
                    (validator-state->dag
                     (get-validator-state val systate))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule system-previous-in-dag-p-when-system-state-initp
  :short "Establishment of the invariant:
          the invariant holds on any initial state."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is easy to prove, because initially all DAGs are empty."))
  (implies (system-state-initp systate)
           (system-previous-in-dag-p systate))
  :enable (system-previous-in-dag-p
           dag-previous-in-dag-p
           validator-init))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection system-previous-in-dag-p-of-create-certificate-next
  :short "Preservation of the invariant by @('create-certificate') events."
  :long
  (xdoc::topstring
   (xdoc::p
    "As mentioned in the overview for this invariant,
     this kind of event can happen only if
     @(tsee signers-have-previous-certificates-p) holds,
     which is checked by @(tsee create-certificate-possiblep).
     First we show that @(tsee signer-has-previous-certificates-p) (singular)
     implies @(tsee certificate-previous-in-dag-p);
     the latter is used in defining our invariant.
     Then we show that @(tsee signers-have-previous-certificates-p) (plural)
     implies @(tsee certificate-previous-in-dag-p) for every signer,
     although here we only need that for the author.
     Next we show that @(tsee create-certificate-possiblep)
     implies @(tsee certificate-previous-in-dag-p) for the author.
     Finally we show that @(tsee create-certificate-next)
     preserves the invariant."))

  (defruled certificate-previous-in-dag-p-when-signer-has-previous
    (implies (and (signer-has-previous-certificates-p
                   signer
                   (certificate->previous cert)
                   (certificate->round cert)
                   systate)
                  (set::in signer (correct-addresses systate)))
             (certificate-previous-in-dag-p
              cert
              (validator-state->dag (get-validator-state signer systate))))
    :enable (signer-has-previous-certificates-p
             certificate-previous-in-dag-p))

  (defruled certificate-previous-in-dag-p-when-signers-have-previous
    (implies (and (signers-have-previous-certificates-p
                   signers
                   (certificate->previous cert)
                   (certificate->round cert)
                   systate)
                  (set::in signer signers)
                  (set::in signer (correct-addresses systate)))
             (certificate-previous-in-dag-p
              cert
              (validator-state->dag (get-validator-state signer systate))))
    :enable (signers-have-previous-certificates-p
             certificate-previous-in-dag-p-when-signer-has-previous
             signers-have-previous-certificates-p-element))

  (defrule certificate-previous-in-dag-p-when-create-certificate-possiblep
    (implies (and (create-certificate-possiblep cert systate)
                  (set::in (certificate->author cert)
                           (correct-addresses systate)))
             (certificate-previous-in-dag-p
              cert
              (validator-state->dag
               (get-validator-state (certificate->author cert) systate))))
    :enable (create-certificate-possiblep
             certificate-previous-in-dag-p-when-signers-have-previous
             certificate->signers))

  (defrule system-previous-in-dag-p-of-create-certificate-next
    (implies (and (system-previous-in-dag-p systate)
                  (create-certificate-possiblep cert systate)
                  (certificatep cert))
             (system-previous-in-dag-p
              (create-certificate-next cert systate)))
    :expand (system-previous-in-dag-p
             (create-certificate-next cert systate))
    :enable system-previous-in-dag-p-necc))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule system-previous-in-dag-p-of-receive-certificate-next
  :short "Preservation of the invariant by @('receive-certificate') events."
  :long
  (xdoc::topstring
   (xdoc::p
    "This kind of event does not modify any DAG."))
  (implies (and (system-previous-in-dag-p systate)
                (receive-certificate-possiblep msg systate))
           (system-previous-in-dag-p
            (receive-certificate-next msg systate)))
  :expand (system-previous-in-dag-p
           (receive-certificate-next msg systate))
  :enable system-previous-in-dag-p-necc)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection system-previous-in-dag-p-of-store-certificate-next
  :short "Preservation of the invariant by @('store-certificate') events."
  :long
  (xdoc::topstring
   (xdoc::p
    "This kind of events is conditioned under
     @(tsee store-certificate-possiblep),
     which checks the needed condition on the certificate
     moved from the buffer to the DAG.
     First we prove that @(tsee store-certificate-possiblep)
     implies @(tsee certificate-previous-in-dag-p),
     and then we prove the preservation of the invariant."))

  (defrule certificate-previous-in-dag-p-when-store-certificate-possiblep
    (implies (and (store-certificate-possiblep cert val systate)
                  (set::in val (correct-addresses systate)))
             (certificate-previous-in-dag-p
              cert
              (validator-state->dag
               (get-validator-state val systate))))
    :enable (store-certificate-possiblep
             certificate-previous-in-dag-p))

  (defrule system-previous-in-dag-p-of-store-certificate-next
    (implies (and (system-previous-in-dag-p systate)
                  (store-certificate-possiblep cert val systate)
                  (certificatep cert))
             (system-previous-in-dag-p
              (store-certificate-next cert val systate)))
    :expand (system-previous-in-dag-p
             (store-certificate-next cert val systate))
    :enable system-previous-in-dag-p-necc))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule system-previous-in-dag-p-of-advance-round-next
  :short "Preservation of the invariant by @('advance-round') events."
  :long
  (xdoc::topstring
   (xdoc::p
    "This kind of event does not modify any DAG."))
  (implies (and (system-previous-in-dag-p systate)
                (advance-round-possiblep val systate))
           (system-previous-in-dag-p
            (advance-round-next val systate)))
  :expand (system-previous-in-dag-p
           (advance-round-next val systate))
  :enable system-previous-in-dag-p-necc)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule system-previous-in-dag-p-of-commit-anchors-next
  :short "Preservation of the invariant by @('commit-anchors') events."
  :long
  (xdoc::topstring
   (xdoc::p
    "This kind of event does not modify any DAG."))
  (implies (and (system-previous-in-dag-p systate)
                (commit-anchors-possiblep val systate))
           (system-previous-in-dag-p
            (commit-anchors-next val systate)))
  :expand (system-previous-in-dag-p
           (commit-anchors-next val systate))
  :enable system-previous-in-dag-p-necc)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule system-previous-in-dag-p-of-timer-expires-next
  :short "Preservation of the invariant by @('timer-expires') events."
  :long
  (xdoc::topstring
   (xdoc::p
    "This kind of event does not modify any DAG."))
  (implies (and (system-previous-in-dag-p systate)
                (timer-expires-possiblep val systate))
           (system-previous-in-dag-p
            (timer-expires-next val systate)))
  :expand (system-previous-in-dag-p
           (timer-expires-next val systate))
  :enable system-previous-in-dag-p-necc)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule system-previous-in-dag-p-of-event-next
  :short "Preservation of the invariant by all events."
  :long
  (xdoc::topstring
   (xdoc::p
    "This follows from the theorems about the various kinds of events."))
  (implies (and (system-previous-in-dag-p systate)
                (event-possiblep val systate))
           (system-previous-in-dag-p
            (event-next val systate)))
  :enable (event-possiblep
           event-next))
