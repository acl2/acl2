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

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ owned-certificates
  :parents (correctness)
  :short "Certificates owned by validators."
  :long
  (xdoc::topstring
   (xdoc::p
    "Validators have certificates in their DAGs and buffers.
     But they may/will also have
     the certificates in the network addressed to them, if/when delivered.
     A message in the network represents a ``promise'' that
     the recipient may/will obtain that certificate,
     if/when the message gets eventually delivered.
     Thus, there is a sense in which the certificates owned by a validator are
     not only the ones in its DAG and buffer,
     but also the ones in the network addressed to the validator
     (even though the validator cannot access them until they are delivered).")
   (xdoc::p
    "We introduce an operation to calculate
     the certificates in actual or potential possession of a validator.
     These are:
     the ones in the DAG;
     the ones in the buffer;
     and the ones in messages addressed to the validator."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define certificates-owned-by ((val addressp) (systate system-statep))
  :guard (set::in val (correct-addresses systate))
  :returns (certs certificate-setp)
  :short "Certificates owned by a validator,
          including the ones in the network addresses to the validator."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is as explained in @(see owned-certificates).")
   (xdoc::p
    "This is only defined for correct validators.
     Faulty validators have no internal state,
     and no messages addresses to them."))
  (b* ((vstate (get-validator-state val systate)))
    (set::union (set::union (validator-state->dag vstate)
                            (validator-state->buffer vstate))
                (message-certificates-with-destination
                 val (get-network-state systate))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled certificates-owned-by-when-init
  :short "Initially, validators own no certificates."
  (implies (and (system-initp systate)
                (set::in val (correct-addresses systate)))
           (equal (certificates-owned-by val systate)
                  nil))
  :enable (certificates-owned-by
           system-initp
           system-validators-initp-necc
           validator-init))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection certificates-owned-by-of-next
  :short "How the certificates owned by a validator
          change (or not) for each transition."
  :long
  (xdoc::topstring
   (xdoc::p
    "The only kind of transition that changes
     the certificates owned by a validator
     is @('create-transition'), which creates a new certificate:
     the certificate is added to the owned certificates.
     This is the case for all correct validators:
     if the validator is the author, we add the certificate to its DAG;
     if the validator is not the author, we add the certificate to the network,
     in a message addressed to the validator.
     Thus, either way, the certificate is added to
     the set of owned certificates.")
   (xdoc::p
    "A @('receive-certificate') just moves a certificate
     from the network to the buffer,
     for the validator that is the destination of the message:
     thus, the set of owned certificates does not change,
     although the buffer component and the network component change,
     but in a way that they compensate each other.
     If the validator is not the destination of the message,
     then nothing changes for the validator,
     none of its owned certificates moves.")
   (xdoc::p
    "A @('store-certificate') is similar to a @('receive-certificate'):
     for the validator who stores the certificate,
     the certificate just moves from the buffer to the DAG,
     with no net change to the set of owned certificates;
     for other validators, DAG and buffer do not change.")
   (xdoc::p
    "For the other three kinds of events,
     there are no changes to DAGs, buffers, and network,
     and thus the owned certificates do not change for any validator."))

  (defruled certificates-owned-by-of-create-certificate-next
    (implies (set::in val (correct-addresses systate))
             (equal (certificates-owned-by val
                                           (create-certificate-next cert
                                                                    systate))
                    (set::insert (certificate-fix cert)
                                 (certificates-owned-by val systate))))
    :enable (certificates-owned-by
             validator-state->dag-of-create-certificate-next
             validator-state->buffer-of-create-certificate-next
             get-network-state-of-create-certificate-next
             message-certificates-with-destination-of-union
             message-certificates-with-destination-of-make-certificate-message))

  (defruled certificates-owned-by-of-receive-certificate-next
    (implies (and (set::in val (correct-addresses systate))
                  (receive-certificate-possiblep msg systate))
             (equal (certificates-owned-by val
                                           (receive-certificate-next msg
                                                                     systate))
                    (certificates-owned-by val systate)))
    :enable (certificates-owned-by
             validator-state->dag-of-receive-certificate-next
             validator-state->buffer-of-receive-certificate-next
             get-network-state-of-receive-certificate-next
             message-certificates-with-destination-of-delete
             set::expensive-rules
             in-of-message-certificates-with-destination
             receive-certificate-possiblep))

  (defruled certificates-owned-by-of-store-certificate-next
    (implies (and (set::in val (correct-addresses systate))
                  (store-certificate-possiblep val1 cert systate))
             (equal (certificates-owned-by val
                                           (store-certificate-next val1
                                                                   cert
                                                                   systate))
                    (certificates-owned-by val systate)))
    :enable (certificates-owned-by
             validator-state->dag-of-store-certificate-next
             validator-state->buffer-of-store-certificate-next
             get-network-state-of-store-certificate-next
             set::expensive-rules
             in-of-message-certificates-with-destination
             store-certificate-possiblep))

  (defruled certificates-owned-by-of-advance-round-next
    (implies (and (set::in val (correct-addresses systate))
                  (advance-round-possiblep val1 systate))
             (equal (certificates-owned-by val
                                           (advance-round-next val1
                                                               systate))
                    (certificates-owned-by val systate)))
    :enable (certificates-owned-by
             validator-state->dag-of-advance-round-next
             validator-state->buffer-of-advance-round-next
             get-network-state-of-advance-round-next))

  (defruled certificates-owned-by-of-commit-anchors-next
    (implies (and (set::in val (correct-addresses systate))
                  (commit-anchors-possiblep val1 systate))
             (equal (certificates-owned-by val
                                           (commit-anchors-next val1
                                                                systate))
                    (certificates-owned-by val systate)))
    :enable (certificates-owned-by
             validator-state->dag-of-commit-anchors-next
             validator-state->buffer-of-commit-anchors-next
             get-network-state-of-commit-anchors-next))

  (defruled certificates-owned-by-of-timer-expires-next
    (implies (and (set::in val (correct-addresses systate))
                  (timer-expires-possiblep val1 systate))
             (equal (certificates-owned-by val
                                           (timer-expires-next val1
                                                               systate))
                    (certificates-owned-by val systate)))
    :enable (certificates-owned-by
             validator-state->dag-of-timer-expires-next
             validator-state->buffer-of-timer-expires-next
             get-network-state-of-timer-expires-next)))
