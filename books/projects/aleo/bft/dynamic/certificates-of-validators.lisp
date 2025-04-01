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

(defxdoc+ certificates-of-validators
  :parents (correctness)
  :short "Certificates associated to validators according to various criteria."
  :long
  (xdoc::topstring
   (xdoc::p
    "We introduce various notions of certificates associated to validators,
     used to formulate correctness properties of the protocol.")
   (xdoc::p
    "One notion is that of all the certificates ``owned'' by a validator,
     in the sense that either the validator has the certificate
     or the certificate is in a network message addressed to the validator.
     The latter represents a ``promise'' that
     the validator may/will eventually obtain the certificate.")
   (xdoc::p
    "Another notion is that of all the certificates signed by a validator.")
   (xdoc::p
    "A third notion is that of all the certificates accepted by a validator,
     i.e. received from the network, and present in the buffer or DAG.
     These are a subset of the owned certificates
     (the notion described above)."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define owned-certificates ((val addressp) (systate system-statep))
  :guard (set::in val (correct-addresses systate))
  :returns (certs certificate-setp)
  :short "Certificates owned by a validator."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is as explained in @(see certificates-of-validators).
     It consists of the certificates in the DAG and buffer,
     as well as the ones in the network addressed to the validator.")
   (xdoc::p
    "This is only defined for correct validators.
     Faulty validators have no internal state,
     and no messages addresses to them."))
  (b* ((vstate (get-validator-state val systate)))
    (set::union (set::union (validator-state->dag vstate)
                            (validator-state->buffer vstate))
                (message-certificates-with-destination
                 val (get-network-state systate))))
  :hooks (:fix)

  ///

  (defruled message-certificate-in-owned-certificates
    (implies (set::in (message-fix msg) (get-network-state systate))
             (set::in (message->certificate msg)
                      (owned-certificates (message->destination msg) systate)))
    :enable in-of-message-certificates-with-destination))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled owned-certificates-when-init
  :short "Initially, validators own no certificates."
  (implies (and (system-initp systate)
                (set::in val (correct-addresses systate)))
           (equal (owned-certificates val systate)
                  nil))
  :enable (owned-certificates
           system-initp
           system-validators-initp-necc
           validator-init))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection owned-certificates-of-next
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
     then nothing changes for the validator;
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

  (defruled owned-certificates-of-create-certificate-next
    (implies (set::in val (correct-addresses systate))
             (equal (owned-certificates val
                                        (create-certificate-next cert
                                                                 systate))
                    (set::insert (certificate-fix cert)
                                 (owned-certificates val systate))))
    :enable
    (owned-certificates
     validator-state->dag-of-create-certificate-next
     validator-state->buffer-of-create-certificate-next
     get-network-state-of-create-certificate-next
     message-certificates-with-destination-of-union
     message-certificates-with-destination-of-make-certificate-messages))

  (defruled owned-certificates-of-receive-certificate-next
    (implies (and (set::in val (correct-addresses systate))
                  (receive-certificate-possiblep msg systate))
             (equal (owned-certificates val
                                        (receive-certificate-next msg
                                                                  systate))
                    (owned-certificates val systate)))
    :enable (owned-certificates
             validator-state->dag-of-receive-certificate-next
             validator-state->buffer-of-receive-certificate-next
             get-network-state-of-receive-certificate-next
             message-certificates-with-destination-of-delete
             set::expensive-rules
             in-of-message-certificates-with-destination
             receive-certificate-possiblep))

  (defruled owned-certificates-of-store-certificate-next
    (implies (and (set::in val (correct-addresses systate))
                  (store-certificate-possiblep val1 cert systate))
             (equal (owned-certificates val
                                        (store-certificate-next val1
                                                                cert
                                                                systate))
                    (owned-certificates val systate)))
    :enable (owned-certificates
             validator-state->dag-of-store-certificate-next
             validator-state->buffer-of-store-certificate-next
             get-network-state-of-store-certificate-next
             set::expensive-rules
             in-of-message-certificates-with-destination
             store-certificate-possiblep))

  (defruled owned-certificates-of-advance-round-next
    (implies (and (set::in val (correct-addresses systate))
                  (advance-round-possiblep val1 systate))
             (equal (owned-certificates val
                                        (advance-round-next val1
                                                            systate))
                    (owned-certificates val systate)))
    :enable (owned-certificates
             validator-state->dag-of-advance-round-next
             validator-state->buffer-of-advance-round-next
             get-network-state-of-advance-round-next))

  (defruled owned-certificates-of-commit-anchors-next
    (implies (and (set::in val (correct-addresses systate))
                  (commit-anchors-possiblep val1 systate))
             (equal (owned-certificates val
                                        (commit-anchors-next val1
                                                             systate))
                    (owned-certificates val systate)))
    :enable (owned-certificates
             validator-state->dag-of-commit-anchors-next
             validator-state->buffer-of-commit-anchors-next
             get-network-state-of-commit-anchors-next))

  (defruled owned-certificates-of-timer-expires-next
    (implies (and (set::in val (correct-addresses systate))
                  (timer-expires-possiblep val1 systate))
             (equal (owned-certificates val
                                        (timer-expires-next val1
                                                            systate))
                    (owned-certificates val systate)))
    :enable (owned-certificates
             validator-state->dag-of-timer-expires-next
             validator-state->buffer-of-timer-expires-next
             get-network-state-of-timer-expires-next)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define signed-certificates ((val addressp) (systate system-statep))
  :guard (set::in val (correct-addresses systate))
  :returns (certs certificate-setp)
  :short "Certificates signed by a validator."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are all the certificates in the system signed by the validator.
     As proved in @(see same-owned-certificates),
     validators own (in the precise sense of @(tsee owned-certificates))
     the same set of certificates;
     so any such set of owned certificates is
     the set of all certificates in the system.
     We pick the set of the signer,
     and we select the ones whose signers include the signer.")
   (xdoc::p
    "We define this notion only for correct validators (signers).
     We could also define it for faulty validators,
     since they can be signers,
     but we only need this notion for correct validators."))
  (certificates-with-signer val (owned-certificates val systate))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled signed-certificates-when-init
  :short "Initially, validators have signed no certificates."
  (implies (and (system-initp systate)
                (set::in val (correct-addresses systate)))
           (equal (signed-certificates val systate)
                  nil))
  :enable signed-certificates)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection signed-certificates-of-next
  :short "How the certificates signed by a validator
          change (or not) for each transition."
  :long
  (xdoc::topstring
   (xdoc::p
    "The only kind of transition that may change
     the certificates signed by a validator
     is @('create-certificate'),
     because all the others do not change the set of owned certificates,
     as proved in @(see owned-certificates-of-next),
     which are a superset of the signed certificates.
     Whether the set of signed certificates actually changes
     depends on whether the validator
     is a signer of the certificate or not;
     so our theorem for @('create-certificate') has a conditional.
     The theorems for the other kinds of transitions
     assert that there is no change in the set of signed certificates."))

  (defruled signed-certificates-of-create-certificate-next
    (implies (set::in val (correct-addresses systate))
             (equal (signed-certificates val
                                         (create-certificate-next cert
                                                                  systate))
                    (if (set::in (address-fix val)
                                 (certificate->signers cert))
                        (set::insert (certificate-fix cert)
                                     (signed-certificates val systate))
                      (signed-certificates val systate))))
    :enable (signed-certificates
             owned-certificates-of-create-certificate-next
             certificates-with-signer-of-insert))

  (defruled signed-certificates-of-receive-certificate-next
    (implies (and (set::in val (correct-addresses systate))
                  (receive-certificate-possiblep msg systate))
             (equal (signed-certificates val
                                         (receive-certificate-next msg
                                                                   systate))
                    (signed-certificates val systate)))
    :enable (signed-certificates
             owned-certificates-of-receive-certificate-next))

  (defruled signed-certificates-of-store-certificate-next
    (implies (and (set::in val (correct-addresses systate))
                  (store-certificate-possiblep val1 cert systate))
             (equal (signed-certificates val
                                         (store-certificate-next val1
                                                                 cert
                                                                 systate))
                    (signed-certificates val systate)))
    :enable (signed-certificates
             owned-certificates-of-store-certificate-next))

  (defruled signed-certificates-of-advance-round-next
    (implies (and (set::in val (correct-addresses systate))
                  (advance-round-possiblep val1 systate))
             (equal (signed-certificates val
                                         (advance-round-next val1
                                                             systate))
                    (signed-certificates val systate)))
    :enable (signed-certificates
             owned-certificates-of-advance-round-next))

  (defruled signed-certificates-of-commit-anchors-next
    (implies (and (set::in val (correct-addresses systate))
                  (commit-anchors-possiblep val1 systate))
             (equal (signed-certificates val
                                         (commit-anchors-next val1
                                                              systate))
                    (signed-certificates val systate)))
    :enable (signed-certificates
             owned-certificates-of-commit-anchors-next))

  (defruled signed-certificates-of-timer-expires-next
    (implies (and (set::in val (correct-addresses systate))
                  (timer-expires-possiblep val1 systate))
             (equal (signed-certificates val
                                         (timer-expires-next val1
                                                             systate))
                    (signed-certificates val systate)))
    :enable (signed-certificates
             owned-certificates-of-timer-expires-next)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define accepted-certificates ((val addressp) (systate system-statep))
  :guard (set::in val (correct-addresses systate))
  :returns (certs certificate-setp)
  :short "Certificates accepted by a validator."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are all the certificates that have been accepted by a validator,
     i.e. the certificates that they are in the buffer or DAG.
     When a validator authors a certificates, it adds it to the DAG,
     so it certainly ``accepts'' it.
     When a validator receives a certificate from the network,
     it adds it to the buffer,
     and then later it possibly moves it to the DAG."))
  (b* ((vstate (get-validator-state val systate)))
    (set::union (validator-state->dag vstate)
                (validator-state->buffer vstate)))
  :hooks (:fix)

  ///

  (defruled in-owned-certificates-when-in-accepted-certificates
    (implies (set::in cert (accepted-certificates val systate))
             (set::in cert (owned-certificates val systate)))
    :enable owned-certificates))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled accepted-certificates-when-init
  :short "Initially, validators have accepted no certificates."
  (implies (and (system-initp systate)
                (set::in val (correct-addresses systate)))
           (equal (accepted-certificates val systate)
                  nil))
  :enable (accepted-certificates
           system-initp
           system-validators-initp-necc
           validator-init))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection accepted-certificates-of-next
  :short "How the certificates accepted by a validator
          change (or not) for each transition."
  :long
  (xdoc::topstring
   (xdoc::p
    "The only kind of transitions that change
     the certificates accepted by a validator
     are @('create-transition'),
     which adds a certificate to the DAG of the author,
     and @('receive-certificates'),
     which adds a certificate to the DAG of the receiver.")
   (xdoc::p
    "A @('store-certificate') just moves a certificate from buffer to DAG,
     so there is no net change to the accepted certificates.")
   (xdoc::p
    "For the other three kinds of events,
     there are no changes to DAGs and buffers,
     and thus the accepted certificates do not change for any validator."))

  (defruled accepted-certificates-of-create-certificate-next
    (implies (set::in val (correct-addresses systate))
             (equal (accepted-certificates val
                                           (create-certificate-next cert
                                                                    systate))
                    (if (equal (address-fix val)
                               (certificate->author cert))
                        (set::insert (certificate-fix cert)
                                     (accepted-certificates val systate))
                      (accepted-certificates val systate))))
    :enable
    (accepted-certificates
     validator-state->dag-of-create-certificate-next
     validator-state->buffer-of-create-certificate-next))

  (defruled accepted-certificates-of-receive-certificate-next
    (implies (and (set::in val (correct-addresses systate))
                  (receive-certificate-possiblep msg systate))
             (equal (accepted-certificates val
                                           (receive-certificate-next msg
                                                                     systate))
                    (if (equal (address-fix val)
                               (message->destination msg))
                        (set::insert (message->certificate msg)
                                     (accepted-certificates val systate))
                      (accepted-certificates val systate))))
    :enable (accepted-certificates
             validator-state->dag-of-receive-certificate-next
             validator-state->buffer-of-receive-certificate-next))

  (defruled accepted-certificates-of-store-certificate-next
    (implies (and (set::in val (correct-addresses systate))
                  (store-certificate-possiblep val1 cert systate))
             (equal (accepted-certificates val
                                           (store-certificate-next val1
                                                                   cert
                                                                   systate))
                    (accepted-certificates val systate)))
    :enable (accepted-certificates
             validator-state->dag-of-store-certificate-next
             validator-state->buffer-of-store-certificate-next
             set::expensive-rules
             store-certificate-possiblep))

  (defruled accepted-certificates-of-advance-round-next
    (implies (and (set::in val (correct-addresses systate))
                  (advance-round-possiblep val1 systate))
             (equal (accepted-certificates val
                                           (advance-round-next val1
                                                               systate))
                    (accepted-certificates val systate)))
    :enable (accepted-certificates
             validator-state->dag-of-advance-round-next
             validator-state->buffer-of-advance-round-next))

  (defruled accepted-certificates-of-commit-anchors-next
    (implies (and (set::in val (correct-addresses systate))
                  (commit-anchors-possiblep val1 systate))
             (equal (accepted-certificates val
                                           (commit-anchors-next val1
                                                                systate))
                    (accepted-certificates val systate)))
    :enable (accepted-certificates
             validator-state->dag-of-commit-anchors-next
             validator-state->buffer-of-commit-anchors-next))

  (defruled accepted-certificates-of-timer-expires-next
    (implies (and (set::in val (correct-addresses systate))
                  (timer-expires-possiblep val1 systate))
             (equal (accepted-certificates val
                                           (timer-expires-next val1
                                                               systate))
                    (accepted-certificates val systate)))
    :enable (accepted-certificates
             validator-state->dag-of-timer-expires-next
             validator-state->buffer-of-timer-expires-next)))
