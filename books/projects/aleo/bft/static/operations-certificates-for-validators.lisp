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

(include-book "transitions")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ operations-certificates-for-validators
  :parents (operations-additional)
  :short "Operations about
          certificates in actual or potential possession of validators."
  :long
  (xdoc::topstring
   (xdoc::p
    "Validators have certificates in their DAGs and buffers.
     But they may/will also have
     the certificates in the network addressed to them, if/when delivered.
     A message in the network represents a ``promise'' that
     the recipient can obtain that certificate,
     when the message gets eventually delivered.
     Thus, there is a sense in which the certificates for a validator are
     not only the ones in its DAG and buffer,
     but also the ones in the network addressed to the validator
     (even though the validator cannot access them until they are delivered).")
   (xdoc::p
    "We introduce operations to calculate
     the set of all the certificates for a validator:
     the ones in the DAG,
     the ones in the buffer,
     and the ones in messages addressed to the validator."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define message-certificates-for-validator ((dest addressp) (msgs message-setp))
  :returns (certs certificate-setp)
  :short "Filter the messages with a given recipient from a set of messages."
  :long
  (xdoc::topstring
   (xdoc::p
    "This can be used to obtain, from the network (which is a set of messages),
     the certificates addressed to a certain validator,
     as part of calculating the set of certificates for each validator
     (see @(tsee certificates-for-validator))."))
  (b* (((when (set::emptyp msgs)) nil)
       (msg (set::head msgs)))
    (if (equal (message->destination msg) dest)
        (set::insert (message->certificate msg)
                     (message-certificates-for-validator
                      dest (set::tail msgs)))
      (message-certificates-for-validator dest (set::tail msgs))))
  :verify-guards :after-returns
  ///

  (defruled in-of-message-certificates-for-validator
    (implies (and (addressp dest)
                  (message-setp msgs))
             (equal (set::in cert
                             (message-certificates-for-validator dest msgs))
                    (and (set::in (message cert dest) msgs)
                         (certificatep cert))))
    :induct t
    :enable (set::expensive-rules
             set::in))

  (defruled message-certificates-for-validator-when-emptyp
    (implies (set::emptyp msgs)
             (equal (message-certificates-for-validator dest msgs)
                    nil)))

  (defruled message-certificates-for-validator-of-insert
    (implies (and (message-setp msgs)
                  (messagep msg)
                  (addressp dest))
             (equal (message-certificates-for-validator
                     dest (set::insert msg msgs))
                    (if (equal (message->destination msg) dest)
                        (set::insert (message->certificate msg)
                                     (message-certificates-for-validator
                                      dest msgs))
                      (message-certificates-for-validator dest msgs))))
    :enable (set::expensive-rules
             set::double-containment-no-backchain-limit
             in-of-message-certificates-for-validator))

  (defruled message-certificates-for-validator-of-delete
    (implies (and (message-setp msgs)
                  (addressp dest))
             (equal (message-certificates-for-validator
                     dest (set::delete msg msgs))
                    (if (and (set::in msg msgs)
                             (equal (message->destination msg) dest))
                        (set::delete (message->certificate msg)
                                     (message-certificates-for-validator
                                      dest msgs))
                      (message-certificates-for-validator dest msgs))))
    :enable (set::expensive-rules
             set::double-containment-no-backchain-limit
             in-of-message-certificates-for-validator))

  (defruled message-certificates-for-validator-of-union
    (implies (and (message-setp msgs1)
                  (message-setp msgs2)
                  (addressp dest))
             (equal (message-certificates-for-validator dest
                                                        (set::union msgs1 msgs2))
                    (set::union (message-certificates-for-validator dest msgs1)
                                (message-certificates-for-validator dest msgs2))))
    :enable (set::expensive-rules
             set::double-containment-no-backchain-limit
             in-of-message-certificates-for-validator)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define certificates-for-validator ((val addressp) (systate system-statep))
  :short "Calculate all the certificates for a validator,
          including the ones in messages."
  :long
  (xdoc::topstring
   (xdoc::p
    "Validators have certificates in their DAGs and buffers.
     But there may/will have also
     the certificates in the network addressed to them,
     if/when they are delivered.
     A message in the network represents a ``promise'' that
     the recipient can obtain that certificate,
     when it gets eventually delivered.
     Thus, there is a sense in which the messages for a validator are
     not only the ones in its DAG and buffer,
     but also the ones in the network addressed to the validator
     (even though the validator cannot access them until they are delivered).")
   (xdoc::p
    "This function returns all the messages for a validator,
     in the sense explained just above.
     The result is the union of the validator's DAG and buffer
     with the messages in the network addressed to the validator."))
  :guard (set::in val (correct-addresses systate))
  :returns (certs certificate-setp)
  (b* ((vstate (get-validator-state val systate)))
    (set::union (set::union (validator-state->dag vstate)
                            (validator-state->buffer vstate))
                (message-certificates-for-validator
                 val (get-network-state systate))))
  :guard-hints
  (("Goal" :in-theory (enable in-all-addresses-when-in-correct-addresses)))

  ///

  (defruled in-certificates-for-validator-when-in-dag
    (implies (set::in cert (validator-state->dag
                            (get-validator-state val systate)))
             (set::in cert (certificates-for-validator val systate)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled message-certificates-for-validator-of-messages-for-certificate
  :short "Relation between message creation and certificates for validators."
  (implies (and (certificatep cert)
                (address-setp dests)
                (addressp val))
           (equal (message-certificates-for-validator
                   val (messages-for-certificate cert dests))
                  (if (set::in val dests)
                      (set::insert cert nil)
                    nil)))
  :induct t
  :enable (message-certificates-for-validator
           messages-for-certificate
           message-certificates-for-validator-of-insert))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled certificates-for-validator-of-create-certificate-next
  :short "A @('create-certificate') event
          adds a certificate (the same one) for each validator."
  (implies (and (certificatep cert)
                (set::in val (correct-addresses systate))
                (create-certificate-possiblep cert systate))
           (equal (certificates-for-validator
                   val (create-certificate-next cert systate))
                  (set::insert cert (certificates-for-validator val systate))))
  :enable (create-certificate-possiblep
           create-certificate-next-val
           certificates-for-validator
           validator-state->dag-of-create-certificate-next
           validator-state->buffer-of-create-certificate-next
           get-network-state-of-create-certificate-next
           set::expensive-rules
           message-certificates-for-validator-of-union
           message-certificates-for-validator-of-messages-for-certificate))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled certificates-for-validator-of-receive-certificate-next
  :short "A @('receive-certificate') event
          does not change the certificates for validators."
  (implies (and (receive-certificate-possiblep msg systate)
                (set::in val (correct-addresses systate)))
           (equal (certificates-for-validator
                   val (receive-certificate-next msg systate))
                  (certificates-for-validator val systate)))
  :enable (receive-certificate-possiblep
           receive-certificate-next
           receive-certificate-next-val
           certificates-for-validator
           set::expensive-rules
           in-of-message-certificates-for-validator
           message-certificates-for-validator-of-delete))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled certificates-for-validator-of-store-certificate-next
  :short "A @('store-certificate') event
          does not change the certificates for validators."
  (implies (store-certificate-possiblep cert event-val systate)
           (equal (certificates-for-validator
                   val (store-certificate-next cert event-val systate))
                  (certificates-for-validator val systate)))
  :enable (store-certificate-possiblep
           store-certificate-next
           store-certificate-next-val
           certificates-for-validator
           get-validator-state-of-update-validator-state
           set::expensive-rules))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled certificates-for-validator-of-advance-round-next
  :short "A @('advance-round') event
          does not change the certificates for validators."
  (implies (advance-round-possiblep event-val systate)
           (equal (certificates-for-validator
                   val (advance-round-next event-val systate))
                  (certificates-for-validator val systate)))
  :enable (advance-round-possiblep
           advance-round-next
           advance-round-next-val
           certificates-for-validator
           get-validator-state-of-update-validator-state))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled certificates-for-validator-of-commit-anchors-next
  :short "A @('commit-anchors') event
          does not change the certificates for validators."
  (implies (commit-anchors-possiblep event-val systate)
           (equal (certificates-for-validator
                   val (commit-anchors-next event-val systate))
                  (certificates-for-validator val systate)))
  :enable (commit-anchors-possiblep
           commit-anchors-next
           commit-anchors-next-val
           certificates-for-validator
           get-validator-state-of-update-validator-state))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled certificates-for-validator-of-timer-expires-next
  :short "A @('timer-expires') event
          does not change the certificates for validators."
  (implies (timer-expires-possiblep event-val systate)
           (equal (certificates-for-validator
                   val (timer-expires-next event-val systate))
                  (certificates-for-validator val systate)))
  :enable (timer-expires-possiblep
           timer-expires-next
           timer-expires-next-val
           certificates-for-validator
           get-validator-state-of-update-validator-state))
