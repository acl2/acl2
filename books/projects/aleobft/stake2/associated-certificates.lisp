; AleoBFT Library
;
; Copyright (C) 2024 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOBFT-STAKE2")

(include-book "initialization")
(include-book "transitions")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ associated-certificates
  :parents (correctness)
  :short "Certificates associated to validators."
  :long
  (xdoc::topstring
   (xdoc::p
    "A validator has certificates in its DAG.
     But the network may contain messages, with certificates,
     that are addressed to the validator:
     even though the validator does not yet have those certificates in its DAG,
     it may eventually have them, if and when the message is delivered.
     It is useful to introduce a notion for
     the certificates associated to a validator,
     in the sense of being in the DAG,
     or in a message addressed to the validator.")
   (xdoc::p
    "We define this notion here,
     and we prove theorems about its initial value,
     and about how its value changes in response to events."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define associated-certs ((val addressp) (systate system-statep))
  :guard (set::in val (correct-addresses systate))
  :returns (certs certificate-setp)
  :short "Certificates associated to a validator."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is as explained in @(see associated-certificates).
     It consists of the certificates in the DAG,
     as well as the ones in the network addressed to the validator.")
   (xdoc::p
    "This is only defined for correct validators.
     Faulty validators have no internal state,
     and no messages addresses to them."))
  (b* (((validator-state vstate) (get-validator-state val systate)))
    (set::union vstate.dag
                (message-certs-with-dest val (get-network-state systate))))
  :hooks (:fix)

  ///

  (defruled message-certificate-in-associated-certs
    (implies (set::in (message-fix msg) (get-network-state systate))
             (set::in (message->certificate msg)
                      (associated-certs (message->destination msg) systate)))
    :enable in-of-message-certs-with-dest))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled associated-certs-when-init
  :short "Initially, validators have no associated certificates."
  (implies (and (system-initp systate)
                (set::in val (correct-addresses systate)))
           (equal (associated-certs val systate)
                  nil))
  :enable (associated-certs
           system-initp
           system-validators-initp-necc
           validator-init))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection associated-certs-of-next
  :short "How the certificates associated to a validator
          change (or not) for each transition."
  :long
  (xdoc::topstring
   (xdoc::p
    "The only kind of event that changes
     the certificates associated to a validator
     is a @('create') event, which creates a new certificate:
     the certificate is added to the associated certificates.
     This is the case for all correct validators:
     if the validator is the author, we add the certificate to its DAG;
     if the validator is not the author, we add the certificate to the network,
     in a message addressed to the validator.
     Thus, either way, the certificate is added to
     the set of associated certificates.")
   (xdoc::p
    "An @('accept') event moves a certificate from the network to the DAG,
     for the validator that is the destination of the message:
     thus, the set of associated certificates does not change,
     although the DAG component and the network component change,
     but in a way that they compensate each other.
     If the validator is not the destination of the message,
     then nothing changes for the validator;
     none of its associated certificates moves.")
   (xdoc::p
    "For the other three kinds of events,
     there are no changes to DAGs and network,
     and thus the associated certificates do not change for any validator."))

  (defruled associated-certs-of-create-next
    (implies (set::in val (correct-addresses systate))
             (equal (associated-certs val (create-next cert systate))
                    (set::insert (certificate-fix cert)
                                 (associated-certs val systate))))
    :enable (associated-certs
             validator-state->dag-of-create-next
             get-network-state-of-create-next
             message-certs-with-dest-of-union
             message-certs-with-dest-of-make-certificate-messages))

  (defruled associated-certs-of-accept-next
    (implies (and (set::in val (correct-addresses systate))
                  (accept-possiblep msg systate))
             (equal (associated-certs val (accept-next msg systate))
                    (associated-certs val systate)))
    :enable (associated-certs
             validator-state->dag-of-accept-next
             get-network-state-of-accept-next
             message-certs-with-dest-of-delete
             set::expensive-rules
             in-of-message-certs-with-dest
             accept-possiblep))

  (defruled associated-certs-of-advance-next
    (implies (and (set::in val (correct-addresses systate))
                  (advance-possiblep val1 systate))
             (equal (associated-certs val (advance-next val1 systate))
                    (associated-certs val systate)))
    :enable associated-certs)

  (defruled associated-certs-of-commit-next
    (implies (and (set::in val (correct-addresses systate))
                  (commit-possiblep val1 systate))
             (equal (associated-certs val (commit-next val1 systate))
                    (associated-certs val systate)))
    :enable associated-certs))
