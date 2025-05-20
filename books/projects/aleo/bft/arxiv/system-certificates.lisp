; AleoBFT Library
;
; Copyright (C) 2024 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOBFT-ARXIV")

(include-book "initialization")
(include-book "transitions")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ system-certificates
  :parents (correctness)
  :short "Certificates in the system."
  :long
  (xdoc::topstring
   (xdoc::p
    "We introduce an operation to collect all the certificates in the system.
     Certificates are in validator DAGs and in network messages.")
   (xdoc::p
    "We define this notion here,
     and we prove theorems about its initial value,
     and about how its value changes in response to events."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define validators-certs ((vals address-setp) (systate system-statep))
  :guard (set::subset vals (correct-addresses systate))
  :returns (certs certificate-setp)
  :short "Certificates from the DAGs of a set of (correct) validators."
  :long
  (xdoc::topstring
   (xdoc::p
    "We union the DAGs of the given validators."))
  (b* (((when (or (not (mbt (address-setp vals)))
                  (set::emptyp vals)))
        nil)
       (vstate (get-validator-state (set::head vals) systate)))
    (set::union (validator-state->dag vstate)
                (validators-certs (set::tail vals) systate)))
  :verify-guards :after-returns
  :guard-hints (("Goal" :in-theory (enable* set::expensive-rules)))
  :hooks (:fix)

  ///

  (defruled in-of-validators-certs-when-in-some-dag
    (implies (and (address-setp vals)
                  (set::subset vals (correct-addresses systate))
                  (set::in val vals)
                  (set::in cert (validator-state->dag
                                 (get-validator-state val systate))))
             (set::in cert (validators-certs vals systate)))
    :induct t
    :enable set::expensive-rules))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define system-certs ((systate system-statep))
  :returns (certs certificate-setp)
  :short "Certificates in the system."
  :long
  (xdoc::topstring
   (xdoc::p
    "We union the DAGs of all correct validators
     with the certificates in all the messages in the network."))
  (set::union (validators-certs (correct-addresses systate) systate)
              (message-set->certificate-set (get-network-state systate)))
  :hooks (:fix)

  ///

  (defruled in-system-certs-when-in-some-dag
    (implies (and (set::in val (correct-addresses systate))
                  (set::in cert (validator-state->dag
                                 (get-validator-state val systate))))
             (set::in cert (system-certs systate)))
    :enable in-of-validators-certs-when-in-some-dag)

  (defruled in-system-certs-when-in-network
    (implies (set::in msg (get-network-state systate))
             (set::in (message->certificate msg)
                      (system-certs systate)))
    :enable message->certificate-in-message-set->certificate-set))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection system-certs-when-init
  :short "Initially, there are no certificates in the system."
  :long
  (xdoc::topstring
   (xdoc::p
    "All DAGs are initially empty,
     and the network is initially empty."))

  (defruled validators-certs-when-init
    (implies (and (system-initp systate)
                  (set::subset vals (correct-addresses systate)))
             (equal (validators-certs vals systate) nil))
    :induct t
    :enable (validators-certs
             system-initp
             system-validators-initp-necc
             validator-init
             set::expensive-rules))

  (defruled system-certs-when-init
    (implies (system-initp systate)
             (equal (system-certs systate) nil))
    :enable (system-certs
             validators-certs-when-init
             system-initp
             message-set->certificate-set)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection system-certs-of-next
  :short "How the certificates in the system
          change (or not) for each transition."
  :long
  (xdoc::topstring
   (xdoc::p
    "The only kind of event that changes the set of system certificates
     is @('create'), by adding the created certificate to the set:
     the certificate is added to the network,
     and possibly to the author's DAG (if the author is correct).
     However, if there are no correct validators at all,
     there is actually no change to the set of system certificates;
     this is an impractical case, which in particular does not satisfy
     the normal fault tolerance assumptions.")
   (xdoc::p
    "An @('accept') event just moves a certificate,
     from the network to a DAG.
     The whole set is unaffected.")
   (xdoc::p
    "An @('advance') or @('commit') event does not change
     any DAG or the network.
     So the set remains the same."))

  ;; create:

  (defruled validators-certs-of-create-next
    (implies (and (set::subset vals (correct-addresses systate))
                  (address-setp vals))
             (equal (validators-certs vals (create-next cert systate))
                    (if (set::in (certificate->author cert) vals)
                        (set::insert (certificate-fix cert)
                                     (validators-certs vals systate))
                      (validators-certs vals systate))))
    :induct t
    :enable (validators-certs
             validator-state->dag-of-create-next
             set::expensive-rules))

  (defruled system-certs-of-create-next
    (equal (system-certs (create-next cert systate))
           (if (set::emptyp (correct-addresses systate))
               (system-certs systate)
             (set::insert (certificate-fix cert)
                          (system-certs systate))))
    :enable (system-certs
             validators-certs-of-create-next
             get-network-state-of-create-next
             message-set->certificate-set-of-make-certificate-messages
             message-set->certificate-set-of-union))

  ;; accept:

  (defruled validators-certs-of-accept-next
    (implies (and (set::subset vals (correct-addresses systate))
                  (address-setp vals)
                  (accept-possiblep msg systate))
             (equal (validators-certs vals (accept-next msg systate))
                    (if (set::in (message->destination msg) vals)
                        (set::insert (message->certificate msg)
                                     (validators-certs vals systate))
                      (validators-certs vals systate))))
    :induct t
    :enable (validators-certs
             validator-state->dag-of-accept-next
             set::expensive-rules))

  (defruled system-certs-of-accept-next
    (implies (accept-possiblep msg systate)
             (equal (system-certs (accept-next msg systate))
                    (system-certs systate)))
    :enable (system-certs
             validators-certs-of-accept-next
             get-network-state-of-accept-next
             message-set->certificate-set-monotone
             accept-possiblep
             in-of-message-set->certificate-set-of-delete
             set::expensive-rules)
    :use (:instance message->certificate-in-message-set->certificate-set
                    (msg (message-fix msg))
                    (msgs (get-network-state systate))))

  ;; advance:

  (defruled validators-certs-of-advance-next
    (implies (and (set::subset vals (correct-addresses systate))
                  (address-setp vals)
                  (advance-possiblep val systate))
             (equal (validators-certs vals (advance-next val systate))
                    (validators-certs vals systate)))
    :induct t
    :enable (validators-certs
             set::expensive-rules))

  (defruled system-certs-of-advance-next
    (implies (advance-possiblep val systate)
             (equal (system-certs (advance-next val systate))
                    (system-certs systate)))
    :enable (system-certs
             validators-certs-of-advance-next))

  ;; commit:

  (defruled validators-certs-of-commit-next
    (implies (and (set::subset vals (correct-addresses systate))
                  (address-setp vals)
                  (commit-possiblep val systate))
             (equal (validators-certs vals (commit-next val systate))
                    (validators-certs vals systate)))
    :induct t
    :enable (validators-certs
             set::expensive-rules))

  (defruled system-certs-of-commit-next
    (implies (commit-possiblep val systate)
             (equal (system-certs (commit-next val systate))
                    (system-certs systate)))
    :enable (system-certs
             validators-certs-of-commit-next)))
