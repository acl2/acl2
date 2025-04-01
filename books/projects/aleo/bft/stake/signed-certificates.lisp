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

(defxdoc+ signed-certificates
  :parents (correctness)
  :short "Certificates signed by validators."
  :long
  (xdoc::topstring
   (xdoc::p
    "All the certificates in the system are associated to some validator,
     as formalized in @(see associated-certificates).
     As proved in @(see same-associated-certificates),
     all the validators have the same associated certificates,
     so all the certificates in the system can be obtained as
     the certificates associated to any validator in the system.")
   (xdoc::p
    "We define an operation to return
     all the certificates in the system signed by a given validator.
     We prove theorems about its initial value,
     and about how its value changes in response to events."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define signed-certs ((val addressp) (systate system-statep))
  :guard (set::in val (correct-addresses systate))
  :returns (certs certificate-setp)
  :short "Certificates signed by a validator."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are all the certificates in the system signed by the validator.
     As proved in @(see same-associated-certificates),
     validators have the same associated certificates,
     so any such set of associated certificates is
     the set of all the certificates in the system.
     We pick the set of the signer,
     and we select the ones whose signers include the signer.")
   (xdoc::p
    "We define this notion only for correct validators (signers).
     We could also define it for faulty validators,
     since they can be signers,
     but we only need this notion for correct validators."))
  (certs-with-signer val (associated-certs val systate))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled signed-certs-when-init
  :short "Initially, validators have signed no certificates."
  (implies (and (system-initp systate)
                (set::in val (correct-addresses systate)))
           (equal (signed-certs val systate)
                  nil))
  :enable (signed-certs
           associated-certs-when-init))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection signed-certs-of-next
  :short "How the certificates signed by a validator
          change (or not) for each transition."
  :long
  (xdoc::topstring
   (xdoc::p
    "The only kind of event that may change
     the certificates signed by a validator
     is @('create'),
     because all the others do not change the set of associated certificates,
     as proved in @(see associated-certs-of-next),
     which are a superset of the signed certificates.
     Whether the set of signed certificates actually changes
     depends on whether the validator
     is a signer of the certificate or not;
     so our theorem for @('create') has a conditional.
     The theorems for the other kinds of events
     assert that there is no change in the set of signed certificates."))

  (defruled signed-certs-of-create-next
    (implies (set::in val (correct-addresses systate))
             (equal (signed-certs val (create-next cert systate))
                    (if (set::in (address-fix val)
                                 (certificate->signers cert))
                        (set::insert (certificate-fix cert)
                                     (signed-certs val systate))
                      (signed-certs val systate))))
    :enable (signed-certs
             associated-certs-of-create-next
             certs-with-signer-of-insert))

  (defruled signed-certs-of-receive-next
    (implies (and (set::in val (correct-addresses systate))
                  (receive-possiblep msg systate))
             (equal (signed-certs val (receive-next msg systate))
                    (signed-certs val systate)))
    :enable (signed-certs
             associated-certs-of-receive-next))

  (defruled signed-certs-of-store-next
    (implies (and (set::in val (correct-addresses systate))
                  (store-possiblep val1 cert systate))
             (equal (signed-certs val (store-next val1 cert systate))
                    (signed-certs val systate)))
    :enable (signed-certs
             associated-certs-of-store-next))

  (defruled signed-certs-of-advance-next
    (implies (and (set::in val (correct-addresses systate))
                  (advance-possiblep val1 systate))
             (equal (signed-certs val (advance-next val1 systate))
                    (signed-certs val systate)))
    :enable (signed-certs
             associated-certs-of-advance-next))

  (defruled signed-certs-of-commit-next
    (implies (and (set::in val (correct-addresses systate))
                  (commit-possiblep val1 systate))
             (equal (signed-certs val (commit-next val1 systate))
                    (signed-certs val systate)))
    :enable (signed-certs
             associated-certs-of-commit-next))

  (defruled signed-certs-of-timeout-next
    (implies (and (set::in val (correct-addresses systate))
                  (timeout-possiblep val1 systate))
             (equal (signed-certs val (timeout-next val1 systate))
                    (signed-certs val systate)))
    :enable (signed-certs
             associated-certs-of-timeout-next)))
