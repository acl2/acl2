; AleoBFT Library
;
; Copyright (C) 2024 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOBFT")

(include-book "system-certificates")

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
     We define this notion only for correct validators (signers).
     We could also define it for faulty validators,
     since they can be signers,
     but we only need this notion for correct validators."))
  (certs-with-signer val (system-certs systate))
  :hooks (:fix)

  ///

  (defruled in-signed-certs-when-in-system-and-signer
    (implies (and (set::in cert (system-certs systate))
                  (set::in signer (certificate->signers cert))
                  (set::in signer (correct-addresses systate)))
             (set::in cert (signed-certs signer systate)))
    :enable in-of-certs-with-signer))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled signed-certs-when-init
  :short "Initially, validators have signed no certificates."
  (implies (and (system-initp systate)
                (set::in val (correct-addresses systate)))
           (equal (signed-certs val systate)
                  nil))
  :enable (signed-certs
           system-certs-when-init))

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
     because all the others do not change the set of system certificates,
     as proved in @(see system-certs-of-next),
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
             system-certs-of-create-next
             certs-with-signer-of-insert))

  (defruled signed-certs-of-accept-next
    (implies (and (set::in val (correct-addresses systate))
                  (accept-possiblep msg systate))
             (equal (signed-certs val (accept-next msg systate))
                    (signed-certs val systate)))
    :enable (signed-certs
             system-certs-of-accept-next))

  (defruled signed-certs-of-advance-next
    (implies (and (set::in val (correct-addresses systate))
                  (advance-possiblep val1 systate))
             (equal (signed-certs val (advance-next val1 systate))
                    (signed-certs val systate)))
    :enable (signed-certs
             system-certs-of-advance-next))

  (defruled signed-certs-of-commit-next
    (implies (and (set::in val (correct-addresses systate))
                  (commit-possiblep val1 systate))
             (equal (signed-certs val (commit-next val1 systate))
                    (signed-certs val systate)))
    :enable (signed-certs
             system-certs-of-commit-next)))
