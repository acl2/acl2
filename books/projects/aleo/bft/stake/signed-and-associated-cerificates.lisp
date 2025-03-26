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

(include-book "same-associated-certificates")
(include-book "signed-certificates")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ signed-and-associated-cerificates
  :parents (correctness)
  :short "Some properties about signed and associated certificates."
  :long
  (xdoc::topstring
   (xdoc::p
    "Currently we have just one property, i.e. one theorem.
     This depends on both @(tsee signed-certs)
     and the @(tsee same-associated-certs-p) invariant,
     so it is natural to put it into its own file and XDOC topic."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled in-signed-certs-when-in-associated-and-signer
  :short "If all validators have the same associated certificates,
          then each certificate signed by a validator
          is in the set of the validator's signed certificates."
  :long
  (xdoc::topstring
   (xdoc::p
    "The set of signed certificates, @(tsee signed-certs),
     is defined over the associated certificates of the same validator.
     But this theorem involves a generic validator @('val'),
     and a certificate @('cert') associated to it,
     and a signer @('signer') of the certificate.
     It says that if all validators have the same associated certificates
     (which they do, as proved in @(see same-associated-certificates)),
     the @('cert') is in the signed certificates of @('signer').
     The equality of the sets of associated certificates is needed
     as a bridge between (the certificates of) @('val') and @('signer')."))
  (implies (and (same-associated-certs-p systate)
                (set::in val (correct-addresses systate))
                (set::in cert (associated-certs val systate))
                (set::in signer (certificate->signers cert))
                (set::in signer (correct-addresses systate)))
           (set::in cert (signed-certs signer systate)))
  :enable (signed-certs
           in-of-certs-with-signer)
  :disable (same-associated-certs-p
            same-associated-certs-p-necc)
  :use (:instance same-associated-certs-p-necc
                  (val1 val)
                  (val2 signer)))
