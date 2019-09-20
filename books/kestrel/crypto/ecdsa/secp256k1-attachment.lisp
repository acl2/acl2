; Elliptic Curve Digital Signature Algorithm Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ECDSA")

(include-book "secp256k1-interface")
(include-book "deterministic-ecdsa-secp256k1")
(include-book "kestrel/utilities/bits-and-bytes-as-digits" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection secp256k1-ecdsa-attachment
  :parents (crypto::attachments elliptic-curve-digital-signature-algorithm)
  :short (xdoc::topstring
          "Executable attachment for the "
          (xdoc::seetopic "secp256k1-ecdsa-interface"
                        "ECDSA interface for the curve secp256k1")
          ".")
  :long
  (xdoc::topstring
   (xdoc::p
    "We define a wrapper of
     the secp256k1 deterministic signature definition with public key recovery,
     and attach the wrapper to the constrained function.
     The wrapper serves to
     use the fixtypes for byte lists and to fix all the inputs
     and convert bytes to bits as required by the signature definition."))

  (define secp256k1-sign-det-rec-wrapper ((hash byte-listp)
                                          (key secp256k1-priv-key-p)
                                          (small-x? booleanp)
                                          (small-s? booleanp))
    :returns
    (mv (error? booleanp)
        (x-index natp)
        (y-even? booleanp)
        (r secp256k1-fieldp
           :hints (("Goal" :in-theory (enable secp256k1-fieldp))))
        (s secp256k1-fieldp
           :hints
          (("Goal"
            :in-theory (enable secp256k1-fieldp)
            :use (:instance
                  posp-of-mv-nth-4-of-ecdsa-sign-deterministic-prehashed
                  (mh (bebytes=>bits hash))
                  (privkey (secp256k1-priv-key-fix key))
                  (small-x? (bool-fix small-x?))
                  (small-s? (bool-fix small-s?)))))))
    (b* ((key (mbe :logic (secp256k1-priv-key-fix key) :exec key))
         (small-x? (mbe :logic (bool-fix small-x?) :exec small-x?))
         (small-s? (mbe :logic (bool-fix small-s?) :exec small-s?))
         (hash-bits (bebytes=>bits hash))
         ((mv error? x-index y-even? r s)
          (ecdsa-sign-deterministic-prehashed hash-bits key small-x? small-s?))
         ((when error?) (mv t 0 nil 0 0)))
      (mv nil x-index y-even? r s))
    :hooks (:fix)
    :prepwork ((defrulel verify-guards-lemma
                 (implies (bit-listp bits)
                          (all-unsigned-byte-p 1 bits)))))

  (defattach secp256k1-sign-det-rec secp256k1-sign-det-rec-wrapper))
