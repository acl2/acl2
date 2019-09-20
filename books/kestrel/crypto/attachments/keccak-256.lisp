; Cryptographic Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "CRYPTO")

(include-book "kestrel/crypto/interfaces/keccak-256" :dir :system)
(include-book "kestrel/crypto/keccak/keccak" :dir :system)

(local (include-book "kestrel/bv-lists/unsigned-byte-listp" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection keccak-256-attachment
  :parents (attachments)
  :short (xdoc::topstring
          "Executable attachment for the "
          (xdoc::seetopic "keccak-256-interface" "Keccak-256 interface")
          " that operates on bytes.")
  :long
  (xdoc::topstring
   (xdoc::p
    "We define a wrapper of the executable definition
     and attach the wrapper to the constrained function.
     The wrapper just serves to use the fixtypes for byte lists,
     and to fix the input accordingly."))

  (define keccak-256-bytes-wrapper ((bytes byte-listp))
    :returns (hash byte-listp
                   :hints (("Goal"
                            :in-theory
                            (enable
                             acl2::byte-listp-rewrite-unsigned-byte-listp
                             acl2::unsigned-byte-listp-rewrite))))
    (b* ((bytes (mbe :logic (byte-list-fix bytes) :exec bytes)))
      (keccak::keccak-256-bytes bytes))
    :guard-hints (("Goal"
                   :in-theory
                   (enable acl2::byte-listp-rewrite-unsigned-byte-listp
                           acl2::unsigned-byte-listp-rewrite)))

    :hooks (:fix)

    ///

    (defrule len-of-keccak-256-bytes-wrapper
      (equal (len (keccak-256-bytes-wrapper bytes))
             32)))

  (defattach keccak-256-bytes keccak-256-bytes-wrapper))
