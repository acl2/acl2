; Cryptographic Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "CRYPTO")

(include-book "kestrel/crypto/interfaces/sha-256" :dir :system)
(include-book "kestrel/crypto/sha-2/sha-256" :dir :system)

(local (include-book "kestrel/bv-lists/unsigned-byte-listp" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection sha-256-attachment
  :parents (attachments)
  :short (xdoc::topstring
          "Executable attachment for the "
          (xdoc::seetopic "sha-256-interface" "SHA-256 interface")
          " that operates on bytes.")
  :long
  (xdoc::topstring
   (xdoc::p
    "We define a wrapper of the executable definition
     and attach the wrapper to the constrained function.
     The wrapper just serves to use the fixtypes for byte lists,
     and to fix the input accordingly."))

  (define sha-256-bytes-wrapper ((bytes byte-listp))
    :guard (< (len bytes) (expt 2 61))
    :returns (hash byte-listp
                   :hints (("Goal"
                            :in-theory
                            (enable
                             acl2::byte-listp-rewrite-unsigned-byte-listp
                             acl2::unsigned-byte-listp-rewrite))))
    (b* ((bytes (mbe :logic (byte-list-fix bytes) :exec bytes)))
      (sha2::sha-256-bytes bytes))

    :hooks (:fix)

    ///

    (defrule len-of-sha-256-bytes-wrapper
      (equal (len (sha-256-bytes-wrapper bytes))
             32)))

  (defattach sha-256-bytes sha-256-bytes-wrapper))
