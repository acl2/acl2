; Cryptographic Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "CRYPTO")

(include-book "kestrel/crypto/interfaces/hmac-sha-512" :dir :system)
(include-book "kestrel/utilities/bits-and-bytes-as-digits" :dir :system)
(include-book "kestrel/crypto/hmac/hmac-sha-512" :dir :system)

(local (include-book "kestrel/bv-lists/unsigned-byte-listp" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection hmac-sha-512-attachment
  :parents (attachments)
  :short (xdoc::topstring
          "Executable attachment for the "
          (xdoc::seetopic "hmac-sha-512-interface" "HMAC-SHA-512 interface")
          ".")
  :long
  (xdoc::topstring
   (xdoc::p
    "We define a wrapper of the executable definition
     and attach the wrapper to the constrained function.
     The wrapper serves to use the fixtypes for byte lists,
     to fix the inputs accordingly,
     and to convert the text input to bits
     as required by the executable definition
     (while the key is in bytes)."))

  (define hmac-sha-512-wrapper ((key byte-listp) (text byte-listp))
    :guard (and (< (len key) (expt 2 125))
                (< (len text) (- (expt 2 125) 128)))
    :returns (result byte-listp
                     :hints (("Goal"
                              :in-theory
                              (enable
                               acl2::byte-listp-rewrite-unsigned-byte-listp
                               acl2::unsigned-byte-listp-rewrite))))
    (b* ((key (mbe :logic (byte-list-fix key) :exec key))
         (text (mbe :logic (byte-list-fix text) :exec text))
         (text-bits (bebytes=>bits text)))
      (hmac::hmac-sha-512 key text-bits))

    :prepwork
    ((defrulel verify-guards-lemma
       (implies (bit-listp x)
                (all-unsigned-byte-p 1 x))
       :enable (bit-listp)))

    :hooks (:fix)

    ///

    (defrule len-of-hmac-sha-512-wrapper
      (equal (len (hmac-sha-512-wrapper key text))
             64)))

  (defattach hmac-sha-512 hmac-sha-512-wrapper))
