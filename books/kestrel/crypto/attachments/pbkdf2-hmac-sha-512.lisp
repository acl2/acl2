; Cryptographic Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "CRYPTO")

(include-book "kestrel/crypto/interfaces/pbkdf2-hmac-sha-512" :dir :system)
(include-book "kestrel/crypto/kdf/pbkdf2-hmac-sha-512" :dir :system)

(local (include-book "kestrel/bv-lists/unsigned-byte-listp" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection pbkdf2-hmac-sha-512-attachment
  :parents (attachments)
  :short (xdoc::topstring
          "Executable attachment for the "
          (xdoc::seetopic "pbkdf2-hmac-sha-512-interface"
                        "PBKDF2-HMAC-SHA-512 interface")
          ".")
  :long
  (xdoc::topstring
   (xdoc::p
    "We define a wrapper of the executable definition
     and attach the wrapper to the constrained function.
     The wrapper just serves to use the fixtypes for byte lists,
     to fix the password and salt input accordingly,
     and to fix the iterations and length inputs to positive integers."))

  (define pbkdf2-hmac-sha-512-wrapper ((password byte-listp)
                                       (salt byte-listp)
                                       (iterations posp)
                                       (length posp))
    :guard (and (< (len password) (expt 2 125))
                (< (len salt) (- (expt 2 125) 132))
                (<= length (* (1- (expt 2 32)) 64)))
    :returns (result byte-listp
                     :hints (("Goal"
                              :in-theory
                              (enable
                               acl2::byte-listp-rewrite-unsigned-byte-listp
                               acl2::unsigned-byte-listp-rewrite))))
    (b* ((password (mbe :logic (byte-list-fix password) :exec password))
         (salt (mbe :logic (byte-list-fix salt) :exec salt))
         (iterations (mbe :logic (pos-fix iterations) :exec iterations))
         (length (mbe :logic (pos-fix length) :exec length)))
      (kdf::pbkdf2-hmac-sha-512 password salt iterations length))

    :hooks (:fix)

    ///

    (defrule len-of-pbkdf2-hmac-sha-512-wrapper
      (equal (len (pbkdf2-hmac-sha-512-wrapper password salt iterations length))
             (pos-fix length))))

  (defattach (pbkdf2-hmac-sha-512 pbkdf2-hmac-sha-512-wrapper)
    :hints (("Goal"
             :use
             (pbkdf2-hmac-sha-512-wrapper-pos-equiv-congruence-on-iterations
              pbkdf2-hmac-sha-512-wrapper-pos-equiv-congruence-on-length)))))
