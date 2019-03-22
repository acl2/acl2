; Cryptography -- HMAC-SHA-512 Placeholder
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "CRYPTO")

(include-book "kestrel/utilities/unsigned-byte-list-fixing" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection hmac-sha-512-placeholder
  :parents (placeholders)
  :short "HMAC-SHA-512 placeholder."
  :long
  (xdoc::topstring
   (xdoc::p
    "HMAC is specified in the
     <a href=\"https://tools.ietf.org/html/rfc2104\">RFC 2104 standard</a>;
     it is parameterized over a hash function.
     HMAC-SHA-512 is the instantiation of HMAC
     with SHA-512 as the hash function.
     SHA-512 is specified in the
     <a href=\"https://csrc.nist.gov/publications/detail/fips/180/4/final\"
     >FIPS PUB 180-4 standard</a>.")
   (xdoc::p
    "According to RFC 2104, the key (a sequence of bytes)
     must be no longer than the hash block size,
     which is 128 bytes according to FIPS PUB 180-4,
     or alternatively the key must be hashable,
     which means less than @($2^{128}$) bits (i.e. @($2^{125}$) bytes) long
     according to FIPS PUB 180-4.
     The first condition implies the second condition,
     so we simply require the second condition,
     as formalized by the guard of the constrained function.
     Note that the second condition is not explicated in RFC 2104,
     but it can be reasonably inferred from the requirement to hash the key.")
   (xdoc::p
    "RFC 2104 does not explicitly state length constraints on the text,
     but those constraints can be derived from
     the input length requirements of the hash function.
     The concatenation of the xor'd (possibly hashed) key with the text
     must be less than @($2^{125}$) bytes long for SHA-512 (see above).
     Since the length of the key may reach the block size (see above),
     the text's length must be below @($2^{125}-128$),
     as formalized by the guard of the constrained function.
     For the outer hash, the input is always well below the SHA-512 limit.")
   (xdoc::p
    "According to FIPS PUB 180-4,
     the output of SHA-512 is a sequence of exactly 512 bits, or 64 bytes.
     We constrain our function to return a list of 64 bytes unconditionally.")
   (xdoc::p
    "We also constrain our function to fix its inputs to true lists of bytes.")
   (xdoc::def "hmac-sha-512"))

  (encapsulate

    (((hmac-sha-512 * *) => *
      :formals (key text)
      :guard (and (unsigned-byte-listp 8 key)
                  (< (len key) (expt 2 125))
                  (unsigned-byte-listp 8 text)
                  (< (len text) (- (expt 2 125) 128)))))

    (local
     (defun hmac-sha-512 (key text)
       (declare (ignore key text))
       (make-list 64 :initial-element 0)))

    (defrule unsigned-byte-listp-8-of-hmac-sha-512
      (unsigned-byte-listp 8 (hmac-sha-512 key text)))

    (defrule len-of-hmac-sha-512
      (equal (len (hmac-sha-512 key text))
             64))

    (defrule hmac-sha-512-fixes-input-key
      (equal (hmac-sha-512 (unsigned-byte-list-fix 8 key) text)
             (hmac-sha-512 key text)))

    (defrule hmac-sha-512-fixes-input-text
      (equal (hmac-sha-512 key (unsigned-byte-list-fix 8 text))
             (hmac-sha-512 key text))))

  (defrule true-listp-of-hmac-sha-512
    (true-listp (hmac-sha-512 key text))
    :rule-classes :type-prescription
    :use (:instance acl2::true-listp-when-unsigned-byte-listp
          (width 8) (x (hmac-sha-512 key text)))
    :disable acl2::true-listp-when-unsigned-byte-listp)

  (defrule consp-of-hmac-sha-512
    (consp (hmac-sha-512 key text))
    :rule-classes :type-prescription
    :use len-of-hmac-sha-512
    :disable len-of-hmac-sha-512))
