; Bitcoin -- Cryptographic Placeholders
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "BITCOIN")

(include-book "bytes")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ crypto-placeholders
  :parents (bitcoin)
  :short "Cryptographic placeholders for Bitcoin."
  :long
  (xdoc::topapp
   (xdoc::p
    "Bitcoin uses a number of cryptographic functions.
     These are largely black boxes,
     in the sense that most of their details
     are not needed in order to describe the behavior of Bitcoin.")
   (xdoc::p
    "We introduce placeholders for these cryptographic functions,
     mostly as (weakly) constrained functions.
     Some of the simpler ones are defined instead of constrained,
     because it is actually easier to define than constrain them,
     and/or because we actually need complete definitions to describe Bitcoin.")
   (xdoc::p
    "These placeholders will be replaced with fully defined functions
     from upcoming cryptographic libraries."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection sha-256
  :short "SHA-256 placeholder."
  :long
  (xdoc::topapp
   (xdoc::p
    "SHA-256 is specified in the
     <a href=\"https://csrc.nist.gov/publications/detail/fips/180/4/final\"
     >FIPS PUB 180-4 standard</a>.")
   (xdoc::p
    "According to FIPS PUB 180-4,
     the input of SHA-256 is a sequence of less than @($2^{64}$) bits,
     or less than @($2^{61}$) bytes.
     This is formalized by the guard of the constrained function.")
   (xdoc::p
    "According to FIPS PUB 180-4,
     the output of SHA-256 is a sequence of exactly 256 bits, or 32 bytes.
     We constrain our function to return a list of 32 bytes unconditionally.")
   (xdoc::p
    "We also constrain our function to fix its argument to a list of bytes.")
   (xdoc::def "sha-256"))

  (encapsulate

    (((sha-256 *) => *
      :formals (bytes)
      :guard (and (byte-listp bytes)
                  (< (len bytes) (expt 2 61)))))

    (local
     (defun sha-256 (bytes)
       (declare (ignore bytes))
       (make-list 32 :initial-element 0)))

    (defrule byte-listp-of-sha-256
      (byte-listp (sha-256 bytes)))

    (defrule len-of-sha-256
      (equal (len (sha-256 bytes))
             32))

    (defrule sha-256-fixes-input
      (equal (sha-256 (byte-list-fix bytes))
             (sha-256 bytes))))

  (defrule true-listp-of-sha-256
    (true-listp (sha-256 bytes))
    :rule-classes :type-prescription)

  (defrule consp-of-sha-256
    (consp (sha-256 bytes))
    :rule-classes :type-prescription
    :use len-of-sha-256
    :disable len-of-sha-256)

  (defcong byte-list-equiv equal (sha-256 bytes) 1
    :hints (("Goal"
             :use (sha-256-fixes-input
                   (:instance sha-256-fixes-input (bytes bytes-equiv)))
             :in-theory (disable sha-256-fixes-input)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection hmac-sha-512
  :short "HMAC-SHA-512 placeholder."
  :long
  (xdoc::topapp
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
     a sequence of exactly 512 bits, or 32 bytes.
     We constrain our function to return a list of 64 bytes unconditionally.")
   (xdoc::p
    "We also constrain our function to fix its arguments to lists of bytes.")
   (xdoc::def "hmac-sha-512"))

  (encapsulate

    (((hmac-sha-512 * *) => *
      :formals (key text)
      :guard (and (byte-listp key)
                  (< (len key) (expt 2 125))
                  (byte-listp text)
                  (< (len text) (- (expt 2 125) 128)))))

    (local
     (defun hmac-sha-512 (key text)
       (declare (ignore key text))
       (make-list 64 :initial-element 0)))

    (defrule byte-list-of-hmac-sha-512
      (byte-listp (hmac-sha-512 key text)))

    (defrule len-of-hmac-sha-512
      (equal (len (hmac-sha-512 key text))
             64))

    (defrule hmac-sha-512-fixes-input-key
      (equal (hmac-sha-512 (byte-list-fix key) text)
             (hmac-sha-512 key text)))

    (defrule hmac-sha-512-fixes-input-text
      (equal (hmac-sha-512 key (byte-list-fix text))
             (hmac-sha-512 key text))))

  (defrule true-listp-of-hmac-sha-512
    (true-listp (hmac-sha-512 key text))
    :rule-classes :type-prescription)

  (defcong byte-list-equiv equal (hmac-sha-512 key text) 1
    :hints (("Goal"
             :use (hmac-sha-512-fixes-input-key
                   (:instance hmac-sha-512-fixes-input-key (key key-equiv)))
             :in-theory (disable hmac-sha-512-fixes-input-key))))

  (defcong byte-list-equiv equal (hmac-sha-512 key text) 2
    :hints (("Goal"
             :use (hmac-sha-512-fixes-input-text
                   (:instance hmac-sha-512-fixes-input-text (text text-equiv)))
             :in-theory (disable hmac-sha-512-fixes-input-text)))))
