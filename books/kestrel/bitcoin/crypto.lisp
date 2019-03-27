; Bitcoin -- Cryptography
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "BITCOIN")

(include-book "kestrel/crypto/hmac-sha-512-placeholder" :dir :system)
(include-book "kestrel/crypto/ripemd-160-placeholder" :dir :system)
(include-book "kestrel/crypto/secp256k1-placeholder" :dir :system)
(include-book "kestrel/crypto/sha-256-placeholder" :dir :system)
(include-book "bytes")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ cryptography
  :parents (bitcoin)
  :short "Cryptography in Bitcoin."
  :long
  (xdoc::topstring
   (xdoc::p
    "Bitcoin uses a number of cryptographic functions
     that are described in external standards.")
   (xdoc::p
    "Our Bitcoin model uses cryptographic functions
     from external libraries.
     Here we introduce thin wrappers of the library cryptographic functions.
     The main purpose of these wrappers is
     to formally relate the cryptographic functions
     with other functions (e.g. type recognizers) in our Bitcoin model.")
   (xdoc::p
    "See the cryptographic libraries for details on
     the formalized cryptographic functions."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sha-256 ((bytes byte-listp))
  :guard (< (len bytes) (expt 2 61))
  :returns (hash byte-listp
                 :hints (("Goal"
                          :in-theory
                          (enable byte-listp-rewrite-unsigned-byte-listp))))
  :short "SHA-256 hash function."
  (crypto::sha-256 bytes)
  :no-function t
  ///

  (more-returns
   (hash true-listp
         :name true-listp-of-sha-256
         :rule-classes :type-prescription)
   (hash consp
         :name consp-of-sha-256
         :rule-classes :type-prescription)
   (hash (equal (len hash) 32)
         :name len-of-sha-256))

  (fty::deffixequiv sha-256
    :hints (("Goal"
             :in-theory
             (enable byte-list-fix-rewrite-unsigned-byte-list-fix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ripemd-160 ((bytes byte-listp))
  :returns (hash byte-listp
                 :hints (("Goal"
                          :in-theory
                          (enable byte-listp-rewrite-unsigned-byte-listp))))
  :short "RIPEMD-160 hash function."
  (crypto::ripemd-160 bytes)
  :no-function t
  ///

  (more-returns
   (hash true-listp
         :name true-listp-of-ripemd-160
         :rule-classes :type-prescription)
   (hash consp
         :name consp-of-ripemd-160
         :rule-classes :type-prescription)
   (hash (equal (len hash) 20)
         :name len-of-ripemd-160))

  (fty::deffixequiv ripemd-160
    :hints (("Goal"
             :in-theory
             (enable byte-list-fix-rewrite-unsigned-byte-list-fix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define hmac-sha-512 ((key byte-listp) (text byte-listp))
  :guard (and (< (len key) (expt 2 125))
              (< (len text) (- (expt 2 125) 128)))
  :returns (hash byte-listp
                 :hints (("Goal"
                          :in-theory
                          (enable byte-listp-rewrite-unsigned-byte-listp))))
  :short "HMAC-SHA-512 keyed hash function."
  (crypto::hmac-sha-512 key text)
  :no-function t
  ///

  (more-returns
   (hash true-listp
         :name true-listp-of-hmac-sha-512
         :rule-classes :type-prescription)
   (hash consp
         :name consp-of-hmac-sha-512
         :rule-classes :type-prescription)
   (hash (equal (len hash) 64)
         :name len-of-hmac-sha-512))

  (fty::deffixequiv hmac-sha-512
    :hints (("Goal"
             :in-theory
             (enable byte-list-fix-rewrite-unsigned-byte-list-fix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define secp256k1-point-to-bytes ((point secp256k1-pointp)
                                  (compressp booleanp))
  :returns (bytes byte-listp
                  :hints (("Goal"
                           :in-theory
                           (enable byte-listp-rewrite-unsigned-byte-listp))))
  :short "Represent a point in compressed or uncompressed form."
  :long
  (xdoc::topstring-p
   "See @(tsee crypto::secp256k1-point-to-bytes).")
  (crypto::secp256k1-point-to-bytes point compressp)
  :no-function t
  :hooks (:fix)
  ///

  (defrule len-of-secp256k1-point-to-bytes
    (equal (len (secp256k1-point-to-bytes point compressp))
           (cond ((secp256k1-infinityp point) 1)
                 (compressp 33)
                 (t 65)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define hash160 ((bytes byte-listp))
  :guard (< (len bytes) (expt 2 61))
  :returns (hash byte-listp)
  :short "Hash160 function."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is SHA-256 followed by RIPEMD-160.
     It is sometimes called `Hash160',
     e.g. see the @('OP_HASH160') opcode,
     or see the documentation of BIP 32."))
  (ripemd-160 (sha-256 bytes))
  ///

  (more-returns
   (hash (equal (len hash) 20) :name len-of-hash160)))
