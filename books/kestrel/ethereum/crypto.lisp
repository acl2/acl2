; Ethereum -- Cryptography
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ETHEREUM")

(include-book "kestrel/crypto/keccak-256-placeholder" :dir :system)
(include-book "bytes")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ cryptography
  :parents (ethereum)
  :short "Cryptography in Ethereum."
  :long
  (xdoc::topstring
   (xdoc::p
    "Ethereum uses a number of cryptographic functions
     that are described in external standards.")
   (xdoc::p
    "Our Ethereum model uses cryptographic functions
     from external libraries.
     Here we introduce thin wrappers of the library cryptographic functions.
     The main purpose of these wrappers is
     to formally relate the cryptographic functions
     with other functions (e.g. type recognizers) in our Ethereum model.")
   (xdoc::p
    "See the cryptographic libraries for details on
     the formalized cryptographic functions."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define keccak-256 ((bytes byte-listp))
  :returns (hash byte-list32p
                 :hints (("Goal"
                          :in-theory
                          (enable byte-list32p
                                  byte-listp-rewrite-unsigned-byte-listp))))
  :short "Keccak-256 hash function."
  :long
  (xdoc::topstring-p
   "This corresponds to @($\\mathtt{KEC}$) [YP:3].")
  (crypto::keccak-256 bytes)
  :no-function t
  ///

  (more-returns
   (hash true-listp
         :name true-listp-of-keccak-256
         :rule-classes :type-prescription)
   (hash consp
         :name consp-of-keccak-256
         :rule-classes :type-prescription)
   (hash (equal (len hash) 32)
         :name len-of-keccak-256))

  (fty::deffixequiv keccak-256
    :hints (("Goal"
             :in-theory
             (enable byte-list-fix-rewrite-unsigned-byte-list-fix)))))
