; Bitcoin Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "BITCOIN")

(include-book "kestrel/crypto/interfaces/ripemd-160" :dir :system)
(include-book "kestrel/crypto/interfaces/sha-256" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ cryptography
  :parents (bitcoin)
  :short "Cryptography in Bitcoin."
  :long
  (xdoc::topstring
   (xdoc::p
    "Bitcoin uses a number of cryptographic functions
     that are described in external standards.
     Our Bitcoin model uses cryptographic functions
     from external libraries.")
   (xdoc::p
    "Here we define the Hash160 function,
     which appears to be specific to Bitcoin."))
  :order-subtopics t
  :default-parent t)

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
  (ripemd-160-bytes (sha-256-bytes bytes))
  ///

  (more-returns
   (hash (equal (len hash) 20) :name len-of-hash160)))
