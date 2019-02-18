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
     the input of SHA-256 is a sequence of less than @($2^{64}$) bits.
     Since Bitcoin uses SHA-256 on byte sequences,
     our SHA-256 interface function operates on bytes directly,
     by taking as input a list of less than @($2^{61}$) such bytes.
     This is formalized by the guard of the constrained function.")
   (xdoc::p
    "According to FIPS PUB 180-4,
     the output of SHA-256 is a sequence of exactly 256 bits.
     Since Bitcoin treats SHA-256 outputs as byte sequences,
     our SHA-256 interface funtion returns 32 bytes.")
   (xdoc::p
    "We assume that the SHA-256 function fixes its argument to its guard.
     This involves not only fixing it to a true list of bytes,
     but also capping its length to be below @($2^{61}$).")
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

    (defrule sha-256-fixes-input-type
      (equal (sha-256 (byte-list-fix bytes))
             (sha-256 bytes)))

    (defrule sha-256-fixes-input-length
      (equal (sha-256 (take (1- (expt 2 61)) bytes))
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
             :use (sha-256-fixes-input-type
                   (:instance sha-256-fixes-input-type (bytes bytes-equiv)))
             :in-theory (disable sha-256-fixes-input-type)))))
