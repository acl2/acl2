; Bitcoin Library -- Cryptographic Interface
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "BITCOIN")

(include-book "kestrel/utilities/fixbytes/ubyte8" :dir :system)
(include-book "kestrel/utilities/xdoc/defxdoc-plus" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ crypto-interface
  :parents (bitcoin)
  :short "Cryptographic interface for Bitcoin."
  :long
  (xdoc::topapp
   (xdoc::p
    "Bitcoin uses a number of cryptographic functions
     that are described in external standards.
     These cryptographic functions are largely black boxes,
     in the sense that most of their details
     are not needed in order to describe the behavior of Bitcoin.
     In other words, the formal model of Bitcoin
     can be parameterized over most of those details.")
   (xdoc::p
    "We introduce (weakly) constrained ACL2 functions
     to represent these cryptographic functions.
     The collection of these functions forms
     a cryptographic interface for (i.e. used by) Bitcoin.")
   (xdoc::p
    "Of course,
     complete specifications and/or implementations of those functions
     are needed to obtain
     a complete specification and/or implementation of Bitcoin.
     Such complete specifications/implementations can replace,
     or be <see topic='@(url defattach)'>attached</see> to,
     the constrained ones introduced here.")
   (xdoc::p
    "We start with just a function for SHA-256,
     and we will add others as needed."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection sha-256
  :short "SHA-256 interface."
  :long
  (xdoc::topapp
   (xdoc::p
    "SHA-256 is specified in the
     <a href=\"https://csrc.nist.gov/publications/detail/fips/180/4/final\"
     >FIPS PUB 180-4 standard</a>.")
   (xdoc::p
    "According to FIPS PUB 180-4,
     the input of SHA-256 is a sequence of less than @($2^{64}$) bits.
     Since Bitcoin uses SHA-256 on unsigned 8-bit byte sequences,
     our SHA-256 interface function operates on these bytes directly,
     by taking as input a list of less than @($2^{61}$) such bytes.
     This is formalized by the guard of the constrained function.")
   (xdoc::p
    "According to FIPS PUB 180-4,
     the output of SHA-256 is a sequence of exactly 256 bits.
     Since Bitcoin treats SHA-256 outputs as unsigned 8-bit byte sequences,
     our SHA-256 interface funtion returns 32 such bytes.")
   (xdoc::p
    "We assume that the SHA-256 function fixes its argument to its guard.
     This involves not only fixing it to a true list of unsigned 8-bit bytes,
     but also capping its length to @($2^{61}$).")
   (xdoc::def "sha-256"))

  (encapsulate

    (((sha-256 *) => *
      :formals (bytes)
      :guard (and (ubyte8-listp bytes)
                  (< (len bytes) (expt 2 61)))))

    (local
     (defun sha-256 (bytes)
       (declare (ignore bytes))
       (make-list 32 :initial-element 0)))

    (defrule ubyte8-listp-of-sha-256
      (ubyte8-listp (sha-256 bytes)))

    (defrule true-listp-of-sha-256
      (true-listp (sha-256 bytes))
      :rule-classes :type-prescription)

    (defrule consp-of-sha-256
      (consp (sha-256 bytes))
      :rule-classes :type-prescription)

    (defrule len-of-sha-256
      (equal (len (sha-256 bytes))
             32))

    (defrule sha-256-fixes-input-type
      (equal (sha-256 (ubyte8-list-fix bytes))
             (sha-256 bytes)))

    (defrule sha-256-fixes-input-length
      (equal (sha-256 (take (expt 2 61) bytes))
             (sha-256 bytes)))))
