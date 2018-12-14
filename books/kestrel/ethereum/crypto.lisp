; Ethereum Library -- Cryptographic Interface
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ETHEREUM")

(include-book "kestrel/ethereum/bytes" :dir :system)
(include-book "kestrel/utilities/xdoc/defxdoc-plus" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ crypto
  :parents (ethereum)
  :short "Cryptographic interface for Ethereum."
  :long
  (xdoc::topapp
   (xdoc::p
    "Ethereum uses a number of cryptographic functions
     that are described in external standards.
     These cryptographic functions are largely black boxes,
     in the sense that most of their details
     are not needed in order to describe the behavior of Ethereum.
     In other words, the formal model of Ethereum
     can be parameterized over most of those details.")
   (xdoc::p
    "We introduce (weakly) constrained ACL2 functions
     to represent these cryptographic functions.
     The collection of these functions forms
     a cryptographic interface for (i.e. used by) Ethereum.")
   (xdoc::p
    "Of course,
     complete specifications and/or implementations of those functions
     are needed to obtain
     a complete specification and/or implementation of Ethereum.
     Such complete specifications/implementations can replace,
     or be <see topic='@(url defattach)'>attached</see> to,
     the constrained functions introduced here.")
   (xdoc::p
    "We start with just a function for Keccak-256.
     We will add the others as needed."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection keccak-256
  :short "Keccak-256 interface."
  :long
  (xdoc::topapp
   (xdoc::p
    "This corresponds to @($\\mathtt{KEC}$) [YP:3].
     It is not defined in [YP], but in
     <a href=\"https://keccak.team/keccak.html\">the Keccak web site</a>.")
   (xdoc::p
    "This function takes as input an arbitrarily long sequence of bytes
     and returns as output a sequence of 32 bytes (i.e. 256 bits).
     These properties are expressed by the guard and theorems.")
   (xdoc::p
    "We also assume that
     this function fixes its argument to be a true list of bytes.")
   (xdoc::def "keccak-256"))

  (encapsulate

    (((keccak-256 *) => * :formals (bytes) :guard (byte-listp bytes)))

    (local (defun keccak-256 (bytes) (declare (ignore bytes)) (repeat 32 0)))

    (defrule byte-listp-of-keccak-256
      (byte-listp (keccak-256 bytes)))

    (defrule len-of-keccak-256
      (equal (len (keccak-256 bytes))
             32))

    (defrule keccak-256-fixes-input
      (equal (keccak-256 (byte-list-fix bytes))
             (keccak-256 bytes))))

  (defrule true-listp-of-keccak-256
    (true-listp (keccak-256 bytes))
    :rule-classes :type-prescription))
