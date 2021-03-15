; MiMC Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (mccarthy@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "MIMC")

(include-book "xdoc/constructors" :dir :system)

(xdoc::defxdoc mimc
  :parents (crypto::cryptography zksemaphore::semaphore)
  :short "A formal specification of the MiMC hash function as used by Semaphore."
  :long
  (xdoc::topstring
   (xdoc::p
    "The MIMC library includes a formal specification of the MiMC hash function,
    as used by "
    (xdoc::ahref
     "https://docs.zkproof.org/pages/standards/accepted-workshop3/proposal-semaphore.pdf"
     "Semaphore") ".")
   (xdoc::p
    "MiMC is defined in the paper "
    (xdoc::ahref
     "https://eprint.iacr.org/2016/492"
     "MiMC: Efficient Encryption and Cryptographic Hashing
      with Minimal Multiplicative Complexity")
    ".")
   (xdoc::p
    "The following "
    (xdoc::tt "include-book")
    " command may be helpful to bring in the library:")
   (xdoc::@{}
    "(include-book \"kestrel/crypto/mimc/mimcsponge\" :dir :system)")
   (xdoc::p "The interface functions are:")
   (xdoc::ul
     (xdoc::li (xdoc::tt "(mimcsponge m n inputs field-order constants exponent nrounds)")
               (xdoc::br)
               "Absorbs the " (xdoc::tt "m") " field element inputs contained in the list "
               (xdoc::tt "inputs") " and produces " (xdoc::tt "n")
               " field element outputs.  Each input and output is a field element "
               "in the finite field of size " (xdoc::tt "field-order") ". "
               "The round constants in " (xdoc::tt "constants") " are also field elements. "
               (xdoc::br)
               (xdoc::tt "exponent") " is the power to which intermediate values are raised. "
               (xdoc::br)
               (xdoc::tt "nrounds") " is the number of rounds, which must match the length of "
               (xdoc::tt "constants") ".")
     (xdoc::li (xdoc::tt "(mimcsponge-semaphore m n inputs)")
               (xdoc::br)
               "Calls " (xdoc::tt "mimcsponge") " with the field order "
               (xdoc::seetopic "zksemaphore::baby-jubjub-prime" "<tt>(zksemaphore::baby-jubjub-prime)</tt>")
               " (which is the same as " (xdoc::tt "(primes::bn-254-group-prime)")
               "),  the constants in " (xdoc::tt "(mimc-feistel-220-constants)")
               ", the exponent " (xdoc::tt "5") ", and the number of rounds " (xdoc::tt "220") ".")
     )
   (xdoc::p
    "See the comments in the source file for more information on the MiMC
  specification including the variations chosen.")
   (xdoc::p
    "The library also includes some concrete tests.")
   ))

(xdoc::defpointer mimcsponge mimc)
(xdoc::defpointer mimcsponge-semaphore mimc)
