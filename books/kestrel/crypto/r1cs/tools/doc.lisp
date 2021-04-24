; Documentation for R1CS verification with Axe
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "R1CS")

(include-book "xdoc/topics" :dir :system)
(include-book "kestrel/utilities/xdoc-paras" :dir :system)

;; TODO: Improve this xdoc
(xdoc::defxdoc
 r1cs-verification-with-axe
 :short "Steps to verify an R1CS using the Axe toolkit."
 :parents (r1cs axe)
 :long
 (xdoc::topstring
  (xdoc::&&
   (xdoc::topparas
    "This topic describes how to use the @(tsee acl2::axe) toolkit to verify an R1CS (rank-1 constraint system).

It may be helpful to follow along with an example.  There is one in
@('[books]/kestrel/ethereum/semaphore/uint32xor-proof.lisp').

To use the Axe R1CS Prover to verify an R1CS, follow these steps:")
   (xdoc::ol

    (xdoc::&&
     (xdoc::p "1. Write or obtain a specification for the R1CS.  You may be able to
use existing formalizations from the ACL2 libraries (e.g.,
formalizations of hash functions), but you may need to account for the
fact that some R1CS variables are single bits.  In general, you will
need to create an ACL2 predicate that takes the inputs and outputs
(corresponding to variables of the R1CS) and determines whether the
outputs are correct with respect to the inputs.  There may be many
input and output variables (hundreds).  The intermediate
variables of the R1CS are not mentioned at all by this spec function.
Often, the spec function will do 3 things:")

     (xdoc::ol-from-string
      "A. Pack the input bits and output bits into larger words (e.g., 32-bit words.

       B. Call a \"core\" specification function (e.g., the specification of a
hash function, from a library) on the input words.

      C. Check that the (packed) output matches the value returned from the
core function."))

    (xdoc::p "2. Load the R1CS by calling load-circom-json to read in the file.  This
    parses the JSON and creates an ACL2 constant representing the R1CS for
    use in Step 3 below.")

    (xdoc::p "3. Lift the R1CS into logic.  This is done by calling lift-r1cs (or a variant of it, like lift-semaphore-r1cs).  It is often largely automatic.")

    (xdoc::&&
     (xdoc::p "4. Invoke the Axe Prover.  This is done by calling verify-r1cs (or a variant of it, like verify-semaphore-r1cs).  You pass it:")

     (xdoc::ol-from-string
      "A. The R1CS

      B. The spec

      C. A list of inputs which should be assumed to be bits

      D. Rules to use, and other prover options")

     (xdoc::topparas "This is the hardest step.  We suggest looking at some example proofs.

The proof will include assumptions that:
A. All of the inputs are field elements
B. The inputs that were indicated to be bits actually are bits
C. The R1CS holds
The conclusion will assert that the spec function (written in step 1)
holds over the appropriate arguments.

Most of the work in this step involves providing lists of rewrite rules
that suffice to rewrite all the idioms in the R1CS into the more
traditional operations used in the spec (e.g., to convert bit packing
from using prime field operations into calls of our operator BVCAT).
Each individual rule should be proved as an ACL2 theorem, but proofs can
be skipped if desired.  We provide many existing rules in our libraries,
but we are still working to create a robust and coherent set of rules
for general R1CS verification.  The actual input to the prover is a
sequences of rule sets, to be applied one after the other.  We are
currently working to formulate robust sequences of rule sets for R1CS
proofs."))))))
