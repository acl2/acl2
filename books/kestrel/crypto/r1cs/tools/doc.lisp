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

(xdoc::defxdoc
 r1cs-verification-with-axe
 :short "Verifying an R1CS using the Axe toolkit."
 :parents (r1cs axe)
 :long
 (xdoc::topstring
  (xdoc::&&
   (xdoc::topparas
    "Kestrel Institute's Axe toolkit (see @(tsee acl2::axe)) can be used to verify R1CS circuits.  Axe is
 is implemented as an ACL2 program.  We use our formalization of the semantics
 of R1CSes in ACL2 (see @(tsee r1cs::r1cs)). This formalization defines the syntax of an R1CS as an ACL2
 object and defines the semantics of such objects by characterizing what it
 means for an R1CS to hold over a valuation (an assignment of values to its variables).
The formalization is based on our ACL2 formalization of prime
 fields (see @(tsee pfield::prime-fields)).

 The verification process takes as input an R1CS in our format (perhaps
 translated from other format, such as a JSON representation).  We then lift the
 R1CS into an equivalent logical term.  For this, we use Axe's R1CS Lifter.  The
 Lifter first forms a mathematical term asserting that the R1CS holds over
 arbitrary symbolic variables.  It then applies the Axe Rewriter to transform
 that term into an equivalent expression over the prime field operators.  To do
 this, the Axe Rewriter opens up the functions that define the R1CS semantics,
 producing a logical term equivalent to the R1CS but no longer depending on the
 R1CS semantics functions.  The resulting term is essentially the conjunction of
 the constraints in the R1CS, expressed in terms of the underlying prime field
 operations, but some simplifications may also have been applied.

 To verify an R1CS, we need a specification to compare it to.  For this, we form
 an ACL2 term expressing the relationship that should hold over the inputs and
 outputs of the R1CS (but not its intermediate variables).  When possible, we
 use our library of existing bit-vector and cryptographic functions.  Typically,
 the specification says that the output variables of the R1CS are equal to some
 expression over the input variables.  We then call the Axe R1CS Prover to
 attempt to prove that, whenever the R1CS holds (over all of its input, output,
 and intermediate variables), the specification relation also holds (over the
 inputs and outputs).  We call this the ``forward direction'' of the proof.  In
 the future, we plan to also consider the backward direction (the claim that, if
 the specification holds over the inputs and outputs, then there exist values
 for the intermediate variables such that the entire R1CS holds).

 We always assume that all values are field elements, and, if necessary, additional
 assumptions on the input variables can be passed to the Prover (such as claims
 that some of them are single bits).

 The Axe Prover supports two main proof tactics, rewriting and variable
 substitution.  Rewriting is used to solve the constraints, attempting to turn
 each one into an equality of a variable and some other term not involving that
 variable.  This is reasonable, as the variables in an R1CS can often be
 ordered, with each constraint defining one or more new variables in terms of
 previously defined variables.  After solving for a variable, substitution can
 be used to replace it, everywhere in the proof, with the term that it is known
 to be equal to.  The rewriting process applies rewrite rules from our large and
 growing library of verified rules.  Crucially, all of these rules are proved as
 theorems in the ACL2 system, so additional rules can be added without
 compromising the soundness of the proof system.  Our library contains many
 rules that recognize R1CS gadgets, covering a variety of common operations such
 as XORing, bit packing, bit rotations, etc.  Often several rounds of rewriting
 and substitution are necessary, as the Prover turns the information in the R1CS
 into more usable forms.  For example, an XOR constraint cannot be solved until
 its input values are known to be single bits, but this may not be known until
 the constraints that define those values are themselves solved.  The Axe Prover
 typically applies a sequence of sets of rules, exhaustively applying rewriting and
 substitution with one rule set before moving on to the next one.  This allows
 us to do the proof in stages, each of which handles one kind of operation
 (e.g., recognizing and transforming bit packing gadgets, or moving negated
 addends to the other sides of equalities).  Once every intermediate variable
 has been eliminated by substitution, we are usually left with a single term for
 each output of the R1CS, representing it as a function of the
 input variables.  Often these terms no longer contain any prime field
 operations, because rewrite rules have recognized all of the R1CS gadgets and
 replaced them with more traditional bit-vector operations (concatenation,
 addition, rotation, etc.).  The final step of the proof is usually to allow the
 Prover to expand the functions in the specification, unrolling all of the
 (bounded) recursion to expose simple bit-vector operations.  If all goes well,
 each of the output bits of the specification will have an expression that
 exactly matches the expression derived from the R1CS (perhaps after some
 normalization, also done by rewriting).  This completes the proof.

This rest of this topic describes the concrete steps for using Axe to verify an R1CS (rank-1 constraint system).  It may be helpful to follow along with an example.  There is one in
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
