Formalization of Rank-1 Constraint Systems (R1CSes)
===============================

For background on R1CSes, see, for example, [Vitalik].  Essentially,
an R1CS is a conjunction of constraints, each of the form:

(a DOT x) * (b DOT x) = (c DOT x)

where a, b, and c are vectors of coefficients (elements of the prime
field consisting of the integers modulo some prime p), and x is a
vector of distinct "pseudo-variables".  Each pseudo-variable is either
a variable, representing an element of the field, or the special
symbol 1, representing the field element 1.  Here, DOT represents
taking the dot product of two vectors except that all additions and
multiplications are done modulo p, and * represents the product of two
scalars modulo p.  Using a pseudo-variable of 1 allows a constant
addend to be represented in a dot product.

We provide a formalization of R1CSes in sparse form (where only
variables with non-zero coefficients are included in the
representation).  See the sparse/ directory.  We define the notion of
an R1CS as a datatype in the ACL2 logic, and we assign meaning to this
datatype via the predicate r1cs-holdsp, which determines whether a
valuation (an assignment of values to variables) satisfies an R1CS.
Our formalization depends on our formalization of prime-fields and
does not bake in a specific prime number.

We provide several verified R1CS "gadgets", that is, ways to represent
certain computations, such as XORing two bits, using only the
operators available in R1CSes.  See gadgets.lisp.

We also provide a "lifter" which turns an R1CS into a (potentially
very large) logical representation, essentially a conjunction of
equalities involving the prime field operators ADD and MUL.  This
lifter is based on our Axe Rewriter.  It can also apply a variety of
verified simplification rules to the R1CS.  See
lift-r1cs/lift-r1cs-new.lisp.

Once lifted, an R1CS can be verified using the Axe Prover.  Typically,
one proves that the R1CS implies its formal specification.  The formal
specification is a predicate defined in the ACL2 logic.  For example,
one might specify a hash function by implementing it as an ACL2
function and then specify correctness of an R1CS for that hash
function by saying that its output bits represent the correct hash of
its input bits.  The specification is usually much more understandable
than the R1CS, because it is not restricted to use only operations
available in an R1CS (any ACL2 function can be used) and because it
does not mention the many (potentially thousands) of internal
variables of the R1CS.  There is also no need to "unroll" recursions
or iterations that represent repeated computations.  We have a growing
library of specifications of hash functions such as Blake2s.  See, for
example, ../blake/.

The Axe Prover can be used to establish that, whenever the R1CS holds,
the specification expression also holds.  We have done such proofs for
several large R1CSes.  (Proofs of the other direction, that if the
spec holds then there exist values for all of the R1CS variables that
make it true, should also be possible using our formalization but have
not been a focus so far.)

The Axe Prover uses rewriting, with each simplification rule having
been proven as a theorem by ACL2.  It also uses variable substitution,
which can eliminate internal variables by splicing their defining
expressions into the expression for the R1CS as a whole.  Much of the
work of the proof is in "solving" the constraints to be of the form
(equal <intermediate-var> <defining-expression>).  See
../../axe/prover-basic.lisp.

[Vitalik]:
https://medium.com/@VitalikButerin/quadratic-arithmetic-programs-from-zero-to-hero-f6d558cea649