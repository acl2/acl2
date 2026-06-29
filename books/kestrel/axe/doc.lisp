; Documentation for Axe
;
; Copyright (C) 2021-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")
; todo: (in-package "AXE") but fix refs

(include-book "portcullis")
;(include-book "xdoc/top" :dir :system)
(include-book "arm/doc")
(include-book "jvm/doc")
(include-book "x86/doc")
(include-book "risc-v/doc")
(include-book "r1cs/doc")
(include-book "kestrel/utilities/xdoc-paras" :dir :system)
(include-book "kestrel/crypto/r1cs/portcullis" :dir :system)
(include-book "equivalence-checker") ;todo: prove-equal-with-axe+, prove-with-axe

(defxdoc axe
  :parents (software-verification kestrel-books projects)
  :short "A toolkit for software verification."
  :long
  (xdoc::topparas
   "The Axe toolkit provides a variety of tools for software verification, including lifters-into-logic, rewriters, theorem provers, and equivalence checkers.

Most of Axe is now available in the ACL2 Community books, under @('kestrel/axe/'), though much work remains to document it.

See <a href=\"https://www.kestrel.edu/research/axe/\">the Axe webpage</a> for more information."))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc axe-core
  :parents (axe)
  :short "The core Axe tools."
  :long (xdoc::topparas "Many of the core Axe tools are independent of which Axe variant is used."))

(defxdoc axe-rewriters
  :parents (axe)
  :short "The Axe rewriter tools.")

(defxdoc axe-provers
  :parents (axe)
  :short "The Axe prover tools.")

(defxdoc axe-lifters
  :parents (axe)
  :short "Axe tools to lift code into logic."
  :long
  (xdoc::topparas
   "The Axe toolkit provides several tools for lifting code into logic.  Currently, Axe can lift JVM bytecode, x86 binaries, RISC-V binaries, and rank-1 constraint systems.

   For lifting JVM bytecode, four lifters are available.  For code that is unrollable, use @(tsee unroll-java-code) (or try the more experimental @(tsee unroll-java-code2), for compositional lifting).  When loops cannot be unrolled and so must be lifted into recursive functions, use @('lift-java-code') (or try the more experimental @('lift-java-code2'), for compositional lifting).

   For lifting x86 binaries, two lifters are available.  For code that is unrollable, use @('x::def-unrolled') (still experimental).  When loops cannot be unrolled and so must be lifted into recursive functions, try @('x::lift-subroutine') (very experimental).

   For lifting rank-1 constraint systems, use @(tsee r1cs::lift-r1cs) or one of its variants."
   ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc rewriter-basic
  :parents (axe-core axe-rewriters)
  :short "A basic, modern Axe rewriter."
  :long "See @('rewriter-basic.lisp').")

(defxdoc prover-basic
  :parents (axe-core axe-provers)
  :short "A basic, modern Axe prover."
  :long "See @('prover-basic.lisp').")

(defxdoc rewriter-legacy
  :parents (axe-core axe-rewriters)
  :short "The legacy Axe rewriter."
  :long "See @('rewriter.lisp').")

(defxdoc rewriter-alt
  :parents (axe-core axe-rewriters)
  :short "Another legacy Axe rewriter."
  :long "See @('rewriter-alt.lisp').")

(defxdoc prover-legacy
  :parents (axe-core axe-provers)
  :short "The legacy Axe prover."
  :long "See @('prover.lisp').")

(defxdoc make-rewriter-simple
  :parents (axe-core axe-rewriters)
  :short "A tool to create custom Axe rewriters."
  :long "See @('make-rewriter-simple.lisp').")

(defxdoc make-prover-simple
  :parents (axe-core axe-provers)
  :short "A tool to create custom Axe prover."
  :long "See @('make-prover-simple.lisp').")

;; TODO: Put back doc in def-simplified.
(defxdoc def-simplified
  :parents (axe-core axe-rewriters)
  :short "A tool to simplify a term or DAG."
  :long "See @('def-simplified.lisp').")

(defxdoc defthm-axe-basic
  :parents (axe-core axe-provers)
  :short "A defthm-like tool that uses Axe."
  :long "See @('defthm-axe-basic.lisp').")

;; unroll-spec has its own doc.  ;; TODO: Update it.
;; unroll-spec-basic has its own doc.

(defxdoc defthm-stp
  :parents (axe-core axe-provers)
  :short "A defthm-like tool that uses the STP solver."
  :long "See @('defthm-stp.lisp').")

;; todo: defconst-computed2, etc.

;; todo: prove-with-tactics, prove-equal-with-tactics, query

;; todo: other macros?

;; todo: the clause-processors

;; todo: the equivalence-checker


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc stp
  :parents (axe-core)
  :short "An SMT solver used by the Axe toolkit."
  :long (xdoc::topparas "STP is an SMT solver available <a href='https://github.com/stp/stp'>here</a>.
  It is used by several tools in the @(see Axe) toolkit.  See @(tsee build::cert_param) for
information on suppressing attempts to use STP during builds.

Different versions of STP support different option syntax, especially for the max conflicts option, so you might need to set the environment variable @('ACL2_STP_VARIETY').  The default (equivalent to a setting of \"2\") should work with the latest STP (as of September, 2023) and with other versions that use the option @('--max-num-confl') (note the dashes).  For older STP versions that use the option @('--max_num_confl') (note the underscores), set @('ACL2_STP_VARIETY') to \"1\".  For very old versions of STP that only support the use of @('-g') for the max conflicts option, set @('ACL2_STP_VARIETY') to \"0\".

For the latest version of STP, which supports new helpful options, set @('ACL2_STP_VARIETY') to \"3\".

To test whether STP is being called correctly in your environment, run the script @('[books]/kestrel/axe/teststp.bash') with no arguments.  Its output should include the string @('\"Valid.\"') if STP is being correctly invoked."))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc dags
  :parents (axe-core)
  :short "Axe's DAG data structure."
  :long
  (xdoc::topparas
    "Axe can represent an ACL2 term in a compact form called a \"DAG\" (directed acyclic graph).  In a DAG, each distinct subterm is represented only once, so DAGs can be much smaller than their corresponding terms.  Certain classes of terms with extensive sharing of subterms can be exponentially larger than their DAG representations.  Most of Axe's algorithms operate directly on DAGs (often stored internally as arrays).

A DAG contains a set of nodes, each of which has a node number (a natural number) and a \"dag-expr\" (DAG expression).  A dag-expr is either:"

    (xdoc::ul-from-string
    "A variable (a symbol), or

A quoted constant, or

The application of a function symbol (almost always a defined ACL2 function) to a list of arguments.  Each argument (or \"darg\" = \"DAG argument\") should be either a quoted constant or the number of a DAG node, which must be smaller than the number of the node that contains this expression.  Since the expression for a given node can only refer to nodes with smaller numbers, the DAG is acyclic.")

    "A DAG is usually represented as an alist from node numbers to their corresponding expressions.  Nodes are listed in decreasing order, with each node number consed onto its expression.  Here is an example DAG containing 5 nodes:

@({
((4 foo 1 3)
 (3 bar '2 2)
 (2 . y)
 (1 binary-* '2 0)
 (0 . x))
}).

The variables in this DAG are @('x') and @('y'), and the functions it calls are @('foo'), @('bar'), and @('binary-*').  Node 4 represents a call of the function @('foo') whose two arguments are nodes 1 and 3.  Node 3 represents a call of the function @('bar') whose two arguments are the constant 2 and node 2.  The term represented by this DAG is:

@({(foo (binary-* '2 x) (bar '2 y))}).

This can be seen by calling the function @('dag-to-term') on the DAG, like this:

@({(dag-to-term '((4 foo 1 3) (3 bar '2 2) (2 . y) (1 binary-* '2 0) (0 . x)))})

but note that the term representation can blow up for DAGs with extensive sharing!

The function @('dag-info') can be used to print information about a DAG.  For example,

@({(dag-info '((4 foo 1 3) (3 bar '2 2) (2 . y) (1 binary-* '2 0) (0 . x)))})

prints:

@({(DAG info:
 Unique nodes: 5
 2 Variables:
  x y
 Functions and counts:
  binary-*:                                                1
  bar:                                                     1
  foo:                                                     1)})

Often Axe stores DAGs in named constants, since the DAGs themselves may be large.  For example, if the DAG above were stored in the constant @('*my-dag*'), then one could do:

@({(dag-to-term *my-dag*)})

and

@({(dag-info *my-dag*)})
."))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc formal-unit-testing
  :parents (axe)
  :short "Small, automatic proofs about code."
  :long
  (xdoc::topparas
    "Formal Unit Testing is a way to increase software assurance by generalizing
concrete unit tests into \"Formal Unit Tests\".  It provides highly automatic
proofs of properties while requiring little user input and no formal methods
expertise.  The @(csee axe) toolkit supports Formal Unit Testing of Java / JVM
bytecode and x86 binary programs, with support for other architectures
planned (e.g., ARM and RISC-V)."

"Formal Unit Testing works as follows:"

"1. The user writes a small test harness that calls the function(s) to be
tested and then checks a desired correctness property."

"2. The Formal Unit Testing tool then attempts to prove that these checks
always pass, for all inputs to the test harness."

"3a. If the proof succeeds, then the tool guarantees the property is correct
for all inputs.  This makes it much more powerful than traditional unit
testing, which covers the code's behavior on only a finite (usually small) set
of concrete inputs."

"3b. In the case where the proof fails, the tool can often produce a concrete
counterexample: an input that violates the desired property.  In this case,
either the code or the property (embodied in the test harness) must be fixed"

"3c. If the tool times out, the user edits the test harness to impose bounds on
the sizes of the program input(s) (e.g., the number of elements in an array)
before trying again.  Such bounds make the analysis problem tractable."

"Formal Unit Testing supports the development of a \"proof suite\" that lives
alongside the traditional test suite and can be integrated into CI/CD pipelines
to ensure that software changes do not violate important guarantees.

See also @(see formal-unit-testing-example)."))

(defxdoc formal-unit-testing-example
  :parents (formal-unit-testing)
  :short "Simple example of Formal Unit Testing"
  :long
  (xdoc::topparas
    "To illustrate the @(see formal-unit-testing) idea, consider the following C code (from an implementation of the AES block cipher):"

   "@({
unsigned char sbox [] = {
  0x63, 0x7c, 0x77, 0x7b, 0xf2, 0x6b, 0x6f, 0xc5, 0x30, 0x01, 0x67, 0x2b, 0xfe, 0xd7, 0xab, 0x76,
  0xca, 0x82, 0xc9, 0x7d, 0xfa, 0x59, 0x47, 0xf0, 0xad, 0xd4, 0xa2, 0xaf, 0x9c, 0xa4, 0x72, 0xc0,
  0xb7, 0xfd, 0x93, 0x26, 0x36, 0x3f, 0xf7, 0xcc, 0x34, 0xa5, 0xe5, 0xf1, 0x71, 0xd8, 0x31, 0x15,
  0x04, 0xc7, 0x23, 0xc3, 0x18, 0x96, 0x05, 0x9a, 0x07, 0x12, 0x80, 0xe2, 0xeb, 0x27, 0xb2, 0x75,
  0x09, 0x83, 0x2c, 0x1a, 0x1b, 0x6e, 0x5a, 0xa0, 0x52, 0x3b, 0xd6, 0xb3, 0x29, 0xe3, 0x2f, 0x84,
  0x53, 0xd1, 0x00, 0xed, 0x20, 0xfc, 0xb1, 0x5b, 0x6a, 0xcb, 0xbe, 0x39, 0x4a, 0x4c, 0x58, 0xcf,
  0xd0, 0xef, 0xaa, 0xfb, 0x43, 0x4d, 0x33, 0x85, 0x45, 0xf9, 0x02, 0x7f, 0x50, 0x3c, 0x9f, 0xa8,
  0x51, 0xa3, 0x40, 0x8f, 0x92, 0x9d, 0x38, 0xf5, 0xbc, 0xb6, 0xda, 0x21, 0x10, 0xff, 0xf3, 0xd2,
  0xcd, 0x0c, 0x13, 0xec, 0x5f, 0x97, 0x44, 0x17, 0xc4, 0xa7, 0x7e, 0x3d, 0x64, 0x5d, 0x19, 0x73,
  0x60, 0x81, 0x4f, 0xdc, 0x22, 0x2a, 0x90, 0x88, 0x46, 0xee, 0xb8, 0x14, 0xde, 0x5e, 0x0b, 0xdb,
  0xe0, 0x32, 0x3a, 0x0a, 0x49, 0x06, 0x24, 0x5c, 0xc2, 0xd3, 0xac, 0x62, 0x91, 0x95, 0xe4, 0x79,
  0xe7, 0xc8, 0x37, 0x6d, 0x8d, 0xd5, 0x4e, 0xa9, 0x6c, 0x56, 0xf4, 0xea, 0x65, 0x7a, 0xae, 0x08,
  0xba, 0x78, 0x25, 0x2e, 0x1c, 0xa6, 0xb4, 0xc6, 0xe8, 0xdd, 0x74, 0x1f, 0x4b, 0xbd, 0x8b, 0x8a,
  0x70, 0x3e, 0xb5, 0x66, 0x48, 0x03, 0xf6, 0x0e, 0x61, 0x35, 0x57, 0xb9, 0x86, 0xc1, 0x1d, 0x9e,
  0xe1, 0xf8, 0x98, 0x11, 0x69, 0xd9, 0x8e, 0x94, 0x9b, 0x1e, 0x87, 0xe9, 0xce, 0x55, 0x28, 0xdf,
  0x8c, 0xa1, 0x89, 0x0d, 0xbf, 0xe6, 0x42, 0x68, 0x41, 0x99, 0x2d, 0x0f, 0xb0, 0x54, 0xbb, 0x16,
};}
})"

"@({unsigned char inv_sbox [] = {
  0x52, 0x09, 0x6a, 0xd5, 0x30, 0x36, 0xa5, 0x38, 0xbf, 0x40, 0xa3, 0x9e, 0x81, 0xf3, 0xd7, 0xfb,
  0x7c, 0xe3, 0x39, 0x82, 0x9b, 0x2f, 0xff, 0x87, 0x34, 0x8e, 0x43, 0x44, 0xc4, 0xde, 0xe9, 0xcb,
  0x54, 0x7b, 0x94, 0x32, 0xa6, 0xc2, 0x23, 0x3d, 0xee, 0x4c, 0x95, 0x0b, 0x42, 0xfa, 0xc3, 0x4e,
  0x08, 0x2e, 0xa1, 0x66, 0x28, 0xd9, 0x24, 0xb2, 0x76, 0x5b, 0xa2, 0x49, 0x6d, 0x8b, 0xd1, 0x25,
  0x72, 0xf8, 0xf6, 0x64, 0x86, 0x68, 0x98, 0x16, 0xd4, 0xa4, 0x5c, 0xcc, 0x5d, 0x65, 0xb6, 0x92,
  0x6c, 0x70, 0x48, 0x50, 0xfd, 0xed, 0xb9, 0xda, 0x5e, 0x15, 0x46, 0x57, 0xa7, 0x8d, 0x9d, 0x84,
  0x90, 0xd8, 0xab, 0x00, 0x8c, 0xbc, 0xd3, 0x0a, 0xf7, 0xe4, 0x58, 0x05, 0xb8, 0xb3, 0x45, 0x06,
  0xd0, 0x2c, 0x1e, 0x8f, 0xca, 0x3f, 0x0f, 0x02, 0xc1, 0xaf, 0xbd, 0x03, 0x01, 0x13, 0x8a, 0x6b,
  0x3a, 0x91, 0x11, 0x41, 0x4f, 0x67, 0xdc, 0xea, 0x97, 0xf2, 0xcf, 0xce, 0xf0, 0xb4, 0xe6, 0x73,
  0x96, 0xac, 0x74, 0x22, 0xe7, 0xad, 0x35, 0x85, 0xe2, 0xf9, 0x37, 0xe8, 0x1c, 0x75, 0xdf, 0x6e,
  0x47, 0xf1, 0x1a, 0x71, 0x1d, 0x29, 0xc5, 0x89, 0x6f, 0xb7, 0x62, 0x0e, 0xaa, 0x18, 0xbe, 0x1b,
  0xfc, 0x56, 0x3e, 0x4b, 0xc6, 0xd2, 0x79, 0x20, 0x9a, 0xdb, 0xc0, 0xfe, 0x78, 0xcd, 0x5a, 0xf4,
  0x1f, 0xdd, 0xa8, 0x33, 0x88, 0x07, 0xc7, 0x31, 0xb1, 0x12, 0x10, 0x59, 0x27, 0x80, 0xec, 0x5f,
  0x60, 0x51, 0x7f, 0xa9, 0x19, 0xb5, 0x4a, 0x0d, 0x2d, 0xe5, 0x7a, 0x9f, 0x93, 0xc9, 0x9c, 0xef,
  0xa0, 0xe0, 0x3b, 0x4d, 0xae, 0x2a, 0xf5, 0xb0, 0xc8, 0xeb, 0xbb, 0x3c, 0x83, 0x53, 0x99, 0x61,
  0x17, 0x2b, 0x04, 0x7e, 0xba, 0x77, 0xd6, 0x26, 0xe1, 0x69, 0x14, 0x63, 0x55, 0x21, 0x0c, 0x7d,
};
})"

"@({unsigned char box (unsigned char i) {
  return sbox[i];
}
})"

"@({unsigned char inv_box (unsigned char i) {
  return inv_sbox[i];
}
})"

"This code represents the substitution boxes (\"sboxes\") used by AES.  The cipher looks up a byte value in the sbox and replaces it with the corresponding value from the array.  To undo this operation when decrypting, it uses the inverse sbox."

"What properties might we want to test?  An important property is that @('sbox') and its inverse, @('inv_sbox'), are in fact true inverses.  This can be tested by the following test harness:"

"@({
// Test that the inverse sbox always inverts the main sbox
bool test_inverse_1 (unsigned char i) {
  return inv_box(box(i)) == i;
})"

"The Formal Unit Tester can automatically check that this harness returns true for all possible values of the input @('i'):"

"@({Test test_inverse_1 passed in 0.79s.})"

"While this particular example could be checked by simply enumerating all values of @('i'), the Formal Unit Tester actually uses SMT-based proof technology instead.  This lets it scale to handle input ranges that would be infeasible to test exhaustively."

"A related property is injectivity: No two different inputs map to the same value:"

"@({
// Test that different indices have different values
bool test_box_injective (unsigned char i, unsigned char j) {
  if (i == j) return true;
  return box(i) != box(j);
}
})"

"Again, the Formal Unit Tester proves this automatically:"

"@({Test test_box_injective passed in 0.92s.})"

"Here is a simple example of a test that fails:"

"@({
// This test is expected to fail (since the name starts with fail_test_)!
bool fail_test_box_not_zero (unsigned char i) {
  return box(i) != 0;
}
})"

"This test asserts that no index maps to 0, which is not true.  The Formal Unit Tester identifies the input that violates the property:"

"@({Failure info: (nil (:var-counterexample ((rdi . 82) (r9 . 0) (r8 . 0) (rcx . 0) (rdx . 0) (rsi . 0))))})"

"To interpret this failure, note that the test is being executed on the x86-64 binary, and calling conventions put the first argument in register @('rdi').  The counterexample contains a value of 82 for @('rdi') and indeed 82 is the index of the @('sbox') array element that contains 0 -- the value that falsifies this test."

"The full example is available in @('[books]/kestrel/axe/x86/examples/formal-unit-tests/sbox/')."

))
