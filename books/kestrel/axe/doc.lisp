; Documentation for Axe
;
; Copyright (C) 2021-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")
; todo: (in-package "AXE") but fix refs

(include-book "portcullis")
;(include-book "xdoc/top" :dir :system)
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
   "The Axe toolkit provides several tools for lifting code into logic.  Currently, Axe can lift JVM bytecode, x86 binaries, RISC-V binaries,and rank-1 constraint systems.

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
  (xdoc::topstring
   (xdoc::topparas
    "Axe can represent an ACL2 term in a compact form called a \"DAG\" (directed acyclic graph).  In a DAG, each distinct subterm is represented only once, so DAGs can be much smaller than their corresponding terms.  Certain classes of terms with extensive sharing of subterms can be exponentially larger than their DAG representations.  Most of Axe's algorithms operate directly on DAGs (often stored internally as arrays).

A DAG contains a set of nodes, each of which has a node number (a natural number) and a \"dag-expr\" (DAG expression).  A dag-expr is either:")
   (xdoc::ul-from-string
    "A variable (a symbol), or

A quoted constant, or

The application of a function symbol (almost always a defined ACL2 function) to a list of arguments.  Each argument (or \"darg\" = \"DAG argument\") should be either a quoted constant or the number of a DAG node, which must be smaller than the number of the node that contains this expression.  Since the expression for a given node can only refer to nodes with smaller numbers, the DAG is acyclic.")

   (xdoc::topparas
    "A DAG is usually represented as an alist from node numbers to their corresponding expresspions.  Nodes are listed in decreasing order, with each node number consed onto its expression.  Here is an example DAG containing 5 nodes:

@({
((4 foo 1 3)
 (3 bar '2 2)
 (2 . y)
 (1 binary-* '2 0)
 (0 . x))
}).

The variables in this DAG are @('x') and @('y'), and the functions it calls are @('foo'), @('bar'), and @('binary-+').  Node 4 represents a call of the function @('foo') whose two arguments are nodes 1 and 3.  Node 3 represents a call of the function @('bar') whose two arguments are the constant 2 and node 2.  The term represented by this DAG is:

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
.")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
