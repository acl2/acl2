; Documentation for Axe
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)
(include-book "kestrel/utilities/xdoc-paras" :dir :system)

(defxdoc axe
  :short "The Axe toolkit"
  :parents (software-verification kestrel-books)
  :long
  (xdoc::topparas
   "The Axe toolkit provides a variety of tools for software verification, including lifters-into-logic, rewriters, theorem provers, and equivalence checkers.

Most of Axe is now available in the ACL2 Community books, under @('[books]/kestrel/axe/'), though much work remains to document it.

See <a href=\"https://www.kestrel.edu/research/axe/\">the Axe webpage</a> for more information."))

(defxdoc dags
  :short "Axe's DAG data structure"
  :parents (axe)
  :long
  (xdoc::topstring
   (xdoc::topparas
    "Axe can represent an ACL2 term in a compact form called a \"DAG\" (directed acyclic graph).  In a DAG, each distinct subterm is represented only once, so DAGs can be much smaller than their corresponding terms.  Certain classes of terms with extensive sharing of subterms can be exponentially larger than their DAG representations.  Most of Axe's algorithms operate directly on DAGs (perhaps stored in internal form in arrays).

A DAG contains a set of nodes, each of which has a node number (a natural number) and a \"dag-expr\" (DAG expression).  A dag-expr is either:")
   (xdoc::ul-from-string
    "A variable (a symbol), or

A quoted constant, or

The application of a function symbol (almost always a defined ACL2 function) to a list of arguments.  Each argument (or \"darg\" = \"DAG argument\") should be either a quoted constant or the number of a DAG node, which must be smaller than the number of the node that contains this expression.  Since the expression for a given node can only refer to nodes with smaller numbers, the DAG is acyclic.")

   (xdoc::topparas
    "The nodes in a DAG are listed in decreasing order, with each node number consed onto its expression.  Here is an example DAG containing 5 nodes:

@({
((4 foo 1 3)
 (3 bar '2 2)
 (2 . y)
 (1 binary-* '2 0)
 (0 . x))
}).

The variables in this DAG are @('x') and @('y'), and the functions it calls are @('foo'), @('bar'), and @('binary-+').  Node 4 represents a call of the function @('foo') whose two arguments are nodes 1 and 3.  Node 3 represents a call of the function @('bar') whose two arguments are the constant 2 and node 2.  The term represented by this DAG is:

@({(foo (binary-* '2 x) (bar '2 y))}).

")))
