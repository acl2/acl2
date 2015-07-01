#|
Leftist Trees, Version 0.1
Copyright (C) 2012 by Ben Selfridge <benself@cs.utexas.edu>

   License: (An MIT/X11-style license)

   Permission is hereby granted, free of charge, to any person obtaining a copy
   of this software and associated documentation files (the "Software"), to
   deal in the Software without restriction, including without limitation the
   rights to use, copy, modify, merge, publish, distribute, sublicense, and/or
   sell copies of the Software, and to permit persons to whom the Software is
   furnished to do so, subject to the following conditions:

   The above copyright notice and this permission notice shall be included in
   all copies or substantial portions of the Software.

   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS
   IN THE SOFTWARE.
|#

; This file was initially generated automatically from legacy documentation
; strings.  See source files in this directory for copyright and license
; information.

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

(defxdoc *empty-lt*
  :parents (leftist-tree-structure)
  :short "The default empty leftist tree"
  :long "<p>The default \"empty\" tree (just NIL)</p>")

(defxdoc build-lt
  :parents (leftist-tree-ops)
  :short "Build a leftist tree from a list"
  :long "<p>Builds a leftist tree from a list of elements. This is accomplished
 by right-folding the INSERT-LT function over the list, starting with
 *EMPTY-LT*.</p>")

(defxdoc delete-min-lt
  :parents (leftist-tree-ops)
  :short "Delete the minimum element of a leftist tree"
  :long "<p>Delete the minimum element of a nonempty tree. This is
 accomplisghed by simply merging the two subtrees.</p>")

(defxdoc find-min-lt
  :parents (leftist-tree-ops)
  :short "Get the minimum element of a leftist tree"
  :long "<p>Get the minimum element of a nonempty tree. Assuming the tree in
 question is PROPER-LT, this is just the root of the tree.</p>")

(defxdoc how-many-lt
  :parents (leftist-trees)
  :short "Returns the number of times an object occurs in a leftist tree"
  :long "<p>Counts the number of occurrences of a given object in a leftist
 tree. This function takes advantage of the heap-ordering property, and returns
 0 if the root of the tree is larger than what we are searching for.</p>")

(defxdoc how-many-ltree-sort
  :parents (leftist-tree-sort)
  :short "Ltree-sort preserves how-many"
  :long "<p>This is needed to prove that ltree-sort is equivalent to
  isort.</p>")

(defxdoc insert-lt
  :parents (leftist-tree-ops)
  :short "Insert an element into a leftist tree"
  :long "<p>Insert an element into a leftist tree. This function is defined in
 terms of MERGE-LT.</p>

 <p>Example usage:</p>

 <p>(INSERT-LT 2 (INSERT-LT 3 (INSERT-LT 4 *EMPTY-LT*)))</p>

 <p>This creates a leftist tree with elements 2, 3, 4.</p>")

(defxdoc is-empty-lt
  :parents (leftist-tree-structure)
  :short "Checks if a tree is empty"
  :long "<p>Checks if a tree is empty. For simplicity, we only require (atom
  tree).</p>")

(defxdoc left-lt
  :parents (leftist-tree-structure)
  :short "Left sub-tree of a leftist tree"
  :long "<p>Returns the left sub-tree of a non-empty tree.</p>")

(defxdoc leftist-tree-fns
  :parents (leftist-trees)
  :short "All functions and constants related to leftist trees."
  :long "<p>------------------------------------------------------------
 Functions and Constants
 ------------------------------------------------------------</p>

 <p>Function/Constant Name Result (supporting function) Type
 ---------------------- ----</p>

 <p>** STRUCTURE ** RANK-LT natural ROOT-LT ?  LEFT-LT ltree RIGHT-LT ltree
 *EMPTY-LT* NIL IS-EMPTY-LT boolean PROPER-LT boolean</p>

 <p>** OPERATIONS ** MERGE-LT ltree MAKE-LT ltree INSERT-LT ltree FIND-MIN-LT ?
 DELETE-MIN-LT ltree BUILD-LT ltree</p>

 <p>** MISCELLANEOUS ** SIZE-LT natural MEMBER-LT boolean LENGTH-RIGHT-SPINE-LT
 natural LENGTH-TO-NIL-LT natural</p>")

(defxdoc leftist-tree-misc
  :parents (leftist-tree-fns)
  :short "Miscellaneous, but nonetheless useful, functions for leftist trees"
  :long "")

(defxdoc leftist-tree-misc-thms
  :parents (leftist-tree-thms)
  :short "Miscellaneous theorems"
  :long "<p>Includes proofs that the rank, length of right spine, and length of
 the shortest path to an empty node are all equal. We also prove that the rank
 and size of a tree are always natp, as this is helpful in a later
 theorem.</p>")

(defxdoc leftist-tree-ops
  :parents (leftist-tree-fns)
  :short "The basic heap operations of leftist trees."
  :long "<p>The core operation here is MERGE-LT. All the other operations are
 defined in terms of MERGE-LT, which makes leftist trees relatively easy to
 reason about.</p>")

(defxdoc leftist-tree-rank-thms
  :parents (leftist-tree-thms)
  :short "Theorems about the rank of leftist trees"
  :long "")

(defxdoc leftist-tree-sort
  :parents (leftist-trees)
  :short "Functions and theorems about leftist tree-based heapsort."
  :long "<p>There are three functions related to heapsort, the most important
 being ltree-sort, which works just like the other sorting functions in the
 books/sorting contribution, except it uses leftist trees to sort its
 input. There are a number of theorems provided that prove the heapsort
 algorithm correct.</p>

 <p>------------------------------------------------------------ Functions and
 Constants ------------------------------------------------------------</p>

 <p>Function/Constant Name Result (supporting function) Type
 ---------------------- ---- LTREE-TO-LIST list LTREE-SORT list HOW-MANY-LT
 natural</p>")

(defxdoc leftist-tree-structure
  :parents (leftist-tree-fns)
  :short "Functions relating to building and recognizing leftist trees."
  :long "")

(defxdoc leftist-tree-structure-thms
  :parents (leftist-tree-thms)
  :short "Theorems proving that the basic operations respect PROPER-LT"
  :long "")

(defxdoc leftist-tree-thms
  :parents (leftist-trees)
  :short "Useful theorems about leftist trees."
  :long "")

(defxdoc leftist-trees
  :parents (projects)
  :short "An implementation of Leftist Trees."
  :long "<p>Leftist trees are an efficient implementation of binary
  heaps. Regular
 (completely balanced) binary heaps are tricky, and in most cases near
 impossible, to implement in functional languages because of the need for
 constant-time access to the last element in the tree (that element being the
 node in the bottom-most level of the tree, furthest to the right). Leftist
 trees avoid this by replacing this \"balanced\" requirement with the
 requirement that the right-most spine of the tree be small relative to the
 overal number of elements in the tree. Since the fundamental heap operations
 (insert, delete-min) only recur on the right spine of the tree in question,
 this guarantees that these operations are O(log(n)), where n is the size of
 the tree.</p>

 <p>Leftist trees look like this:</p>

 <p>(rank root left right)</p>

 <p>where \"rank\" is defined to be the length of the right spine of the tree,
 \"root\" is the root element of the tree, \"left\" is the left sub-tree, and
 \"right\" is the right sub-tree.</p>

 <p>Leftist trees are heap-ordered, and they are \"balanced\" in a loose
 sense. In particular, the size of the tree is at least as big as an
 exponential function of the rank:</p>

 <p>size(tree) &gt;= 2^(rank(tree)) - 1,</p>

 <p>or, solving for rank(tree) and noting that the rank is always an
 integer,</p>

 <p>rank(tree) &lt;= floor(log(size(tree) + 1)).</p>

 <p>The important tree operations are INSERT-LT, FIND-MIN-LT, and
 DELETE-MIN-LT. A useful function called BUILD-LT is also provided, which
 constructs a leftist tree from a list. An important constant is *EMPTY-LT*,
 which is the empty tree (for this implementation, just NIL).</p>

 <p>To learn how to use the trees, see :DOC LEFTIST-TREE-FNS. To see some
 useful theorems about leftist trees, including the rank bound above, see :DOC
 LEFTIST-TREE-THMS.</p>

 <p>Sources: - Okasaki, Chris. Purely Functional Data Structures. Cambridge,
 U.K.: Cambridge UP, 1998. 17-20. Print.</p>

 ")

(defxdoc length-right-spine-lt
  :parents (leftist-tree-misc)
  :short "Length of the right spine of a leftist tree"
  :long "<p>This is equivalent to RANK-LT.</p>

 <p>This function actually counts the length of the right spine of the tree. We
 will prove that this equals the rank of the tree.</p>")

(defxdoc length-to-nil-lt
  :parents (leftist-tree-misc)
  :short "Length of the shortest path to an empty node"
  :long "<p>This is equivalent to RANK-LT.</p>

 <p>Returns the length of the shortest path to an empty node. We will prove
 that this equals the rank of the tree.</p>")

(defxdoc lrt-equals-rank-lt
  :parents (leftist-tree-misc-thms)
  :short ""
  :long "<p>(length-right-spine-lt tree) ==&gt; (rank-lt tree)</p>")

(defxdoc ltn-equals-rank-lt
  :parents (leftist-tree-misc-thms)
  :short ""
  :long "<p>(length-to-nil-lt tree) ==&gt; (rank-lt tree)</p>")

(defxdoc ltree-sort
  :parents (leftist-trees)
  :short "Sort an input list using leftist tree-based heapsort"
  :long "<p>Sorts an input list by first INSERT-LTing each element of the list
 into a leftist tree, then DELETE-MIN-LTing the min element from the tree one
 by one.</p>")

(defxdoc ltree-to-list
  :parents (leftist-tree-sort)
  :short "Convert a leftist tree to a list"
  :long "<p>Assuming the leftist tree in question is proper, this will result
 in a sorted list.</p>")

(defxdoc member-insert-lt
  :parents (leftist-tree-misc-thms)
  :short ""
  :long "<p>(proper-lt tree) ==&gt; (member-lt x (insert-lt x tree))</p>")

(defxdoc member-lt
  :parents (leftist-tree-misc)
  :short "Tests membership in a leftist tree"
  :long "<p>Tests whether something is an element of the tree. Note that this
 is not simply a brute-force search; if the root of the tree is greater than
 what we are looking for, we return nil. So in order for this function to work,
 the tree has to be PROPER-LT.</p>")

(defxdoc merge-lt
  :parents (leftist-tree-ops)
  :short "Merge two leftist trees"
  :long "<p>Merge two leftist trees.</p>

 <p>Two leftist trees are merged by \"merging their right spines as you would
 merge two sorted lists, and then swapping the children of nodes along this
 path as necessary to restore the leftist property.\" (Okasaki)</p>")

(defxdoc orderedp-ltree-sort
  :parents (leftist-tree-sort)
  :short "Ltree-sort produces an ordered list"
  :long "")

(defxdoc proper-build-lt
  :parents (leftist-tree-structure-thms)
  :short ""
  :long "<p>(proper-lt (build-lt l))</p>")

(defxdoc proper-delete-min-lt
  :parents (leftist-tree-structure-thms)
  :short ""
  :long "<p>(proper-lt tree) ==&gt; (proper-lt (delete-min-lt tree))</p>")

(defxdoc proper-insert-lt
  :parents (leftist-tree-structure-thms)
  :short ""
  :long "<p>(proper-lt tree) ==&gt; (proper-lt (insert-lt x tree))</p>")

(defxdoc proper-lt
  :parents (leftist-tree-structure)
  :short "Checks that a tree is a legitimate leftist tree"
  :long "<p>Checks that a tree is a legitimate Leftist Tree.  The basic
 recursive requirements are: * both the left and right sub-trees are proper
 * (rank) the rank is 1 + the rank of the right sub-tree * (leftist) the rank
 of right sub-tree is less than or equal to the rank of the left sub-tree *
 (heap-ordered) if either of the sub-trees are non-trivial, then their roots
 are larger than the root of the tree</p>")

(defxdoc proper-merge-lt
  :parents (leftist-tree-structure-thms)
  :short ""
  :long "<p>(and (proper-lt tree1) (proper-lt tree2))
     ==&gt; (proper-lt (merge-lt tree1 tree2))</p>")

(defxdoc rank-is-natp-lt
  :parents (leftist-tree-misc-thms)
  :short ""
  :long "<p>(proper-lt tree) ==&gt; (natp (rank-lt tree))</p>")

(defxdoc rank-lt
  :parents (leftist-tree-structure)
  :short "Rank of a leftist tree"
  :long "<p>Returns the rank of the tree. The rank of a tree is formally
 defined to be the length of its right spine. Empty trees have rank 0.</p>")

(defxdoc right-lt
  :parents (leftist-tree-structure)
  :short "Right sub-tree of a leftist tree"
  :long "<p>Returns the right sub-tree of a non-empty tree.</p>")

(defxdoc root-lt
  :parents (leftist-tree-structure)
  :short "Root of a leftist tree"
  :long "<p>Returns the root of a non-empty tree.</p>")

(defxdoc size-is-natp-lt
  :parents (leftist-tree-misc-thms)
  :short ""
  :long "<p>(proper-lt tree) ==&gt; (natp (size-lt tree))</p>")

(defxdoc size-lt
  :parents (leftist-tree-misc)
  :short "Total number of elements in a leftist tree"
  :long "<p>Returns the total number of elements in the tree.</p>")

(defxdoc size-rank-lt
  :parents (leftist-tree-rank-thms)
  :short ""
  :long "<p>(proper-lt tree) ==&gt; (&lt;= (- (expt 2 (rank-lt tree))
     1) (size-lt tree))</p>")

(defxdoc true-listp-ltree-sort
  :parents (leftist-tree-sort)
  :short "Ltree-sort produces a true-listp"
  :long "")
