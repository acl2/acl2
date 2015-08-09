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

 leftist-tree-defuns.lisp

   This file contains the function definitions and lays out
   the structure of leftist trees (otherwise known as leftist
   heaps). With an eye towards heapsort, we use lexorder as
   the basic ordering function, since that is the ordering
   used in the other sorting algorithms in books/sorting.

   This implementation follows "Purely Functional Data
   Structures" by Chris Okasaki.

|#

(in-package "ACL2")

; NOTE: Legacy doc strings defined in this file were replaced Nov. 2014 by the
; auto-generated defxdoc form in file leftist-trees-xdoc.lisp.

(deflabel leftist-trees
;;; This legacy doc string was replaced Nov. 2014 by a corresponding
;;; auto-generated defxdoc form in file leftist-trees-xdoc.lisp.
;   :doc ":DOC-SECTION leftist-trees
;
; An implementation of Leftist Trees.  ~/~/
;
; Leftist trees are an efficient implementation of binary heaps. Regular
; (completely balanced) binary heaps are tricky, and in most cases near
; impossible, to implement in functional languages because of the need
; for constant-time access to the last element in the tree (that element
; being the node in the bottom-most level of the tree, furthest to the
; right). Leftist trees avoid this by replacing this \"balanced\"
; requirement with the requirement that the right-most spine of the tree
; be small relative to the overal number of elements in the tree. Since
; the fundamental heap operations (insert, delete-min) only recur on the
; right spine of the tree in question, this guarantees that these
; operations are O(log(n)), where n is the size of the tree.
;
; Leftist trees look like this:
;
;     (rank root left right)
;
; where \"rank\" is defined to be the length of the right spine of the
; tree, \"root\" is the root element of the tree, \"left\" is the left
; sub-tree, and \"right\" is the right sub-tree.
;
; Leftist trees are heap-ordered, and they are \"balanced\" in a loose
; sense. In particular, the size of the tree is at least as big as an
; exponential function of the rank:
;
;     size(tree) >= 2^(rank(tree)) - 1,
;
; or, solving for rank(tree) and noting that the rank is always an
; integer,
;
;     rank(tree) <= floor(log(size(tree) + 1)).
;
; The important tree operations are INSERT-LT, FIND-MIN-LT, and
; DELETE-MIN-LT. A useful function called BUILD-LT is also provided,
; which constructs a leftist tree from a list. An important constant is
; *EMPTY-LT*, which is the empty tree (for this implementation, just
; NIL).
;
; To learn how to use the trees, see :DOC LEFTIST-TREE-FNS. To see some
; useful theorems about leftist trees, including the rank bound above,
; see :DOC LEFTIST-TREE-THMS.
;
; Sources:
;   - Okasaki, Chris. Purely Functional Data Structures. Cambridge,
;     U.K.: Cambridge UP, 1998. 17-20. Print.
;
; ~/
; "
)

;;; This legacy doc string was replaced Nov. 2014 by a corresponding
;;; auto-generated defxdoc form in file leftist-trees-xdoc.lisp.
; (defdoc leftist-tree-fns
;   ":doc-section leftist-trees
; All functions and constants related to leftist trees.~/~/
; ------------------------------------------------------------
; Functions and Constants
; ------------------------------------------------------------
;
; Function/Constant Name      Result
;   (supporting function)     Type
; ----------------------      ----
;
; ** STRUCTURE **
; RANK-LT                     natural
; ROOT-LT                     ?
; LEFT-LT                     ltree
; RIGHT-LT                    ltree
; *EMPTY-LT*                  NIL
; IS-EMPTY-LT                 boolean
; PROPER-LT                   boolean
;
; ** OPERATIONS **
; MERGE-LT                    ltree
;   MAKE-LT                   ltree
; INSERT-LT                   ltree
; FIND-MIN-LT                 ?
; DELETE-MIN-LT               ltree
; BUILD-LT                    ltree
;
; ** MISCELLANEOUS **
; SIZE-LT                     natural
; MEMBER-LT                   boolean
; LENGTH-RIGHT-SPINE-LT       natural
; LENGTH-TO-NIL-LT            natural
; ~/")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; STRUCTURE OF LEFTIST TREES ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; This legacy doc string was replaced Nov. 2014 by a corresponding
;;; auto-generated defxdoc form in file leftist-trees-xdoc.lisp.
; (defdoc leftist-tree-structure
;   ":doc-section leftist-tree-fns
; Functions relating to building and recognizing leftist trees.
; ~/~/
; ~/")

(defun rank-lt (tree)
;;; This legacy doc string was replaced Nov. 2014 by a corresponding
;;; auto-generated defxdoc form in file leftist-trees-xdoc.lisp.
;   ":doc-section leftist-tree-structure
; rank of a leftist tree~/~/
; Returns the rank of the tree. The rank of a tree is formally defined
; to be the length of its right spine. Empty trees have rank 0.~/"
  (if (atom tree)
      0
    (car tree)))

(defun root-lt (tree)
;;; This legacy doc string was replaced Nov. 2014 by a corresponding
;;; auto-generated defxdoc form in file leftist-trees-xdoc.lisp.
;   ":doc-section leftist-tree-structure
; root of a leftist tree~/~/
; Returns the root of a non-empty tree.~/"
  (cadr tree))

(defun left-lt (tree)
;;; This legacy doc string was replaced Nov. 2014 by a corresponding
;;; auto-generated defxdoc form in file leftist-trees-xdoc.lisp.
;   ":doc-section leftist-tree-structure
; left sub-tree of a leftist tree~/~/
; Returns the left sub-tree of a non-empty tree.~/"
  (caddr tree))

(defun right-lt (tree)
;;; This legacy doc string was replaced Nov. 2014 by a corresponding
;;; auto-generated defxdoc form in file leftist-trees-xdoc.lisp.
;   ":doc-section leftist-tree-structure
; right sub-tree of a leftist tree~/~/
; Returns the right sub-tree of a non-empty tree.~/"
  (cadddr tree))

(defconst *empty-lt* NIL
;;; This legacy doc string was replaced Nov. 2014 by a corresponding
;;; auto-generated defxdoc form in file leftist-trees-xdoc.lisp.
;   ":doc-section leftist-tree-structure
; the default empty leftist tree~/~/
; The default \"empty\" tree (just NIL)~/"
)

(defun is-empty-lt (tree)
;;; This legacy doc string was replaced Nov. 2014 by a corresponding
;;; auto-generated defxdoc form in file leftist-trees-xdoc.lisp.
;   ":doc-section leftist-tree-structure
; checks if a tree is empty~/~/
; Checks if a tree is empty. For simplicity, we only require (atom
; tree).~/"
  (atom tree))

(defun proper-lt (tree)
;;; This legacy doc string was replaced Nov. 2014 by a corresponding
;;; auto-generated defxdoc form in file leftist-trees-xdoc.lisp.
;   ":doc-section leftist-tree-structure
; checks that a tree is a legitimate leftist tree~/~/
; Checks that a tree is a legitimate Leftist Tree.
; The basic recursive requirements are:
;     * both the left and right sub-trees are proper
;     * (rank) the rank is 1 + the rank of the right sub-tree
;     * (leftist) the rank of right sub-tree is less than or
;       equal to the rank of the left sub-tree
;     * (heap-ordered) if either of the sub-trees are non-trivial,
;       then their roots are larger than the root of the tree
; ~/"
  (if (is-empty-lt tree)
      (and (null tree)
	   (equal (rank-lt tree) 0))
    (and (proper-lt (left-lt tree))
         (proper-lt (right-lt tree))
         (equal (rank-lt tree)
                (+ 1 (rank-lt (right-lt tree))))
         (<= (rank-lt (right-lt tree))
             (rank-lt (left-lt tree)))
         (implies (consp (left-lt tree))
                  (lexorder (root-lt tree)
                            (root-lt (left-lt tree))))
         (implies (consp (right-lt tree))
                  (lexorder (root-lt tree)
                            (root-lt (right-lt tree)))))))

;;;;;;;;;;;;;;;;;;;;;
;; HEAP OPERATIONS ;;
;;;;;;;;;;;;;;;;;;;;;

;;; This legacy doc string was replaced Nov. 2014 by a corresponding
;;; auto-generated defxdoc form in file leftist-trees-xdoc.lisp.
; (defdoc leftist-tree-ops
;   ":doc-section leftist-tree-fns
; The basic heap operations of leftist trees.~/~/
; The core operation here is MERGE-LT. All the other operations are
; defined in terms of MERGE-LT, which makes leftist trees relatively
; easy to reason about.~/")

(defun make-lt (x a b)
  (if (<= (rank-lt b) (rank-lt a))
      (list (+ 1 (rank-lt b)) x a b)
    (list (+ 1 (rank-lt a)) x b a)))

(defun merge-lt (tree1 tree2)
;;; This legacy doc string was replaced Nov. 2014 by a corresponding
;;; auto-generated defxdoc form in file leftist-trees-xdoc.lisp.
;   ":doc-section leftist-tree-ops
; merge two leftist trees~/~/
; Merge two leftist trees.
;
; Two leftist trees are merged by \"merging their right spines as you
; would merge two sorted lists, and then swapping the children of nodes
; along this path as necessary to restore the leftist property.\"
; (Okasaki)~/"
  (declare (xargs :measure (+ (acl2-count tree1)
                              (acl2-count tree2))))
  (cond ((is-empty-lt tree2) tree1)
        ((is-empty-lt tree1) tree2)
        (t (if (lexorder (root-lt tree1) (root-lt tree2))
               (make-lt (root-lt tree1)
                        (left-lt tree1)
                        (merge-lt (right-lt tree1) tree2))
             (make-lt (root-lt tree2)
                      (left-lt tree2)
                      (merge-lt tree1 (right-lt tree2)))))))

(defun insert-lt (x tree)
;;; This legacy doc string was replaced Nov. 2014 by a corresponding
;;; auto-generated defxdoc form in file leftist-trees-xdoc.lisp.
;   ":doc-section leftist-tree-ops
; insert an element into a leftist tree~/~/
; Insert an element into a leftist tree. This function is defined in
; terms of MERGE-LT.
;
; Example usage:
;
;     (INSERT-LT 2 (INSERT-LT 3 (INSERT-LT 4 *EMPTY-LT*)))
;
; This creates a leftist tree with elements 2, 3, 4.~/"
  (merge-lt (list 1 x NIL NIL) tree))

(defun find-min-lt (tree)
;;; This legacy doc string was replaced Nov. 2014 by a corresponding
;;; auto-generated defxdoc form in file leftist-trees-xdoc.lisp.
;   ":doc-section leftist-tree-ops
; get the minimum element of a leftist tree~/~/
; Get the minimum element of a nonempty tree. Assuming the tree in
; question is PROPER-LT, this is just the root of the tree.~/"
  (cond ((is-empty-lt tree) nil)
        (t (root-lt tree))))

(defun delete-min-lt (tree)
;;; This legacy doc string was replaced Nov. 2014 by a corresponding
;;; auto-generated defxdoc form in file leftist-trees-xdoc.lisp.
;   ":doc-section leftist-tree-ops
; delete the minimum element of a leftist tree~/~/
; Delete the minimum element of a nonempty tree. This is accomplisghed
; by simply merging the two subtrees.~/"
  (cond ((is-empty-lt tree) nil)
        (t (merge-lt (left-lt tree) (right-lt tree)))))

(defun build-lt (l)
;;; This legacy doc string was replaced Nov. 2014 by a corresponding
;;; auto-generated defxdoc form in file leftist-trees-xdoc.lisp.
; ":doc-section leftist-tree-ops
; build a leftist tree from a list~/~/
; Builds a leftist tree from a list of elements. This is accomplished by
; right-folding the INSERT-LT function over the list, starting with
; *EMPTY-LT*.~/"
  (if (atom l)
      *empty-lt*
    (insert-lt (car l) (build-lt (cdr l)))))

;;;;;;;;;;;;;;;;;;;
;; MISCELLANEOUS ;;
;;;;;;;;;;;;;;;;;;;

;;; This legacy doc string was replaced Nov. 2014 by a corresponding
;;; auto-generated defxdoc form in file leftist-trees-xdoc.lisp.
; (defdoc leftist-tree-misc
;   ":doc-section leftist-tree-fns
; Miscellaneous, but nonetheless useful, functions for leftist trees~/~/
; ~/")

(defun size-lt (tree)
;;; This legacy doc string was replaced Nov. 2014 by a corresponding
;;; auto-generated defxdoc form in file leftist-trees-xdoc.lisp.
;   ":doc-section leftist-tree-misc
; total number of elements in a leftist tree~/~/
; Returns the total number of elements in the tree.~/"
  (cond ((is-empty-lt tree) 0)
	(t (+ 1
	      (size-lt (left-lt tree))
	      (size-lt (right-lt tree))))))

(defun member-lt (x tree)
;;; This legacy doc string was replaced Nov. 2014 by a corresponding
;;; auto-generated defxdoc form in file leftist-trees-xdoc.lisp.
;   ":doc-section leftist-tree-misc
; tests membership in a leftist tree~/~/
; Tests whether something is an element of the tree. Note that this is
; not simply a brute-force search; if the root of the tree is greater
; than what we are looking for, we return nil. So in order for this
; function to work, the tree has to be PROPER-LT.~/"
  (cond ((is-empty-lt tree) nil)
	((equal x (root-lt tree)) t)
	((lexorder x (root-lt tree)) nil)
	(t (or (member-lt x (left-lt tree))
	       (member-lt x (right-lt tree))))))

(defun length-right-spine-lt (tree)
;;; This legacy doc string was replaced Nov. 2014 by a corresponding
;;; auto-generated defxdoc form in file leftist-trees-xdoc.lisp.
;   ":doc-section leftist-tree-misc
; length of the right spine of a leftist tree~/
; This is equivalent to RANK-LT.~/
; This function actually counts the length of the right spine of the
; tree. We will prove that this equals the rank of the tree.~/"
  (if (is-empty-lt tree)
      0
    (+ 1 (length-right-spine-lt (right-lt tree)))))

(defun length-to-nil-lt (tree)
;;; This legacy doc string was replaced Nov. 2014 by a corresponding
;;; auto-generated defxdoc form in file leftist-trees-xdoc.lisp.
;   ":doc-section leftist-tree-misc
; length of the shortest path to an empty node~/
; This is equivalent to RANK-LT.~/
; Returns the length of the shortest path to an empty node. We will
; prove that this equals the rank of the tree.~/"
  (cond ((is-empty-lt tree) 0)
        (t (+ 1 (min (length-to-nil-lt (left-lt tree))
                     (length-to-nil-lt (right-lt tree)))))))
