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

FILE: top.lisp

 An implementation of Leftist Trees (otherwise known as Leftist Heaps)
 as described in Purely Functional Data Structures (Chris Okasaki,
 Cambridge University Press 1998).

 Leftist trees are an efficient implementation of binary
 heaps. Regular (completely balanced) binary heaps are tricky, and in
 most cases near impossible, to implement in functional languages
 because of the need for constant-time access to the last element in
 the tree (that element being the node in the bottom-most level of the
 tree, furthest to the right). Leftist trees avoid this by not
 requiring the tree to be completely balanced.

 Instead, a leftist tree keeps track of its own "rank," which is
 defined to be the length of its right-most spine. The "shape"
 requirement on leftist trees can be stated as:

     (shape) The rank of a tree's left sub-tree is at least as large
     as the rank of its right sub-tree.

 The full list of requirements for leftist trees then becomes:

     (rank) The rank of the empty tree is zero. The rank of a
         non-empty tree is one more than the rank of its right
         sub-tree.

     (heap-ordered) The minimum element in the tree is always the root
         node.

     (shape) The rank of a tree's left sub-tree is at least as large
         as the rank of its right sub-tree.

 Of course, these requirements hold recursively for the left- and
 right-subtrees of every leftist tree.

 The following main functions, constants, and theorems are exported:

 ; ------------------------------------------------------------
 ; Functions and Constants
 ; ------------------------------------------------------------

 ; Function/Constant Name      Result
 ;   (supporting function)     Type
 ; ----------------------      ----

 ; ** STRUCTURE **
 ; rank-lt                     natural
 ; root-lt                     ?
 ; left-lt                     ltree
 ; right-lt                    ltree
 ; *empty-lt*                  NIL
 ; is-empty-lt                 boolean
 ; proper-lt                   boolean

 ; ** OPERATIONS **
 ; merge-lt                    ltree
 ;   make-lt                   ltree
 ; insert-lt                   ltree
 ; find-min-lt                 ?
 ; delete-min-lt               ltree
 ; build-lt                    ltree

 ; ** MISCELLANEOUS **
 ; size-lt                     natural
 ; member-lt                   boolean
 ; length-right-spine-lt       natural
 ; length-to-nil-lt            natural
 ; how-many-lt                 natural

 ; ** HEAPSORT **
 ; ltree-to-list               list
 ; ltree-sort                  list

 ; ------------------------------------------------------------
 ; Theorems
 ; ------------------------------------------------------------

 ; ** BASIC OPERATIONS RESPECT STRUCTURE
(defthm proper-merge-lt
  (implies (and (proper-lt tree1)
                (proper-lt tree2))
           (proper-lt (merge-lt tree1 tree2))))

(defthm proper-insert-lt
  (implies (proper-lt tree)
           (proper-lt (insert-lt x tree))))

(defthm proper-delete-min-lt
  (implies (proper-lt tree)
           (proper-lt (delete-min tree))))

(defthm proper-build-lt
  (proper-lt (build-lt l)))

 ; ** RANK THEOREMS
(defthm size-rank-lt
  (implies (proper-lt tree)
           (<= (- (expt 2 (rank-lt tree)) 1)
               (size-lt tree))))

 ; ** HOW-MANY THEOREMS
(defthm how-many-lt-zero
  (implies (not (lexorder (root-lt tree) e))
           (equal (how-many-lt e tree) 0)))

(defthm how-many-merge-lt
  (implies (and (proper-lt tree1)
                (proper-lt tree2))
           (equal (how-many-lt e (merge-lt tree1 tree2))
                  (+ (how-many-lt e tree1)
                     (how-many-lt e tree2)))))

(defthm how-many-insert-lt
  (implies (proper-lt tree)
           (equal (how-many-lt e (insert-lt e tree))
                  (+ 1 (how-many-lt e tree)))))

(defthm how-many-delete-min-lt
  (implies (and (proper-lt tree)
                (consp tree))
           (equal (how-many-lt e (delete-min-lt tree))
                  (+ (how-many-lt e (left-lt tree))
                     (how-many-lt e (right-lt tree))))))

(defthm how-many-build-lt
  (equal (how-many-lt e (build-lt l))
         (how-many e l)))

 ; ** HEAPSORT THEOREMS
(defthm orderedp-proper-ltree-to-list
  (implies (proper-lt tree)
           (orderedp (ltree-to-list tree))))

(defthm orderedp-ltree-sort
  (orderedp (ltree-sort l)))

(defthm true-listp-ltree-sort
  (true-listp (ltree-sort l)))

(defthm how-many-ltree-to-list
  (implies (proper-lt tree)
           (equal (how-many e (ltree-to-list tree))
                  (how-many-lt e tree))))

(defthm how-many-ltree-sort
  (equal (how-many e (ltree-sort x))
         (how-many e x)))

|#

(in-package "ACL2")

(include-book "leftist-tree-defuns")
(include-book "leftist-tree-defthms")
(include-book "leftist-tree-sort")
(include-book "leftist-trees-xdoc")
