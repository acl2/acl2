; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREESET")

(include-book "std/util/define" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(include-book "binary-tree-defs")
(include-book "bst-defs")
(include-book "heap-defs")

(set-induction-depth-limit 0)

(local (include-book "set"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define setp (x)
  (declare (xargs :type-prescription (booleanp (setp x))))
  :parents (set)
  :short "Recognizer for @(see set)s."
  :long
  (xdoc::topstring
   (xdoc::p
     "Time complexity: @($O(n^2)$) (Note: the current implementation is
      inefficient. This should eventually be @($O(n)$) once we introduce a more
      efficient binary search tree property check via an @(tsee mbe).)"))
  (and (binary-tree-p x)
       (bst-p x)
       (heapp x)))

(define sfix ((set setp))
  :parents (set)
  :short "Fixer for @(see set)s."
  (mbe :logic (if (setp set) set nil)
       :exec (the (or cons null) set)))

(define set-equiv
  ((x setp)
   (y setp))
  (declare (xargs :type-prescription (booleanp (set-equiv x y))))
  :parents (set)
  :short "Equivalence up to @(tsee sfix)."
  (equal (sfix x)
         (sfix y))
  :inline t
  :no-function t)

(defequiv set-equiv)

(define emptyp ((set setp))
  (declare (xargs :type-prescription (booleanp (emptyp set))))
  :parents (set)
  :short "Check if a @(see set) is empty."
  (tree-emptyp (sfix set))
  :no-function t
  :inline t)

(define head ((set setp))
  :parents (set)
  :short "Get an element of the nonempty @(see set)."
  :long
  (xdoc::topstring
   (xdoc::p
     "For empty trees, returns @('nil').")
   (xdoc::p
     "From a user perspective, this should likely be viewed as an arbitrary
      element of the set, to be used only in conjunction with @(tsee left) and
      @(tsee right) to fold over the set. Under the hood, this is the root
      element of the underlying tree, which will be the unique maximum value
      with respect to @(tsee heap<)."))
  (tree-head (sfix set))
  :no-function t
  :inline t)

(define left ((set setp))
  :parents (set)
  :short "Get the \"left\" subset of the nonempty @(see set)."
  :long
  (xdoc::topstring
   (xdoc::p
     "For empty sets, returns @('nil').")
   (xdoc::p
     "From a user perspective, this should likely be viewed as an arbitrary
      proper subset excluding the @(tsee head) and disjoint from the @(tsee
      right) subset. Concretely, it is the subset for which all elements are
      @(tsee bst<) the @(tsee head). In terms of the underlying tree
      representation, this is the left subtree."))
  (tree-left (sfix set))
  :no-function t
  :inline t)

(define right ((set setp))
  :parents (set)
  :short "Get the \"right\" subset of the nonempty @(see set)."
  :long
  (xdoc::topstring
   (xdoc::p
     "For empty sets, returns @('nil').")
   (xdoc::p
     "From a user perspective, this should likely be viewed as an arbitrary
      proper subset excluding the @(tsee head) and disjoint from the @(tsee
      left) subset. Concretely, it is the subset for which the @(tsee head) is
      @(tsee bst<) all elements. In terms of the underlying tree representation,
      this is the right subtree."))
  (tree-right (sfix set))
  :no-function t
  :inline t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define to-list
  ((set setp))
  :parents (set)
  :short "Create a list of values from a set."
  (tree-post-order (sfix set)))
