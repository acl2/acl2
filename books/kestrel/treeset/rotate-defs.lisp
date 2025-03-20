; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREESET")

(include-book "std/util/define" :dir :system)

(include-book "set-defs")
(include-book "cardinality-defs")
(include-book "in-defs")

(set-induction-depth-limit 0)

(local (include-book "rotate"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define rotate-left
  ((tree binary-tree-p))
  :guard (not (tree-emptyp (tree-right tree)))
  :returns (tree$ binary-tree-p)
  :short "Perform a left tree rotation."
  :long
  (xdoc::topstring
   (xdoc::p
     "When the right subtree is empty (contrary to the guard), we logically
      just return the tree."))
  (if (mbt (not (tree-emptyp (tree-right tree))))
      (tree-node (tree-head (tree-right tree))
                 (tree-node (tree-head tree)
                            (tree-left tree)
                            (tree-left (tree-right tree)))
                 (tree-right (tree-right tree)))
    (tree-fix tree))
  :no-function t
  :inline t)

(define rotate-right
  ((tree binary-tree-p))
  :guard (not (tree-emptyp (tree-left tree)))
  :returns (tree$ binary-tree-p)
  :short "Perform a right tree rotation."
  :long
  (xdoc::topstring
   (xdoc::p
     "When the left subtree is empty (contrary to the guard), we logically
      just return the tree."))
  (if (mbt (not (tree-emptyp (tree-left tree))))
      (tree-node (tree-head (tree-left tree))
                 (tree-left (tree-left tree))
                 (tree-node (tree-head tree)
                            (tree-right (tree-left tree))
                            (tree-right tree)))
    (tree-fix tree))
  :no-function t
  :inline t)
