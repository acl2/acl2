; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREESET")

(include-book "std/util/define" :dir :system)

(include-book "binary-tree-defs")
(include-book "bst-order-defs")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

(local (include-book "bst"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bst<-all-l
  ((tree binary-tree-p)
   x)
  (declare (xargs :type-prescription (booleanp (bst<-all-l tree x))))
  :parents (binary-tree)
  :short "Check that all members of a tree are @(tsee bst<) some value."
  (or (tree-emptyp tree)
      (and (bst< (tree-head tree) x)
           (bst<-all-l (tree-left tree) x)
           (bst<-all-l (tree-right tree) x))))

(define bst<-all-r
  (x
   (tree binary-tree-p))
  (declare (xargs :type-prescription (booleanp (bst<-all-r x tree))))
  :parents (binary-tree)
  :short "Check that some value is @(tsee bst<) all members of a tree."
  (or (tree-emptyp tree)
      (and (bst< x (tree-head tree))
           (bst<-all-r x (tree-left tree))
           (bst<-all-r x (tree-right tree)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bst-p
  ((tree binary-tree-p))
  (declare (xargs :type-prescription (booleanp (bst-p tree))))
  :parents (binary-tree)
  :short "Check the binary search tree property."
  (or (tree-emptyp tree)
      (and (bst-p (tree-left tree))
           (bst-p (tree-right tree))
           (bst<-all-l (tree-left tree) (tree-head tree))
           (bst<-all-r (tree-head tree) (tree-right tree)))))
