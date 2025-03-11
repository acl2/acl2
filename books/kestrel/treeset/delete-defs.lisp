; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREESET")

(include-book "std/util/define" :dir :system)

(include-book "cardinality-defs")
(include-book "in-defs")
(include-book "join-defs")
(include-book "rotate-defs")
(include-book "set-defs")

(set-induction-depth-limit 0)

(local (include-book "delete"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-delete
  (x
   (tree binary-tree-p))
  (declare (xargs :type-prescription (or (consp (tree-delete x tree))
                                         (equal (tree-delete x tree) nil))))
  :parents (implementation)
  :short "Remove a value from the tree."
  :long
  (xdoc::topstring
   (xdoc::p
     "The tree is expected to be a binary search tree. If it is not, the
      element @('x') intended to be deleted might outside the search path and
      thus remain in the tree.")
   (xdoc::p
     "After deletion, the tree is rebalanced with respect to the @(tsee
     heapp) property."))
  (b* (((when (tree-emptyp tree))
        nil)
       ((when (equal x (tree-head tree)))
        (cond ((tree-emptyp (tree-left tree))
               (tree-right tree))
              ((tree-emptyp (tree-right tree))
               (tree-left tree))
              (t (tree-join-at (tree-head tree)
                               (tree-left tree)
                               (tree-right tree)))))
       )
    (if (bst< x (tree-head tree))
        (tree-node-with-hint (tree-head tree)
                             (tree-delete x (tree-left tree))
                             (tree-right tree)
                             tree)
      (tree-node-with-hint (tree-head tree)
                           (tree-left tree)
                           (tree-delete x (tree-right tree))
                           tree))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define delete1
  (x
   (set setp))
  (declare (xargs :type-prescription (or (consp (delete1 x set))
                                         (equal (delete1 x set) nil))))
  (tree-delete x (sfix set)))

(define delete-macro-loop
  ((list true-listp))
  :guard (and (consp list)
              (consp (rest list)))
  (if (endp (rest (rest list)))
      (list 'delete1
            (first list)
            (second list))
    (list 'delete1
          (first list)
          (delete-macro-loop (rest list)))))

(defmacro delete (x y &rest rst)
  (declare (xargs :guard t))
  (delete-macro-loop (list* x y rst)))

(add-macro-fn delete delete1 t)
