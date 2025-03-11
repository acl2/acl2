; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREESET")

(include-book "std/util/define" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(include-book "std/basic/two-nats-measure" :dir :system)

(include-book "set-defs")
(include-book "sum-acl2-count")

(set-induction-depth-limit 0)

(local (include-book "cardinality"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fast-tree-nodes-count
  ((trees binary-tree-listp)
   (acc natp))
  (declare (xargs :type-prescription (natp (fast-tree-nodes-count trees acc))))
  (b* ((acc (mbe :logic (nfix acc)
                 :exec (the unsigned-byte acc))))
    (cond ((endp trees)
           acc)
          ((tree-emptyp (first trees))
           (fast-tree-nodes-count (rest trees) acc))
          (t (fast-tree-nodes-count (list* (tree-left (first trees))
                                           (tree-right (first trees))
                                           (rest trees))
                                    (+ 1 acc)))))
  :measure (acl2::nat-list-measure
            (list (sum-acl2-count trees)
                  (len trees))))

(define tree-nodes-count
  ((tree binary-tree-p))
  (declare (xargs :type-prescription (natp (tree-nodes-count tree))))
  :parents (implementation)
  :short "The number of elements in a tree."
  (mbe :logic (if (tree-emptyp tree)
                  0
                (+ 1
                   (tree-nodes-count (tree-left tree))
                   (tree-nodes-count (tree-right tree))))
       :exec (fast-tree-nodes-count (list tree) 0)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define cardinality
  ((set setp))
  (declare (xargs :type-prescription (natp (cardinality set))))
  :parents (set)
  :short "The number of elements in a @(see set)."
  :long
  (xdoc::topstring
   (xdoc::p
     "Time complexity: @($O(n)$)."))
  (tree-nodes-count (sfix set)))
