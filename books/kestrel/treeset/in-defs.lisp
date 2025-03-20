; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREESET")

(include-book "std/util/define" :dir :system)

(include-book "set-defs")

(set-induction-depth-limit 0)

(local (include-book "in"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tree-in
  (x
   (tree binary-tree-p))
  (declare (xargs :type-prescription (booleanp (tree-in x tree))))
  :parents (implementation)
  :short "Determine if a value appears in the tree."
  :long
  (xdoc::topstring
   (xdoc::p
     "No assumptions are made about the structure of the tree, so this search
      takes linear time. In practice, this function is only used as part of the
      logical definition of @(tsee in) (which is provided a more efficient
      implementation with @(tsee mbe))."))
  (and (not (tree-emptyp tree))
       (or (equal x (tree-head tree))
           (tree-in x (tree-left tree))
           (tree-in x (tree-right tree)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define in
  (x
   (set setp))
  (declare (xargs :type-prescription (booleanp (in x set))))
  :parents (set)
  :short "Determine if a value is a member of the set."
  :long
  (xdoc::topstring
   (xdoc::p
     "Time complexity: @($O(log(n))$)."))
  (mbe :logic (tree-in x (sfix set))
       :exec (and (not (emptyp set))
                  (or (equal x (head set))
                      (if (bst< x (head set))
                          (in x (left set))
                        (in x (right set)))))))
