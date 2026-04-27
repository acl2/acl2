; Copyright (C) 2025-2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREESET")

(include-book "tree-defs")
(include-book "bst-defs")
(include-book "heap-defs")
(include-book "subset-defs")
(include-book "insert-defs")
(include-book "union-defs")

(local (include-book "std/util/defredundant" :dir :system))
(local (include-book "iter"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defredundant
  :names (tree-iter-p
          all-well-formed-p
          pairwise-tree-subset-p-of-left-loop
          pairwise-tree-subset-p-of-left
          tree-iter-to-tree
          tree-left-spine-acc
          tree-left-spine
          tree-iter-value
          tree-iter-next
          ))
