; Copyright (C) 2025-2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREESET")

(include-book "kestrel/data/utilities/total-order/total-order-defs" :dir :system)

(include-book "tree-defs")
(include-book "rotate-defs")

(local (include-book "std/util/defredundant" :dir :system))
(local (include-book "split"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defredundant
  :names (tree-split
          acl2-number-tree-split
          symbol-tree-split
          eqlable-tree-split
          ))
