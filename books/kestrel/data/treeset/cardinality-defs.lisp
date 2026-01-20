; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREESET")

(include-book "std/util/defredundant" :dir :system)
(include-book "kestrel/data/sum-acl2-count-defs" :dir :system)

(include-book "set-defs")

(local (include-book "cardinality"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defredundant
  :names (fast-tree-nodes-count
          tree-nodes-count
          cardinality))

(add-macro-alias tree-nodes-count tree-nodes-count$inline)
(add-macro-alias cardinality cardinality$inline)
