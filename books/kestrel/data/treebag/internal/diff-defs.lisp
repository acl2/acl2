; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREEBAG")

(include-book "kestrel/data/treemap/internal/tree-defs" :dir :system)
(include-book "kestrel/data/treemap/internal/heap-defs" :dir :system)
(include-book "kestrel/data/treemap/internal/join-defs" :dir :system)
(include-book "kestrel/data/treemap/internal/split-defs" :dir :system)

(include-book "map-values-all-posp-defs")

(local (include-book "std/util/defredundant" :dir :system))
(local (include-book "diff"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defredundant
  :names (tree-diff
          ))
