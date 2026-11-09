; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "GRAPH")

(include-book "kestrel/data/treeset/min-max-defs" :dir :system)
(include-book "kestrel/data/treeset/insert-defs" :dir :system)
(include-book "kestrel/data/treeset/delete-defs" :dir :system)
(include-book "kestrel/data/treeset/diff-defs" :dir :system)
(include-book "kestrel/data/treeset/cardinality-defs" :dir :system)
(include-book "kestrel/data/treemap/map-defs" :dir :system)
(include-book "kestrel/data/treemap/lookup-defs" :dir :system)
(include-book "kestrel/data/treemap/update-defs" :dir :system)
(include-book "kestrel/data/treemap/delete-defs" :dir :system)

(include-book "../graph-defs")
(include-book "../successors-defs")

(local (include-book "std/util/defredundant" :dir :system))
(local (include-book "kahn"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defredundant
  :names (kahn-remaining
          kahn-order
          kahn-increment
          kahn-counters
          kahn-decrement
          kahn-loop
          ))
