; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "GRAPH")

(include-book "kestrel/data/treeset/insert-defs" :dir :system)
(include-book "kestrel/data/treeset/intersect-defs" :dir :system)
(include-book "kestrel/data/treeset/diff-defs" :dir :system)
(include-book "kestrel/data/treemap/map-defs" :dir :system)
(include-book "kestrel/data/treemap/keys-defs" :dir :system)

(include-book "../graph-defs")
(include-book "../nodes-defs")
(include-book "../predecessors-defs")
(include-book "kahn-defs")
(include-book "cyclic-defs")

(local (include-book "std/util/defredundant" :dir :system))
(local (include-book "topological-sort"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defredundant
  :names (reachable+p-sortedp
          topological-orderp
          topological-sort
          ))
