; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "GRAPH")

(include-book "kestrel/data/treemap/keys-defs" :dir :system)
(include-book "kestrel/data/treemap/lookup-defs" :dir :system)

(include-book "graph-defs")
(include-book "nodes-defs")

(local (include-book "std/util/defredundant" :dir :system))
(local (include-book "adjacency"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defredundant
  :names (adjacency
          adjacency!
          successors
          labels
          ))
