; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "GRAPH")

(include-book "kestrel/data/treeset/in-defs" :dir :system)

(include-book "graph-defs")
(include-book "nodes-defs")
(include-book "internal/add-node-defs")
(include-book "internal/add-edge-defs")

(local (include-book "std/util/defredundant" :dir :system))
(local (include-book "add-edge"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defredundant
  :names (add-edge
          add-edge!
          ))
