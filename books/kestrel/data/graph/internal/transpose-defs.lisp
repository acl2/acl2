; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "GRAPH")

(include-book "kestrel/data/tmap/map-defs" :dir :system)
(include-book "kestrel/data/tmap/size-defs" :dir :system)
(include-book "kestrel/data/tmap/min-max-defs" :dir :system)
(include-book "kestrel/data/tmap/lookup-defs" :dir :system)
(include-book "kestrel/data/tmap/update-defs" :dir :system)
(include-book "kestrel/data/tmap/delete-defs" :dir :system)
(include-book "kestrel/data/tmap/cursor/defs" :dir :system)

(include-book "adj-list-defs")
(include-book "add-node-defs")

(local (include-book "std/util/defredundant" :dir :system))
(local (include-book "transpose"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defredundant
  :names (adjacency-transpose
          adj-list-transpose
          ))
