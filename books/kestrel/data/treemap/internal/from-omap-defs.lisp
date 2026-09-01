; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREEMAP")

(include-book "kestrel/data/utilities/omap-defs" :dir :system)
(include-book "kestrel/data/treeset/internal/heap-order-defs" :dir :system)

(include-book "tree-defs")
(include-book "heap-defs")

(local (include-book "std/util/defredundant" :dir :system))
(local (include-book "from-omap"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defredundant
  :names (tree-from-omap-below
          tree-from-omap-acc
          tree-from-omap
          ))
