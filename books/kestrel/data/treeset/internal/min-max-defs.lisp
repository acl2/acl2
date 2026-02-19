; Copyright (C) 2025-2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREESET")

(include-book "kestrel/data/utilities/total-order/max-defs" :dir :system)
(include-book "kestrel/data/utilities/total-order/min-defs" :dir :system)

(include-book "tree-defs")

(local (include-book "std/util/defredundant" :dir :system))
(local (include-book "min-max"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defredundant
  :names (tree-min
          tree-max
          tree-leftmost
          tree-rightmost
          ))
