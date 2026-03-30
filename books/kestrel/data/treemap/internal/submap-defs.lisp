; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREEMAP")

(include-book "tree-defs")
(include-book "keys-defs")
(include-book "lookup-defs")
(include-book "split-defs")

(local (include-book "std/util/defredundant" :dir :system))
(local (include-book "submap"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defredundant
  :names (tree-submap-p
          tree-submap-p-sk-witness
          tree-submap-p-sk
          fast-tree-submap-p
          acl2-number-fast-tree-submap-p
          symbol-fast-tree-submap-p
          eqlable-fast-tree-submap-p
          ))
