; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREEMAP")

(include-book "kestrel/data/treeset/in-defs" :dir :system)

(include-book "tree-defs")
(include-book "bst-defs")
(include-book "heap-defs")
(include-book "keys-defs")

(local (include-book "std/util/defredundant" :dir :system))
(local (include-book "lookup"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defredundant
  :names (tree-lookup
          tree-search-assoc
          acl2-number-tree-search-assoc
          symbol-tree-search-assoc
          eqlable-tree-search-assoc
          tree-search-lookup!
          acl2-number-tree-search-lookup!
          symbol-tree-search-lookup!
          eqlable-tree-search-lookup!
          ))
