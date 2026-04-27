; Copyright (C) 2025-2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREESET")

(include-book "kestrel/data/utilities/fixed-size-words/u32-defs" :dir :system)

(include-book "../hash-defs")

(local (include-book "std/util/defredundant" :dir :system))
(local (include-book "tree"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defredundant
  :names (tree-element-p
          irr-tree-element
          tree-element-fix
          tree-element-equiv
          tree-element->val
          tree-element->hash
          tree-element
          treep
          tree-fix
          tree-equiv
          tree-empty-p
          tree->head
          tree->left
          tree->right
          tree-node
          tree-listp
          tree-list-fix
          tree-all-acl2-numberp
          tree-all-symbolp
          tree-all-eqlablep
          acl2-number-treep
          symbol-treep
          eqlable-treep
          ))

(defequiv tree-element-equiv)
(defequiv tree-equiv)
