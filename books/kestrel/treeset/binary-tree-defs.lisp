; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREESET")

(include-book "std/util/defredundant" :dir :system)

(set-induction-depth-limit 0)

(local (include-book "binary-tree"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defredundant
  :names (binary-tree-p
          tree-fix
          tree-equiv
          tree-emptyp
          tree-head
          tree-left
          tree-right
          tree-node
          tree-node-with-hint
          binary-tree-listp
          tree-pre-order
          tree-in-order
          tree-post-order))

(add-macro-alias tree-fix tree-fix$inline)
(add-macro-alias tree-equiv tree-equiv$inline)
(add-macro-alias tree-emptyp tree-emptyp$inline)
(add-macro-alias tree-head tree-head$inline)
(add-macro-alias tree-left tree-left$inline)
(add-macro-alias tree-right tree-right$inline)
(add-macro-alias tree-node tree-node$inline)
(add-macro-alias tree-node-with-hint tree-node-with-hint$inline)

(defequiv tree-equiv)
