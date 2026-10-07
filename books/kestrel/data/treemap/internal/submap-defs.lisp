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

; Matt K. mod: Two necessary additions because of verify-guards fix, 9/19/2026.
; Perhaps these could std::defredundant could be improved to make these
; unnecessary.

(DEFUN-SK TREE-SUBMAP-P-SK (X Y)
  (DECLARE (XARGS :VERIFY-GUARDS NIL))
  (DECLARE (XARGS :GUARD T))
  (FORALL
   (KEY)
   (NON-EXEC (IMPLIES (TREESET::IN KEY (TREE-KEY-SET X))
                      (AND (TREESET::IN KEY (TREE-KEY-SET Y))
                           (EQUAL (TREE-LOOKUP KEY X)
                                  (TREE-LOOKUP KEY Y))))))
  :REWRITE
  (IMPLIES
   (TREE-SUBMAP-P-SK X Y)
   (NON-EXEC (IMPLIES (TREESET::IN KEY (TREE-KEY-SET X))
                      (AND (TREESET::IN KEY (TREE-KEY-SET Y))
                           (EQUAL (TREE-LOOKUP KEY X)
                                  (TREE-LOOKUP KEY Y))))))
  :SKOLEM-NAME TREE-SUBMAP-P-SK-WITNESS
  :THM-NAME TREE-SUBMAP-P-SK-NECC)

(verify-guards TREE-SUBMAP-P-SK)

(std::defredundant
  :names (tree-submap-p
          tree-submap-p-sk-witness
          tree-submap-p-sk
          fast-tree-submap-p
          acl2-number-fast-tree-submap-p
          symbol-fast-tree-submap-p
          eqlable-fast-tree-submap-p
          ))
