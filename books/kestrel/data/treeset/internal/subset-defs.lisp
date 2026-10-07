; Copyright (C) 2025-2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREESET")

(include-book "tree-defs")
(include-book "in-defs")
(include-book "split-defs")

(local (include-book "std/util/defredundant" :dir :system))
(local (include-book "subset"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Matt K. mod: Two necessary additions because of verify-guards fix, 9/19/2026.
; Perhaps these could std::defredundant could be improved to make these
; unnecessary.

(DEFUN-SK TREE-SUBSET-P-SK (X Y)
  (DECLARE (XARGS :VERIFY-GUARDS nil))
  (DECLARE (XARGS :GUARD T))
  (FORALL (ELEM)
          (NON-EXEC (IMPLIES (TREE-IN ELEM X)
                             (TREE-IN ELEM Y))))
  :REWRITE (IMPLIES (TREE-SUBSET-P-SK X Y)
                    (NON-EXEC (IMPLIES (TREE-IN ELEM X)
                                       (TREE-IN ELEM Y))))
  :SKOLEM-NAME TREE-SUBSET-P-SK-WITNESS
  :THM-NAME TREE-SUBSET-P-SK-NECC)

(verify-guards TREE-SUBSET-P-SK)

(std::defredundant
  :names (tree-subset-p
          tree-subset-p-sk-witness
          tree-subset-p-sk
          fast-tree-subset-p
          acl2-number-fast-tree-subset-p
          symbol-fast-tree-subset-p
          eqlable-fast-tree-subset-p
          ))
