; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "GRAPH")

(include-book "std/util/define-sk" :dir :system)

(include-book "kestrel/data/treeset/diff-defs" :dir :system)
(include-book "kestrel/data/treemap/map-defs" :dir :system)
(include-book "kestrel/data/treemap/keys-defs" :dir :system)

(include-book "../graph-defs")
(include-book "../nodes-defs")
(include-book "kahn-defs")
(include-book "reachable-defs")

(local (include-book "std/util/defredundant" :dir :system))
(local (include-book "cyclic"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; As in reachable-defs.lisp, the defun-sk and its guard verification are given
;; explicitly.

(defun-sk cyclicp-sk (graph)
  (declare (xargs :verify-guards nil))
  (declare (xargs :guard t))
  (exists (node)
    (non-exec (reachable+p node node graph)))
  :skolem-name cyclicp-sk-witness
  :thm-name cyclicp-sk-suff)

(verify-guards cyclicp-sk)

(std::defredundant
  :names (cyclicp-sk-witness
          cyclicp-sk
          cyclicp
          ))
