; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "GRAPH")

(include-book "std/util/define-sk" :dir :system)

(include-book "kestrel/data/treeset/min-max-defs" :dir :system)
(include-book "kestrel/data/treeset/insert-defs" :dir :system)
(include-book "kestrel/data/treeset/delete-defs" :dir :system)
(include-book "kestrel/data/treeset/diff-defs" :dir :system)
(include-book "kestrel/data/treeset/cardinality-defs" :dir :system)
(include-book "kestrel/data/treemap/map-defs" :dir :system)
(include-book "kestrel/data/treemap/keys-defs" :dir :system)
(include-book "kestrel/data/treemap/lookup-defs" :dir :system)
(include-book "kestrel/data/treemap/update-defs" :dir :system)

(include-book "../graph-defs")
(include-book "../nodes-defs")
(include-book "../adjacency-defs")
(include-book "../successors-defs")
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
          kahn-remaining
          kahn-increment
          kahn-counters
          kahn-decrement
          kahn-loop
          cyclicp
          ))
