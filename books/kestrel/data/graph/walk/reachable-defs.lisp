; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "GRAPH")

(include-book "std/util/define-sk" :dir :system)
(include-book "std/basic/two-nats-measure" :dir :system)

(include-book "kestrel/data/tset/min-max-defs" :dir :system)
(include-book "kestrel/data/tset/insert-defs" :dir :system)
(include-book "kestrel/data/tset/delete-defs" :dir :system)
(include-book "kestrel/data/tset/union-defs" :dir :system)
(include-book "kestrel/data/tset/diff-defs" :dir :system)
(include-book "kestrel/data/tset/cardinality-defs" :dir :system)

(include-book "../graph-defs")
(include-book "../nodes-defs")
(include-book "../adjacency-defs")
(include-book "../successors-defs")
(include-book "walk-defs")
(include-book "walk-in-defs")

(local (include-book "std/util/defredundant" :dir :system))
(local (include-book "reachable"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; As in tset/subset-defs.lisp: std::defredundant cannot reproduce a
;; define-sk whose guards are verified separately, so the defun-sk and its
;; guard verification are given explicitly.

(defun-sk reachable+p-sk (from to graph)
  (declare (xargs :verify-guards nil))
  (declare (xargs :guard t))
  (exists (walk)
    (non-exec
      (and (walk-in walk graph)
           (equal (walk->start walk) from)
           (equal (walk-end walk) to)
           (consp (walk->steps walk)))))
  :skolem-name reachable+p-sk-witness
  :thm-name reachable+p-sk-suff)

(verify-guards reachable+p-sk)

(std::defredundant
  :names (reachable+p-sk-witness
          reachable+p-sk
          reachable+p-search
          reachable+p
          ))
