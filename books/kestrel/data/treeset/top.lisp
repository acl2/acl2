; Copyright (C) 2025-2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREESET")

(include-book "defs")
(include-book "hash")
(include-book "set")
(include-book "to-oset")
(include-book "min-max")
(include-book "in")
(include-book "cardinality")
(include-book "subset")
(include-book "extensionality")
(include-book "insert")
(include-book "delete")
(include-book "generic-typed")
(include-book "induction")
(include-book "union")
(include-book "intersect")
(include-book "diff")
(include-book "iter")
(include-book "fty")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; For ordinary use of treesets, it is recommend that you include the "defs"
;; books (or some subset of the books it includes), and then this book (or some
;; subset of its includes) *locally*.
