; FTY Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "FTY")

(include-book "centaur/fty/deftypes" :dir :system)

(include-book "kestrel/data/treeset/internal/tree" :dir :system)
(include-book "kestrel/data/treeset/set" :dir :system)
(include-book "kestrel/data/treeset/in-defs" :dir :system)
(include-book "kestrel/data/treeset/min-max" :dir :system)
(include-book "kestrel/data/treeset/cardinality-defs" :dir :system)
(include-book "kestrel/data/treeset/insert" :dir :system)
(include-book "kestrel/data/treeset/delete" :dir :system)
(include-book "kestrel/data/treeset/union" :dir :system)
(include-book "kestrel/data/treeset/intersect" :dir :system)
(include-book "kestrel/data/treeset/diff" :dir :system)
(include-book "kestrel/data/treeset/generic-typed" :dir :system)
(include-book "kestrel/data/treeset/generic-count" :dir :system)
