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

(include-book "kestrel/data/treemap/internal/tree" :dir :system)
(include-book "kestrel/data/treemap/map" :dir :system)
(include-book "kestrel/data/treemap/keys" :dir :system)
(include-book "kestrel/data/treemap/values" :dir :system)
(include-book "kestrel/data/treemap/in-defs" :dir :system)
(include-book "kestrel/data/treemap/lookup" :dir :system)
(include-book "kestrel/data/treemap/min-max" :dir :system)
(include-book "kestrel/data/treemap/update" :dir :system)
(include-book "kestrel/data/treemap/update-star" :dir :system)
(include-book "kestrel/data/treemap/delete" :dir :system)
(include-book "kestrel/data/treemap/restrict" :dir :system)
(include-book "kestrel/data/treemap/generic-typed" :dir :system)
(include-book "kestrel/data/treemap/generic-count" :dir :system)

(include-book "kestrel/data/treeset/set" :dir :system)
(include-book "kestrel/data/treeset/in" :dir :system)
(include-book "kestrel/data/treeset/insert" :dir :system)
(include-book "kestrel/data/treeset/min-max" :dir :system)
(include-book "kestrel/data/treeset/delete" :dir :system)
(include-book "kestrel/data/treeset/cardinality" :dir :system)
