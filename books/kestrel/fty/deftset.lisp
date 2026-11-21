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

(include-book "kestrel/data/tset/internal/tree" :dir :system)
(include-book "kestrel/data/tset/set" :dir :system)
(include-book "kestrel/data/tset/in-defs" :dir :system)
(include-book "kestrel/data/tset/min-max" :dir :system)
(include-book "kestrel/data/tset/cardinality" :dir :system)
(include-book "kestrel/data/tset/insert" :dir :system)
(include-book "kestrel/data/tset/delete" :dir :system)
(include-book "kestrel/data/tset/union" :dir :system)
(include-book "kestrel/data/tset/intersect" :dir :system)
(include-book "kestrel/data/tset/diff" :dir :system)
(include-book "kestrel/data/tset/generic-typed" :dir :system)
(include-book "kestrel/data/tset/cursor/generic-typed" :dir :system)
(include-book "kestrel/data/tset/generic-count" :dir :system)
