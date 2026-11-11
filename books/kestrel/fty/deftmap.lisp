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

(include-book "kestrel/data/tmap/internal/tree" :dir :system)
(include-book "kestrel/data/tmap/map" :dir :system)
(include-book "kestrel/data/tmap/keys" :dir :system)
(include-book "kestrel/data/tmap/values" :dir :system)
(include-book "kestrel/data/tmap/in-defs" :dir :system)
(include-book "kestrel/data/tmap/lookup" :dir :system)
(include-book "kestrel/data/tmap/min-max" :dir :system)
(include-book "kestrel/data/tmap/update" :dir :system)
(include-book "kestrel/data/tmap/update-star" :dir :system)
(include-book "kestrel/data/tmap/delete" :dir :system)
(include-book "kestrel/data/tmap/restrict" :dir :system)
(include-book "kestrel/data/tmap/generic-typed" :dir :system)
(include-book "kestrel/data/tmap/generic-count" :dir :system)

(include-book "kestrel/data/tset/set" :dir :system)
(include-book "kestrel/data/tset/in" :dir :system)
(include-book "kestrel/data/tset/insert" :dir :system)
(include-book "kestrel/data/tset/min-max" :dir :system)
(include-book "kestrel/data/tset/delete" :dir :system)
(include-book "kestrel/data/tset/cardinality" :dir :system)
