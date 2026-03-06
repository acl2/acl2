; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREEMAP")

(include-book "kestrel/data/treeset/set-defs" :dir :system)

(include-book "internal/restrict-defs")
(include-book "map-defs")

(local (include-book "std/util/defredundant" :dir :system))
(local (include-book "restrict"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defredundant
  :names (restrict
          restrict$inline
          restrict-=
          restrict-eq
          restrict-eql
          ))
