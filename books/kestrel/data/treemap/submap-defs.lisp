; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREEMAP")

(include-book "kestrel/data/treeset/in-defs" :dir :system)

(include-book "internal/submap-defs")
(include-book "map-defs")
(include-book "keys-defs")
(include-book "lookup-defs")

(local (include-book "std/util/defredundant" :dir :system))
(local (include-book "submap"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defredundant
  :names (submap
          submap$inline
          submap-sk-witness
          submap-sk
          submap-=
          submap-eq
          submap-eql
          ))
