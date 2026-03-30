; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREEMAP")

(include-book "internal/tree-defs")
(include-book "internal/update-star-defs")
(include-book "map-defs")
(include-book "keys-defs")

(local (include-book "std/util/defredundant" :dir :system))
(local (include-book "update-star"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defredundant
  :names (update*-macro-loop
          update*-macro-fn
          update*
          update*$inline
          update*-=
          update*-eq
          update*-eql))
