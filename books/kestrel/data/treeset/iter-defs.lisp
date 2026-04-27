; Copyright (C) 2025-2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREESET")

(include-book "internal/iter-defs")
(include-book "set-defs")
(include-book "min-max-defs")
(include-book "cardinality-defs")

(local (include-book "std/util/defredundant" :dir :system))
(local (include-book "iter"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defredundant
  :names (iterp
          iter
          iter-fix
          iter-equiv
          iter-empty
          donep
          from-iter
          value
          next
          iter-measure
          ))

(defequiv iter-equiv)
