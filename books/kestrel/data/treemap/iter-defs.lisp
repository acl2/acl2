; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREEMAP")

(include-book "internal/iter")
(include-book "map-defs")
(include-book "update-defs")

(local (include-book "std/util/defredundant" :dir :system))
(local (include-book "iter"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defredundant
  :names (iterp
          iter-min
          iter-max
          iter-fix
          iter-equiv
          after-lastp
          before-firstp
          has-valuep
          from-iter
          before
          after
          entry-key
          entry-val
          entry
          next
          prev
          nexts
          prevs
          ))

(defequiv iter-equiv)
