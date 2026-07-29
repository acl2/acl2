; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREESET")

(include-book "internal/iter")
(include-book "set-defs")

(local (include-book "std/util/defredundant" :dir :system))
(local (include-book "iter"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defredundant
  :names (iterp
          iter
          iter-fix
          iter-equiv
          after-lastp
          before-firstp
          has-valuep
          from-iter
          value
          next
          prev
          nexts
          prevs
          ))

(defequiv iter-equiv)
