; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREESET")

(include-book "std/util/defredundant" :dir :system)

(include-book "binary-tree-defs")
(include-book "bst-defs")
(include-book "heap-defs")

(local (include-book "set"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defredundant
  :names (setp
          sfix
          set-equiv
          emptyp
          head
          left
          right
          to-list))

(add-macro-alias set-equiv set-equiv$inline)
(add-macro-alias emptyp emptyp$inline)
(add-macro-alias head head$inline)
(add-macro-alias left left$inline)
(add-macro-alias right right$inline)

(defequiv set-equiv)
