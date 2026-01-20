; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREESET")

(include-book "std/util/defredundant" :dir :system)

(include-book "binary-tree-defs")
(include-book "join-defs")
(include-book "set-defs")
(include-book "split-defs")

(local (include-book "intersect"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defredundant
  :names (tree-intersect
          intersect-macro-loop
          binary-intersect
          intersect))

(add-macro-alias binary-intersect binary-intersect$inline)
(add-macro-fn intersect binary-intersect$inline t)
