; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TSET")

(include-book "std/osets/defs" :dir :system)

(include-book "../../internal/tree-defs")
(include-book "../../internal/in-order-defs")
(include-book "zip-frame-defs")
(include-book "zipper-defs")

(local (include-book "std/util/defredundant" :dir :system))
(local (include-book "zip-side"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defredundant
  :names (zip-path-tree-before
          zip-path-tree-after
          zip-tree-before
          zip-tree-after
          zip-path-before
          zip-path-after
          zip-before
          zip-after
          zip-oset-before
          zip-oset-after))
