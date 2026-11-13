; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TSET")

(include-book "../../internal/tree-defs")
(include-book "zip-frame-defs")
(include-book "zipper-defs")

(local (include-book "std/util/defredundant" :dir :system))
(local (include-book "zip-move"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defredundant
  :names (zip-descend-left
          zip-descend-right
          zip-ascend-one
          zip-descend-leftmost
          zip-descend-rightmost
          zip-descend-leftmost-hole
          zip-descend-rightmost-hole
          zip-ascend-to-left-frame
          zip-ascend-to-right-frame))
