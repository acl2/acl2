; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TSET")

(include-book "kestrel/data/utilities/fixed-size-words/u32-defs" :dir :system)

(include-book "../../hash-defs")
(include-book "../../internal/heap-order-defs")
(include-book "../../internal/tree-defs")
(include-book "../../internal/split-defs")
(include-book "zip-frame-defs")
(include-book "zipper-defs")
(include-book "zip-move-defs")

(local (include-book "std/util/defredundant" :dir :system))
(local (include-book "zip-insert-hole"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defredundant
  :names (zip-ascend-while-lower
          zip-insert-hole-loop
          zip-insert-hole))
