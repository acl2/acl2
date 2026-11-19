; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TSET")

(include-book "kestrel/data/utilities/total-order/compare-defs" :dir :system)

(include-book "../../internal/tree-defs")
(include-book "zip-frame-defs")
(include-book "zipper-defs")
(include-book "zip-move-defs")
(include-book "zip-side-defs")

(local (include-book "std/util/defredundant" :dir :system))
(local (include-book "zip-seek"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defredundant
  :names (zip-seek
          zip-seek-loop
          acl2-number-zip-seek-loop
          symbol-zip-seek-loop
          eqlable-zip-seek-loop
          zip-path-brackets-p))
