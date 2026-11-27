; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TSET")

(include-book "../../internal/tree-defs")
(include-book "../../internal/join-defs")
(include-book "zip-frame-defs")
(include-book "zipper-defs")
(include-book "zip-seek-defs")

(local (include-book "std/util/defredundant" :dir :system))
(local (include-book "zip-delete-entry"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defredundant
  :names (zip-delete-entry))
