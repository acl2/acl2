; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TMAP")

(include-book "../map-defs")
(include-book "../update-defs")
(include-book "cursor-defs")
(include-book "entry-defs")
(include-book "from-cursor-defs")
(include-book "seek-defs")
(include-book "internal/zip-update-entry-defs")

(local (include-book "std/util/defredundant" :dir :system))
(local (include-book "update-entry"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defredundant
  :names (update-entry))
