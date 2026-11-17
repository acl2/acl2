; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TMAP")

(include-book "../../internal/tree-defs")
(include-book "zip-frame-defs")

(local (include-book "std/util/defredundant" :dir :system))
(local (include-book "zipper"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defredundant
  :names (zipp
          irr-zip
          zip-fix
          zip-equiv
          zip->focus
          zip->path
          zip
          zip-frame-plug
          zip-path-plug
          zip-plug
          zip-root))

(defequiv zip-equiv)
