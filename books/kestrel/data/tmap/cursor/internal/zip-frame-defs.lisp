; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TMAP")

(include-book "../../internal/tree-defs")

(local (include-book "std/util/defredundant" :dir :system))
(local (include-book "zip-frame"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defredundant
  :names (zip-frame-p
          irr-zip-frame
          zip-frame-fix
          zip-frame-equiv
          zip-frame->from-left
          zip-frame->elem
          zip-frame->sibling
          zip-frame
          zip-frame-listp
          zip-frame-list-fix
          zip-path-no-left-frames-p
          zip-path-no-right-frames-p))

(defequiv zip-frame-equiv)
