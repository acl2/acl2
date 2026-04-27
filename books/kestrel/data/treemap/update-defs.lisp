; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREEMAP")

(include-book "kestrel/data/utilities/omap-defs" :dir :system)

(include-book "internal/update-defs")
(include-book "map-defs")
(include-book "keys-defs")

(local (include-book "std/util/defredundant" :dir :system))
(local (include-book "update"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defredundant
  :names (update-macro-loop
          update-macro-fn
          update$inline
          update
          singleton-with-hash
          singleton
          update-from-alist-rev
          update-from-alist
          from-alist
          update-from-omap
          from-omap
          map-macro-loop
          map-macro-fn
          update-=
          update-eq
          update-eql
          update-with-hash
          ))
