; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREEMAP")

(include-book "internal/keys-defs")
(include-book "map-defs")

(local (include-book "std/util/defredundant" :dir :system))
(local (include-book "keys"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defredundant
  :names (keys
          map-keys-acl2-numberp
          map-keys-symbolp
          map-keys-eqlablep
          acl2-number-mapp
          symbol-mapp
          eqlable-mapp
          ))
