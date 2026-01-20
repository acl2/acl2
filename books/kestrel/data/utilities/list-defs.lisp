; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "DATA")

(local (include-book "std/util/defredundant" :dir :system))
(local (include-book "std/lists/list-defuns" :dir :system))

(local (include-book "list"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defredundant
  :names (acl2::list-fix
          list-fix
          acl2::fast-list-equiv
          list-equiv
          list-equal
          set-equiv
          ))

(defequiv list-equiv
  :package :equiv)

(defequiv set-equiv
  :package :equiv)
