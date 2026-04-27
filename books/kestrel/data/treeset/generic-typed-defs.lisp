; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREESET")

(include-book "set-defs")
(include-book "in-defs")
(include-book "min-max-defs")
(include-book "cardinality-defs")
(include-book "delete-defs")

(local (include-book "std/util/defredundant" :dir :system))
(local (include-book "generic-typed"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defredundant
  :names (genericp
          set-all-genericp
          set-all-genericp-sk-witness
          set-all-genericp-sk
          ))
