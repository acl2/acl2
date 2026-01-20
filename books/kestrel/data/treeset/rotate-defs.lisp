; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREESET")

(include-book "std/util/defredundant" :dir :system)

(include-book "set-defs")
(include-book "cardinality-defs")
(include-book "in-defs")

(local (include-book "rotate"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defredundant
  :names (rotate-left
          rotate-right))

(add-macro-alias rotate-left rotate-left$inline)
(add-macro-alias rotate-right rotate-right$inline)
