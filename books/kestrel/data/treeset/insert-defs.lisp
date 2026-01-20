; Copyright (C) 2025-2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TREESET")

(include-book "kestrel/data/utilities/oset-defs" :dir :system)

(include-book "internal/insert-defs")
(include-book "set-defs")

(local (include-book "std/util/defredundant" :dir :system))
(local (include-book "insert"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defredundant
  :names (insert-macro-loop
          insert-macro-fn
          insert$inline
          insert
          singleton-with-hash
          singleton
          insert-all
          from-list
          from-oset
          insert-=
          insert-eq
          insert-eql
          ))

;; (add-macro-alias insert1 insert1$inline)
;; (add-macro-fn insert insert1$inline)
;; (add-macro-alias from-list from-list$inline)
