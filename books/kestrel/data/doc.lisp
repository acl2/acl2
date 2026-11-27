; Copyright (C) 2026 by Kestrel Institute
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "DATA")

(include-book "deque/top")
(include-book "hash/top")
(include-book "tset/doc")
(include-book "tmap/doc")
(include-book "tbag/doc")
(include-book "graph/doc")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc data-lib
  :parents (acl2::kestrel-books)
  :short
  (xdoc::topstring
    "A library for efficient data structures."))
