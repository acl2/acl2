; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "DATA")

(include-book "total-order/total-order-defs")

(local (include-book "std/util/defredundant" :dir :system))
(local (include-book "std/osets/top" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defredundant
  :names #!SET(setp
               emptyp
               sfix
               head
               tail
               cardinality
               insert
               in
               delete
               fast-difference
               difference
               fast-union
               union
               fast-subset
               subset
               fast-intersect
               intersect
               halve-list-aux
               halve-list
               mergesort-exec
               mergesort
               ))
