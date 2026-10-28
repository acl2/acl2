; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "SET")

; This book introduces the definitions from top.lisp redundantly, without the
; theorems about them.

(include-book "misc/total-order-defs" :dir :system)

(local (include-book "std/util/defredundant" :dir :system))
(local (include-book "top"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::defredundant
  :names (setp
          emptyp
          sfix
          head
          tail
          insert
          in
          fast-subset
          subset
          fast-measure
          fast-union
          fast-intersect
          fast-intersectp
          fast-difference
          delete
          union
          intersect
          intersectp
          difference
          cardinality
          halve-list-aux
          halve-list
          mergesort-exec
          mergesort))
