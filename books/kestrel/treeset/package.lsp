; Copyright (C) 2025 by Kestrel Institute
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/portcullis" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defpkg "TREESET"
  (set-difference-eq
    (union-eq '(defxdoc+
                defmacro+)
              *std-pkg-symbols*)
    (union-eq '(set-equiv)
              #!STD
              '(setp
                sfix
                emptyp
                head
                insert
                in
                subset
                delete
                union
                intersect
                difference
                cardinality
                pick-a-point-subset-strategy
                double-containment
                min
                max
                ))))
