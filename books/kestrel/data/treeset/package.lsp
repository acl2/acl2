; Copyright (C) 2025-2026 by Kestrel Institute
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/data/portcullis" :dir :system)
(include-book "std/portcullis" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defpkg "TREESET"
  (union-eq '(define-sk
              defmacro+
              defxdoc+
              data::min-<<
              data::max-<<
              enable*
              )
            (set-difference-eq *std-pkg-symbols*
                               #!STD
                               '(cardinality
                                 delete
                                 difference
                                 double-containment
                                 emptyp
                                 fix
                                 head
                                 tail
                                 in
                                 insert
                                 intersect
                                 max
                                 min
                                 pick-a-point-subset-strategy
                                 setp
                                 subset
                                 union
                                 union-eq
                                 union-eql
                                 value
                                 ))))
