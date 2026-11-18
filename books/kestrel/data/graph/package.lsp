; Copyright (C) 2026 by Kestrel Institute
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/data/portcullis" :dir :system)
(include-book "std/portcullis" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defpkg "GRAPH"
  (union-eq '(define-sk
              defmacro+
              defxdoc+
              enable*
              graph
              lnfix
              )
            (set-difference-eq *std-pkg-symbols*
                               #!STD
                               '(cardinality
                                 delete
                                 difference
                                 emptyp
                                 fix
                                 in
                                 insert
                                 intersect
                                 labels
                                 step
                                 union
                                 ))))
