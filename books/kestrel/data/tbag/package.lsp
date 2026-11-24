; Copyright (C) 2026 by Kestrel Institute
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/data/portcullis" :dir :system)
(include-book "kestrel/data/tset/portcullis" :dir :system)
(include-book "std/portcullis" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defpkg "TBAG"
  (union-eq '(data::max-<<
              data::min-<<
              define-sk
              defmacro+
              defxdoc+
              enable*
              fast-nat-equiv
              lnfix
              nat-equiv
              tbag
              tset::acl2-number-hash
              tset::eqlable-hash
              tset::hash
              tset::heap<
              tset::heap<-rules
              tset::heap<-with-hashes
              tset::symbol-hash
              tset::heap<-trichotomy
              )
            (set-difference-eq *std-pkg-symbols*
                               #!STD
                               '(cardinality
                                 count
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
                                 values
                                 zip
                                 ))))
