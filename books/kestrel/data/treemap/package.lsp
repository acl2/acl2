; Copyright (C) 2026 by Kestrel Institute
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/data/portcullis" :dir :system)
(include-book "kestrel/data/treeset/portcullis" :dir :system)
(include-book "std/portcullis" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defpkg "TREEMAP"
  (union-eq '(data::max-<<
              data::min-<<
              define-sk
              defmacro+
              defxdoc+
              enable*
              lnfix
              treeset::acl2-number-hash
              treeset::eqlable-hash
              treeset::hash
              treeset::heap<
              treeset::heap<-rules
              treeset::heap<-with-hashes
              treeset::symbol-hash
              )
            (set-difference-eq *std-pkg-symbols*
                               ;; TODO: prune some of these
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
