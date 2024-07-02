; Ordered Bags (Obags) Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/portcullis" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defpkg "OBAG" (set-difference-eq
                (append *std-pkg-symbols*
                        '(defxdoc+
                          fast-<<))
                '(set::cardinality
                  set::delete
                  set::difference
                  set::emptyp
                  set::head
                  set::in
                  set::insert
                  set::intersect
                  set::tail
                  set::union)))
