; Theorems about Osets
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "SET")

(include-book "std/osets/top" :dir :system)
(include-book "std/util/defrule" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection theorems-about-osets

  :parents (acl2::theorems-about-non-kestrel-books)

  :short "Theorems about <see topic='@(url std/osets)'>finite sets</see>."

  (std::defrule cardinality-of-tail
    (equal (cardinality (tail x))
           (if (empty x)
               0
             (1- (cardinality x))))
    :enable cardinality)

  (std::defrule subset-of-tail-left
    (implies (subset x y)
             (subset (tail x) y))
    :enable subset))
