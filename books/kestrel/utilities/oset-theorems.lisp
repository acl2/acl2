; Theorems about Osets
;
; Copyright (C) 2016 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file provides some theorems about osets.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "SET")

(include-book "std/osets/top" :dir :system)
(include-book "std/util/defrule" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection theorems-about-osets

  :parents (theorems-about-non-kestrel-books)

  :short "Some theorems about
          <see topic='@(url std/osets)'>finite sets</see>."

  (std::defrule cardinality-of-tail
    :parents (theorems-about-osets)
    (equal (cardinality (tail x))
           (if (empty x)
               0
             (1- (cardinality x))))
    :enable cardinality))
