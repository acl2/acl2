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
(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection theorems-about-osets
  :parents (acl2::theorems-about-non-kestrel-books)
  :short (xdoc::topstring
          "Theorems about "
          (xdoc::seetopic "std/osets" "finite sets")
          ".")
  :long
  (xdoc::topstring-p
   "Note that the theorem that rewrites @(tsee in) to @(tsee member-equal)
    is disabled by default.
    It can be locally enabled in certain proofs as needed.")

  (std::defrule cardinality-of-tail
    (equal (cardinality (tail x))
           (if (empty x)
               0
             (1- (cardinality x))))
    :enable cardinality)

  (std::defrule subset-of-tail-left
    (implies (subset x y)
             (subset (tail x) y))
    :enable subset)

  (std::defruled in-to-member-when-setp
    (implies (setp x)
             (iff (in a x)
                  (member-equal a x)))
    :enable (setp in empty head tail)))
