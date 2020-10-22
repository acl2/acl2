; Standard System Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "check-and-call")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define flatten-conjuncts ((term pseudo-termp))
  :returns (conjuncts pseudo-term-listp :hyp :guard)
  :parents (std/system/term-transformations)
  :short "View a term as an @(tsee and) tree and return its leaves."
  (b* (((mv andp left right) (check-and-call term))
       ((when (not andp)) (list term))
       (left-conjuncts (flatten-conjuncts left))
       (right-conjuncts (flatten-conjuncts right)))
    (append left-conjuncts right-conjuncts)))
