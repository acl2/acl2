; List Utilities -- Theorems about REV
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "xdoc/constructors" :dir :system)
(include-book "std/lists/rev" :dir :system)
(include-book "std/util/defrule" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection rev-theorems
  :parents (list-utilities rev)
  :short "Some theorems about the library function @(tsee rev)."
  :long
  (xdoc::topstring-p
   "The theorems @('car-of-rev-rewrite-car-of-last')
    and @('car-of-last-rewrite-car-of-rev')
    are disabled by default.
    They may be useful to turn @('(car (rev ...))') into @('(car (last ...))')
    or vice versa.
    A theory invariants prevents them from being both enabled
    (which would cause a loop in the rewriter).")

  (defruled car-of-rev-rewrite-car-of-last
    (equal (car (rev x))
           (car (last x)))
    :enable rev
    :disable last
    :prep-books ((include-book "std/lists/last" :dir :system)
                 (include-book "std/lists/append" :dir :system)))

  (defruled car-of-last-rewrite-car-of-rev
    (equal (car (last x))
           (car (rev x)))
    :in-theory '(car-of-rev-rewrite-car-of-last))

  (theory-invariant (incompatible (:rewrite car-of-rev-rewrite-car-of-last)
                                  (:rewrite car-of-last-rewrite-car-of-rev))))
