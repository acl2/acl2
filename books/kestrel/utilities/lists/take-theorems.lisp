; List Utilities -- Theorems about TAKE
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "xdoc/constructors" :dir :system)
(include-book "std/lists/rcons" :dir :system)
(include-book "std/util/defrule" :dir :system)

(local (include-book "std/lists/repeat" :dir :system))
(local (include-book "std/lists/take" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection take-theorems
  :parents (list-utilities take)
  :short "Some theorems about the built-in function @(tsee take)."
  :long
  (xdoc::topstring-p
   "The theorem @('take-of-1+-to-rcons') is disabled by default.
    It may be useful when reasoning about @(tsee take) and @(tsee rcons).")

  (defruled take-of-1+-to-rcons
    (implies (natp n)
             (equal (take (1+ n) x)
                    (rcons (nth n x) (take n x))))
    :enable (rcons repeat)))
