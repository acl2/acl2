; List Utilities -- Theorems about INDEX-OF
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/lists/index-of" :dir :system)
(include-book "std/util/defrule" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection index-of-theorems
  :parents (list-utilities index-of)
  :short "Some theorems about the library function @(tsee index-of)."

  (defrule index-of-nth-when-no-duplicatesp
    (implies (and (integer-range-p 0 (len x) i)
                  (no-duplicatesp-equal x))
             (equal (index-of (nth i x) x)
                    i))
    :enable index-of
    :prep-books ((include-book "std/lists/nth" :dir :system))))
