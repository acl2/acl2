; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "TMAP")

(include-book "std/util/defrule" :dir :system)

(include-book "../cursor-defs")
(include-book "../begin-end-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil :type-prescription :none))

(local (include-book "../entry"))
(local (include-book "../begin-end"))
(local (include-book "before-after"))

(local (include-book "zip-step-side"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This book relates beginp and endp to the zipper's tests, for use in the
;; proofs of the other cursor books. All rules are disabled.

(defruled beginp-becomes-zip-at-begin-p
  (equal (beginp cursor)
         (zip-at-begin-p (cursor-fix cursor)))
  :enable (beginp
           entryp
           emptyp-of-before-becomes-not-consp
           zip-at-begin-p-becomes-not-consp-of-zip-before))

(defruled endp-becomes-zip-at-end-p
  (equal (endp cursor)
         (zip-at-end-p (cursor-fix cursor)))
  :enable (endp
           entryp
           emptyp-of-after-becomes-not-consp
           zip-at-end-p-becomes-not-consp-of-zip-after))
