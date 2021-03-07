; A lightweight book about the various numeric types
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Simple rules about arithmetic types.  Since these could be expensive, we
;; keep them disabled.

(defthmd integerp-when-natp
  (implies (natp x)
           (integerp x)))

(defthmd rationalp-when-integerp
  (implies (integerp x)
           (rationalp x)))

(defthmd acl2-numberp-when-rationalp
  (implies (rationalp x)
           (acl2-numberp x)))
