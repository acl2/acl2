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

;;; These establish acl2-numberp:

(defthmd acl2-numberp-when-natp
  (implies (natp x)
           (acl2-numberp x)))

(defthmd acl2-numberp-when-integerp
  (implies (integerp x)
           (acl2-numberp x)))

(defthmd acl2-numberp-when-rationalp
  (implies (rationalp x)
           (acl2-numberp x)))

;;; These establish rationalp

(defthmd rationalp-when-natp
  (implies (natp x)
           (rationalp x)))

(defthmd rationalp-when-integerp
  (implies (integerp x)
           (rationalp x)))

;;; These establish integerp

(defthmd integerp-when-natp
  (implies (natp x)
           (integerp x)))

;;; These establish >=0

(defthmd <=-of-0-when-0-natp
  (implies (natp x)
           (<= 0 x)))
