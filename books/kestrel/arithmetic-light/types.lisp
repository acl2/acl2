; A lightweight book about the various numeric types
;
; Copyright (C) 2021-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Simple rules about arithmetic types.  Since these could be expensive, we
;; keep them disabled.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; These establish acl2-numberp:

(defthmd acl2-numberp-when-natp
  (implies (natp x)
           (acl2-numberp x)))

(defthmd acl2-numberp-when-integerp
  (implies (integerp x)
           (acl2-numberp x)))

;; Note that there is also a built-in theorem rationalp-implies-acl2-numberp.
(defthmd acl2-numberp-when-rationalp
  (implies (rationalp x)
           (acl2-numberp x)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; These establish rationalp:

(defthmd rationalp-when-natp
  (implies (natp x)
           (rationalp x)))

(defthmd rationalp-when-integerp
  (implies (integerp x)
           (rationalp x)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; These establish integerp:

(defthmd integerp-when-natp
  (implies (natp x)
           (integerp x)))

;; TODO: Uncomment, but that causes problems:
;; (theory-invariant (incompatible (:rewrite integerp-when-natp)
;;                                 (:definition natp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; These establish >= 0

(defthmd <=-of-0-when-natp
  (implies (natp x)
           (<= 0 x)))

;; TODO: Uncomment, but that causes problems:
;; (theory-invariant (incompatible (:rewrite <=-of-0-when-natp)
;;                                 (:definition natp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; for books we want to certify on acl2(r)
(defthmd real/rationalp-when-natp
  (implies (natp x)
           (real/rationalp x)))

;; for books we want to certify on acl2(r)
(defthmd real/rationalp-when-integerp
  (implies (integerp x)
           (real/rationalp x)))
