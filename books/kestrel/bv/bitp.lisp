; A lightweight book about the built-in function bitp
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Note that this BV library usually uses (unsigned-byte-p x 1) instead of (bitp x).

(in-theory (disable bitp))

;; Kept disabled for speed
(defthmd acl2-numberp-when-bitp
  (implies (bitp x)
           (acl2-numberp x)))

;; Kept disabled for speed
(defthmd rationalp-when-bitp
  (implies (bitp x)
           (rationalp x)))

;; Kept disabled for speed
(defthmd integerp-when-bitp
  (implies (bitp x)
           (integerp x)))

;; Kept disabled for speed
(defthmd natp-when-bitp
  (implies (bitp x)
           (natp x)))
