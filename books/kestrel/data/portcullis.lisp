; Copyright (C) 2026 by Kestrel Institute
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "DATA")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The following constants must be defined in this portcullis in order to use
;; them with the sharp-dot reader.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Unsigned fixnums

;; This is the unsigned version of acl2::*fixnum-type*.
(defconst *u-fixnum-type*
  (list 'unsigned-byte *fixnum-bits*))

(defconst *u-fixnum-max*
  (- (expt 2 *fixnum-bits*) 1))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Unsigned 8-bit words

(defconst *u8-max*
  (- (expt 2 8) 1))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Unsigned 32-bit words

(defconst *u32-max*
  (- (expt 2 32) 1))
