; The BV (bit vector) library.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Syntaxp support:
(include-book "bv-syntax")

;; Recognizers for BVs:
(include-book "unsigned-byte-p")
(include-book "unsigned-byte-p-forced")

;; Underlying functions:
(include-book "lognot")
(include-book "logand")
(include-book "logand2")
(include-book "logior")
(include-book "logior-b")
(include-book "logorc1")
(include-book "logeqv")
(include-book "logxor")
(include-book "logxor-b")
(include-book "logapp")
(include-book "logtail")
(include-book "logext")

;; Functions to break down and create BVs:
(include-book "bvchop-def")
(include-book "bvchop")
(include-book "getbit-def")
(include-book "getbit")
(include-book "slice-def")
(include-book "slice")
(include-book "slice2")
(include-book "bvcat-def")
(include-book "bvcat")
(include-book "bvcat2")
(include-book "putbits")

;; Bit-wise operations:
(include-book "bvnot")
(include-book "bvand")
(include-book "bvor")
(include-book "bvxor")
(include-book "defs-bitwise")

;; Single bit operations:
(include-book "bitxor")
(include-book "bitnot")
(include-book "bitand")
(include-book "bitor")

;; Arithmetic operations:
(include-book "bvplus")
(include-book "bvminus")
(include-book "bvuminus")
(include-book "bvmult")
(include-book "bvmod")
(include-book "bvdiv")

;; Signed arithmetic operations:
(include-book "sbvdiv")

;; Sign extension and masks
(include-book "repeatbit")
(include-book "bvsx-def")
(include-book "bvsx")

;; Comparison operations:
(include-book "bvlt")
(include-book "sbvlt")

;; If-then-else:
(include-book "bvif")

;; Rotate operations:
(include-book "leftrotate")
(include-book "rightrotate")

;; Shift operations:
(include-book "bvshl")
(include-book "bvshr")
(include-book "defs-shifts")

;; Trim (only for rewriting)
(include-book "trim")

; Operations specialized to particular sizes:
(include-book "ops32")
(include-book "ops64")

;; Rules about bitwise operations:
(include-book "bitwise")
