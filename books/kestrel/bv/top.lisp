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

(include-book "arith") ;todo deprecate
(include-book "arith2") ;todo deprecate
(include-book "floor-mod-expt") ;todo deprecate

;; Recognizers for BVs:
(include-book "unsigned-byte-p")
(include-book "unsigned-byte-p2")
(include-book "unsigned-byte-p-forced")

(include-book "signed-byte-p")

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
(include-book "getbit2")
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

;; Single bit operations:
(include-book "bitxor")
(include-book "bitnot")
(include-book "bitand")
(include-book "bitor")
(include-book "bitxnor")

;; Arithmetic operations:
(include-book "bvplus")
(include-book "bvminus")
(include-book "bvuminus")
(include-book "bvmult")
(include-book "bvmod")
(include-book "bvdiv")
(include-book "overflow-and-underflow")

;; Signed arithmetic operations:
(include-book "sbvdiv")
(include-book "sbvrem")

;; Sign extension and masks
(include-book "repeatbit")
(include-book "repeatbit2")
(include-book "bvsx-def")
(include-book "bvsx")

;; Comparison operations:
(include-book "bvlt")
(include-book "sbvlt")

;; If-then-else:
(include-book "bvif")
(include-book "bvif2")

;; Rotate operations:
(include-book "leftrotate")
(include-book "rightrotate")
(include-book "rightrotate32")
(include-book "rotate")

;; Shift operations:
(include-book "bvshl")
(include-book "bvshr")
(include-book "bvashr")
(include-book "defs-shifts")

;; Trim (only for rewriting)
(include-book "trim")

; Operations specialized to particular sizes:
(include-book "ops32")
(include-book "ops64")

;; Rules about bitwise operations:
(include-book "bitwise")

;; Collections of definitions:
(include-book "defs-arith")
(include-book "defs-bitwise")
(include-book "defs")

(include-book "bool-to-bit")
(include-book "bit-to-bool")

(include-book "idioms")

(include-book "rules0")
(include-book "rules")
(include-book "rules2")
(include-book "rules3")
(include-book "rules4")
(include-book "rules5")
(include-book "rules6")
