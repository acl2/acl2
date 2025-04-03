; The BV (bit vector) library.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
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
(include-book "bitp")
(include-book "unsigned-byte-p")
(include-book "unsigned-byte-p2")
(include-book "unsigned-byte-p-forced")

(include-book "signed-byte-p")

(include-book "bytep")

;; Underlying functions:
(include-book "lognot")
(include-book "logand")
(include-book "logand-b")
(include-book "logior")
(include-book "logior-b")
(include-book "logorc1")
(include-book "logeqv")
(include-book "logxor")
(include-book "logxor-b")
(include-book "logapp")
(include-book "logtail")
(include-book "logext")
(include-book "logops")

;; Functions to break down and create BVs:
(include-book "bvchop-def")
(include-book "bvchop")
(include-book "getbit-def")
(include-book "getbit")
(include-book "getbit-rules")
(include-book "getbit2")
(include-book "slice-def")
(include-book "slice")
(include-book "slice-rules")
(include-book "slice2")
(include-book "bvcat-def")
(include-book "bvcat")
(include-book "bvcat2")
(include-book "putbits")

(include-book "bvequal")

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
(include-book "bvplus-def")
(include-book "bvplus")
(include-book "bvminus")
(include-book "bvminus-rules")
(include-book "bvuminus")
(include-book "bvmult-def")
(include-book "bvmult")
(include-book "bvmult-rules")
(include-book "bvmod")
(include-book "bvdiv")
(include-book "bvdiv-rules")
(include-book "overflow-and-underflow")

;; Signed arithmetic operations:
(include-book "sbvdiv")
(include-book "sbvdiv-rules")
(include-book "sbvdivdown")
(include-book "sbvdivdown-rules")
(include-book "sbvrem")
(include-book "sbvrem-rules")
(include-book "sbvmoddown")

;; Sign extension and masks
(include-book "repeatbit")
(include-book "repeatbit2")
(include-book "bvsx-def")
(include-book "bvsx")

;; Comparison operations:
(include-book "bvequal")
(include-book "bvlt")
(include-book "sbvlt-def")
(include-book "sbvlt")

;; If-then-else:
(include-book "bvif")
(include-book "bvif2")

;; Rotate operations:
(include-book "leftrotate")
(include-book "leftrotate16")
(include-book "leftrotate32")
(include-book "leftrotate64")
(include-book "leftrotate-rules")
(include-book "rightrotate")
(include-book "rightrotate32")
(include-book "rightrotate-rules")
(include-book "rotate")

;; Shift operations:
(include-book "bvshl")
(include-book "bvshr")
(include-book "bvashr-def")
(include-book "bvashr")

;; Counting one bits:
(include-book "bvcount")

;; Trim (only for rewriting)
(include-book "trim")
(include-book "trim-intro-rules")
(include-book "trim-rules")
(include-book "convert-to-bv-rules")

; Operations specialized to particular sizes:
(include-book "ops32")
(include-book "ops64")

;; Rules about bitwise operations:
(include-book "bitwise")

;; Collections of definitions:
(include-book "defs-arith")
(include-book "defs-bitwise")
(include-book "defs")

;; Conversions between booleans and bits
(include-book "bool-to-bit-def")
(include-book "bool-to-bit")
(include-book "bit-to-bool-def")

;; Rules to replace BV ops with more common BV ops and sizes:
(include-book "idioms")

;; Proof of a ripple-carry adder:
(include-book "adder")

;; One's complement arithmetic:
(include-book "ones-complement")

;; Rules about BV operations of size 1:
(include-book "single-bit")

;; "Pick a bit" proof support:
(include-book "pick-a-bit")

;; Mixed rules:
(include-book "unsigned-byte-p-forced-rules")
(include-book "bvcat-rules")
(include-book "bvsx-rules")
(include-book "rules0")
(include-book "rules")
(include-book "rules2")
(include-book "rules3")
(include-book "rules4")
(include-book "rules5")
(include-book "rules6")
(include-book "rules7")
(include-book "rules8")
(include-book "rules9")
(include-book "rules10")
(include-book "rules11")
(include-book "rules12")
(include-book "if-becomes-bvif-rules")

(include-book "intro")
;; (include-book "bitops") ; excluding this since it brings in bitops

(include-book "validation-stp")
(include-book "validation-smt-lib")

(include-book "rtl")

;; (include-book "tests") ; not including this one because it just contains tests

(include-book "doc")
