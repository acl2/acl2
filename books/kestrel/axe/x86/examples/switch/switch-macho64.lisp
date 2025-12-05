; A proof of a simple x86 binary function with a switch statement
;
; Copyright (C) 2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric McCarthy (mccarthy@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; STATUS: INCOMPLETE (awaiting jump table support in Axe)

;; This example demonstrates lifting a switch statement that compiles to a jump
;; table.  The compiler generates a jump table for the switch statement, which
;; uses indirect jumps (jmpq *%rax).  This is currently not supported by the Axe
;; x86 lifter.  Once jump table support is implemented, this example should work.

;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)
(include-book "support")

; (depends-on "switch.macho64")

 ;; Lift the subroutine into logic:
(def-unrolled classify-value
    :executable "switch.macho64"
    :target "_classify_value"
    :extra-rules '(read-of-write-when-disjoint-regions48p-gen-smt
                   read-when-equal-of-read-bytes-and-subregion48p-smt
                   acl2::bv-array-read-chunk-little-when-multiple-4-8-smt
                   acl2::slice-trim-axe-all
                   acl2::bvplus-trim-arg2-axe-all
                   acl2::bvplus-trim-arg3-axe-all
                   acl2::slice-of-bvplus-of-bvcat-special
                   acl2::bv-array-read-trim-index-axe-all
                   acl2::bv-array-read-of-bvplus-of-constant-no-wrap-bv-smt
                   x86isa::x86-fetch-decode-execute-of-if)
    :remove-rules '(acl2::bv-array-read-chunk-little-unroll)
    :position-independent nil
    :inputs ((x u32))
    :output :rax
    :monitor '(;acl2::bv-array-read-shorten-when-in-first-half
;acl2::bv-array-read-of-bvplus-of-constant-no-wrap-bv-smt
;               bv-array-read-chunk-little-of-bvchop-trim-index
               ;bv-array-read-chunk-little-when-multiple
               )
    :stack-slots 10)

;; The above command created the function classify-value, which represents the
;; values returned by the C function classify_value, in terms of its input, x.

;; Shows that the program correctly implements the switch statement.
;; For inputs 0-3, it returns 100, 200, 300, 400 respectively.
;; For all other inputs, it returns -1 (0xFFFFFFFF in 32-bit representation).
(defthm classify-value-correct-case-0
  (equal (classify-value 0)
         100))

(defthm classify-value-correct-case-1
  (equal (classify-value 1)
         200))

(defthm classify-value-correct-case-2
  (equal (classify-value 2)
         300))

(defthm classify-value-correct-case-3
  (equal (classify-value 3)
         400))

(defthm classify-value-correct-default
  (implies (bvlt 32 3 x) ; (not (member-equal x '(0 1 2 3)))
           (equal (classify-value x)
                  (bvuminus 32 1))))
