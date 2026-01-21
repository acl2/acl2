; Lifting tests for functions that work with char* pointers from different memory locations
;
; Copyright (C) 2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric McCarthy (mccarthy@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; STATUS: Partial success - functions with external pointers lift,
;;         functions with fixed addresses fail

;; This example tests lifting functions that work with char* pointers
;; from various memory locations (stack, heap, globals, literals).

;; charptr-locations.elf64 was produced on Linux by:
;;
;;   gcc -o charptr-locations.elf64 charptr-locations.c
;;
;; with GCC 15.2.0 (in "--platform linux/amd64 gcc:latest" Docker container).

; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)

; (depends-on "charptr-locations.elf64")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Start with the simplest: read_only_byte which takes a pointer parameter
;; This avoids the complexity of fixed memory addresses

(def-unrolled read-only-byte
  :executable "charptr-locations.elf64"
  :target "read_only_byte"
  :inputs ((str_ptr u64))
  :output :eax
  :extra-assumptions '((canonical-address-p$inline str_ptr)
                       (equal (logext 64 str_ptr) str_ptr))
  :stack-slots 2)

;; Simple theorem: reading from a NULL pointer returns -1
(defthm read-only-byte-null-returns-minus-one
  (equal (read-only-byte 0 x86)
         #xFFFFFFFF)  ; -1 in 32-bit unsigned
  :hints (("Goal" :in-theory (enable read-only-byte))))

;; Now try read_write_byte which is similar but non-const
;; NOTE: This version without stack assumptions fails with SET-MS errors

; (def-unrolled read-write-byte
;   :executable "charptr-locations.elf64"
;   :target "read_write_byte"
;   :inputs ((str_ptr u64))
;   :output :eax
;   :extra-assumptions '((canonical-address-p$inline str_ptr)
;                        (< str_ptr #x800000000000)  ; User space
;                        (equal (logext 64 str_ptr) str_ptr))
;   :stack-slots 2)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; LESSONS LEARNED:
;; 1. Functions that take external pointers need canonical address assumptions
;; 2. Some functions need additional stack pointer assumptions to avoid SET-MS errors
;;    - Specifically: (canonical-address-p$inline (bvplus 64 OFFSET (rsp x86)))
;;    - Where OFFSET is negative (e.g., -32, -16, -8) for stack locations
;; 3. Functions that use fixed addresses (like test_global, test_literal) currently fail
;;    with SET-MS/SET-FAULT errors

;; Successfully lifted functions:
;; - read-only-byte: Takes const char*, returns byte value or -1 for NULL

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; test_global reads from a global variable at a fixed address
;; (This one has SET-MS/SET-FAULT errors, needs investigation)

; (def-unrolled test-global
;   :executable "charptr-locations.elf64"
;   :target "test_global"
;   :stack-slots 2)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Then try a function with an external pointer parameter

; (def-unrolled read-only-byte
;   :executable "charptr-locations.elf64"
;   :target "read_only_byte"
;   :inputs ((str_ptr u64))
;   :output :eax
;   :extra-assumptions '((canonical-address-p$inline str_ptr)
;                        (< str_ptr #x800000000000)  ; User space
;                        (equal (logext 64 str_ptr) str_ptr))
;   :stack-slots 2)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; More complex: process_string with loop
;; This function reads up to 4 bytes from a string and sums them
;;
;; NOTE: This function has a loop that iterates up to 4 times, accessing
;; str_ptr[i] where i goes from 0 to 3. The lifting fails with SET-MS errors.
;; The error occurs with MOVZX instructions trying to access STR_PTR+2, STR_PTR+3.
;; Even though we have assumptions about these addresses, the symbolic execution
;; cannot resolve the loop-dependent memory accesses.

; (def-unrolled process-string
;   :executable "charptr-locations.elf64"
;   :target "process_string"
;   :inputs ((str_ptr u64))
;   :output :eax
;   :extra-assumptions '((canonical-address-p$inline str_ptr)
;                        (< str_ptr #x800000000000)
;                        (equal (logext 64 str_ptr) str_ptr)
;                        ;; Need at least 4 bytes readable
;                        (canonical-address-p$inline (bvplus 64 1 str_ptr))
;                        (canonical-address-p$inline (bvplus 64 2 str_ptr))
;                        (canonical-address-p$inline (bvplus 64 3 str_ptr))
;                        ;; Stack assumptions - need to cover all local variables
;                        (canonical-address-p$inline (bvplus 64 -32 (rsp x86)))
;                        (canonical-address-p$inline (bvplus 64 -25 (rsp x86))) ; RSP-25 from error
;                        (canonical-address-p$inline (bvplus 64 -24 (rsp x86)))
;                        (canonical-address-p$inline (bvplus 64 -16 (rsp x86)))
;                        (canonical-address-p$inline (bvplus 64 -8 (rsp x86)))
;                        (canonical-address-p$inline (bvplus 64 -4 (rsp x86))))
;   :stack-slots 4)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Try test_literal - passes a string literal to read_only_byte
;; FAILED: SET-MS error when calling read_only_byte with fixed address 0x40201d

; (def-unrolled test-literal
;   :executable "charptr-locations.elf64"
;   :target "test_literal"
;   :output :eax
;   :stack-slots 2)

;; Try test_stack - creates stack array and calls read_write_byte
;(def-unrolled test-stack
;  :executable "charptr-locations.elf64"
;  :target "test_stack"
;  :output :eax
;  :stack-slots 4)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Challenge: test_heap with malloc/free

; (def-unrolled test-heap
;   :executable "charptr-locations.elf64"
;   :target "test_heap"
;   :stack-slots 4)
;   ;; This will likely need special handling for malloc/free external calls
