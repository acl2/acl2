; Test lifting the simplest possible char* function - no null check, just read byte
;
; Copyright (C) 2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric McCarthy (mccarthy@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; STATUS: SUCCESS - get_byte lifts and reads a byte from a pointer

;; This example tests lifting the simplest possible char* function.
;; No null check, no loops - just read a byte from a pointer.

;; simple-byte.elf64 was produced on Linux by:
;;
;;   gcc -O0 -fno-omit-frame-pointer -o simple-byte.elf64 simple-byte.c
;;
;; with GCC 15.2.0 (in "--platform linux/amd64 gcc:latest" Docker container).
;; The -O0 flag disables optimization and -fno-omit-frame-pointer ensures
;; frame pointers are preserved for easier debugging.

; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)

; (depends-on "simple-byte.elf64")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Try lifting get_byte - a very simple char* function
(def-unrolled get-byte
  :executable "simple-byte.elf64"
  :target "get_byte"
  :inputs ((str_ptr u64))
  :output :eax  ; the lower 32 bits of RAX
  :extra-assumptions '((canonical-address-p$inline str_ptr)
                       (equal (logext 64 str_ptr) str_ptr))
  :stack-slots 2)

;; The function reads 1 byte from STR_PTR,
;; then sign-extends it to 32 bits.

;; Simple theorem: the result is a 32-bit value
(defthm get-byte-returns-32-bit
  (unsigned-byte-p 32 (get-byte str_ptr x86))
  :hints (("Goal" :in-theory (enable get-byte))))
