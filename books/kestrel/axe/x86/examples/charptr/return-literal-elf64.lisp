; Test lifting functions that return string literals
;
; Copyright (C) 2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric McCarthy (mccarthy@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; STATUS: partial success
;; - get_literal: lifts to constant 4202500 (0x402004), theorem proved
;;   Attempts to verify that the returned address points to "hello" failed.
;; - get_literal_char: lifts successfully, returns 116 in RAX, theorem proved

;; This example tests lifting functions that work with string literals.
;; String literals are stored in the .rodata section and have fixed addresses.

;; See return-literal.c

;; return-literal.elf64 was produced on Linux by:
;;
;;   gcc -O0 -fno-omit-frame-pointer -o return-literal.elf64 return-literal.c
;;
;; with GCC 15.2.0 (in "--platform linux/amd64 gcc:latest" Docker container).
;; The -O0 flag disables optimization and -fno-omit-frame-pointer ensures
;; frame pointers are preserved for easier debugging.

;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroller" :dir :system)

; (depends-on "return-literal.elf64")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Lift get_literal which returns a pointer to "hello" string literal
(def-unrolled get-literal
  :executable "return-literal.elf64"
  :target "get_literal"
  :stack-slots 2)

;; Test that get_literal returns the expected constant address (0x402004)
(defthmd get-literal-returns-expected-address
  (equal (rax (get-literal x86)) 4202500) ; 0x402004 in hex
  :hints (("Goal" :in-theory (enable get-literal))))

;; TODO: Verify the returned address points to "hello"
;; How do we show that?
;; ATTEMPTED: Using read-byte to check memory at addr 4202500 contains 'h','e','l','l','o'
;; RESULT: Cannot prove - the lifting assumptions seem to elide .rodata section bytes (:ELIDED)
;; The assumption shows: (EQUAL (READ-BYTES '328 '4202496 X86) :ELIDED)
;; SOLUTION: Would need lifting to include actual .rodata bytes in assumptions,
;;           or a different approach to verify memory contents
;; Example of attempted theorem:
;;   (let ((addr (rax (get-literal x86))))
;;     (and (equal (read-byte addr x86) #x68)  ; 'h'
;;          (equal (read-byte (+ 1 addr) x86) #x65) ...))
;; NOTE: Use read-byte (defined in kestrel/x86/read-and-write.lisp) for memory access

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Lift get_literal_char which returns the first char of "test"
(def-unrolled get-literal-char
  :executable "return-literal.elf64"
  :target "get_literal_char"
  :stack-slots 2)

;; Test that get_literal_char returns 116 (ASCII 't') in RAX
;; The lifted function returns an x86 state, so we extract the RAX register value
(defthmd get-literal-char-returns-116
  (equal (rax (get-literal-char x86)) 116)
  :hints (("Goal" :in-theory (enable get-literal-char))))
