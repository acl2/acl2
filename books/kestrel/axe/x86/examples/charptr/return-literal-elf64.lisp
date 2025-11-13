; Test lifting functions that return string literals
;
; Copyright (C) 2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric McCarthy (mccarthy@kestrel.edu)
; Supporting Author: Eric Smith (eric.smith@kestrel.edu)

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


;; Verify the returned address points to "hello"
;; I used :print t to show the non-elided byte lists in the assumptions and
;; copied the key assumption here:
(thm
  (implies (equal (read-bytes '328 '4202496 x86)
                  '(1 0 2 0 104 101 108 108 111
                    0 116 101 115 116 0 0 1 27 3 59 52 0 0
                    0 5 0 0 0 16 240 255 255 80 0 0 0 64 240
                    255 255 124 0 0 0 246 240 255 255 144
                    0 0 0 1 241 255 255 176 0 0 0 25 241 255
                    255 208 0 0 0 0 0 0 0 20 0 0 0 0 0 0 0 1
                    122 82 0 1 120 16 1 27 12 7 8 144 1 7 16
                    16 0 0 0 28 0 0 0 184 239 255 255 34 0 0
                    0 0 0 0 0 20 0 0 0 0 0 0 0 1 122 82 0 1
                    120 16 1 27 12 7 8 144 1 0 0 16 0 0 0 28
                    0 0 0 188 239 255 255 1 0 0 0 0 0 0 0 28
                    0 0 0 48 0 0 0 94 240 255 255 11 0 0 0
                    0 65 14 16 134 2 67 13 6 70 12 7 8 0 0 0
                    28 0 0 0 80 0 0 0 73 240 255 255 24 0 0
                    0 0 65 14 16 134 2 67 13 6 83 12 7 8 0 0
                    0 28 0 0 0 112 0 0 0 65 240 255 255 11 0
                    0 0 0 65 14 16 134 2 67 13 6 70 12 7 8 0
                    0 0 0 0 0 0 0 0 0 0 4 0 0 0 16 0 0 0 5 0
                    0 0 71 78 85 0 2 128 0 192 4 0 0 0 1 0 0
                    0 0 0 0 0 4 0 0 0 16 0 0 0 1 0 0 0 71 78
                    85 0 0 0 0 0 3 0 0 0 2 0 0 0 0 0 0 0))
           (let ((addr (rax (get-literal x86))))
             (and (equal (read-byte addr x86) (char-code #\h))
                  (equal (read-byte (+ 1 addr) x86) (char-code #\e))
                  (equal (read-byte (+ 2 addr) x86) (char-code #\l))
                  (equal (read-byte (+ 3 addr) x86) (char-code #\l))
                  (equal (read-byte (+ 4 addr) x86) (char-code #\o))
                  (equal (read-byte (+ 5 addr) x86) 0) ; null terminator for "hello" string
                  )))
  :hints (("Goal" :in-theory (enable read-byte-becomes-read ; to match the normal forms that Axe uses
                                     ))))

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
