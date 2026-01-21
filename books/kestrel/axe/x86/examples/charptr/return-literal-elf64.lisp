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

;; STATUS: COMPLETE
;; - get_literal: lifts to constant 4202500 (0x402004), theorems proved
;;   (both address and content verification)
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

;; Lift get_literal which returns a pointer to "hello" string literal.
(def-unrolled get-literal
  :executable "return-literal.elf64"
  :target "get_literal"
  :stack-slots 2)

;; Note that .rodata in this executable is at #x402000 (decimal 4202496),
;; and is 15 bytes long (000000000000000f):
;;   % readelf -S return-literal.elf64 | grep -A1 .rodata
;;     [11] .rodata           PROGBITS         0000000000402000  00002000
;;          000000000000000f  0000000000000000   A       0     0     4
;; Then note that "hello" is at offset 4:
;;   % readelf -p .rodata return-literal.elf64 | grep 'hello'
;;     [     4]  hello
;; See .rodata in hex dump form:
;;   % readelf -x .rodata return-literal.elf64
;;   Hex dump of section '.rodata':
;;     0x00402000 01000200 68656c6c 6f007465 737400   ....hello.test.

;; Test that get_literal returns the expected address in .rodata:
(defthmd get-literal-returns-expected-address
  (equal (rax (get-literal x86)) #x402004) ; decimal 4202500
  :hints (("Goal" :in-theory (enable get-literal))))

;; ----

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

;; ----
;; Axe does not seem to have a "loader" per se.

;; We can fake just the .rodata part this way:
(defun return-literal-.rodata-loaded-p (x86)
  (declare (xargs :stobjs x86))
  (equal (read-bytes 15 4202496 x86)  ; just .rodata section, from the hex dump above
         '(01 00 02 00
           #x68 #x65 #x6c #x6c
           #x6f 00   #x74 #x65
           #x73 #x74 0)))

;; This should be replaced by a more general rule:
(defthmd read-bytes-subrange-helper
  (implies (equal (read-bytes 15 4202496 x86)
                  '(1 0 2 0 104 101 108 108 111 0 116 101 115 116 0))
           (equal (read-bytes 6 4202500 x86)
                  '(104 101 108 108 111 0)))
  :hints (("Goal" :expand ((:free (n addr) (read-bytes n addr x86))))))

;; Verify the 6 bytes at the returned address are "hello\0",
;; assuming the .rodata has been loaded.
(defthmd get-literal-points-to-hello
    (implies (return-literal-.rodata-loaded-p x86)
             (equal (read-bytes 6 (rax (get-literal x86))
                                x86)
                    (list (char-code #\h)
                          (char-code #\e)
                          (char-code #\l)
                          (char-code #\l)
                          (char-code #\o)
                          0))) ; null
  :hints (("Goal" :in-theory (enable get-literal read-bytes-subrange-helper))))


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
