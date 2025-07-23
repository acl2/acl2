; A simple test of the unrolling lifter
;
; Copyright (C) 2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Simple test of the unrolling lifter (in this file we return the full new
;; state as the result of lifting).

;; May not be strictly needed for this example but will be in general:
;; cert_param: (uses-stp)

(include-book "kestrel/axe/x86/unroll-x86-code" :dir :system)
(include-book "std/testing/must-be-redundant" :dir :system)

;; (depends-on "add.elf64")
;; Lift the add function into logic by unrolling:
(def-unrolled add "add.elf64" :target "add")

;;expected result:
(must-be-redundant
  (defun add (x86)
    (declare (xargs :non-executable t :mode :logic))
    (declare (xargs :stobjs x86 :verify-guards nil))
    (prog2$ (acl2::throw-nonexec-error 'add
                                       (list x86))
            (set-rip (logext 64 (read 8 (rsp x86) x86))
                     (set-rax (bvplus 32 (rsi x86) (rdi x86))
                              (set-rdx (bvchop 32 (rdi x86))
                                       (set-rsp (+ 8 (rsp x86))
                                                (write 4 (bvplus 48 281474976710640 (rsp x86))
                                                       (rsi x86)
                                                       (write 4 (bvplus 48 281474976710644 (rsp x86))
                                                              (rdi x86)
                                                              (write 8 (bvplus 48 281474976710648 (rsp x86))
                                                                     (rbp x86)
                                                                     (set-flag :af
                                                                               (add-af-spec32 (bvchop 32 (rsi x86))
                                                                                              (bvchop 32 (rdi x86)))
                                                                               (set-flag :cf
                                                                                         (cf-spec32 (+ (bvchop 32 (rsi x86))
                                                                                                       (bvchop 32 (rdi x86))))
                                                                                         (set-flag :of
                                                                                                   (of-spec32 (+ (logext 32 (rsi x86))
                                                                                                                 (logext 32 (rdi x86))))
                                                                                                   (set-flag :pf
                                                                                                             (pf-spec32 (bvplus 32 (rsi x86) (rdi x86)))
                                                                                                             (set-flag :sf
                                                                                                                       (sf-spec32 (bvplus 32 (rsi x86) (rdi x86)))
                                                                                                                       (set-flag :zf
                                                                                                                                 (zf-spec (bvplus 32 (rsi x86) (rdi x86)))
                                                                                                                                 x86))))))))))))))))
