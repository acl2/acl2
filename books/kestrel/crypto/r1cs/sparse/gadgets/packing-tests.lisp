; Tests of the R1CS gadget for bit packing/unpacking
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "R1CS")

(include-book "packing")
(include-book "std/testing/assert-equal" :dir :system)

;; Example of packing 8 bits into a byte (b0 is the least significant bit):
;; Uses 7717 as the prime.
;; The constraint asserts that a = 1*b0+2*b1+4*b2+...+128*b7.
(acl2::assert-equal (make-packing-constraint 'a '(b0 b1 b2 b3 b4 b5 b6 b7) 7717)
                    '( ;; each bit is multiplied by the power of 2 coefficient that
                      ;; shifts it into its place:
                      (A (1 B0)
                         (2 B1)
                         (4 B2)
                         (8 B3)
                         (16 B4)
                         (32 B5)
                         (64 B6)
                         (128 B7))
                      (B (1 1))
                      (C (1 A))))
