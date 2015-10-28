;; AUTHOR:
;; Cuong Kim Chau <ckcuong@cs.utexas.edu>
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")

;; ======================================================================

(include-book "x86-fp-bitscan-instructions"
              :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))
(include-book "x86-fp-mov-instructions"
              :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))
(include-book "x86-fp-arithmetic-instructions"
              :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))
(include-book "x86-fp-logical-instructions"
              :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))
(include-book "x86-fp-shuffle-and-unpack-instructions"
              :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))
(include-book "x86-fp-convert-instructions"
              :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))
(include-book "x86-fp-mxcsr-instructions"
              :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))
(include-book "x86-fp-simd-integer-instructions"
              :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))

;; ======================================================================
