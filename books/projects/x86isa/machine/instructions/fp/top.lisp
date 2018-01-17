;; AUTHOR:
;; Cuong Kim Chau <ckcuong@cs.utexas.edu>

(in-package "X86ISA")

;; ======================================================================

;; All the floating-point instructions implemented so far are 128-bit
;; Legacy SSE (or in some cases, SSE2) versions. Just to be very
;; clear, the following versions of the floating-point instructions
;; are unimplemented: MMX, AVX, and AVX2.

(include-book "bitscan"
              :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))
(include-book "arithmetic"
              :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))
(include-book "logical"
              :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))
(include-book "shuffle-and-unpack"
              :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))
(include-book "mxcsr"
              :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))
(include-book "simd-integer"
              :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))
(include-book "convert"
              :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))
(include-book "mov"
              :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))

;; Exception Types and Alignment Checking: A Quick Reference
;; (TO-DO: make this into a doc topic or a function later...)

;; Type 1 (Legacy SSE): #GP if not 16 byte aligned

;; Type 2 (Legacy SSE): #GP if not 16 byte aligned

;; Type 3:              #AC if alignment checking is enabled and an
;;                      unaligned memory reference of 8 Bytes or less is
;;                      made while the current privilege level is 3.

;; Type 4 (Legacy SSE): #GP if not 16 byte aligned (PCMPESTRI, PCMPESTRM,
;;                      PCMPISTRI, and PCMPISTRM instructions do not
;;                      cause #GP if the memory operand is not aligned to
;;                      16-Byte boundary)

;; Type 5:             #AC if alignment checking is enabled and an unaligned
;;                     memory reference is made while the current
;;                     privilege level is 3.

;; Type 6:            #AC for 4 or 8 byte memory references if alignment
;;                    checking is enabled and an unaligned memory
;;                    reference is made while the current privilege level
;;                    is 3.

;; Type 7:            No FP exceptions, no memory argument

;; Type 8:            No memory argument

;; Type 11:           No AC

;; Type 12:           No AC


;; ======================================================================
