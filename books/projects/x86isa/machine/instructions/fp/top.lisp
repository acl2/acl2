; X86ISA Library

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2015, Regents of the University of Texas
; All rights reserved.

; Redistribution and use in source and binary forms, with or without
; modification, are permitted provided that the following conditions are
; met:

; o Redistributions of source code must retain the above copyright
;   notice, this list of conditions and the following disclaimer.

; o Redistributions in binary form must reproduce the above copyright
;   notice, this list of conditions and the following disclaimer in the
;   documentation and/or other materials provided with the distribution.

; o Neither the name of the copyright holders nor the names of its
;   contributors may be used to endorse or promote products derived
;   from this software without specific prior written permission.

; THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
; "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
; LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
; A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
; HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
; SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
; LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
; DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
; THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
; (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
; OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

; Original Author(s):
; Cuong Chau          <ckcuong@cs.utexas.edu>

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
