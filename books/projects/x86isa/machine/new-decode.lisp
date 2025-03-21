; X86ISA Library

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2018, Regents of the University of Texas
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
; Shilpi Goel         <shigoel@cs.utexas.edu>

;; WIP: This book is not used anywhere yet, but it contains some
;; functions related to operand addressing that I plan to use in the
;; future.  My eventual goal is to move towards a more structured and
;; declarative style of instruction specification.

(in-package "X86ISA")
(include-book "decoding-and-spec-utils"
              :ttags (:syscall-exec :undef-flg))
(include-book "std/util/defenum" :dir :system)
(include-book "inst-structs")

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))

;; ----------------------------------------------------------------------

(defenum reg-type-p
  (#.*gpr-access* #.*xmm-access*)
  :parents (decoding-utilities)
  :short "Kind of register access (e.g., GPR or XMM)")

(define get-operand-size
  ((addressing-method-code addressing-method-code-p)
   (operand-type-code      operand-type-code-p)
   (rex-byte               :type (unsigned-byte  8))
   (prefixes               :type (unsigned-byte #.*prefixes-width*)))

  :guard (prefixes-p prefixes)

  :parents (decoding-and-spec-utils)

  ;; TODO: What about AVX512?  Do the Intel descriptions of
  ;; operand-type-code account for that?

  ;; TODO: Some branches in this function may not be accurate right
  ;; now.

  ;; Intel Manuals, Vol. 1, Section 3.6, Table 3-4
  ;; Intel Manuals, Vol. 2, Section 2.2.1.2

  :short "Determining the size of an instruction's operand"

  :returns (size natp
                 :hyp (and (addressing-method-code-p addressing-method-code)
                           (operand-type-code-p operand-type-code))
                 :rule-classes :type-prescription)

  (cond

   ((equal operand-type-code 'b)
    ;; Byte, regardless of operand-size attribute.
    1)

   ((equal operand-type-code 'w)
    ;; Word, regardless of operand-size attribute.
    2)

   ((equal operand-type-code 'd)
    ;; Doubleword, regardless of operand-size attribute.
    4)

   ((equal operand-type-code 'q)
    ;; Quadword, regardless of operand-size attribute.
    8)

   ((equal operand-type-code 'dq)
    ;; Double-quadword, regardless of operand-size attribute.
    16)

   ((equal operand-type-code 'qq)
    ;; Quad-Quadword (256-bits), regardless of operand-size attribute.
    32)

   ((equal operand-type-code 'pi)
    ;; Quadword MMX technology register (for example: mm0).
    8)

   ((equal operand-type-code 'sd)
    ;; Scalar element of a 128-bit double-precision floating data.
    8)

   ((equal operand-type-code 'si)
    ;; Doubleword integer register (for example: eax).
    4)

   ((equal operand-type-code 'ss)
    ;; Scalar element of a 128-bit single-precision floating data.
    4)

   (t

    (b* ((imm? (equal addressing-method-code 'I))
         (op-size-override?
          (eql #.*operand-size-override*
               (the (unsigned-byte 8) (prefixes->opr prefixes))))
         (rex.w (logbitp #.*w* rex-byte)))

      (cond

       ((equal operand-type-code 'v)
        ;; Word, doubleword or quadword (in 64-bit mode), depending on
        ;; operand-size attribute.
        (if rex.w
            (if imm?
                ;; Fetch 4 bytes (sign-extended to 64 bits) if operand is
                ;; immediate.
                4
              8)
          (if op-size-override?
              2 ;; 16-bit operand-size
            ;; Default 32-bit operand size (in 64-bit mode)
            4)))

       ((equal operand-type-code 'y)
        ;; Doubleword or quadword (in 64-bit mode), depending on
        ;; operand-size attribute.
        ;; Note: operand size override prefix is irrelevant here.
        (if rex.w 8 4))

       ((equal operand-type-code 'z)
        ;; Word for 16-bit operand-size or doubleword for 32 or 64-bit
        ;; operand-size.
        ;; Note: rex.w is irrelevant here.
        (if op-size-override?
            2 ;; 16-bit operand-size
          ;; Default 32-bit operand size (in 64-bit mode)
          4))

       ((equal operand-type-code 'p)
        ;; 32-bit, 48-bit, or 80-bit pointer, depending on
        ;; operand-size attribute.
        ;; Note: I cross-referenced description of
        ;; "LDS/LES/LFS/LGS/LSS-Load Far Pointer" for clarification.
        (if rex.w
            10 ;; 2 + 8 (16-bit selector; 64-bit offset)
          (if op-size-override?
              4 ;; 2 + 2 (16-bit selector; 16-bit offset)
            ;; Default 32-bit operand size (in 64-bit mode)
            6 ;; 2 + 4 (16-bit selector; 32-bit offset)
            )))

       ((equal operand-type-code 's)
        ;; 6-byte or 10-byte pseudo-descriptor.
        (if rex.w
            10
          6))

       ((equal operand-type-code 'pd)
        ;; 128-bit or 256-bit packed double-precision floating-point data.
        ;; TODO: I think this is wrong.  I probably need to account
        ;; for VEX/EVEX prefixes here, not REX.
        (if rex.w
            16
          32))

       ((equal operand-type-code 'ps)
        ;; 128-bit or 256-bit packed single-precision floating-point data.
        ;; TODO: I think this is wrong.  I probably need to account
        ;; for VEX/EVEX prefixes here, not REX.
        (if rex.w
            16
          32))

       ((equal operand-type-code 'x)
        ;; dq or qq based on the operand-size attribute.
        ;; TODO: I think this is wrong.  I probably need to account
        ;; for VEX/EVEX prefixes here, not REX.
        (if rex.w
            32 ;; qq
          16   ;; dq
          ))

       ((equal operand-type-code 'a)
        ;; Two one-word operands in memory or two double-word operands
        ;; in memory, depending on operand-size attribute (used only
        ;; by the BOUND instruction).
        ;; Note: The BOUND instruction is invalid in the 64-bit mode.
        (if op-size-override? 2 4))

       ((equal operand-type-code 'c)
        ;; Byte or word, depending on operand-size attribute.
        ;; Note: I don't see this operand-type-code being used
        ;; anywhere in the one- and two-byte opcode maps.
        (if op-size-override? 1 2))

       (t
        (er hard 'get-operand-size
            "This should've been reachable! ~
             Addressing Method Code: ~x0 Operand Type Code: ~x1 ~
             Rex Byte: ~x2 Prefixes: ~x3~%"
            addressing-method-code
            operand-type-code
            rex-byte
            prefixes)))))))

;; ----------------------------------------------------------------------
