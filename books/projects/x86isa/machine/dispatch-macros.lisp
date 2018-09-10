; X86ISA Library

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/

; Copyright (C) 2018, Centaur Technology, Inc.
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
; Shilpi Goel         <shilpi@centtech.com>

(in-package "X86ISA")
(include-book "std/util/define" :dir :system)
(include-book "cpuid-constants")

(local (xdoc::set-default-parents 'opcode-maps))

;; Macros and functions used by utilities in dispatch.lisp to create opcode
;; dispatch functions

;; ----------------------------------------------------------------------

;; Exception-related definitions:

;; **************************************************
;; Variable bindings related to exceptions
;; --------------------------------------------------

;; VARIABLE                 TERM
;;
;; prefixes                 1st return value of get-prefixes; logically:
;;                          (mv-nth 1 (get-prefixes proc-mode start-rip 0 0 15 x86))
;;                          Fetched in x86-fetch-decode-execute for all opcodes

;; cplx86                   (cpl x86)

;; modr/m                   byte fetched in x86-fetch-decode-execute (for
;;                          one-byte opcodes),
;;                          two-byte-opcode-decode-and-execute (for two-byte
;;                          opcodes), three-byte-opcode-decode-and-execute (for
;;                          three-byte opcodes), vex-decode-and-execute (for
;;                          vex-encoded instructions), and
;;                          evex-decode-and-execute (for evex-encoded
;;                          instructions).

;; cr4                      (ctri #.*cr4* x86)
;; cr0                      (ctri #.*cr0* x86)

;; ia32_efer                (msri #.*ia32_efer-idx* x86)

;; cpuid-flag               CPUID information listed in Table 3-8, Intel Vol. 2.
;;
;;                          TODO:
;;
;;                          From Table 3-8: "Note that CPUID leaves above 2 and
;;                          below 80000000H are visible only when
;;                          IA32_MISC_ENABLE[bit 22] has its default value of 0."
;;
;;                          Is the above relevant for detecting feature support
;;                          for instructions too (as opposed to just during the
;;                          execution of the CPUID instruction)?


;; **************************************************

(defmacro ud-Lock-used ()
  `(eql #.*lock* (prefixes->lck prefixes)))

(defmacro ud-Opr-used ()
  `(eql #.*operand-size-override* (prefixes->opr prefixes)))

(defmacro ud-Reps-used ()
  `(or (eql #.*repe* (prefixes->rep prefixes))
       (eql #.*repne* (prefixes->rep prefixes))))

(defmacro ud-ModR/M.Mod-indicates-Register ()
  `(eql (modr/m->mod modr/m) #b11))

(defmacro ud-Lock-used-mod-indicates-register ()
  ;; For now, we check this only for instructions that require a modr/m byte.
  ;; There are some instructions that do not take a modr/m byte but that throw
  ;; a #UD when lock occurs and the destination is a register operand (e.g.,
  ;; ADC opcodes 0x14 and 0x15).  For those cases, use (ud-Lock-used) instead.
  `(and
    ;; ModR/M.mod = #b11 means that the modr/m byte points to a register, and
    ;; not to a memory operand.  See Table 2-2 (32-bit Addressing Forms with
    ;; the ModR/M byte) in Intel Vol. 2.
    (ud-ModR/M.Mod-indicates-Register)
    (eql #.*lock* (prefixes->lck prefixes))))

(defmacro ud-Lock-used-Dest-not-Memory-Op ()
  `(ud-Lock-used-mod-indicates-register))

(defmacro ud-source-operand-is-a-register ()
  `(ud-ModR/M.Mod-indicates-Register))

(defmacro ud-second-operand-is-a-register ()
  `(ud-ModR/M.Mod-indicates-Register))

(defmacro ud-cpl-is-not-zero ()
  `(not (eql (cplx86) 0)))

(defmacro ud-simd-specification (feature-flag &key (cr4-osfxsr? 't))
  (declare (xargs :guard (and (member-equal feature-flag *fp-simd-feature-flags*)
			      (booleanp cr4-osfxsr?))))

  ;; *** UD checks for conditions that can be detected at decode time ***

  ;; This macro is applicable to non-AVX instructions in only
  ;; protected/compatibility and 64-bit modes.

  ;; Note that we don't check for "If an unmasked SIMD floating-point exception
  ;; and CR4.OSXMMEXCPT[bit 10] = 0."  here (which shows up in Types 2 and 3,
  ;; Intel Vol. 2, and in Tables 22-4, 22-5, and 22-6 Intel Vol. 3) --- this is
  ;; because this condition can't be checked at decode time and must be
  ;; detected in the instruction's semantic function.

  ;; --------------------------------------------------

  ;; This definition for UD is applicable to the following with the cr4-osfxsr?
  ;; value set to T:

  ;; Source: Intel Manuals (May 2018 Edition)
  ;; Section 2.4 (AVX and SSE Exception Specification), Chapter 2, Intel Vol. 2
  ;; Section 22.25.3 (Exception Conditions of Legacy SIMD Instructions
  ;; Operating on MMX Registers), Chapter 22, Intel Vol. 3

  ;; Exceptions Type 1 (Section 2.4.1, Intel Vol. 2)

  ;; Exceptions Type 2 (Section 2.4.2, Intel Vol. 2)

  ;; Exceptions Type 3 (Section 2.4.3, Intel Vol. 2)

  ;; Exceptions Type 4 (Section 2.4.4, Intel Vol. 2)

  ;; Exceptions Type 5 (Section 2.4.5, Intel Vol. 2)

  ;; Exceptions Type 7 (Section 2.4.7, Intel Vol. 2)

  ;; Exception Conditions of Legacy SIMD/MMX Instructions with FP Exception and
  ;; 16-Byte Alignment (Table 22-4, Intel Vol. 3)

  ;; Exception Conditions for Legacy SIMD/MMX Instructions with XMM and FP
  ;; Exception (Table 22-5, Intel Vol. 3)

  ;; Exception Conditions for Legacy SIMD/MMX Instructions with XMM and without
  ;; FP Exception (Table 22-6, Intel Vol. 3)

  ;; --------------------------------------------------

  ;; This definition for UD is applicable to the following with the cr4-osfxsr?
  ;; value set to NIL:

  ;; Exception Conditions for SIMD/MMX Instructions with Memory Reference
  ;; (Table 22-7, Intel Vol. 3)

  ;; Exception Conditions for Legacy SIMD/MMX Instructions without FP Exception
  ;; (Table 22-8, Intel Vol. 3) --- for MASKMOVQ, this requires ModR/M.mod !=
  ;; #b11, which we check separately.

  ;; Exception Conditions for Legacy SIMD/MMX Instructions without Memory
  ;; Reference (Table 22-9, Intel Vol. 3)

  ;; --------------------------------------------------

  `(or (equal (cr0-slice :cr0-em (cr0)) 1)
       ,@(if cr4-osfxsr?
	     `((equal (cr4-slice :cr4-osfxsr (cr4)) 0))
	   nil)
       (ud-lock-used)
       ;; If a corresponding CPUID feature flag is 0.
       ;; Source: Intel Vol. 2 (May 2018 edition)
       ;; Figure 3-7 (Feature Information Returned in the ECX register)
       ;; Table 3-10 (Feature Information Returned in the ECX register)
       ;; Figure 3-8 (Feature Information Returned in the EDX register)
       ;; Table 3-11 (More on Feature Information Returned in the EDX register)
       (equal (feature-flag ,feature-flag) 0)))

(defmacro ud-exc-type-1 (feature-flag)
  `(ud-simd-specification ,feature-flag :cr4-osfxsr? t))

(defmacro ud-exc-type-2 (feature-flag)
  `(ud-simd-specification ,feature-flag :cr4-osfxsr? t))

(defmacro ud-exc-type-3 (feature-flag)
  `(ud-simd-specification ,feature-flag :cr4-osfxsr? t))

(defmacro ud-exc-type-4 (feature-flag)
  `(ud-simd-specification ,feature-flag :cr4-osfxsr? t))

(defmacro ud-exc-type-5 (feature-flag)
  `(ud-simd-specification ,feature-flag :cr4-osfxsr? t))

(defmacro ud-exc-type-7 (feature-flag)
  `(ud-simd-specification ,feature-flag :cr4-osfxsr? t))

(defmacro ud-exc-22-4 (feature-flag)
  `(ud-simd-specification ,feature-flag :cr4-osfxsr? t))

(defmacro ud-exc-22-5 (feature-flag)
  `(ud-simd-specification ,feature-flag :cr4-osfxsr? t))

(defmacro ud-exc-22-6 (feature-flag)
  `(ud-simd-specification ,feature-flag :cr4-osfxsr? t))

(defmacro ud-exc-22-7 (feature-flag)
  `(ud-simd-specification ,feature-flag :cr4-osfxsr? nil))

(defmacro ud-exc-22-8 (feature-flag)
  `(ud-simd-specification ,feature-flag :cr4-osfxsr? nil))

(defmacro ud-exc-22-9 (feature-flag)
  `(ud-simd-specification ,feature-flag :cr4-osfxsr? nil))


(defmacro nm-cr0-ts-is-1 ()
  `(eql (cr0-slice :cr0-ts (cr0)) 1))

(defmacro nm-cr0-em-is-1 ()
  `(eql (cr0-slice :cr0-em (cr0)) 1))

(defmacro gp-cpl-not-0 ()
  `(not (eql (cplx86) 0)))

(defmacro gp-cr4-pce-is-0 ()
  `(eql (cr4-slice :cr4-pce (cr4)) 0))

(defmacro gp-cr4-umip-is-1 ()
  `(eql (cr4-slice :cr4-umip (cr4)) 0))

(defmacro gp-cr0-pe-is-0 ()
  `(eql (cr0-slice :cr0-pe (cr0)) 0))


;; Some x86isa-specific macros:

(defmacro cplx86 ()
  `(cpl x86))

(defmacro cr0 ()
  `(the (unsigned-byte 32)
     (loghead 32 (ctri #.*cr0* x86))))

(defmacro cr4 ()
  `(the (unsigned-byte 22)
     (loghead 22 (ctri #.*cr4* x86))))

(defmacro ia32_efer ()
  `(msri #.*ia32_efer-idx* x86))

;; ----------------------------------------------------------------------
