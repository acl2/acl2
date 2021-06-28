; X86ISA Library

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2018, Shilpi Goel
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
; Shilpi Goel         <shigoel@gmail.com>

(in-package "X86ISA")
(include-book "../utils/structures")
(include-book "cpuid-constants")
(include-book "cpuid")

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

(defmacro ud-not-in-prot-or-64-mode ()
  `(not (or (eql proc-mode #.*64-bit-mode*)
	    (eql proc-mode #.*protected-mode*))))

(defmacro ud-not-in-vmx-operation ()
  ;; BOZO Rob -- this is not modeled yet in x86 model, so return nil..
  `nil)

(defmacro ud-invept-not-supported ()
  ;; BOZO Rob -- we do not support this yet either in x86 model:
  ;;   (IA32_VMX_PROCBASED_CTLS2[33]=1) but does not support the INVEPT instruction (IA32_VMX_EPT_VPID_CAP[20]=0)
  `nil)

(defmacro ud-invvpid-not-supported ()
  ;; BOZO Rob -- and similary, x86 doesn't support this yet:
  ;;   (IA32_VMX_PROCBASED_CTLS2[37]=1) but does not support the INVVPID instruction (IA32_VMX_EPT_VPID_CAP[32]=0)
  `nil)

(defmacro ud-invpcid-not-supported ()
  `(= (cpuid-flag #ux_07 :reg #.*ebx* :bit 10) 0))

(defmacro ud-repne-f2-V86-cpuid-case ()
  ;; BOZO Rob -- we don't really have V86 mode supported yet in x86, so return nil here:
  `nil)

(defmacro ud-rep-f3-used ()
  `(eql #.*repe* (prefixes->rep prefixes)))

(defmacro nm-cr0-ts-is-1 ()
  `(eql (cr0Bits->ts (cr0)) 1))

(defmacro nm-cr0-em-is-1 ()
  `(eql (cr0Bits->em (cr0)) 1))

(defmacro nm-exc-all-types ()
  ;; for all vex/evex exception types, we have a requirement on cr0.ts bit:
  `(nm-cr0-ts-is-1))

(defmacro gp-cpl-not-0 ()
  `(not (eql (cplx86) 0)))

(defmacro gp-cr4-pce-is-0 ()
  `(eql (cr4Bits->pce (cr4)) 0))

(defmacro gp-cr4-umip-is-1 ()
  `(eql (cr4Bits->umip (cr4)) 0))

(defmacro gp-cr0-pe-is-0 ()
  `(eql (cr0Bits->pe (cr0)) 0))

;; ----------------------------------------------------------------------

;; These macros are the access points to the specific registers in the x86 model:

(defmacro cplx86 ()
  `(ifix (cpl x86)))

(defmacro cs.d ()
  `(b* (((the (unsigned-byte 16) cs-attr)
	 (seg-hidden-attri #.*cs* x86)))
     (code-segment-descriptor-attributesBits->d cs-attr)))

(defmacro cr0 ()
  `(the (unsigned-byte 32)
     (loghead 32 (ifix (ctri #.*cr0* x86)))))

(defmacro cr4 ()
  `(the (unsigned-byte 22)
     (loghead 22 (ifix (ctri #.*cr4* x86)))))

(defmacro ia32_efer ()
  `(msri #.*ia32_efer-idx* x86))

(defmacro feature-flag-macro (x)
  `(feature-flag ,x x86))

(defmacro feature-flags-macro (x)
  `(feature-flags ,x x86))

;; ----------------------------------------------------------------------

(defmacro chk-exc (type-id feature-flags)
  `(chk-exc-fn :legacy ,type-id ',feature-flags
	       ;; captured inputs:
	       proc-mode prefixes rex-byte opcode modr/m sib x86))

(defmacro chk-exc-vex (type-id feature-flags)
  `(chk-exc-fn :vex ,type-id ',feature-flags
	       ;; captured inputs:
	       proc-mode prefixes rex-byte opcode modr/m sib x86))

(defmacro chk-exc-evex (type-id feature-flags)
  `(chk-exc-fn :evex ,type-id ',feature-flags
	       ;; captured inputs:
	       proc-mode prefixes rex-byte opcode modr/m sib x86))

;;;;;;

(local (include-book "arithmetic-5/top" :dir :system))

(define chk-exc-fn ((decode-context symbolp)
		    (type-id        symbolp)
		    (feature-flags  symbol-listp)
		    ;; these parameters are captured from the expected
		    ;; environment in which chk-exc calls should expand:
		    (proc-mode     :type (integer 0 #.*num-proc-modes-1*))
		    (prefixes      :type (unsigned-byte #.*prefixes-width*))
		    (rex-byte      :type (unsigned-byte 8))
		    (opcode        :type (unsigned-byte 8))
		    (modr/m        :type (unsigned-byte 8))
		    (sib           :type (unsigned-byte 8))
		    x86)

  :guard (and (member-eq decode-context '(:legacy :vex :evex))
	      (subset-equal feature-flags *supported-feature-flags*))
  :guard-hints (("Goal" :in-theory (e/d () (x86$ap xr ifix))))
  (declare (ignore opcode modr/m sib)) ;; don't use these yet, but include them anyways..

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

  (cond
;   (t nil) ;; BOZO Rob -- I want to enable the rest of this definition, but the
   ;; guard proof is excruciatingly (although it does go through) and I need to
   ;; figure out how to get it to go through quicker..
   ((and (eq decode-context :vex)
	 (or (ud-Reps-used)
	     (ud-Opr-used)
	     (not (eql rex-byte 0))
	     (not (or (eql proc-mode #.*64-bit-mode*)
		      (eql proc-mode #.*compatibility-mode*)
		      (eql proc-mode #.*protected-mode*)))))
    :ud)
   ((eq type-id :type-vex-gpr)
    ;; from table 2.5.1 from volume 2.. we only need to additionally check
    ;; the cpuid requirements:
    (cond ((equal (feature-flags feature-flags x86) 0) :ud)))
   ((equal (cr0Bits->ts (cr0)) 1)
    :nm)
   ((and (not (member-eq type-id '(:type-22-7 :type-22-8 :type-22-9)))
	 (equal (cr4Bits->osfxsr (cr4)) 0))
    :ud)
   ;; BOZO -- Rob -- still need to add more here :(
   ((or (equal (cr0Bits->em (cr0)) 1)
	(ud-lock-used)
	;; If a corresponding CPUID feature flag is 0.
	;; Source: Intel Vol. 2 (May 2018 edition)
	;; Figure 3-7 (Feature Information Returned in the ECX register)
	;; Table 3-10 (Feature Information Returned in the ECX register)
	;; Figure 3-8 (Feature Information Returned in the EDX register)
	;; Table 3-11 (More on Feature Information Returned in the EDX register)
	(equal (feature-flags feature-flags x86) 0))
    :ud)))

;; ----------------------------------------------------------------------
