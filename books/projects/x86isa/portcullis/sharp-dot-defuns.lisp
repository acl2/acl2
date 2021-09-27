; X86ISA Library

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2020, Shilpi Goel
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
(include-book "utils")
(include-book "std/util/bstar" :dir :system)

;; ----------------------------------------------------------------------

;; Indices and length of fields in the x86 state (see
;; machine/concrete-state.lisp):

(defun define-general-purpose-registers ()

  ;; These indices are from Tables 2-1, 2-2, and 2-3 (addressing modes) of
  ;; Intel manual, May'18, Volume 2:
  `(defconsts (*RAX* *RCX* *RDX* *RBX* *RSP* *RBP* *RSI* *RDI*
                     *R8* *R9* *R10* *R11* *R12* *R13* *R14* *R15*
                     *64-bit-general-purpose-registers-len*)
     ,(b* ((lst (increasing-list 0 1 16))
           (len  (len lst)))
          (cons 'mv (append lst (list len))))))

(defun define-32-bit-general-purpose-registers ()

  ;; These are the same as *RAX* etc. above:
  `(defconsts (*EAX* *ECX* *EDX* *EBX* *ESP* *EBP* *ESI* *EDI*
                     *R8d* *R9d* *R10d* *R11d* *R12d* *R13d* *R14d* *R15d*)
     ,(b* ((lst (increasing-list 0 1 15))
           (len  (len lst)))
        (cons 'mv (append lst (list len))))))

(defun define-segment-registers ()

  ;; These indices are used in the Reg field of the ModR/M byte of the
  ;; instructions 'MOV ..., <seg-reg>', to represent <seg-reg> ('MOV ..., CS'
  ;; is disallowed, but the only index not used for the other segment registers
  ;; is 1:
  `(defconsts (*ES* *CS* *SS* *DS* *FS* *GS*
                    *segment-register-names-len*)
     ,(b* ((lst (increasing-list 0 1 6))
           (len  (len lst)))
        (cons 'mv (append lst (list len))))))

(defun define-gdtr/idtr-registers ()

  ;; Specific to the formal model:
  `(defconsts (*GDTR* *IDTR* *gdtr-idtr-names-len*)
     ,(b* ((lst (increasing-list 0 1 2))
           (len  (len lst)))
          (cons 'mv (append lst (list len))))))

(defun define-ldtr/tr-registers ()

  ;; Specific to the formal model:
  `(defconsts (*LDTR* *TR* *ldtr-tr-names-len*)
     ,(b* ((lst (increasing-list 0 1 2))
           (len  (len lst)))
          (cons 'mv (append lst (list len))))))

;; Source: Intel Manual, Feb-14, Vol. 3A, Section 2.5
(defun define-control-registers ()

  ;; These indices are used in the Reg field of the ModR/M byte of the
  ;; instructions MOV from/to control registers:
  `(defconsts (*CR0* ;; cr0 controls operating mode and states of
                     ;; processor
               *CR1* ;; cr1 is reserved
               *CR2* ;; cr2 holds the page fault linear address (the
                     ;; one that caused the page fault)
               *CR3* ;; cr3 is associated with paging
               *CR4* ;; cr4 enables or indicates support for processor
                     ;; extensions
               *CR5* ;; cr5 is reserved
               *CR6* ;; cr6 is reserved
               *CR7* ;; cr7 is reserved
               *CR8* ;; cr8 provides read/write access to the TPR.
                     ;; (Task Priority Register) available only in 64
                     ;; bit mode
               ;; cr9 thru cr15 are not implemented in our model yet.
               *CR9* *CR10* *CR11* *CR12* *CR13* *CR14* *CR15*
               *XCR0* ; TODO: separate this from the *CR...*s
               *control-register-names-len*)
     ,(b* ((lst (increasing-list 0 1 17))
           (len  (len lst)))
          (cons 'mv (append lst (list len))))))

(defun define-debug-registers ()

  ;; These indices are used in the Reg field of the ModR/M byte of the
  ;; instructions MOV from/to debug registers:
  `(defconsts (*DR0* ;; dr0 holds breakpoint 0 virtual address, 64/32 bit
               *DR1* ;; dr1 holds breakpoint 1 virtual address, 64/32 bit
               *DR2* ;; dr2 holds breakpoint 2 virtual address, 64/32 bit
               *DR3* ;; dr3 holds breakpoint 3 virtual address, 64/32 bit
               *DR4* ;; dr4 is reserved
               *DR5* ;; dr5 is reserved
               *DR6* ;; dr6
               *DR7* ;; dr7
               *debug-register-names-len*)
     ,(b* ((lst (increasing-list 0 1 8))
           (len  (len lst)))
          (cons 'mv (append lst (list len))))))

(defun define-fp-registers ()
  ;; 80-bit registers

  ;; Note: The Intel manual refers to these registers as R0, R1, ... ,
  ;; R7, but in our model, we will refer to them as FP0, FP1, ...,
  ;; FP7.

  `(defconsts (*FP0* *FP1* *FP2* *FP3* *FP4* *FP5* *FP6* *FP7*
                     *fp-data-register-names-len*)

     ,(b* ((lst (increasing-list 0 1 8))
           (len  (len lst)))
          (cons 'mv (append lst (list len))))))

(defun define-mmx-registers ()
  ;; 64-bit registers

  ;; The MM registers (MM0 through MM7) are aliased to the low 64-bits
  ;; of the FPU data registers.

  `(defconsts (*MM0* *MM1* *MM2* *MM3* *MM4* *MM5* *MM6* *MM7*
                     *mmx-register-names-len*)

     ,(b* ((lst (increasing-list 0 1 8))
           (len  (len lst)))
          (cons 'mv (append lst (list len))))))

(defun define-xmm-registers ()
  ;; 128-bit registers

  `(defconsts (*XMM0* *XMM1* *XMM2* *XMM3* *XMM4* *XMM5* *XMM6* *XMM7*
                      *XMM8* *XMM9* *XMM10* *XMM11*
                      *XMM12* *XMM13* *XMM14* *XMM15*
                      *xmm-register-names-len*)

     ,(b* ((lst (increasing-list 0 1 16))
           (len  (len lst)))
        (cons 'mv (append lst (list len))))))

(defun define-ymm-registers ()
  ;; 256-bit registers

  `(defconsts (*YMM0* *YMM1* *YMM2* *YMM3* *YMM4* *YMM5* *YMM6* *YMM7*
                      *YMM8* *YMM9* *YMM10* *YMM11*
                      *YMM12* *YMM13* *YMM14* *YMM15*
                      *ymm-register-names-len*)

     ,(b* ((lst (increasing-list 0 1 16))
           (len  (len lst)))
        (cons 'mv (append lst (list len))))))

(defun define-zmm-registers ()
  ;; 512-bit registers

  `(progn
     ;; mv can't be given more than 32 arguments, so I've had to
     ;; separately define *zmm-register-names-len*.
     (defconst *zmm-register-names-len* 32)
     (defconsts (*ZMM0* *ZMM1* *ZMM2* *ZMM3* *ZMM4* *ZMM5* *ZMM6* *ZMM7*
                        *ZMM8* *ZMM9* *ZMM10* *ZMM11*
                        *ZMM12* *ZMM13* *ZMM14* *ZMM15*
                        *ZMM16* *ZMM17* *ZMM18* *ZMM19* *ZMM20*
                        *ZMM21* *ZMM22* *ZMM23* *ZMM24* *ZMM25*
                        *ZMM26* *ZMM27* *ZMM28* *ZMM29* *ZMM30*
                        *ZMM31*)

       ,(b* ((lst (increasing-list 0 1 31))
             (len  (len lst)))
          (cons 'mv (append lst (list len)))))))

(defun define-opmsk-registers ()
  ;; 64-bit registers

  `(defconsts (*K0* *K1* *K2* *K3* *K4* *K5* *K6* *K7*
                    *opmsk-register-names-len*)

     ,(b* ((lst (increasing-list 0 1 8))
           (len  (len lst)))
        (cons 'mv (append lst (list len))))))

(defun define-model-specific-registers ()

  ;; Source: Section 2.1 (Architectural MSRs), Intel Vol. 4, Model-Specific
  ;; Registers

  ;; At this point, we only model the MSRs that we need.  Remember,
  ;; these are Intel-specific registers, and may or may not be
  ;; available on AMD machines.

  ;; The constants ending with IDX are used to index into the STOBJ
  ;; field for model-specific registers.

  ;; Note that *ia32_efer-idx* and *ia32_efer* (as well as the other pairs) are
  ;; different.  The latter is the "address" of the register on the real
  ;; machine and the former is the index of the register in the x86 stobj.  So
  ;; the *...-IDX* values are specific to the formal model.

  `(defconsts (
               ;; extended features enables --- If
               ;; CPUID.80000001.EDX.[bit 20] or
               ;; CPUID.80000001.EDX.[bit 29]
               *IA32_EFER*
               *IA32_EFER-IDX*

               ;; Map of BASE Address of FS (R/W) --- If
               ;; CPUID.80000001.EDX.[bit 29] = 1
               *IA32_FS_BASE*
               *IA32_FS_BASE-IDX*

               ;; Map of BASE Address of GB (R/W) --- If
               ;; CPUID.80000001.EDX.[bit 29] = 1
               *IA32_GS_BASE*
               *IA32_GS_BASE-IDX*

               ;; Swap Target of BASE Address of GS (R/W) --- If
               ;; CPUID.80000001.EDX.[bit 29] = 1
               *IA32_KERNEL_GS_BASE*
               *IA32_KERNEL_GS_BASE-IDX*

               ;; System Call Target Address (R/W) --- If
               ;; CPUID.80000001.EDX.[bit 29] = 1
               *IA32_STAR*
               *IA32_STAR-IDX*

               ;; IA-32e Mode System Call Target Address (R/W) --- If
               ;; CPUID.80000001.EDX.[bit 29] = 1
               *IA32_LSTAR*
               *IA32_LSTAR-IDX*

               ;; System Call Flag Mask (R/W) --- If
               ;; CPUID.80000001.EDX.[bit 29] = 1
               *IA32_FMASK*
               *IA32_FMASK-IDX*

               *IA32_MISC_ENABLE*
               *IA32_MISC_ENABLE-IDX*

               *model-specific-register-names-len*)

     ,(b* ((lst (list #uxC000_0080 ;; ia32_efer and idx
                      0
                      #uxC000_0100 ;; ia32_fs_base and idx
                      1
                      #uxC000_0101 ;; ia32_gs_base and idx
                      2
                      #uxC000_0102 ;; ia32_kernel_gs_base and idx
                      3
                      #uxC000_0081 ;; ia32_star and idx
                      4
                      #uxC000_0082 ;; ia32_lstar and idx
                      5
                      #uxC000_0084 ;; ia32_fmask and idx
                      6
                      #ux01_a0     ;; ia32_misc_enable and idx
                      7
                      ))
           (len  (/ (len lst) 2)))
        (cons 'mv (append lst (list len))))))

;; ----------------------------------------------------------------------
