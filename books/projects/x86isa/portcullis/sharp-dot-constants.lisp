; X86ISA Library

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2015, Regents of the University of Texas
; Copyright (C) 2018, Kestrel Technology, LLC
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
; Contributing Author(s):
; Alessandro Coglio   <coglio@kestrel.edu>

(in-package "X86ISA")
(include-book "std/util/defconsts" :dir :system)
(local (include-book "sharp-dot-defuns"))

;; ======================================================================

;; Some expt constants:

(defconst *2^0*       (expt 2  0))
(defconst *2^1*       (expt 2  1))
(defconst *2^2*       (expt 2  2))
(defconst *2^3*       (expt 2  3))
(defconst *2^4*       (expt 2  4))
(defconst *2^5*       (expt 2  5))
(defconst *2^6*       (expt 2  6))
(defconst *2^7*       (expt 2  7))
(defconst *2^8*       (expt 2  8))
(defconst *2^8-1*     (- *2^8* 1))
(defconst *2^12*      (expt 2 12))
(defconst *2^12-1*    (- *2^12* 1))
(defconst *2^15*      (expt 2 15))
(defconst *2^16*      (expt 2 16))
(defconst *2^16-1*    (- *2^16* 1))
(defconst *2^18*      (expt 2 18))
(defconst *2^21*      (expt 2 21))
(defconst *2^21-1*    (- *2^21* 1))
(defconst *2^22*      (expt 2 22))
(defconst *2^22-1*    (- *2^22* 1))
(defconst *2^24*      (expt 2 24))
(defconst *2^25*      (expt 2 25))
(defconst *2^26*      (expt 2 26))
(defconst *2^27*      (expt 2 27))
(defconst *2^27-1*    (- *2^27* 1))
(defconst *2^28*      (expt 2 28))
(defconst *2^30*      (expt 2 30))
(defconst *2^31*      (expt 2 31))
(defconst *2^32*      (expt 2 32))
(defconst *2^35*      (expt 2 35))
(defconst *2^43*      (expt 2 43))
(defconst *2^44*      (expt 2 44))
(defconst *2^45*      (expt 2 45))
(defconst *2^47*      (expt 2 47))
(defconst *-2^47*     (- (expt 2 47)))
(defconst *2^47-1*    (- *2^47* 1))
(defconst *2^47-8*    (- *2^47* 8))
(defconst *2^47-16*   (- *2^47* 16))
(defconst *2^48*      (expt 2 48))
(defconst *2^48-1*    (- *2^48* 1))
(defconst *2^48-8*    (- *2^48* 8))
(defconst *2^48-16*   (- *2^48* 16))
(defconst *2^52*      (expt 2 52))
(defconst *2^63*      (expt 2 63))
(defconst *2^64*      (expt 2 64))
(defconst *2^64-1*    (- *2^64* 1))
(defconst *2^127*     (expt 2 127))
(defconst *2^128*     (expt 2 128))
(defconst *2^256*     (expt 2 256))
(defconst *2^512*     (expt 2 512))
(defconst *2^32-1*    (- *2^32*  1))
(defconst *2^32-2*    (- *2^32*  2))
(defconst *2^32-3*    (- *2^32*  3))
(defconst *2^32-4*    (- *2^32*  4))
(defconst *2^32-5*    (- *2^32*  5))
(defconst *2^32-6*    (- *2^32*  6))
(defconst *2^32-7*    (- *2^32*  7))
(defconst *2^32-8*    (- *2^32*  8))
(defconst *2^32-9*    (- *2^32*  9))
(defconst *2^32-10*   (- *2^32* 10))
(defconst *2^32-11*   (- *2^32* 11))
(defconst *2^32-12*   (- *2^32* 12))
(defconst *2^32-13*   (- *2^32* 13))
(defconst *2^32-14*   (- *2^32* 14))
(defconst *2^32-15*   (- *2^32* 15))
(defconst *2^32-16*   (- *2^32* 16))

;; ======================================================================
;; Prefixes (Intel manual, Mar'17, Vol. 2A, Section 2):

(defconst *prefixes-width*
  ;; Width of the prefixes layout structure; see :doc
  ;; legacy-prefixes-layout-structure.
  52)

;; Group 1:
(defconst *lock*                  #xF0)
(defconst *repe*                  #xF3)
(defconst *repne*                 #xF2)

;; Group 2:
(defconst *es-override*           #x26)
(defconst *cs-override*           #x2E)
(defconst *ss-override*           #x36)
(defconst *ds-override*           #x3E)
(defconst *fs-override*           #x64)
(defconst *gs-override*           #x65)

;; Group 3:
(defconst *operand-size-override* #x66)

;; Group 4:
(defconst *addr-size-override*    #x67)

;; SIMD Prefixes:
(defconst *mandatory-66h*         #x66)
(defconst *mandatory-f2h*         #xF2)
(defconst *mandatory-f3h*         #xF3)

;; VEX Prefix:

(defconst *vex-width*
  ;; Width of the vex prefixes layout structure; see :doc
  ;; vex-prefixes-layout-structures.
  24)

(defconst *vex2-byte0*            #xC5) ;; First byte of the 2-byte VEX prefix
(defconst *vex3-byte0*            #xC4) ;; First byte of the 3-byte VEX prefix

;; EVEX Prefix:

(defconst *evex-width*
  ;; Width of the evex prefixes layout structure; see :doc
  ;; evex-prefixes-layout-structures.
  32)

(defconst *evex-byte0*            #x62) ;; First byte of the 4-byte EVEX prefix

;; The following constants apply to both VEX and EVEX prefixes.

;; Two-bit values of the PP field:
(defconst *v66*                   #b01)
(defconst *vF3*                   #b10)
(defconst *vF2*                   #b11)
;; 4-bit values of the M-MMMM field:
(defconst *v0F*                   #b00001)
(defconst *v0F38*                 #b00010)
(defconst *v0F3A*                 #b00011)

;; ======================================================================

;; Identifiers of some arithmetic and logical instructions: (note: different
;; from the opcode; specific to the formal model)

;; Even IDs: Arithmetic Instructions

(defconst *OP-ADD*       0)
(defconst *OP-ADC*       2)
(defconst *OP-SUB*       4)
(defconst *OP-SBB*       6)
(defconst *OP-CMP*       8)
(defconst *OP-SAL/SHL*   10)
(defconst *OP-SHR*       12)
(defconst *OP-SAR*       14)
(defconst *OP-RCL*       16)
(defconst *OP-RCR*       18)
(defconst *OP-ROL*       20)
(defconst *OP-ROR*       22)
(defconst *OP-NEG*       24)
(defconst *OP-MUL*       26)
(defconst *OP-DIV*       28)
(defconst *OP-IMUL*      30)
(defconst *OP-IDIV*      32)
(defconst *OP-MAX*       34)
(defconst *OP-MIN*       36)

;; Odd IDs: Logical Instructions

(defconst *OP-OR*        1)
(defconst *OP-AND*       3)
(defconst *OP-XOR*       5)
(defconst *OP-TEST*      7)
(defconst *OP-BT*        9)
(defconst *OP-CMPXCHG*   11)
(defconst *OP-ANDN*      13)

;; FP IDs:

(defconst *OP-SP* 0)
(defconst *OP-DP* 1)

;; Single/Double FP conversions:

(defconst *SP-TO-DP* 0)
(defconst *DP-TO-SP* 1)

;; SIMD packs:

(defconst *LOW-PACK*  0)
(defconst *HIGH-PACK* 1)

;; IDs: Comparison Instructions

(defconst *OP-CMPEQ*      0)
(defconst *OP-CMPLT*      1)
(defconst *OP-CMPLE*      2)
(defconst *OP-CMPUNORD*   3)
(defconst *OP-CMPNEQ*     4)
(defconst *OP-CMPNLT*     5)
(defconst *OP-CMPNLE*     6)
(defconst *OP-CMPORD*     7)
(defconst *OP-COMI*       8)
(defconst *OP-UCOMI*      9)

;; ======================================================================
;; REX bits (Intel manual, Mar'17, Vol. 2A, Section 2.2.1.2):

(defconst *b* 0)
(defconst *x* 1)
(defconst *r* 2)
(defconst *w* 3)

;; Rflags (Intel manual, Mar'17, Vol. 1, Figure 3-8):

(defconst *cf*    0) ;; Carry Flag
(defconst *pf*    2) ;; Parity Flag
(defconst *af*    4) ;; Auxiliary-carry Flag
(defconst *zf*    6) ;; Zero Flag
(defconst *sf*    7) ;; Sign Flag
(defconst *tf*    8) ;; Trap Flag
(defconst *if*    9) ;; Interrupt-enable Flag
(defconst *df*   10) ;; Direction Flag
(defconst *of*   11) ;; Overflow Flag
(defconst *iopl* 12) ;; I/O Privilege Level
(defconst *nt*   14) ;; Nested Task
(defconst *rf*   16) ;; Resume Flag
(defconst *vm*   17) ;; Virtual-8086 Mode
(defconst *ac*   18) ;; Alignment Check
(defconst *vif*  19) ;; Virtual Interrupt Flag
(defconst *vip*  20) ;; Virtual Interrupt Pending
(defconst *id*   21) ;; ID flag

(defconst *flg-names*
  (list *cf* *pf* *af* *zf* *sf* *tf* *if* *df*
        *of* *iopl* *nt* *rf* *vm* *ac* *vif* *vip* *id*))

(make-event
 `(defconst *max-flg-index*
    ,(max-list *flg-names*)))

;; FP Status Register (Intel Manual, Feb'14, Vol. 1, Section 8.1.3)

(defconst *fp-ie*   0) ;; Invalid Operation Flag
(defconst *fp-de*   1) ;; Denormalized Operand Flag
(defconst *fp-ze*   2) ;; Zero Divide Flag
(defconst *fp-oe*   3) ;; Overflow Flag
(defconst *fp-ue*   4) ;; Underflow Flag
(defconst *fp-pe*   5) ;; Precision Flag
(defconst *fp-sf*   6) ;; Stack Fault
(defconst *fp-es*   7) ;; Error Summary Status
(defconst *fp-c0*   8) ;; Condition Code
(defconst *fp-c1*   9) ;; Condition Code
(defconst *fp-c2*  10) ;; Condition Code
(defconst *fp-top* 11) ;; Top of stack pointer
(defconst *fp-c3*  14) ;; Condition Code
(defconst *fp-b*   15) ;; FPU Busy

(defconst *fp-status-names*
  (list *fp-ie* *fp-de* *fp-ze* *fp-oe* *fp-ue* *fp-pe* *fp-sf*
        *fp-es* *fp-c0* *fp-c1* *fp-c2* *fp-top* *fp-c3* *fp-b*))

;; MXCSR (Intel Manual, Feb'14, Vol. 1, Section 10.2.3)

;;    Bits 16 through 31 of the MXCSR register are reserved and are
;;    cleared on a power-up or reset of the processor; attempting to
;;    write a non-zero value to these bits, using either the FXRSTOR
;;    or LDMXCSR instructions, will result in a general-protection
;;    exception (#GP) being generated.

(defconst *mxcsr-ie*        0) ;; Invalid Operation Flag
(defconst *mxcsr-de*        1) ;; Denormal Flag
(defconst *mxcsr-ze*        2) ;; Divide-by-Zero Flag
(defconst *mxcsr-oe*        3) ;; Overflow Flag
(defconst *mxcsr-ue*        4) ;; Underflow Flag
(defconst *mxcsr-pe*        5) ;; Precision Flag
(defconst *mxcsr-daz*       6) ;; Denormals are Zeros
(defconst *mxcsr-im*        7) ;; Invalid Operation Mask
(defconst *mxcsr-dm*        8) ;; Denormal Mask
(defconst *mxcsr-zm*        9) ;; Divide-by-Zero Mask
(defconst *mxcsr-om*       10) ;; Overflow Mask
(defconst *mxcsr-um*       11) ;; Underflow Mask
(defconst *mxcsr-pm*       12) ;; Precision Mask
(defconst *mxcsr-rc*       13) ;; Rounding Control
(defconst *mxcsr-ftz*      15) ;; Flush to Zero
(defconst *mxcsr-reserved* 16) ;; Reserved


(defconst *mxcsr-names*
  (list *mxcsr-ie* *mxcsr-de* *mxcsr-ze* *mxcsr-oe* *mxcsr-ue*
        *mxcsr-pe* *mxcsr-daz* *mxcsr-im* *mxcsr-dm* *mxcsr-zm*
        *mxcsr-om* *mxcsr-um* *mxcsr-pm* *mxcsr-rc* *mxcsr-ftz*
        *mxcsr-reserved*))


;; Access GPR, XMM, YMM, or ZMM (specific to the formal model):

(defconst *gpr-access*     0)
(defconst *xmm-access*     1) ;; Non-VEX Encoded SIMD Instructions
(defconst *vex-xmm-access* 2)
(defconst *ymm-access*     3)
(defconst *zmm-access*     4)

;; Rounding Control bit definitions (Intel manual, Mar'17, Vol. 1, Table 4-8):

(defconst *rc-rn*             0)
(defconst *rc-rd*             1)
(defconst *rc-ru*             2)
(defconst *rc-rz*             3)

;; Constants for (unordered) compare scalar floating-point
;; instructions (COMISS,  UCOMISS, etc.) (specific to the formal model):

(defconst *unordered*    0)
(defconst *greater_than* 1)
(defconst *less_than*    2)
(defconst *equal*        3)

;; Single-precision floating-point
;; format (Intel manual, Mar'17, Vol. 1, Table 4-3)

(defconst *ieee-sp-exp-width*          8)
(defconst *ieee-sp-frac-width*        23)

;; Double-precision floating-point format
;; format (Intel manual, Mar'17, Vol. 1, Table 4-3)

(defconst *ieee-dp-exp-width*         11)
(defconst *ieee-dp-frac-width*        52)

;; Extended Feature Enable Register (Intel manual, Mar'17, Vol. 3A, Table 2-1)

(defconst *ia32_efer-sce*  0)  ;; Syscall Enable (R/W) --- enables
                               ;; SYSCALL/SYSRET
(defconst *ia32_efer-lme*  8)  ;; Long Mode Enabled (R/W)
(defconst *ia32_efer-lma* 10)  ;; Long Mode Active (R)
(defconst *ia32_efer-nxe* 11)  ;; Execute Disable Bit Enable (R/W)
                               ;; (Enables page access restriction by
                               ;; preventing instruction fetches from
                               ;; PAE pages with the XD bit set)

(defconst *ia32_efer-names*
  (list *ia32_efer-sce* *ia32_efer-lme* *ia32_efer-lma* *ia32_efer-nxe*))

;; ======================================================================

; Constants related to the memory model in the x86 state:

; Virtual Memory:

(defconst *max-linear-address-size*  48)
(defconst *max-linear-address-size+1* (1+ *max-linear-address-size*))
(defconst *max-linear-address-size+2* (+ 2 *max-linear-address-size*))
(defconst *max-linear-address-size+3* (+ 3 *max-linear-address-size*))
(defconst *max-linear-address-size+4* (+ 4 *max-linear-address-size*))
(defconst *max-linear-address-size+5* (+ 5 *max-linear-address-size*))
(defconst *max-linear-address-size+6* (+ 6 *max-linear-address-size*))
(defconst *max-linear-address-size+7* (+ 7 *max-linear-address-size*))
(defconst *max-linear-address-size+8* (+ 8 *max-linear-address-size*))
(defconst *max-linear-address-size+9* (+ 9 *max-linear-address-size*))
(defconst *max-linear-address-size+10* (+ 10 *max-linear-address-size*))
(defconst *max-linear-address-size+11* (+ 11 *max-linear-address-size*))
(defconst *max-linear-address-size+12* (+ 12 *max-linear-address-size*))
(defconst *max-linear-address-size+13* (+ 13 *max-linear-address-size*))
(defconst *max-linear-address-size+14* (+ 14 *max-linear-address-size*))
(defconst *max-linear-address-size+15* (+ 15 *max-linear-address-size*))
(defconst *max-linear-address-size-1* (1- *max-linear-address-size*))
(defconst *2^max-linear-address-size-1* (expt 2 *max-linear-address-size-1*))
(defconst *-2^max-linear-address-size-1* (- *2^max-linear-address-size-1*))
(defconst *max-linear-address-space* (expt 2 *max-linear-address-size*))

; Physical Memory:

(defconst *physical-address-size* 52)
(defconst *physical-address-size+1* (+ 1 *physical-address-size*))
(defconst *physical-address-size+2* (+ 2 *physical-address-size*))
(defconst *physical-address-size+4* (+ 4 *physical-address-size*))
(defconst *physical-address-size+7* (+ 7 *physical-address-size*))
(defconst *mem-size-in-bytes*  (expt 2 *physical-address-size*))
(defconst *mem-size-in-words*  (floor *mem-size-in-bytes* 2))
(defconst *mem-size-in-dwords* (floor *mem-size-in-bytes* 4))
(defconst *mem-size-in-qwords* (floor *mem-size-in-bytes* 8))

(defconst *mem-size-in-bytes-1*  (+ -1 *mem-size-in-bytes*))
(defconst *mem-size-in-bytes-2*  (+ -2 *mem-size-in-bytes*))
(defconst *mem-size-in-bytes-3*  (+ -3 *mem-size-in-bytes*))
(defconst *mem-size-in-bytes-4*  (+ -4 *mem-size-in-bytes*))
(defconst *mem-size-in-bytes-5*  (+ -5 *mem-size-in-bytes*))
(defconst *mem-size-in-bytes-6*  (+ -6 *mem-size-in-bytes*))
(defconst *mem-size-in-bytes-7*  (+ -7 *mem-size-in-bytes*))
(defconst *mem-size-in-bytes-8*  (+ -8 *mem-size-in-bytes*))
(defconst *mem-size-in-bytes-9*  (+ -9 *mem-size-in-bytes*))
(defconst *mem-size-in-bytes-10*  (+ -10 *mem-size-in-bytes*))
(defconst *mem-size-in-bytes-11*  (+ -11 *mem-size-in-bytes*))
(defconst *mem-size-in-bytes-12*  (+ -12 *mem-size-in-bytes*))
(defconst *mem-size-in-bytes-13*  (+ -13 *mem-size-in-bytes*))
(defconst *mem-size-in-bytes-14*  (+ -14 *mem-size-in-bytes*))
(defconst *mem-size-in-bytes-15*  (+ -15 *mem-size-in-bytes*))

;; ======================================================================

;; Constants related to Flags (specific to the formal model):

(defconst *unchanged* 2)
(defconst *undefined* 3)

;; ======================================================================

;; Instruction Sets:

;; Floating-Point (specific to the formal model):
(defconst *fpu*    0)
(defconst *mmx*    1)
(defconst *sse*    2)
(defconst *sse2*   3)
(defconst *sse3*   4)
(defconst *avx*    5)
(defconst *avx2*   6)
(defconst *avx512* 7)

;; ======================================================================

;; Constants related to modes of operation of an x86 processor
;; (specific to the formal model):

;; IA-32e Mode, introduced by Intel 64(R) Architecture, has the following two
;; sub-modes:
(defconst *64-bit-mode*        0)
(defconst *compatibility-mode* 1)

;; IA-32 architecture supports the following modes:
(defconst *protected-mode*     2) ;; Virtual-8086 mode is built into it
(defconst *real-address-mode*  3)
(defconst *smm-mode*           4) ;; System Management Mode

;; Total Number of Processor Modes:
(defconst *num-proc-modes*     5)
(defconst *num-proc-modes-1*   (1- *num-proc-modes*))

;; ======================================================================

;; Exceptions and Interrupts
;; Reference: Table 6-1, Chapter 6 (Interrupts and Exceptions), Intel Vol. 1

;     Mnemonic    Vector     Description &
;                            Source

(defconst *#DE*     0)  ;    Divide Error
                        ;    DIV and IDIV instructions.

(defconst *#DB*     1)  ;    Debug
                        ;    Any code or data reference.

(defconst *#NMI*    2)  ;    Reserved: NMI Interrupt
                        ;    Non-maskable external interrupt.

(defconst *#BP*     3)  ;    Breakpoint
                        ;    INT3 instruction.

(defconst *#OF*     4)  ;    Overflow
                        ;    INTO instruction.

(defconst *#BR*     5)  ;    BOUND Range Exceeded
                        ;    BOUND instruction.

(defconst *#UD*     6)  ;    Invalid Opcode (UnDefined Opcode)
                        ;    UD instruction or reserved opcode.

(defconst *#NM*     7)  ;    Device Not Available (No Math Coprocessor)
                        ;    Floating-point or WAIT/FWAIT instruction.

(defconst *#DF*     8)  ;    Double Fault
                        ;    Any instruction that can generate an exception, an
                        ;    NMI, or an INTR.

(defconst *#resMF*  9)  ;    CoProcessor Segment Overrun (reserved)
                        ;    Floating-point instruction.
                        ;    NOTE: IA-32 processors after the Intel386
                        ;    processor do not generate this exception.

(defconst *#TS*     10) ;    Invalid TSS
                        ;    Task switch or TSS access.

(defconst *#NP*     11) ;    Segment Not Present
                        ;    Loading segment registers or accessing system segments.

(defconst *#SS*     12) ;    Stack Segment Fault
                        ;    Stack operations and SS register loads.

(defconst *#GP*     13) ;    General Protection
                        ;    Any memory reference and other protection checks.

(defconst *#PF*     14) ;    Page Fault
                        ;    Any memory reference

(defconst *#res15*  15) ;    Reserved

(defconst *#MF*     16) ;    Floating-Point Error (Math Fault)
                        ;    Floating-point or WAIT/FWAIT instruction.

(defconst *#AC*     17) ;    Alignment Check
                        ;    Any data reference in memory.
                        ;    This exception was introduced in the Intel486 processor.

(defconst *#MC*     18) ;    Machine Check
                        ;    Error codes (if any) and source are model dependent.
                        ;    This exception was introduced in the Pentium
                        ;    processor and enhanced in the P6 family
                        ;    processors.

(defconst *#XM*     19) ;    SIMD Floating-Point Exception
                        ;    SIMD Floating-Point Instruction
                        ;    This exception was introduced in the Pentium III
                        ;    processor.


(defconst *#VE*     20) ;    Virtualization Exception
                        ;    EPT violations
                        ;    This exception can occur only on processors that
                        ;    support the 1-setting of the “EPT-violation #VE”
                        ;    VM-execution control.

;; 21-31   Reserved
;;
;; 32-255  Maskable Interrupts
;;         External interrupt from INTR pin or INT n instruction.

;; ======================================================================

;; Indices and length of fields in the x86 state (see
;; machine/concrete-state.lisp):

(make-event (define-general-purpose-registers))
(make-event (define-32-bit-general-purpose-registers))

(make-event (define-segment-registers))
(defconst *segment-register-names-len-1* (1- *segment-register-names-len*))

(make-event (define-gdtr/idtr-registers))

(make-event (define-ldtr/tr-registers))

(make-event (define-control-registers))

(make-event (define-debug-registers))

(make-event (define-fp-registers))

(make-event (define-mmx-registers))

(make-event (define-xmm-registers))

(make-event (define-ymm-registers))

(make-event (define-zmm-registers))

(make-event (define-opmsk-registers))

(make-event (define-model-specific-registers))

;; ======================================================================
