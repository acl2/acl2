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
; Shilpi Goel         <shigoel@cs.utexas.edu>

(in-package "X86ISA")
(include-book "std/util/defconsts" :dir :system)

;; ======================================================================

(local (include-book "arithmetic/top-with-meta" :dir :system))

(defun power-of-2-measure (x)
  (cond ((or (not (natp x))
             (<= x 1))
         0)
        (t (floor x 1))))

(defn power-of-2 (x count)
  (declare (xargs :measure (power-of-2-measure x)
                  :guard (natp count)))
  (if (natp x)
      (if (<= x 1)
          count
        (power-of-2 (* 1/2 x) (1+ count)))
    count))

(defun gl-int (start by count)
  (declare (xargs :guard (and (natp start)
                              (natp by)
                              (natp count))))
  (if (zp count)
      nil
    (cons start
          (gl-int (+ by start) by (1- count)))))

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
;; Prefixes (Intel manual, Mar'17, Vol. 2A, Section 2.1.1):

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

(defconst *mandatory-66h*         #x66)
(defconst *mandatory-f2h*         #xF2)
(defconst *mandatory-f3h*         #xF3)

;; ======================================================================

;; Identifiers of some arithmetic and logical instructions: (note: different
;; from the opcode)

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

(defun max-list (l)
  (if (or (endp l)
          (equal (len l) 1))
      (car l)
    (if (> (car l) (max-list (cdr l)))
        (car l)
      (max-list (cdr l)))))

(defconst *max-flg-index*
  (max-list *flg-names*))

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
  (list *fp-ie* *fp-de* *fp-ze* *fp-oe*  *fp-ue*  *fp-pe* *fp-sf*
        *fp-es* *fp-c0* *fp-c1* *fp-c2*  *fp-top* *fp-c3* *fp-b*))

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
(defconst *mxcsr-fz*       15) ;; Flush to Zero
(defconst *mxcsr-reserved* 16) ;; Reserved


(defconst *mxcsr-names*
  (list *mxcsr-ie* *mxcsr-de*  *mxcsr-ze* *mxcsr-oe* *mxcsr-ue*
        *mxcsr-pe* *mxcsr-daz* *mxcsr-im* *mxcsr-dm* *mxcsr-zm*
        *mxcsr-om* *mxcsr-um*  *mxcsr-pm* *mxcsr-rc* *mxcsr-fz*
        *mxcsr-reserved*))


;; Access GPR or XMM:

(defconst *gpr-access* 0)
(defconst *xmm-access* 1)

;; Rounding Control bit definitions (Intel manual, Mar'17, Vol. 1, Table 4-8):

(defconst *rc-rn*             0)
(defconst *rc-rd*             1)
(defconst *rc-ru*             2)
(defconst *rc-rz*             3)

;; Constants for (unordered) compare scalar floating-point
;; instructions (COMISS,  UCOMISS, etc.):

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

; The following note also appears with the definition of the processor state.

    ;; For our ACL2 model, we define a paging-like mechanism to model the
    ;; complete x86 52-bit address space.  The memory is laid out in a flat
    ;; array, to be viewed as back-to-back "pseudo-pages" each of size 2^27
    ;; bytes (128MB).  The address of a byte is split into two pieces: a 25-bit
    ;; pseudo-page address and a 27-bit offset within a page.  The mem-table
    ;; data structure is of size *mem-table-size* = 2^25 -- thus, indices are
    ;; 25 bits -- and it maps these indices to 25-bit pseudo-page addresses.
    ;; However, the mem-table values are actually 26-bit values: the least
    ;; significant bit is initially 1, but is 0 when the entry is valid, in
    ;; which case the most significant 25 bits represent a pseudo-page address.
    ;; The offset of a byte address is a 27-bit wide address, which when added
    ;; to (pseudo-page address << 27), gives the "real" address of a byte
    ;; stored in mem-array.  Mem-array-next-addr keeps track of the 25-bit
    ;; index of the pseudo-page to be allocated next.

    ;; Here is an example of how this works.  Suppose we have the following,
    ;; where again, the least significant bit of 0 indicates a valid entry, and
    ;; where {i, 1'bx} denotes concatenation of the bit-vector i with the
    ;; single bit x.

    ;;   mem-table[#x0654321] = {0, 1'b0}
    ;;   mem-table[#x16789ab] = {1, 1'b0}
    ;;   mem-table[#x0111111] = {2, 1'b0}

    ;; All additional values in mem-table are the initial value of 1, which means
    ;; "page is not present".

    ;; Intel manual, Mar'17, Vol. 1, Section 3.2.1 says that the maximum size of
    ;; the physical address space is 2^46 bytes in 64-bit mode. However, Table
    ;; 4-1 in Vol. 3 says that the physical address width is up to 52 bits
    ;; in 64-bit mode. Furtermore, AMD manual, Oct'13, Vol. 1, Section 2.1.4.1
    ;; says that physical addresses are up to 52 bits in size. Based on all of
    ;; this, our model assumes a 2^52-byte physical memory -- see the constant
    ;; *physical-address-size*.

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

(defconst *default-mem-value*

; If we change this default memory value, we also need to change the
; :initially value in the mem-array field of our x86-64 stobj.

  0)

(defconst *initial-mem-array-pages* 2) ; arbitrary

(defconst *2^x-byte-pseudo-page*
  ;; Log size of pseudo page; i.e.; for 128MB pseudo pages, this is 27
  27)

(defconst *pseudo-page-size-in-bytes*
  ;; Pseudo page size
  (expt 2 *2^x-byte-pseudo-page*))

(defconst *pseudo-page-size-in-bytes-1*
  (1- *pseudo-page-size-in-bytes*))

(defconst *2^x-number-pseudo-pages*
  ;; Previously named *non-zero-mem-table-entry-size*
  ;; Log size of the number of pseudo pages
  (- *physical-address-size*
     *2^x-byte-pseudo-page*))

(defconst *initial-mem-array-length*
  ;; Initial allocation of pseudo pages
  (* *initial-mem-array-pages*
     *pseudo-page-size-in-bytes*))

(defconst *mem-table-size*
  ;; Size of table for address-to-pseudo-page translation
  (floor *mem-size-in-bytes*
         *pseudo-page-size-in-bytes*))

(defconst *mem-table-size-bits*
  (power-of-2 *mem-table-size* 0))

(defconst *mem-table-size-bits+1*
  (+ 1 *mem-table-size-bits*))

(defconst *2^mem-table-size-bits+1*
  (expt 2 *mem-table-size-bits+1*))

(defconst *mem-table-size-1*
  (1- *mem-table-size*))

(defconst *mem-array-resize-factor*
  ;; Growth factor used when additional pseudo pages are required
  2)

;; ======================================================================

;; Constants related to Flags:

(defconst *unchanged* 2)
(defconst *undefined* 3)

;; ======================================================================

;; Indices and length of fields in the x86 state (see
;; machine/state-concrete.lisp):

(defun define-general-purpose-registers ()

  `(defconsts (*RAX* *RCX* *RDX* *RBX* *RSP* *RBP* *RSI* *RDI*
                     *R8*  *R9*  *R10* *R11* *R12* *R13* *R14* *R15*
                     *64-bit-general-purpose-registers-len*)
     ,(b* ((lst (gl-int 0 1 16))
           (len  (len lst)))
          (cons 'mv (append lst (list len))))))

(defun define-segment-registers ()

  `(defconsts (*ES* *CS* *SS* *DS* *FS* *GS*
                    *segment-register-names-len*)
     ,(b* ((lst (gl-int 0 1 6))
           (len  (len lst)))
          (cons 'mv (append lst (list len))))))

(defun define-gdtr/idtr-registers ()

  `(defconsts (*GDTR* *IDTR* *gdtr-idtr-names-len*)
     ,(b* ((lst (gl-int 0 1 2))
           (len  (len lst)))
          (cons 'mv (append lst (list len))))))

(defun define-ldtr/tr-registers ()

  `(defconsts (*LDTR* *TR* *ldtr-tr-names-len*)
     ,(b* ((lst (gl-int 0 1 2))
           (len  (len lst)))
          (cons 'mv (append lst (list len))))))

;; Source: Intel Manual, Feb-14, Vol. 3A, Section 2.5
(defun define-control-registers ()

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
               *CR9*  *CR10* *CR11* *CR12* *CR13* *CR14* *CR15*
               *XCR0*
               *control-register-names-len*)
     ,(b* ((lst (gl-int 0 1 17))
           (len  (len lst)))
          (cons 'mv (append lst (list len))))))

(defun define-debug-registers ()

  `(defconsts (*DR0* ;; dr0 holds breakpoint 0 virtual address, 64/32 bit
               *DR1* ;; dr1 holds breakpoint 1 virtual address, 64/32 bit
               *DR2* ;; dr2 holds breakpoint 2 virtual address, 64/32 bit
               *DR3* ;; dr3 holds breakpoint 3 virtual address, 64/32 bit
               *DR4* ;; dr4 is reserved
               *DR5* ;; dr5 is reserved
               *DR6* ;; dr6
               *DR7* ;; dr7
               *debug-register-names-len*)
     ,(b* ((lst (gl-int 0 1 8))
           (len  (len lst)))
          (cons 'mv (append lst (list len))))))

(defun define-fp-registers ()
  ;; 80-bit registers

  ;; Note: The Intel manual refers to these registers as R0, R1, ... ,
  ;; R7, but in our model, we will refer to them as FP0, FP1, ...,
  ;; FP7.

  `(defconsts (*FP0* *FP1* *FP2* *FP3* *FP4* *FP5* *FP6* *FP7*
                     *fp-data-register-names-len*)

     ,(b* ((lst (gl-int 0 1 8))
           (len  (len lst)))
          (cons 'mv (append lst (list len))))))

(defun define-mmx-registers ()
  ;; 64-bit registers

  ;; The MM registers (MM0 through MM7) are aliased to the low 64-bits
  ;; of the FPU data registers.

  `(defconsts (*MM0* *MM1* *MM2* *MM3* *MM4* *MM5* *MM6* *MM7*
                     *mmx-register-names-len*)

     ,(b* ((lst (gl-int 0 1 8))
           (len  (len lst)))
          (cons 'mv (append lst (list len))))))

(defun define-xmm-registers ()
  ;; 128-bit registers

  `(defconsts (*XMM0* *XMM1* *XMM2* *XMM3* *XMM4* *XMM5* *XMM6* *XMM7*
                      *XMM8* *XMM9* *XMM10* *XMM11*
                      *XMM12* *XMM13* *XMM14* *XMM15*
                      *xmm-register-names-len*)

     ,(b* ((lst (gl-int 0 1 16))
           (len  (len lst)))
          (cons 'mv (append lst (list len))))))

(defun define-model-specific-registers ()
  ;; At this point, we only model the MSRs that we need.  Remember,
  ;; these are Intel-specific registers, and may or may not be
  ;; available on AMD machines.

  ;; The constants ending with IDX are used to index into the STOBJ
  ;; field for model-specific registers.


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
                      ))
           (len  (/ (len lst) 2)))
          (cons 'mv (append lst (list len))))))

(make-event (define-general-purpose-registers))
(make-event (define-segment-registers))
(make-event (define-gdtr/idtr-registers))
(make-event (define-ldtr/tr-registers))
(make-event (define-control-registers))
(make-event (define-debug-registers))
(make-event (define-fp-registers))
(make-event (define-mmx-registers))
(make-event (define-xmm-registers))
(make-event (define-model-specific-registers))

;; ======================================================================
