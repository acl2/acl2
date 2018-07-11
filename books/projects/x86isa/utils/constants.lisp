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
; Warren A. Hunt, Jr. <hunt@cs.utexas.edu>
; Matt Kaufmann       <kaufmann@cs.utexas.edu>
; Robert Krug         <rkrug@cs.utexas.edu>

(in-package "X86ISA")

(include-book "decoding-utilities")

;; ======================================================================

(defsection x86-constants
  :parents (utils)
  :short "<b>@('x86')-specific layout constants and functions/macros</b>"

  :long "<p>We define some <i>layout constants</i> to describe the bit
  fields of registers and data structures like the page tables.</p>

<p>Some important constants are as follows:</p>

<p>Source: Intel Manual, Feb-14, Vol. 3A, Section 2.5</p>

@(def *cr0-layout*)

@(def *cr3-layout*)

@(def *cr4-layout*)

@(def *cr8-layout*)

@(def *xcr0-layout*)

<p>Source: Intel Manual, Feb-14, Vol. 3A, Section 2.2.1</p>
@(def *ia32_efer-layout*)

<p>Source: Intel Manual, Feb-14, Vol. 1, Section 3.4.3</p>
@(def *rflags-layout*)

<p>Source: Intel Manual, Feb-14, Vol. 1, Section 8.1.3</p>
@(def *fp-status-layout*)

<p>Source: Intel Manual, Feb-14, Vol. 1, Section 10.2.3</p>
@(def *mxcsr-layout*)

<p>Source: Intel Manual, Feb-14, Vol. 3, Tables 4-14 through 4-19</p>
@(def *ia32e-page-tables-layout*)
@(def *ia32e-pml4e-layout*)
@(def *ia32e-pdpte-1GB-page-layout*)
@(def *ia32e-pdpte-pg-dir-layout*)
@(def *ia32e-pde-2MB-page-layout*)
@(def *ia32e-pde-pg-table-layout*)
@(def *ia32e-pte-4K-page-layout*)

<p>All the layout constants have corresponding slice accessor and
updater macros, defined using @(see slice) and @(see !slice)
respectively.  Since they are all very similar, we simply list the
accessor and updater macros for @('*cr0-layout*') below.</p>

<p>Slice accessor for @('CR0') register:</p>
@(def cr0-slice)
<p>Slice updater for @('CR0') register:</p>
@(def !cr0-slice)
"

  )

(local (xdoc::set-default-parents x86-layout-constants))

;; ======================================================================

;; Fundamental data-types:

(defconst *byte-size*         8)
(defconst *word-size*        16)
(defconst *doubleword-size*  32)
(defconst *quad-size*        64)

;; ======================================================================

;; Defining constants from layout (layout-constant-alistp) tables:

(defun keep-symbols-info (alst names indices)
  (declare (xargs :guard (and (alistp alst)
                              (true-listp names)
                              (true-listp indices))
                  :verify-guards nil))
  ;; the output list is reversed w.r.t. the input list,
  ;; but the result is only used
  ;; in DEFCONSTS  (where order does not really matter)
  ;; and in LAYOUT-NAMES (which reverses the list)
  (if (endp alst)
      (mv names indices)
    (if (symbolp (caar alst))
        (b* ((name (mk-name "*" (caar alst) "*"))
             (index (if (and (consp (cdar alst))
                             (consp (cddar alst)))
                        (nfix (cadar alst)) ;; Position
                      (cw "~%~%Input not a well-formed layout-constant-alistp?!~%~%"))))
            (keep-symbols-info (cdr alst)
                               (cons name names)
                               (cons index indices)))
      (keep-symbols-info (cdr alst) names indices))))

(defun define-layout-constants (layout)
  (b* (((mv names indices)
        (keep-symbols-info layout nil nil)))

      `(defconsts ,names
         ,(cons 'mv indices))))


(defun layout-names (name layout)
  (b* (((mv names &)
        (keep-symbols-info layout nil nil))
       (names (reverse names)))

      `(defconst ,(mk-name "*" name "*")
         ,(cons 'list names))))

;; ======================================================================

; Intel manual, Mar'17, Vol. 3A, Figure 3-7
(defconst *hidden-segment-register-layout*
  '((:base-addr  0  64) ;; Segment Base Address
    (:limit     64  32) ;; Segment Limit
    (:attr      96  16) ;; Attributes
    ))
; These fields are "cached" from the segment descriptor (Figure 3-8):
; - The Segment Base is 32 bits in the segment descriptor,
;   so the 64 bits in :BASE-ADDR above can hold it.
; - The Segment Limit is 20 bits in the segment descriptor,
;   and based on the G (granularity) flag it covers up to 4 GiB,
;   so the 32 bits in :LIMIT above can hold it.
;   IMPORTANT: this means that the cached limit field must be
;   populated only after G flag is taken into account.
; - There are 12 remaining bits in the segment descriptor,
;   so the 16 bits in :ATTR above can hold them.

(defthm hidden-segment-register-layout-ok
  (layout-constant-alistp *hidden-segment-register-layout* 0 112)
  :rule-classes nil)

; Intel manual, Mar'17, Vol. 3A, Figure 3-6
(defconst *segment-selector-layout*
  '((:rpl        0  2) ;; Requestor Privilege Level (RPL)
    (:ti         2  1) ;; Table Indicator (0 = GDT, 1 = LDT)
    (:index      3 13) ;; Index of descriptor in GDT or LDT
    ))

(defthm segment-selector-layout-ok
  (layout-constant-alistp *segment-selector-layout* 0 16)
  :rule-classes nil)

(defconst *cr0-layout*
  '((:cr0-pe    0  1) ;; Protection Enable
    (:cr0-mp    1  1) ;; Monitor coProcessor
    (:cr0-em    2  1) ;; Emulation Bit
    (:cr0-ts    3  1) ;; Task Switched
    (:cr0-et    4  1) ;; Extension Type
    (:cr0-ne    5  1) ;; Numeric Error
    (0          6 10) ;; 0 (Reserved)
    (:cr0-wp   16  1) ;; Write Protect
    (0         17  1) ;; 0 (Reserved)
    (:cr0-am   18  1) ;; Alignment Mask
    (0         19 10) ;; 0 (Reserved)
    (:cr0-nw   29  1) ;; Not Write-through
    (:cr0-cd   30  1) ;; Cache Disable
    (:cr0-pg   31  1) ;; Paging Bit
    ))

(defthm cr0-layout-ok
  (layout-constant-alistp *cr0-layout* 0 32)
  :rule-classes nil)

(defconst *cr3-layout*
  '((0          0  3) ;; 0
    (:cr3-pwt   3  1) ;; Page-Level Writes Tranparent
    (:cr3-pcd   4  1) ;; Page-Level Cache Disable
    (0          5  7) ;; 0
    (:cr3-pdb  12 40) ;; Page Directory Base
    (0         52 12) ;; Reserved (must be zero)
    ))

(defthm cr3-layout-ok
  (layout-constant-alistp *cr3-layout* 0 64)
  :rule-classes nil)

(defconst *cr4-layout*
  '((:cr4-vme         0  1) ;; Virtual-8086 Mode Extensions
    (:cr4-pvi         1  1) ;; Protected-Mode Virtual Interrupts
    (:cr4-tsd         2  1) ;; Time-Stamp Disable
    (:cr4-de          3  1) ;; Debugging Extensions
    (:cr4-pse         4  1) ;; Page Size Extensions
    (:cr4-pae         5  1) ;; Physical Address Extension
    (:cr4-mce         6  1) ;; Machine-Check Enable
    (:cr4-pge         7  1) ;; Page Global Enable
    (:cr4-pce         8  1) ;; Performance Monitoring Counter Enable
    (:cr4-osfxsr      9  1) ;; OS Support for FXSAVE and FXRSTOR
    (:cr4-osxmmexcpt 10  1) ;; OS Support for unmasked SIMD FP Exceptions
    (0               11  2) ;; 0 (Reserved)
    (:cr4-vmxe       13  1) ;; VMX Enable Bit
    (:cr4-smxe       14  1) ;; SMX Enable Bit
    (0               15  1) ;; 0 (Reserved)
    (:cr4-fsgsbase   16  1) ;; FSGSBase-Enable Bit (Enables the
                            ;; instructions RDFSBASE, RDGSBASE,
                            ;; WRFSBASE, and WRGSBASE.)
    (:cr4-pcide      17  1) ;; PCID-Enable Bit
    (:cr4-osxsave    18  1) ;; XSAVE and Processor Extended States
                            ;; Enable Bit
    (0               19  1) ;; 0 (Reserved)
    (:cr4-smep       20  1) ;; Supervisor Mode Execution Prevention
    (:cr4-smap       21  1)
    ;; Bit
    ;;  (0               21 43) ;; 0 (Reserved)

    ))

(defthm cr4-layout-ok
  (layout-constant-alistp *cr4-layout* 0 ;; 64
                   ;; A lesser value here avoids
                   ;; bignum creation.
                   22)
  :rule-classes nil)

; Intel manual, Mar'17, Vol. 3A, Section 10.8.6
(defconst *cr8-layout*
  '(
    ;; Task Priority Level (width = 4). This sets
    ;; the threshold value corresponding to the
    ;; highest- priority interrupt to be
    ;; blocked. A value of 0 means all interrupts
    ;; are enabled. This field is available in 64-
    ;; bit mode. A value of 15 means all
    ;; interrupts will be disabled.

    (:cr8-trpl        0  4) ;; Task Priority Level
;;  (0                4 59) ;; 0 (Reserved)

    ))

(defthm cr8-layout-ok
  (layout-constant-alistp *cr8-layout* 0 ;; 64
                   ;; A lesser value here avoids
                   ;; bignum creation.
                   4
                   )
  :rule-classes nil)

; Intel manual, Mar'17, Vol. 3A, Figure 2-8
(defconst *xcr0-layout*

  ;; Software can access XCR0 only if CR4.OSXSAVE[bit 18] = 1. (This bit
  ;; is also readable as CPUID.01H:ECX.OSXSAVE[bit 27].)

  '((:xcr0-fpu/mmx-state 0 1) ;; This bit must be 1.  An attempt
                              ;; to write 0 to this bit causes a
                              ;; #GP exception.
    (:xcr0-sse-state    1  1)
    (:xcr0-avx-state    2  1)
    (0                  3 60) ;; 0 (Reserved)

    ))

(defthm xcr0-layout-ok
  (layout-constant-alistp *xcr0-layout* 0 64)
  :rule-classes nil)

;; IA32_EFER (Intel Manual, Feb-14, Vol. 3A, Section 2.2.1):
(defconst *ia32_efer-layout*
  '((:ia32_efer-sce   0  1) ;; Syscall Enable (R/W) (enables SYSCALL/SYSRET)
    (0                1  7) ;; Reserved?
    (:ia32_efer-lme   8  1) ;; Long Mode Enabled (R/W)
    (0                9  1) ;; Reserved?
    (:ia32_efer-lma  10  1) ;; Long Mode Active (R)
    (:ia32_efer-nxe  11  1) ;; Execute Disable Bit Enable (R/W)
                            ;; (Enables page access restriction by
                            ;; preventing instruction fetches from
                            ;; PAE pages with the XD bit set)
;   (0               12 52) ;; Reserved (must be zero)
    ))

(defthm ia32_efer-layout-ok
  (layout-constant-alistp *ia32_efer-layout* 0 12)
  :rule-classes nil)

;; Rflags (Intel Manual, Feb-14, Vol. 1, Section 3.4.3):

(defconst *rflags-layout*
  '((:cf           0  1) ; carry flag
    (1             1  1) ; 1 (reserved)
    (:pf           2  1) ; parity flag
    (0             3  1) ; 0 (reserved)
    (:af           4  1) ; auxiliary-carry flag
    (0             5  1) ; 0 (reserved)
    (:zf           6  1) ; zero flag
    (:sf           7  1) ; sign flag
    (:tf           8  1) ; trap flag
    (:if           9  1) ; interrupt-enable flag
    (:df          10  1) ; direction flag
    (:of          11  1) ; overflow flag
    (:iopl        12  2) ; i/o privilege level
    (:nt          14  1) ; nested task
    (0            15  1) ; 0 (reserved)
    (:rf          16  1) ; resume flag
    (:vm          17  1) ; virtual-8086 mode
    (:ac          18  1) ; alignment check
    (:vif         19  1) ; virtual interrupt flag
    (:vip         20  1) ; virtual interrupt pending
    (:id          21  1) ; id flag
    (0            22 10) ; 0 (reserved)
;   (reserved     32 32) ; reserved bits
    ))

(defthm rflags-layout-ok
  (layout-constant-alistp *rflags-layout* 0 32)
  :rule-classes nil)

;; FP Status Register (Intel Manual, Feb-14, Vol. 1, Section 8.1.3)

(defconst *fp-status-layout*
  '((:fp-ie       0  1) ;; Invalid Operation Flag
    (:fp-de       1  1) ;; Denormalized Operand Flag
    (:fp-ze       2  1) ;; Zero Divide Flag
    (:fp-oe       3  1) ;; Overflow Flag
    (:fp-ue       4  1) ;; Underflow Flag
    (:fp-pe       5  1) ;; Precision Flag
    (:fp-sf       6  1) ;; Stack Fault
    (:fp-es       7  1) ;; Error Summary Status
    (:fp-c0       8  1) ;; Condition Code
    (:fp-c1       9  1) ;; Condition Code
    (:fp-c2      10  1) ;; Condition Code
    (:fp-top     11  3) ;; Top of stack pointer
    (:fp-c3      14  1) ;; Condition Code
    (:fp-b       15  1) ;; FPU Busy
    ))

(defthm fp-status-layout-ok
  (layout-constant-alistp *fp-status-layout* 0 16)
  :rule-classes nil)

(defconst *mxcsr-layout*

  ;; MXCSR (Intel Manual, Feb-14, Vol. 1, Section 10.2.3)

  ;;    Bits 16 through 31 of the MXCSR register are reserved and are
  ;;    cleared on a power-up or reset of the processor; attempting to
  ;;    write a non-zero value to these bits, using either the FXRSTOR
  ;;    or LDMXCSR instructions, will result in a general-protection
  ;;    exception (#GP) being generated.

  '((:ie        0  1) ;; Invalid Operation Flag
    (:de        1  1) ;; Denormal Flag
    (:ze        2  1) ;; Divide-by-Zero Flag
    (:oe        3  1) ;; Overflow Flag
    (:ue        4  1) ;; Underflow Flag
    (:pe        5  1) ;; Precision Flag
    (:daz       6  1) ;; Denormals are Zeros
    (:im        7  1) ;; Invalid Operation Mask
    (:dm        8  1) ;; Denormal Mask
    (:zm        9  1) ;; Divide-by-Zero Mask
    (:om       10  1) ;; Overflow Mask
    (:um       11  1) ;; Underflow Mask
    (:pm       12  1) ;; Precision Mask
    (:rc       13  2) ;; Rounding Control
    (:fz       15  1) ;; Flush to Zero
    (:reserved 16 16) ;; Reserved bits
    ))

(defthm mxcsr-layout-ok
  (layout-constant-alistp *mxcsr-layout* 0 32)
  :rule-classes nil)

;; The constants defined by the following events (and NOT the events
;; themselves) will be redundant (in most cases) with those defined in
;; portcullis/sharp-dot-constants.  In that book, these constants have
;; been defined manually (mostly), as opposed to the table-driven
;; method here.  This should assure us just a bit more that our
;; constant definitions are okay.
(make-event (define-layout-constants *rflags-layout*))
(make-event (layout-names 'flg-names *rflags-layout*))
(make-event (define-layout-constants *fp-status-layout*))
(make-event (layout-names 'fp-status-names *fp-status-layout*))
(make-event (define-layout-constants *mxcsr-layout*))
(make-event (layout-names 'mxcsr-names *mxcsr-layout*))
(make-event (define-layout-constants *ia32_efer-layout*))
(make-event (layout-names 'ia32_efer-names *ia32_efer-layout*))
(make-event (define-layout-constants *cr0-layout*))
(make-event (layout-names 'cr0-names *cr0-layout*))
(make-event (define-layout-constants *cr3-layout*))
(make-event (layout-names 'cr3-names *cr3-layout*))
(make-event (define-layout-constants *cr4-layout*))
(make-event (layout-names 'cr4-names *cr4-layout*))

(defconst *cr8-trpl* 0)

(make-event (define-layout-constants *xcr0-layout*))
(make-event (layout-names 'xcr0-names *xcr0-layout*))

;; ======================================================================

;; Memory Management:

;; Segmentation:

;; Source: AMD Manual, Apr'16, Vol. 2, Section 4.8

;; User-level descriptors:

(defconst *code-segment-descriptor-layout*

  '((:limit15-0        0  16)  ;; Ignored in 64-bit mode
    (:base15-0         16 16)  ;; Ignored in 64-bit mode
    (:base23-16        32  8)  ;; Ignored in 64-bit mode
    (:a                40  1)  ;; Ignored in 64-bit mode
    (:r                41  1)  ;; Ignored in 64-bit mode
    (:c                42  1)
    (:msb-of-type      43  1)  ;; must be 1
    (:s                44  1)  ;; S = 1 in 64-bit mode (code/data segment)
    (:dpl              45  2)
    (:p                47  1)
    (:limit19-16       48  4)  ;; Ignored in 64-bit mode
    (:avl              52  1)  ;; Ignored in 64-bit mode
                               ;; As per AMD manuals, this is ignored
                               ;; in 64-bit mode but the Intel manuals
                               ;; say it's not.  We're following the
                               ;; Intel manuals.
    (:l                53  1)
    (:d                54  1)
    (:g                55  1)  ;; Ignored in 64-bit mode
                               ;; As per AMD manuals, this is ignored
                               ;; in 64-bit mode but the Intel manuals
                               ;; say it's not.  We're following the
                               ;; Intel manuals.
    (:base31-24        56  8)) ;; Ignored in 64-bit mode
  )

(defthm code-segment-descriptor-layout-ok
  (layout-constant-alistp *code-segment-descriptor-layout* 0 64)
  :rule-classes nil)

(defconst *code-segment-descriptor-attributes-layout*
  '((:a                0  1)
    (:r                1  1)
    (:c                2  1)
    (:msb-of-type      3  1) ;; must be 1
    (:s                4  1) ;; S = 1 in 64-bit mode
    (:dpl              5  2)
    (:p                7  1)
    (:avl              8  1)
    (:l                9  1)
    (:d               10  1)
    (:g               11  1)
    ))

(defthm code-segment-descriptor-attributes-layout-ok
  (layout-constant-alistp *code-segment-descriptor-attributes-layout* 0 16)
  :rule-classes nil)

(defconst *data-segment-descriptor-layout*

  '((:limit15-0        0  16)  ;; Ignored in 64-bit mode
    (:base15-0         16 16)  ;; Ignored in 64-bit mode
    (:base23-16        32  8)  ;; Ignored in 64-bit mode
    (:a                40  1)  ;; Ignored in 64-bit mode
    (:w                41  1)  ;; Ignored in 64-bit mode
    (:e                42  1)  ;; Ignored in 64-bit mode
    (:msb-of-type      43  1)  ;; must be 0
    (:s                44  1)  ;; S = 1 in 64-bit mode (code/data segment)
    (:dpl              45  2)  ;; Ignored in 64-bit mode
    (:p                47  1)  ;; !! NOT IGNORED: Segment present bit !!
    (:limit19-16       48  4)  ;; Ignored in 64-bit mode
    (:avl              52  1)
    (:l                53  1)  ;; L = 1 in 64-bit mode
    (:d/b              54  1)  ;; Ignored in 64-bit mode
    (:g                55  1)  ;; Ignored in 64-bit mode
    (:base31-24        56  8)) ;; Ignored in 64-bit mode
  )

(defthm data-segment-descriptor-layout-ok
  (layout-constant-alistp *data-segment-descriptor-layout* 0 64)
  :rule-classes nil)

(defconst *data-segment-descriptor-attributes-layout*
  '((:a                0  1)
    (:w                1  1)
    (:e                2  1)
    (:msb-of-type      3  1) ;; must be 0
    (:s                4  1) ;; S = 1 in 64-bit mode
    (:dpl              5  2)
    (:p                7  1)
    (:avl              8  1)
    (:l                9  1)
    (:d/b             10  1)
    (:g               11  1)
    ))

(defthm data-segment-descriptor-attributes-layout-ok
  (layout-constant-alistp *data-segment-descriptor-attributes-layout* 0 16)
  :rule-classes nil)

;; System-Segment descriptors (64-bit mode): Note that the following
;; layout constants are different in the 32-bit mode, or even the
;; compatibility mode.

(defconst *system-segment-descriptor-layout*

  '((:limit15-0        0  16)
    (:base15-0         16 16)
    (:base23-16        32  8)
    (:type             40  4)
    (:s                44  1) ;; S = 0 in 64-bit mode
    (:dpl              45  2)
    (:p                47  1)
    (:limit19-16       48  4)
    (:avl              52  1)
    (0                 53  2) ;; L and D/B bits are ignored.
    (:g                55  1)
    (:base31-24        56  8)
    (:base63-32        64 32)
    (0                 96  8)
    (:all-zeroes?     104  5) ;; Check whether these are all zeroes or
                              ;; not.
    (0                109  19)
    ))

(defthm system-segment-descriptor-layout-ok
  (layout-constant-alistp *system-segment-descriptor-layout* 0 128)
  :rule-classes nil)

(defconst *system-segment-descriptor-attributes-layout*
  '((:type             0  4)
    (:s                4  1) ;; S = 0 in 64-bit mode
    (:dpl              5  2)
    (:p                7  1)
    (:avl              8  1)
    (:g                9  1)
    ))

(defthm system-segment-descriptor-attributes-layout-ok
  (layout-constant-alistp *system-segment-descriptor-attributes-layout* 0 16)
  :rule-classes nil)

(defconst *call-gate-descriptor-layout*

  '((:offset15-0       0  16)
    (:selector         16 16)
    (0                 32  8)
    (:type             40  4)
    (:s                44  1) ;; S = 0 in 64-bit mode
    (:dpl              45  2)
    (:p                47  1)
    (:offset31-16      48 16)
    (:offset63-32      64 32)
    (0                 96  8)
    (:all-zeroes?      104 5) ;; Check whether these are all zeroes or
                              ;; not.
    (0                109 19)
    ))

(defthm call-gate-descriptor-layout-ok
  (layout-constant-alistp *call-gate-descriptor-layout* 0 128)
  :rule-classes nil)

(defconst *call-gate-descriptor-attributes-layout*
  '((:type             0  4)
    (:s                4  1)
    (:dpl              5  2)
    (:p                7  1)
    ))

(defthm call-gate-descriptor-attributes-layout-ok
  (layout-constant-alistp *call-gate-descriptor-attributes-layout* 0 16)
  :rule-classes nil)

(defconst *interrupt/trap-gate-descriptor-layout*

  '((:offset15-0       0  16)
    (:selector         16 16)
    (:ist              32  3)
    (0                 35  5)
    (:type             40  4)
    (:s                44  1) ;; S = 0 in 64-bit mode
    (:dpl              45  2)
    (:p                47  1)
    (:offset31-16      48 16)
    (:offset63-32      64 32)
    (0                 96  8)
    (:all-zeros?      104  5) ;; Check whether these are all zeroes or
                              ;; not.
    (0                109 19)
    ))

(defthm interrupt/trap-gate-descriptor-layout-ok
  (layout-constant-alistp *interrupt/trap-gate-descriptor-layout* 0 128)
  :rule-classes nil)

(defconst *interrupt/trap-gate-descriptor-attributes-layout*
  '((:ist              0  3)
    (:type             3  4)
    (:s                7  1)
    (:dpl              8  2)
    (:p               10  1)
    ))

(defthm interrupt/trap-gate-descriptor-attributes-layout-ok
  (layout-constant-alistp *interrupt/trap-gate-descriptor-attributes-layout* 0 16)
  :rule-classes nil)

; AMD manual, Apr'16, Vol. 2, Figure 4-8
(defconst *gdtr/idtr-layout*
  '((:base-addr    0 64) ;; Segment Base Address
    (:limit       64 16) ;; Segment Limit
    ))

(defthm gdtr/idtr-layout-ok
  (layout-constant-alistp *gdtr/idtr-layout* 0 80)
  :rule-classes nil)

; Paging (Intel manual, Mar'17, Vol. 3A, Tables 4-14 through 4-19, Figure 4-11):

(defconst *ia32e-page-tables-layout*

  ;; This constant defines the common bit-fields for page table
  ;; structure entries.

  ;; The field reference-addr refers to the 40 bits in a paging
  ;; structure entry that contain the address of the inferior paging
  ;; structure. If this paging entry maps a page (PS=1) instead of
  ;; referencing an inferior structure (PS=0), do not use the
  ;; reference-addr field to access the address of the page. Use
  ;; dedicated macros (e.g., those defined in context of
  ;; *ia32e-pdpte-1GB-page-layout*) in that case, because unlike
  ;; reference-addr, the address of the mapped page is contained in
  ;; different-sized fields for each paging structure.

  '((:p              0  1)  ;; Page present
    (:r/w            1  1)  ;; Read/Write
    (:u/s            2  1)  ;; User/supervisor
    (:pwt            3  1)  ;; Page-level Write-Through
    (:pcd            4  1)  ;; Page-level Cache-Disable
    (:a              5  1)  ;; Accessed
    (:d              6  1)  ;; Dirty
    (:ps             7  1)  ;; Page size
    (0               8  4)  ;; Ignored
    (:reference-addr 12 40) ;; Address of inferior paging table
    (0               52 11) ;; Ignored and/or Reserved
    (:xd             63 1)  ;; Execute Disable
    ))

(defthm ia32e-page-tables-layout-ok
  (layout-constant-alistp *ia32e-page-tables-layout* 0 64)
  :rule-classes nil)

(make-event (define-layout-constants *ia32e-page-tables-layout*))
(make-event (layout-names 'ia32e-page-tables-names *ia32e-page-tables-layout*))

(defconst *ia32e-pml4e-layout*
  '((:pml4e-p        0  1)   ;; Page present (must be 1)
    (:pml4e-r/w      1  1)   ;; Read/write
    (:pml4e-u/s      2  1)   ;; User/supervisor
    (:pml4e-pwt      3  1)   ;; Page-level Write-Through
    (:pml4e-pcd      4  1)   ;; Page-level Cache-Disable
    (:pml4e-a        5  1)   ;; Accessed (whether this entry has been
                             ;; used for LA translation)
    (0               6  1)   ;; Ignored
    (:pml4e-ps       7  1)   ;; Page size (Must be zero)
    (0               8  4)   ;; Ignored
    (:pml4e-pdpt     12 40)  ;; Address of page-directory pointer
                             ;; table
    (0               52  11) ;; Ignored and/or Reserved
    (:pml4e-xd       63  1)) ;; If IA32_EFER.NXE = 1, Execute disable;
                             ;; otherwise 0 (reserved)
  )

(defthm ia32e-pml4e-layout-ok
  (layout-constant-alistp *ia32e-pml4e-layout* 0 64)
  :rule-classes nil)

(make-event (define-layout-constants *ia32e-pml4e-layout*))
(make-event (layout-names 'ia32e-pml4e-names
                          *ia32e-pml4e-layout*))

(defconst *ia32e-pdpte-1GB-page-layout*
  '((:pdpte-p        0  1)   ;; Page present (must be 1)
    (:pdpte-r/w      1  1)   ;; Read/write
    (:pdpte-u/s      2  1)   ;; User/supervisor
    (:pdpte-pwt      3  1)   ;; Page-level Write-Through
    (:pdpte-pcd      4  1)   ;; Page-level Cache-Disable
    (:pdpte-a        5  1)   ;; Accessed (whether this entry has been
                             ;; used for LA translation)
    (:pdpte-d        6  1)   ;; Dirty (whether s/w has written to the
                             ;; 1 GB page referenced by this entry)
    (:pdpte-ps       7  1)   ;; Page size (Must be 1 for 1GB pages)
    (:pdpte-g        8  1)   ;; Global translation
    (0               9  3)   ;; Ignored
    (:pdpte-pat      12 1)   ;; PAT
    (0               13 17)  ;; Reserved
    (:pdpte-page     30 22)  ;; Address of 1 GB page
    (0               52 11)  ;; Ignored and/or Reserved
    (:pdpte-xd       63  1))  ;; If IA32_EFER.NXE = 1, Execute disable;
                              ;; otherwise 0 (reserved)
  )

(defthm ia32e-pdpte-1GB-page-layout-ok
  (layout-constant-alistp *ia32e-pdpte-1GB-page-layout* 0 64)
  :rule-classes nil)

(make-event (define-layout-constants *ia32e-pdpte-1GB-page-layout*))
(make-event (layout-names 'ia32e-pdpte-1GB-page-names
                          *ia32e-pdpte-1GB-page-layout*))

(defconst *ia32e-pdpte-pg-dir-layout*
  '((:pdpte-p        0  1)   ;; Page present (must be 1)
    (:pdpte-r/w      1  1)   ;; Read/write
    (:pdpte-u/s      2  1)   ;; User/supervisor
    (:pdpte-pwt      3  1)   ;; Page-level Write-Through
    (:pdpte-pcd      4  1)   ;; Page-level Cache-Disable
    (:pdpte-a        5  1)   ;; Accessed (whether this entry has been
                             ;; used for LA translation)
    (0               6  1)   ;; Ignored
    (:pdpte-ps       7  1)   ;; Page size (Must be 0)
    (0               8  4)   ;; Ignored
    (:pdpte-pd      12 40)   ;; Physical addres of 4-K aligned PD
                             ;; referenced by this entry
    (0              52  11)  ;; Ignored and/or Reserved
    (:pdpte-xd      63  1))  ;; If IA32_EFER.NXE = 1, Execute disable;
                             ;; otherwise 0 (reserved)
  )

(defthm ia32e-pdpte-pg-dir-layout-ok
  (layout-constant-alistp *ia32e-pdpte-pg-dir-layout* 0 64)
  :rule-classes nil)

(make-event (define-layout-constants *ia32e-pdpte-pg-dir-layout*))
(make-event (layout-names 'ia32e-pdpte-pg-dir-names
                          *ia32e-pdpte-pg-dir-layout*))

(defconst *ia32e-pde-2MB-page-layout*
  '((:pde-p        0  1)    ;; Page present (must be 1)
    (:pde-r/w      1  1)    ;; Read/write
    (:pde-u/s      2  1)    ;; User/supervisor
    (:pde-pwt      3  1)    ;; Page-level Write-Through
    (:pde-pcd      4  1)    ;; Page-level Cache-Disable
    (:pde-a        5  1)    ;; Accessed
    (:pde-d        6  1)    ;; Dirty
    (:pde-ps       7  1)    ;; Page size (Must be 1 for 2MB pages)
    (:pde-g        8  1)    ;; Global translation
    (0             9  3)    ;; Ignored
    (:pde-pat      12 1)    ;; PAT
    (0             13 8)    ;; Reserved
    (:pde-page     21 31)   ;; Physical addres of the 2MB page
                            ;; referenced by this entry
    (0             52 11)   ;; Ignored and/or Reserved
    (:pde-xd       63  1))  ;; If IA32_EFER.NXE = 1, Execute
                            ;; disable; otherwise 0 (reserved)
  )

(defthm ia32e-pde-2MB-page-layout-ok
  (layout-constant-alistp *ia32e-pde-2MB-page-layout* 0 64)
  :rule-classes nil)

(make-event (define-layout-constants *ia32e-pde-2MB-page-layout*))
(make-event (layout-names 'ia32e-pde-2MB-page-names
                          *ia32e-pde-2MB-page-layout*))

(defconst *ia32e-pde-pg-table-layout*
  '((:pde-p        0  1)    ;; Page present (must be 1)
    (:pde-r/w      1  1)    ;; Read/write
    (:pde-u/s      2  1)    ;; User/supervisor
    (:pde-pwt      3  1)    ;; Page-level Write-Through
    (:pde-pcd      4  1)    ;; Page-level Cache-Disable
    (:pde-a        5  1)    ;; Accessed
    (0             6  1)    ;; Ignored
    (:pde-ps       7  1)    ;; Page size (Must be 0)
    (0             8  4)    ;; Ignored
    (:pde-pt       12 40)   ;; Physical addres of the 4K-aligned
                            ;; page table referenced by this entry
    (0             52 11)   ;; Ignored and/or Reserved
    (:pde-xd       63  1))  ;; If IA32_EFER.NXE = 1, Execute
                            ;; disable; otherwise 0 (reserved)
  )

(defthm ia32e-pde-pg-table-layout-ok
  (layout-constant-alistp *ia32e-pde-pg-table-layout* 0 64)
  :rule-classes nil)

(make-event (define-layout-constants *ia32e-pde-pg-table-layout*))
(make-event (layout-names 'ia32e-pde-pg-table-names
                          *ia32e-pde-pg-table-layout*))


(defconst *ia32e-pte-4K-page-layout*
  '((:pte-p        0  1)    ;; Page present (must be 1)
    (:pte-r/w      1  1)    ;; Read/write
    (:pte-u/s      2  1)    ;; User/supervisor
    (:pte-pwt      3  1)    ;; Page-level Write-Through
    (:pte-pcd      4  1)    ;; Page-level Cache-Disable
    (:pte-a        5  1)    ;; Accessed
    (:pte-d        6  1)    ;; Dirty
    (:pte-pat      7  1)    ;; PAT
    (:pte-g        8  1)    ;; Global translation
    (0             9  3)    ;; Ignored
    (:pte-page    12 40)    ;; Physical address of the 4K page
                            ;; referenced by this entry
    (0            52  11)   ;; Ignored
    (:pte-xd      63  1))   ;; If IA32_EFER.NXE = 1, Execute
                            ;; disable; otherwise 0 (reserved)
  )

(defthm ia32e-pte-4k-page-layout-ok
  (layout-constant-alistp *ia32e-pte-4k-page-layout* 0 64)
  :rule-classes nil)

(make-event (define-layout-constants *ia32e-pte-4k-page-layout*))
(make-event (layout-names 'ia32e-pte-4k-page-names
                          *ia32e-pte-4k-page-layout*))


;; Some parts of page tables are consistent across paging modes ---
;; the page present, read/write, user/supervisor, accessed, dirty,
;; page size, and execute disable bits.

;; (defconst *32-bit-page-tables*
;;   ;; Incomplete, with variable parts pretended to be 0
;;   '((:p        0  1)    ; page present
;;     (:r-w      1  1)    ; read/write
;;     (:u-s      2  1)    ; user/supervisor
;;     (0         3  2)    ; 0?
;;     (:accessed 5  1)    ; accessed
;;     (:dirty    6  1)    ; dirty
;;     (:p-s      7  1)    ; page size
;;     (0         8  23)))
; 0?

;; ======================================================================

;; Slicing operations:

;; RFLAGS:

(defmacro rflags-slice (flg rflags)
  ;; Top 32 bits of RFLAGS are reserved.  So we put the width of
  ;; RFLAGS = 32 instead of 64.
  (slice flg rflags 32 *rflags-layout*))

(defmacro !rflags-slice (flg val rflags)
  ;; Top 32 bits of RFLAGS are reserved.  So we put the width of
  ;; RFLAGS = 32 instead of 64.
  (!slice flg val rflags 32 *rflags-layout*))

(defmacro fp-status-slice (flg fp-status)
  (slice flg fp-status 16 *fp-status-layout*))

(defmacro !fp-status-slice (flg val fp-status)
  (!slice flg val fp-status 16 *fp-status-layout*))

(defmacro mxcsr-slice (flg mxcsr)
  (slice flg mxcsr
         32
         *mxcsr-layout*))

(defmacro !mxcsr-slice (flg val mxcsr)
  (!slice flg val mxcsr
          32
          *mxcsr-layout*))

(defmacro ia32_efer-slice (flg ia32_efer)
  (slice flg ia32_efer
         ;; 64
         12 ;; Top bits are reserved.  A lesser value here avoids
            ;; bignum creation.
         *ia32_efer-layout*))

(defmacro !ia32_efer-slice (flg val ia32_efer)
  (!slice flg val ia32_efer
          ;; 64
          12 ;; Top bits are reserved.  A lesser value here avoids
             ;; bignum creation.
          *ia32_efer-layout*))

(defmacro cr0-slice (flg cr0)
  (slice flg cr0 32 *cr0-layout*))

(defmacro !cr0-slice (flg val cr0)
  (!slice flg val cr0 32 *cr0-layout*))

(defmacro cr3-slice (flg cr3)
  (slice flg cr3 64 *cr3-layout*))

(defmacro !cr3-slice (flg val cr3)
  (!slice flg val cr3 64 *cr3-layout*))

(defmacro cr4-slice (flg cr4)
  (slice flg cr4 ;; 64
         22      ;; Top bits are reserved.  A lesser value here avoids
                 ;; bignum creation.
         *cr4-layout*))

(defmacro !cr4-slice (flg val cr4)
  (!slice flg val cr4 ;; 64
          22          ;; Top bits are reserved. A lesser value here avoids
                      ;; bignum creation.
          *cr4-layout*))

(defmacro hidden-seg-reg-layout-slice (flg segment-selector-layout)
  (slice flg segment-selector-layout 112 *hidden-segment-register-layout*))

(defmacro !hidden-seg-reg-layout-slice (flg val segment-selector-layout)
  (!slice flg val segment-selector-layout 112 *hidden-segment-register-layout*))

(defmacro seg-sel-layout-slice (flg segment-selector-layout)
  (slice flg segment-selector-layout 16 *segment-selector-layout*))

(defmacro !seg-sel-layout-slice (flg val segment-selector-layout)
  (!slice flg val segment-selector-layout 16 *segment-selector-layout*))

(defmacro code-segment-descriptor-layout-slice (flg layout)
  (slice flg layout 64 *code-segment-descriptor-layout*))

(defmacro !code-segment-descriptor-layout-slice (flg val layout)
  (!slice flg val layout 64 *code-segment-descriptor-layout*))

(defmacro code-segment-descriptor-attributes-layout-slice (flg layout)
  (slice flg layout 16 *code-segment-descriptor-attributes-layout*))

(defmacro !code-segment-descriptor-attributes-layout-slice (flg val layout)
  (!slice flg val layout 16 *code-segment-descriptor-attributes-layout*))

(defmacro data-segment-descriptor-layout-slice (flg layout)
  (slice flg layout 64 *data-segment-descriptor-layout*))

(defmacro !data-segment-descriptor-layout-slice (flg val layout)
  (!slice flg val layout 64 *data-segment-descriptor-layout*))

(defmacro data-segment-descriptor-attributes-layout-slice (flg layout)
  (slice flg layout 16 *data-segment-descriptor-attributes-layout*))

(defmacro !data-segment-descriptor-attributes-layout-slice (flg val layout)
  (!slice flg val layout 16 *data-segment-descriptor-attributes-layout*))

(defmacro system-segment-descriptor-layout-slice (flg layout)
  (slice flg layout 128 *system-segment-descriptor-layout*))

(defmacro !system-segment-descriptor-layout-slice (flg val layout)
  (!slice flg val layout 128 *system-segment-descriptor-layout*))

(defmacro system-segment-descriptor-attributes-layout-slice (flg layout)
  (slice flg layout 16 *system-segment-descriptor-attributes-layout*))

(defmacro !system-segment-descriptor-attributes-layout-slice (flg val layout)
  (!slice flg val layout 16 *system-segment-descriptor-attributes-layout*))

(defmacro call-gate-descriptor-layout-slice (flg layout)
  (slice flg layout 128 *call-gate-descriptor-layout*))

(defmacro !call-gate-descriptor-layout-slice (flg val layout)
  (!slice flg val layout 128 *call-gate-descriptor-layout*))

(defmacro call-gate-descriptor-attributes-layout-slice (flg layout)
  (slice flg layout 16 *call-gate-descriptor-attributes-layout*))

(defmacro !call-gate-descriptor-attributes-layout-slice (flg val layout)
  (!slice flg val layout 16 *call-gate-descriptor-attributes-layout*))

(defmacro interrupt/trap-gate-descriptor-layout-slice (flg layout)
  (slice flg layout 128 *interrupt/trap-gate-descriptor-layout*))

(defmacro !interrupt/trap-gate-descriptor-layout-slice (flg val layout)
  (!slice flg val layout 128 *interrupt/trap-gate-descriptor-layout*))

(defmacro interrupt/trap-gate-descriptor-attributes-layout-slice (flg layout)
  (slice flg layout 16 *interrupt/trap-gate-descriptor-attributes-layout*))

(defmacro !interrupt/trap-gate-descriptor-attributes-layout-slice (flg val layout)
  (!slice flg val layout 16 *interrupt/trap-gate-descriptor-attributes-layout*))

(defmacro gdtr/idtr-layout-slice (flg layout)
  (slice flg layout 128 *gdtr/idtr-layout*))

(defmacro !gdtr/idtr-layout-slice (flg val layout)
  (!slice flg val layout 128 *gdtr/idtr-layout*))

(defmacro ia32e-page-tables-slice (flg ia32e-page-tables)
  (slice flg ia32e-page-tables 64 *ia32e-page-tables-layout*))

(defmacro !ia32e-page-tables-slice (flg val ia32e-page-tables)
  (!slice flg val ia32e-page-tables 64 *ia32e-page-tables-layout*))

(defmacro ia32e-pml4e-slice (flg ia32e-pml4e)
  (slice flg ia32e-pml4e 64 *ia32e-pml4e-layout*))

(defmacro !ia32e-pml4e-slice (flg val ia32e-pml4e)
  (!slice flg val ia32e-pml4e 64 *ia32e-pml4e-layout*))

(defmacro ia32e-pdpte-1GB-page-slice (flg ia32e-pdpte-1GB-page)
  (slice flg ia32e-pdpte-1GB-page 64 *ia32e-pdpte-1GB-page-layout*))

(defmacro !ia32e-pdpte-1GB-page-slice (flg val ia32e-pdpte-1GB-page)
  (!slice flg val ia32e-pdpte-1GB-page 64 *ia32e-pdpte-1GB-page-layout*))

(defmacro ia32e-pdpte-pg-dir-slice (flg ia32e-pdpte-pg-dir)
  (slice flg ia32e-pdpte-pg-dir 64 *ia32e-pdpte-pg-dir-layout*))

(defmacro !ia32e-pdpte-pg-dir-slice (flg val ia32e-pdpte-pg-dir)
  (!slice flg val ia32e-pdpte-pg-dir 64 *ia32e-pdpte-pg-dir-layout*))

(defmacro ia32e-pde-2MB-page-slice (flg ia32e-pde-2MB-page)
  (slice flg ia32e-pde-2MB-page 64 *ia32e-pde-2MB-page-layout*))

(defmacro !ia32e-pde-2MB-page-slice (flg val ia32e-pde-2MB-page)
  (!slice flg val ia32e-pde-2MB-page 64 *ia32e-pde-2MB-page-layout*))

(defmacro ia32e-pde-pg-table-slice (flg ia32e-pde-pg-table)
  (slice flg ia32e-pde-pg-table 64 *ia32e-pde-pg-table-layout*))

(defmacro !ia32e-pde-pg-table-slice (flg val ia32e-pde-pg-table)
  (!slice flg val ia32e-pde-pg-table 64 *ia32e-pde-pg-table-layout*))

(defmacro ia32e-pte-4K-page-slice (flg ia32e-pte-4K-page)
  (slice flg ia32e-pte-4K-page 64 *ia32e-pte-4K-page-layout*))

(defmacro !ia32e-pte-4K-page-slice (flg val ia32e-pte-4K-page)
  (!slice flg val ia32e-pte-4K-page 64 *ia32e-pte-4K-page-layout*))

;; ======================================================================
