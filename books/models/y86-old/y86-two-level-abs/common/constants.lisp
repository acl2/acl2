; constants.lisp                             Warren A. Hunt ,Jr.

; X86 specific constants.  Where possible, these are meant to exactly
; follow the numbers used by X86 binary representations.

(in-package "ACL2")

(include-book "std/util/bstar"    :dir :system)
(include-book "misc-events")
(include-book "operations")

; ======================================================================

(defconst *b-size*   8)  ; Byte
(defconst *w-size*  16)  ; Word
(defconst *d-size*  32)  ; Double
(defconst *q-size*  64)  ; Quad

(defconst *a-size*  32)  ; Physical address size
(defconst *m-size*  32)  ; Machine size

; ======================================================================

; Memory-model related constants:

;  Memory size

(defconst *physical-address-size* 32)
(defconst *mem-size-in-bytes*  (expt 2 *physical-address-size*))
(defconst *mem-size-in-words*  (floor *mem-size-in-bytes* 2))
(defconst *mem-size-in-dwords* (floor *mem-size-in-bytes* 4))
(defconst *mem-size-in-qwords* (floor *mem-size-in-bytes* 8))

(defconst *default-mem-value*

; If we change this default memory value, we also need to change the
; :initially value in the mem-array field of our x86-32 stobj.

  0)

(defconst *initial-mem-array-pages* 100) ; arbitrary

(defconst *2^x-byte-pseudo-page*
  ;; Log size of pseudo page; i.e.; for 16MB pseudo pages, this is 24
  24)

(defconst *pseudo-page-size-in-bytes*
  ;; Pseudo page size
  (expt 2 *2^x-byte-pseudo-page*))

(defconst *initial-mem-array-length*
  ;; Initial allocation of pseudo pages
  (* *initial-mem-array-pages*
     *pseudo-page-size-in-bytes*))

(defconst *mem-table-size*
  ;; Size of table for address-to-pseudo-page translation
  (floor *mem-size-in-bytes*
         *pseudo-page-size-in-bytes*))

(defconst *non-zero-mem-table-entry-size*
  ;; Log size of the number of pseudo pages
  (- *physical-address-size*
     *2^x-byte-pseudo-page*))

(defconst *mem-array-resize-factor*
  ;; Growth factor used when additional pseudo pages are required
  2)

; ======================================================================

; Some "useful" constants.  We define these because the ACL2
; definition mechanism does not evaluate and "fold" constants.


(defconst *2^0*       (expt 2  0))
(defconst *2^1*       (expt 2  1))
(defconst *2^2*       (expt 2  2))
(defconst *2^3*       (expt 2  3))
(defconst *2^4*       (expt 2  4))
(defconst *2^5*       (expt 2  5))
(defconst *2^6*       (expt 2  6))
(defconst *2^7*       (expt 2  7))
(defconst *2^8*       (expt 2  8))
(defconst *2^16*      (expt 2 16))
(defconst *2^24*      (expt 2 24))
(defconst *2^27*      (expt 2 27))
(defconst *2^30*      (expt 2 30))
(defconst *2^32*      (expt 2 32))

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

; X86-specific information.

; These numberings are specific to what is used by the X86 processor
; family.

(defconst *x86-32-reg-numbers*
  '((:eax . 0)  (%eax . 0)
    (:ecx . 1)  (%ecx . 1)
    (:edx . 2)  (%edx . 2)
    (:ebx . 3)  (%ebx . 3)
    (:esp . 4)  (%esp . 4)
    (:ebp . 5)  (%ebp . 5)
    (:esi . 6)  (%esi . 6)
    (:edi . 7)  (%edi . 7)))

(defun x86-rton (name)
  (declare (xargs :guard (symbolp name)))
  (cdr (assoc name *x86-32-reg-numbers*)))

(defmacro rtn (name)
  `(x86-rton ,name))

; X86-specific registers and their sub-fields

(defconst *x86-eflags*
  '((:cf    0  1)  ; Carry Flag
    (1      1  1)  ; 1
    (:pf    2  1)  ; Parity Flag
    (0      3  1)  ; 0
    (:af    4  1)  ; Auxiliary-carry Flag
    (0      5  1)  ; 0
    (:zf    6  1)  ; Zero Flag
    (:sf    7  1)  ; Sign Flag
    (:tf    8  1)  ; Trap Flag
    (:if    9  1)  ; Interrupt-enable Flag
    (:df   10  1)  ; Direction Flag
    (:of   11  1)  ; Overflow Flag
    (:iopl 12  2)  ; I/O Privilege Level
    (:nt   14  1)  ; Nested Task
    (0     15  1)  ; 0
    (:rf   16  1)  ; Resume Flag
    (:vm   17  1)  ; Virtual-8086 Mode
    (:ac   18  1)  ; Alignment Check
    ;; Pentium and follow-on processors include additional flags
    (:vif  19  1)  ; Virtual Interrupt Flag
    (:vip  20  1)  ; Virtual Interrupt Pending
    (:id   21  1)  ; ID flag
    (0     22 10)  ; 0
    ))

(defthm x86-eflags-table-ok
  (reg-info-alistp *x86-eflags* 0 *m-size*)
  :rule-classes nil)

(defmacro x86-eflags (flg eflags)
  (x86-reg-slice flg eflags *x86-eflags*))

(defmacro x86-update-eflags (flg val eflags)
  (x86-update-reg-slice flg val eflags *x86-eflags*))


(defconst *x86-segment-selector*
  '((:rpl   0  2)  ; Requestor Privilege Level (RPL)
    (:ti    2  1)  ; Table Indicator (0 = GDT, 1 = LDT)
    (:index 3 13)  ; Index of descriptor in GDT or LDT
    ))

(defthm x86-segment-selector-ok
  (reg-info-alistp *x86-segment-selector* 0 *w-size*)
  :rule-classes nil)

(defmacro x86-segment-selector (flg eflags)
  (x86-reg-slice flg eflags *x86-segment-selector*))

(defmacro x86-update-segment-selector (flg val eflags)
  (x86-update-reg-slice flg val eflags *x86-segment-selector*))


(defconst *gdtr-offset* 0)
(defconst *idtr-offset* 1)

(defconst *x86-system-table-register-selector*
  '((:limit 0 16)
    (:base 16 32)))

;; Fix constant (expt 2 48)!!!
(defthm x86-system-table-register-selector-ok
  (reg-info-alistp *x86-system-table-register-selector* 0 (expt 2 48))
  :rule-classes nil)

(defmacro x86-system-table-register-selector (flg eflags)
  (x86-reg-slice flg eflags
                 *x86-system-table-register-selector*))

(defmacro x86-update-system-table-register-selector (flg val eflags)
  (x86-update-reg-slice flg val eflags
                        *x86-system-table-register-selector*))


(defconst *x86-seg-descriptor-0-fields*
  '((:base-15_0        0 16) ; Segment Base Address (bits 15..0)
    (:seg-limit-15_0  16 16) ; Segment Limit (bits 15..0)
    ))

(defthm x86-seg-descriptor-0-fields-ok
  (reg-info-alistp *x86-seg-descriptor-0-fields* 0 *m-size*)
  :rule-classes nil)

(defmacro x86-seg-descriptor-field-0 (flg seg-field)
  (x86-reg-slice flg seg-field *x86-seg-descriptor-0-fields*))

(defmacro x86-update-seg-descriptor-field-0 (flg val seg-field)
  (x86-update-reg-slice flg val seg-field *x86-seg-descriptor-0-fields*))


(defconst *x86-seg-descriptor-1-fields*
  '((:base-23_16       0  8) ; Segment Base Address (bits 23..16)
    (:accessed         8  1) ; Accessed
    (:w/r              9  1) ; read-Write (for data); execute-Read (for code)
    (:e/c             10  1) ; Expand-down (for data); Conforming (for code)
    (:data/code       11  1) ; Data (0) segment or Code (1) segment
    (:system          12  1) ; System (0) segment or code/data (1) segment, effects
                             ; meaning of 4 bits above.
    (:dpl             13  2) ; Descriptor Privilege Level (0 -- OS, ... 3 -- user)
    (:present         15  1) ; descriptor Present
    (:seg-limit-19_16 16  4) ; Segment Limit (bits 19..16)
    (:avaiable        20  1) ; Available
    (0                21  1) ; 0
    (:d/b             22  1) ; Default-operation size (1 for 32-bit, 0 for 16-bit)
    (:granularity     23  1) ; Granularity
    (:base-31_24      24  8) ; Segment Base Address (bits 31..24)
    ))

(defthm x86-seg-descriptor-1-fields-ok
  (reg-info-alistp *x86-seg-descriptor-1-fields* 0 *m-size*)
  :rule-classes nil)

(defmacro x86-seg-descriptor-field-1 (flg seg-field)
  (x86-reg-slice flg seg-field *x86-seg-descriptor-1-fields*))

(defmacro x86-update-seg-descriptor-field-1 (flg val seg-field)
  (x86-update-reg-slice flg val seg-field *x86-seg-descriptor-1-fields*))


(defconst *x86-cr0*
  '((:pe    0  1)  ; Protection Enable
    (:mp    1  1)  ; Monitor coProcessor
    (:em    2  1)  ; Emulation Mode (for coprocessors)
    (:ts    3  1)  ; Task Switched
    (:et    4  1)  ; Extension Type
    (:ne    5  1)  ; Numeric Error
    (0      6 10)  ; 0
    (:wp   16  1)  ; Write Protect
    (0     17  1)  ; 0
    (:am   18  1)  ; Alignment Mask
    (0     19 10)  ; 0
    (:nw   29  1)  ; Not Write-through
    (:cd   30  1)  ; Cache Disable
    (:pg   31  1)  ; PaGing enable
    ))

(defthm x86-cr0-table-ok
  (reg-info-alistp *x86-cr0* 0 *m-size*)
  :rule-classes nil)

(defmacro x86-cr0 (flg cr0)
  (x86-reg-slice flg cr0 *x86-cr0*))

(defmacro x86-update-cr0 (flg val cr0)
  (x86-update-reg-slice flg val cr0 *x86-cr0*))


(defconst *x86-cr3*
  '((0      0  3)  ; 0
    (:pwt   3  1)  ; Page-Llevel Writes Tranparent
    (:pcd   4  1)  ; Page-level Cache Disable
    (0      5  7)  ; 0
    (:pdb  12 20)  ; Page Directory Base
    ))

(defthm x86-cr0-table-ok
  (reg-info-alistp *x86-cr0* 0 *m-size*)
  :rule-classes nil)

(defmacro x86-cr3 (flg cr3)
  (x86-reg-slice flg cr3 *x86-cr3*))

(defmacro x86-update-cr3 (flg val cr3)
  (x86-update-reg-slice flg val cr3 *x86-cr3*))


(defconst *x86-virtual-addr*
  '((:poffset  0 12) ; Offset into page
    (:pte     12 10) ; Page-table index
    (:pde     22 10) ; Page-directory index
    ))

(defthm x86-virtual-address-table-ok
  (reg-info-alistp *x86-virtual-addr* 0 *m-size*)
  :rule-classes nil)

(defmacro x86-virtual-addr-slice (flg addr)
  (x86-reg-slice flg addr *x86-virtual-addr*))

(defmacro x86-update-virtual-addr-slice (flg addr val)
  (x86-update-reg-slice flg val addr *x86-virtual-addr*))


(defconst *x86-page-directory-entry*
  '((:present         0  1) ; Present
    (:read/write      1  1) ; Read/Write
    (:user/supervisor 2  1) ; User/Supervisor
    (:write-through   3  1) ; Write-through
    (:cache-disabled  4  1) ; Cache disabled
    (:accessed        5  1) ; Accessed
    (0                6  1) ; Reserved (set to 0)
    (:page-size       7  1) ; Page-size (0 indicated 4K bytes)
    (:global-table    8  1) ; Global table (ingored)
    (:available       9  3) ; Available for OS programmer
    (:pg-tb-bs-addr  12 20) ; Page-table-base address
    ))

(defthm x86-page-directory-entry-ok
  (reg-info-alistp *x86-page-directory-entry* 0 *m-size*)
  :rule-classes nil)

(defmacro x86-page-directory-slice (flg addr)
  (x86-reg-slice flg addr *x86-page-directory-entry*))

(defmacro x86-update-page-directory-slice (flg addr val)
  (x86-update-reg-slice flg val addr *x86-page-directory-entry*))


(defconst *x86-page-table-entry*
  '((:present         0  1) ; Present
    (:read/write      1  1) ; Read/Write
    (:user/supervisor 2  1) ; User/Supervisor
    (:write-through   3  1) ; Write-through
    (:cache-disabled  4  1) ; Cache disabled
    (:accessed        5  1) ; Accessed
    (:dirty           6  1) ; Dirty
    (0                7  1) ; Reserved, set to 0
    (:global-table    8  1) ; Global table (ingored)
    (:available       9  3) ; Available for OS programmer
    (:pg-base-addr   12 20) ; Base address of page
    ))

(defthm x86-page-table-entry-ok
  (reg-info-alistp *x86-page-directory-entry* 0 *m-size*)
  :rule-classes nil)

(defmacro x86-page-table-slice (flg addr)
  (x86-reg-slice flg addr *x86-page-directory-entry*))

(defmacro x86-update-page-table-slice (flg addr val)
  (x86-update-reg-slice flg val addr *x86-page-directory-entry*))


; ACL2 X86 model-specific information.

; We are trying to write a model of the X86.  Below, we have attempted
; to identify the "top-level" X86 registers.  We are building several
; models on top of this state representation.

; We use much of this information for our Y86 model.  The Y86 is a
; subset of the X86, and we reuse the X86 representation of the state
; for our Y86 model; however, the Y86 just has three 1-bit, flag (:sf
; :zf :of) registers.  Even so, our Y86 model uses the corresponding
; three bits from the 32-bit X86 EFLAGS register.

; The structure our 32-bit X86 state is a list (actually array) of
; values.  Thus, :eip has address 0.  These positions and addresses
; are independent of the indicies used internally by the X86.

(defconst *m86-32-reg-names*
  ;; 32-bit GP registers, :eax "address" is 0
  `(:eax :ecx :edx :ebx :esp :ebp :esi :edi))

(defconst *m86-32-segment-reg-names*
  ;; 32-bit segment register, :es "address is 0
  `(:es :cs :ss :ds :fs :gs))

(defconst *m86-32-gdtr-idtr-names*
  ;; 48-bit system-table (GDTR and IDTR) registers
  '(:gdtr :idtr))

(defconst *m86-32-ldtr-tr-names*
  ;; 16-bit system-segment (Task Register and LDTR) registers
  '(:ldtr :tr))

(defconst *m86-32-control-reg-names*
  '(:msw                                      ;; Control status register
    :cr0 :cr1 :cr2 :cr3 :cr4 :cr5 :cr6 :cr7   ;; Control registers
    :cr8 :cr9 :cr10 :cr11 :cr12 :cr13 :cr14 :cr15
    :xcr0))

(defconst *m86-32-debug-reg-names*
  '(:dr0 :dr1 :dr2 :dr3 :dr4 :dr5 :dr6 :dr7)) ;; Debug registers

(defconst *m86-32-fp-reg-names*
  `(:fp0 :fp1 :fp2 :fp3 :fp4 :fp5 :fp6 :fp7   ;; Floating-point, 80-bit registers
    :fp-cntl :fp-status :fp-tag :fp-opcode    ;; 16-bit FP status registers
    :fp-last-inst :fp-last-data))             ;; 48-bit last-instruction registers

(defconst *m86-32-xmm-reg-names*
  `(:mxcsr                                   ;; 32-bit status register
    :xmm0 :xmm1 :xmm2 :xmm3                  ;; 128-bit data registers
    :xmm0 :xmm5 :xmm6 :xmm7))

(defconst *m86-32-model-specific-registers*
  `(;; This is a complex internal X86 state.
    ;; At this point, we do not model the X86 MSRs.
    ))


(defconst *m86-32-reg-names-len*          (len *m86-32-reg-names*))
(defconst *m86-32-segment-reg-names-len*  (len *m86-32-segment-reg-names*))
(defconst *m86-32-gdtr-idtr-names-len*    (len *m86-32-gdtr-idtr-names*))
(defconst *m86-32-ldtr-tr-names-len*      (len *m86-32-ldtr-tr-names*))

(defconst *m86-32-control-reg-names-len*  (len *m86-32-control-reg-names*))
(defconst *m86-32-debug-reg-names-len*    (len *m86-32-debug-reg-names*))
(defconst *m86-fp-reg-names-len*          (len *m86-32-fp-reg-names*))
(defconst *m86-32-xmm-reg-names-len*      (len *m86-32-xmm-reg-names*))


(defun m86-32-reg-pos (name state-names n)
  (declare (xargs :guard (and (eqlablep name) (natp n))))
  (if (atom state-names)
      0
    (if (eql name (car state-names))
        n
      (m86-32-reg-pos name (cdr state-names) (1+ n)))))

(defconst *mr-eax* (m86-32-reg-pos :eax *m86-32-reg-names* 0))
(defconst *mr-ecx* (m86-32-reg-pos :ecx *m86-32-reg-names* 0))
(defconst *mr-edx* (m86-32-reg-pos :edx *m86-32-reg-names* 0))
(defconst *mr-ebx* (m86-32-reg-pos :ebx *m86-32-reg-names* 0))
(defconst *mr-esp* (m86-32-reg-pos :esp *m86-32-reg-names* 0))
(defconst *mr-ebp* (m86-32-reg-pos :ebp *m86-32-reg-names* 0))
(defconst *mr-esi* (m86-32-reg-pos :esi *m86-32-reg-names* 0))
(defconst *mr-edi* (m86-32-reg-pos :edi *m86-32-reg-names* 0))


(defun m86-reg-pos1 (reg reg-names n)
  (declare (xargs :guard (and (symbolp reg)
                              (symbol-listp reg-names)
                              (natp n))))
  (if (atom reg-names)
      (or (cw "m86-reg-pos1:  Name not found:  ~p0.~%" reg) 0)
    (if (eq (car reg-names) reg)
        n
      (m86-reg-pos1 reg (cdr reg-names) (1+ n)))))

(defthm natp-m86-reg-pos1
  (implies (natp n)
           (and (integerp (m86-reg-pos1 reg reg-names n))
                (<= 0 (m86-reg-pos1 reg reg-names n))))
  :rule-classes :type-prescription)

(defun m86-reg-pos (reg reg-names)
  (declare (xargs :guard (and (symbolp reg)
                              (symbol-listp reg-names))))
  (m86-reg-pos1 reg reg-names 0))

(defthm natp-m86-reg-pos
  (and (integerp (m86-reg-pos reg reg-names))
       (<= 0 (m86-reg-pos reg reg-names)))
  :rule-classes :type-prescription)

(in-theory (disable m86-reg-pos))

(defconst *cr0* (m86-reg-pos :cr0 *m86-32-control-reg-names*))
(defconst *cr1* (m86-reg-pos :cr1 *m86-32-control-reg-names*))
(defconst *cr2* (m86-reg-pos :cr2 *m86-32-control-reg-names*))
(defconst *cr3* (m86-reg-pos :cr3 *m86-32-control-reg-names*))
(defconst *cr4* (m86-reg-pos :cr4 *m86-32-control-reg-names*))
