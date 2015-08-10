
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; y86.lisp
;;;
;;; Here is a model of the 32-bit Y86 ISA.
;;;
;;; Based on work by Warren Hunt
;;;
;;; See memory/memory.lisp and memory/memory-low.lisp for how to
;;; get back Alan's fast and raw memory model.  Search for
;;; "fast and raw".
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "../Utilities/records")
(include-book "../Utilities/misc")
(include-book "std/util/bstar" :dir :system)

(include-book "../Memory/memory")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Guards

(defun y86-register-guard (st)
  (and
   ;; General-purpose registers (so are esp, ebp, but these have
   ;; special purposes as well w.r.t. the stack)
   (n32p (g :eax st))
   (n32p (g :ecx st))
   (n32p (g :edx st))
   (n32p (g :ebx st))
   (n32p (g :esi st))
   (n32p (g :edi st))
   ;; "extra" registers
   (n32p (g :imme1 st))
   (n32p (g :valu1 st))
   ;; Stack pointer
   (n32p (g :esp st))
   ;; Frame pointer
   (n32p (g :ebp st))
   ;; Instruction pointer
   (n32p (g :eip st))
   ;; Control registers - named to match X86, though X86 has further
   ;; such registers

   ;; cr0 - bits to control processor state (eg. mmu mode), many of
   ;; the Intel controls here will not be implemented

   ;; cr3 - base of the page table hierarchy
   (n32p (g :cr0 st))
   (n32p (g :cr3 st))
   ;; System-level flags (not yet used...)
   (n32p (g :eflags st))))

(defun y86-flags-guard (st)
  (and (n01p (g :f-cf  st)) ; new
       (n01p (g :f-zf  st))
       (n01p (g :f-sf  st))
       (n01p (g :f-of  st))))

(defun y86-memory-guard (st)
  (memoryp (g :mem st)))

(defun y86-supervisor-guard (st)
  (and (n01p (g :supervisor-mode st))
       (n32p (g :user-esp        st))
       (n32p (g :sys-esp         st))
       (n32p (g :user-eip        st))
       (n32p (g :sys-eip         st))))

(defun y86-misc-guard (st)
  (n32p (g :zteps st)))

(defun y86-p (st)
  ;; The "normal" guard incuding the logical story for memory.  Cannot
  ;; be used when executing via a concrete state, since that uses the
  ;; "raw" memory model.
  (and (y86-register-guard st)
       (y86-flags-guard st)
       (y86-memory-guard st)
       (y86-supervisor-guard st)
       (y86-misc-guard st)))

(defun y86-raw-p (st)
  ;; The guard to use when executing via a concrete state.  Does not
  ;; include the logical story for the memory.
  (and (y86-register-guard st)
       (y86-flags-guard st)
       ;;(y86-memory-guard st)
       (y86-supervisor-guard st)
       (y86-misc-guard st)))

;;; These y86-p-implies-parts-are-xxx-p type theorems should all be
;;; generated automatically.  Hopefully these will be sufficient.

(defthm y86-p-fc
  ;; copied and pasted from def's in y86.lisp
  (implies (y86-p s)
           (and
            ;; General-purpose registers (so are esp, ebp, but these have
            ;; special purposes as well w.r.t. the stack)
            (n32p (g :eax s))
            (n32p (g :ecx s))
            (n32p (g :edx s))
            (n32p (g :ebx s))
            (n32p (g :esi s))
            (n32p (g :edi s))
            ;; "extra" registers
            (n32p (g :imme1 s))
            (n32p (g :valu1 s))
            ;; Stack pointer
            (n32p (g :esp s))
            ;; Frame pointer
            (n32p (g :ebp s))
            ;; Instruction pointer
            (n32p (g :eip s))
            ;; Control registers - named to match X86, though X86 has further
            ;; such registers

            ;; cr0 - bits to control processor state (eg. mmu mode), many of
            ;; the Intel controls here will not be implemented

            ;; cr3 - base of the page table hierarchy
            (n32p (g :cr0 s))
            (n32p (g :cr3 s))
            ;; System-level flags (not yet used...)
            (n32p (g :eflags s))
            ;; flags
            (n01p (g :f-cf  s))        ; new
            (n01p (g :f-zf  s))
            (n01p (g :f-sf  s))
            (n01p (g :f-of  s))
            ;; memory
            (memoryp (g :mem s))
            ;; supervisor mode stuff
            (n01p (g :supervisor-mode s))
            (n32p (g :user-esp        s))
            (n32p (g :sys-esp         s))
            (n32p (g :user-eip        s))
            (n32p (g :sys-eip         s))
            ;; not used here, but included just in case
            (n32p (g :zteps s))))
  :rule-classes :forward-chaining)

;;; !!! The need to enable good-32-address-p indicates the need for a
;;; forward-chaining rule or maybe that good-32-address-p is a bad
;;; predicate.
(defthm |(y86-p (w32 addr val s))|
  (implies (and (y86-p s)
                (good-32-address-p addr s)
                (n32p val))
           (y86-p (w32 addr val s)))
  :hints (("Goal" :in-theory (enable good-32-address-p))))

(in-theory (disable y86-register-guard
                    y86-flags-guard
                    y86-supervisor-guard
                    y86-misc-guard
                    y86-p
                    y86-raw-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Helper functions

(defun rA (x)
  ;; Extract the 4-bit register number for rA.
  (logand #xF (bits-04 x 1)))

(defun rB (x)
  ;; Extract the 4-bit register number for rB.
  (logand #xF (bits-04 x 0)))

(defun NumR (x)
  ;; Convert number to register name.
  (case x
    (0  :eax)
    (1  :ecx)
    (2  :edx)
    (3  :ebx)
    (4  :esp)
    (5  :ebp)
    (6  :esi)
    (7  :edi)
    (8  :imme1)  ; new
    (10 :valu1)  ; new
    (otherwise :eax)))

(defun regVal (x st)
  (g (NumR x) st))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; handling page faults

;;; What do we want here?

;;; Given the current way we jump into here, re-entering the faulting
;;; instruction would require mutual-recursion.

(defstub handle-page-fault (st) t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; "plain" Y86 instructions

(defun y86-nop (st)
  (b* ((eip    (g :eip st))
       (eip+1  (n32+ 1 eip))
       (st (s :eip eip+1 st)))
      st))

(defun y86-halt (st)
  st)

(defun y86-rrmovl (st)
  (b* ((eip    (g :eip st))
       (eip+1  (n32+ 1 eip))
       ((when (not (good-08-address-p eip+1 st)))
        (handle-page-fault st))
       (reg    (r08 eip+1 st))
       (eip+2  (n32+ 2 eip))
       (ValA   (regVal (rA reg) st))
       (NameB  (NumR (rB reg)))
       (st (s :eip eip+2 st))
       (st (s NameB ValA st)))
      st))

(defun y86-irmovl (st)
  (b* ((eip    (g :eip st))
       (eip+1  (n32+ 1 eip))
       ((when (not (good-08-address-p eip+1 st)))
        (handle-page-fault st))
       (reg    (r08 eip+1 st))
       (eip+2  (n32+ 2 eip))
       (NameB  (NumR (rB reg)))
       ((when (not (good-32-address-p eip+2 st)))
        (handle-page-fault st))
       (imm    (r32 eip+2 st))
       (eip+6  (n32+ 6 eip))
       (st (s :eip eip+6 st))
       (st (s NameB imm st)))
      st))

(defun y86-rmmovl (st)
  (b* ((eip    (g :eip st))
       (eip+1  (n32+ 1 eip))
       ((when (not (good-08-address-p eip+1 st)))
        (handle-page-fault st))
       (reg    (r08 eip+1 st))
       (ValA   (regVal (rA reg) st))
       (ValB   (regVal (rB reg) st))
       (eip+2  (n32+ 2 eip))
       ((when (not (good-32-address-p eip+2 st)))
        (handle-page-fault st))
       (disp   (r32 eip+2 st))
       (eA     (n32+ ValB disp))
       ((when (not (good-32-address-p eA st)))
        (handle-page-fault st))
       (st (w32 eA ValA st))
       (eip+6  (n32+ 6 eip))
       (st (s :eip eip+6 st)))
      st))

(defun y86-mrmovl (st)
  (b* ((eip    (g :eip st))
       (eip+1  (n32+ 1 eip))
       ((when (not (good-08-address-p eip+1 st)))
        (handle-page-fault st))
       (reg    (r08 eip+1 st))
       (NameA  (NumR (rA reg)))
       (ValB   (regVal (rB reg) st))
       (eip+2  (n32+ 2 eip))
       ((when (not (good-32-address-p eip+2 st)))
        (handle-page-fault st))
       (disp   (r32 eip+2 st))
       (eA     (n32+ ValB disp))
       ((when (not (good-32-address-p eA st)))
        (handle-page-fault st))
       (Mval   (r32 eA st))
       (st (s NameA Mval st))
       (eip+6  (n32+ 6 eip))
       (st (s :eip eip+6 st)))
      st))

(defun cf (x y)
  (if (= x y)
      0
    1))

(defun zf (x)
  (if (= x 0)
      1
    0))

(defun sf (x)
  (if (< x 0)
      1
    0))

(defun of (x y)
  (if (= x y)
      0
    1))

(defun subl-cf (CrA CrB)
  (if (< CrB CrA)
      1
    0))

(defun sall-cf (shift CrB)
  (if (logbitp (+ 32 (- shift)) CrB) ; last bit shifted off
      1
    0))

(defun sall-of (CrB)
  (if (xor (logbitp 31 CrB) (logbitp 30 CrB)) ; xor of top two bits
      1
    0))

(defun shrl-cf (shift CrB)
  (if (logbitp (+ -1 shift) CrB) ; last bit shifted off
      1
    0))

(defun shrl-of (CrB)
  (if (logbitp 31 CrB) ; top bit
      1
    0))

(defun unpack (x)
  x)

(defthm |(n01p (cf x y))|
  (n01p (cf x y)))

(defthm |(n01p (zf x))|
  (n01p (zf x)))

(defthm |(n01p (of x y))|
  (n01p (of x y)))

(defthm |(n01p (sf x))|
  (n01p (sf x)))

(defthm |(n01p (subl-cf x y))|
  (n01p (subl-cf x y)))

(defthm |(n01p (sall-cf x y))|
  (n01p (sall-cf x y)))

(defthm |(n01p (sall-of x))|
  (n01p (sall-of x)))

(defthm |(n01p (shrl-cf x y))|
  (n01p (shrl-cf x y)))

(defthm |(n01p (shrl-of x))|
  (n01p (shrl-of x)))

(defthm |(unpack (nat-to-boolean (cf x y))))|
  (equal (unpack (nat-to-boolean (cf x y)))
         (not (= x y))))

(defthm |(unpack (nat-to-boolean (zf x)))|
  (equal (unpack (nat-to-boolean (zf x)))
         (= x 0)))

(defthm |(unpack (nat-to-boolean (sf x)))|
  (equal (unpack (nat-to-boolean (sf x)))
         (< x 0)))

(defthm |(unpack (nat-to-boolean (of x y)))|
  (equal (unpack (nat-to-boolean (of x y)))
         (not (= x y))))

(defthm |(unpack (nat-to-boolean (subl-cf x y)))|
  (equal (unpack (nat-to-boolean (subl-cf x y)))
         (< y x)))

(defthm |(unpack (nat-to-boolean (sall-cf shift CrB)))|
  (equal (unpack (nat-to-boolean (sall-cf shift CrB)))
         (logbitp (+ 32 (- shift)) CrB)))

(defthm |(unpack (nat-to-boolean (sall-of CrB)))|
  (equal (unpack (nat-to-boolean (sall-of CrB)))
         (xor (logbitp 31 CrB) (logbitp 30 CrB))))

(defthm |(unpack (nat-to-boolean (shrl-cf shift CrB)))|
  (equal (unpack (nat-to-boolean (shrl-cf shift CrB)))
         (logbitp (+ -1 shift) CrB)))

(defthm |(unpack (nat-to-boolean (shrl-of CrB)))|
  (equal (unpack (nat-to-boolean (shrl-of CrB)))
         (logbitp 31 CrB)))

(defun op2 (function CrA CrB cf)
  ;; Returns 32-bit answer, carry flag, zero flag, sign flag, and overflow flag
  (case function
        ;; addl
         (0 (b* ((nat-32-bit-sum (n32+ CrA CrB))
                 (int-32-bit-sum (n32-to-i32 nat-32-bit-sum))
                 (nat-sum        (+ CrA CrB))
                 (CrA-int        (n32-to-i32 CrA))
                 (CrB-int        (n32-to-i32 CrB))
                 (integer-sum    (+ CrA-int CrB-int)))
                (mv nat-32-bit-sum
                    (cf nat-32-bit-sum nat-sum)
                    (zf nat-32-bit-sum)
                    (sf int-32-bit-sum)
                    (of int-32-bit-sum integer-sum))))
         ;; subl
         (1 (b* ((CrA-int               (n32-to-i32 CrA))
                 (CrB-int               (n32-to-i32 CrB))
                 (minus-CrA-int         (- CrA-int))
                 (minus-CrA-nat         (n32 minus-CrA-int))
                 (integer-difference    (+ minus-CrA-int CrB-int))
                 (nat-32-bit-difference (n32+ minus-CrA-nat CrB))
                 (int-32-bit-difference (n32-to-i32 nat-32-bit-difference)))
                (mv nat-32-bit-difference
                    (subl-cf CrA CrB)
                    (zf nat-32-bit-difference)
                    (sf int-32-bit-difference)
                    (of int-32-bit-difference integer-difference))))
         ;; andl
         (2 (b* ((result     (n32 (logand CrA CrB)))
                 (int-result (n32-to-i32 result)))
                (mv result
                    0
                    (zf result)
                    (sf int-result)
                    0)))
         ;; xorl
         (3 (b* ((result     (n32 (logxor CrA CrB)))
                 (int-result (n32-to-i32 result)))
                (mv result
                    0
                    (zf result)
                    (sf int-result)
                    0)))
         ;; adcl
         (4 (b* ((cf (unpack cf))
                 (nat-32-bit-sum (n32+ (n32+ CrA CrB)
                                       (if cf 1 0)))
                 (int-32-bit-sum (n32-to-i32 nat-32-bit-sum))
                 (nat-sum        (+ (+ CrA CrB)
                                    (if cf 1 0)))
                 (CrA-int        (n32-to-i32 CrA))
                 (CrB-int        (n32-to-i32 CrB))
                 (integer-sum    (+ (+ CrA-int CrB-int)
                                    (if cf 1 0))))
                (mv nat-32-bit-sum
                    (cf nat-32-bit-sum nat-sum)
                    (zf nat-32-bit-sum)
                    (sf int-32-bit-sum)
                    (of int-32-bit-sum integer-sum))))
         ;; cmpl
         (5 (b* ((CrA-int               (n32-to-i32 CrA))
                 (CrB-int               (n32-to-i32 CrB))
                 (minus-CrA-int         (- CrA-int))
                 (minus-CrA-nat         (n32 minus-CrA-int))
                 (integer-difference    (+ minus-CrA-int CrB-int))
                 (nat-32-bit-difference (n32+ minus-CrA-nat CrB))
                 (int-32-bit-difference (n32-to-i32 nat-32-bit-difference)))
                (mv CrB
                    (subl-cf CrA CrB)
                    (zf nat-32-bit-difference)
                    (sf int-32-bit-difference)
                    (of int-32-bit-difference integer-difference))))
         ;; orl
         (6 (b* ((result     (n32 (logior CrA CrB)))
                 (int-result (n32-to-i32 result)))
                (mv result
                    0
                    (zf result)
                    (sf int-result)
                    0)))
         ;; sall
         ;; N.B. Gives wrong result for shift=0.  All flags should
         ;; be unchanged.  Also, overflow flag is only defined for
         ;; 1 bit shifts.
         (7 (b* ((shift (logand (1- (expt 2 5)) CrA))
                 (CrB-int (n32-to-i32 CrB))
                 (nat-shifted (ash CrB-int shift))
                 (integer-shifted (ash (n32-to-i32 CrB) shift)))
                (mv nat-shifted
                    (sall-cf shift CrB)
                    (zf nat-shifted)
                    (sf integer-shifted)
                    (sall-of CrB))))
         ;; shrl
         ;; N.B. Gives wrong result for shift=0.  All flags should
         ;; be unchanged.  Also, overflow flag is only defined for
         ;; 1 bit shifts.
         (8 (b* ((shift           (logand (1- (expt 2 5)) CrA))
                 (nat-shifted     (ash CrB (- shift)))
                 (integer-shifted (ash (n32-to-i32 CrB) (- shift))))
                (mv nat-shifted
                    (shrl-cf shift CrB)
                    (zf nat-shifted)
                    (sf integer-shifted)
                    (shrl-of CrB))))
         (otherwise
          (mv 0 0 0 0 0))))

(defun y86-op (st function)
  (b* ((eip    (g :eip st))
       (eip+1  (n32+ eip 1))
       ((when (not (good-08-address-p eip+1 st)))
        (handle-page-fault st))
       (reg    (r08 eip+1 st))
       (eip+2  (n32+ 2 eip))
       (ValA   (regVal (rA reg) st))
       (NameB  (NumR (rB reg)))
       (ValB   (regVal (rB reg) st))
       (cf (nat-to-boolean (g :f-cf st)))
       (st (s :eip eip+2 st))
       ((mv result cf zf sf of)
        (op2 function ValA ValB cf))
       (st (s NameB result st))
       (st (s :f-cf cf st))
       (st (s :f-zf zf st))
       (st (s :f-sf sf st))
       (st (s :f-of of st)))
      st))

(defun jump-p (function st)
  (let ((cf (nat-to-boolean (g :f-cf st)))
        (zf (nat-to-boolean (g :f-zf st)))
        (sf (nat-to-boolean (g :f-sf st)))
        (of (nat-to-boolean (g :f-of st))))
    (case function
      ;; jmp
      (0 t)
      ;; jle
      (1 (or (xor (unpack sf) (unpack of)) (unpack zf)))
      ;; jl
      (2 (xor (unpack sf) (unpack of)))
      ;; je
      (3 (unpack zf))
      ;; jne
      (4 (not (unpack zf)))
      ;; jge
      (5 (not (xor (unpack sf) (unpack of))))
      ;; jg
      (6 (and (not (xor (unpack sf) (unpack of))) (not (unpack zf))))
      ;; jb
      (7 (unpack cf))
      ;; jbe
      (8 (or (unpack cf) (unpack zf)))
      (otherwise nil))))

;;; we make jumps relative, rather than absolute as before
(defun y86-jXX (st function)
  (b* ((eip   (g :eip st))
       (eip+1 (n32+ 1 eip)))
      ;; If we do not jump, but would have page-faulted reading the jump
      ;; address, do we fault here, or wait till the next instruction
      ;; (which must page-fault also)?  Does this matter?
      (if (jump-p function st)
          (b* (((when (not (good-32-address-p eip+1 st)))
                (handle-page-fault st))
               (offset (r32 eip+1 st))
               (dest (n32+ (g :eip st)
                           (n32-to-i32 offset)))
               (st (s :eip dest st)))
              st)
        (b* ((eip+5  (n32+ 5 eip))
             (st (s :eip eip+5 st)))
            st))))

(defun y86-call (st)
  (b* ((eip    (g :eip st))
       (eip+1  (n32+ 1 eip))
       ((when (not (good-32-address-p eip+1 st)))
        (handle-page-fault st))
       (offset   (r32 eip+1 st))
       (dest (n32+ (g :eip st)
                   (n32-to-i32 offset)))
       (esp    (g :esp st))
       (eip+5  (n32+ 5 eip))
       (esp-4  (n32+ -4 esp))
       ((when (not (good-32-address-p esp-4 st)))
        (handle-page-fault st))
       (st (w32 esp-4 eip+5 st))
       (st (s :eip dest st))
       (st (s :esp esp-4 st)))
      st))

(defun y86-ret (st)
  (b* ((esp    (g :esp st))
       ((when (not (good-32-address-p esp st)))
        (handle-page-fault st))
       (Mval   (r32 esp st))
       (esp+4  (n32+ 4 esp))
       (st (s :eip Mval st))
       (st (s :esp esp+4 st)))
      st))

(defun y86-pushl (st)
  (b* ((eip    (g :eip st))
       (eip+1  (n32+ 1 eip))
       ((when (not (good-08-address-p eip+1 st)))
        (handle-page-fault st))
       (reg    (r08 eip+1 st))
       (esp    (g :esp st))
       (eip+2  (n32+ 2 eip))
       (esp-4  (n32+ -4 esp))
       (ValA   (regVal (rA reg) st))
       ((when (not (good-32-address-p esp-4 st)))
        (handle-page-fault st))
       (st (w32 esp-4 ValA st))
       (st (s :eip eip+2 st))
       (st (s :esp esp-4 st)))
      st))

(defun y86-popl (st)
  (b* ((eip    (g :eip st))
       (eip+1  (n32+ eip 1))
       ((when (not (good-08-address-p eip+1 st)))
        (handle-page-fault st))
       (reg    (r08 eip+1 st))
       (esp    (g :esp st))
       ((when (not (good-32-address-p esp st)))
        (handle-page-fault st))
       (Mval   (r32 esp st))
       (esp+4  (n32+ 4 esp))
       (eip+2  (n32+ 2 eip))
       (NameA  (NumR (rA reg)))
       (st (s :eip eip+2 st))
       (st (s :esp esp+4 st))
       ;; Ordering is critical
       (st (s NameA Mval st)))
      st))

(defun y86-iaddl (st)
  (b* ((eip    (g :eip st))
       (eip+1  (n32+ eip 1))
       ((when (not (good-08-address-p eip+1 st)))
        (handle-page-fault st))
       (reg    (r08 eip+1 st))
       (eip+2  (n32+ 2 eip))
       (NameB  (NumR (rB reg)))
       (ValB   (regVal (rB reg) st))
       ((when (not (good-32-address-p eip+2 st)))
        (handle-page-fault st))
       (imm    (r32 eip+2 st))
       (eip+6  (n32+ 6 eip))
       (st (s :eip eip+6 st))
       (imm+B  (n32+ ValB imm))
       (st (s NameB imm+B st)))
      st))

(defun y86-leave (st)
  (b* ((eip    (g :eip st))
       (eip+1  (n32+ 1 eip))
       ;; rrmovl %ebp, %esp
       (esp    (g :ebp st))
       ;; popl %ebp
       ((when (not (good-32-address-p esp st)))
        (handle-page-fault st))
       (Mval   (r32 esp st))
       (esp+4  (n32+ 4 esp))
       (st (s :eip eip+1  st))
       (st (s :esp esp+4  st))
       (st (s :ebp Mval st)))
      st))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; "special" Y86 instructions

(defun y86-ex-svc (st function)
  (declare (ignore function))
  (b* ((st (s :supervisor-mode 1 st))
       (st (s :user-eip (g :eip st) st))
       (st (s :user-esp (g :esp st) st))
       (st (s :eip      (g :sys-eip st) st))
       (st (s :esp      (g :sys-esp st) st)))
      ;; And so on...
      st))

(defun y86-ex-function (st function)
  ;; Notice, for now, no charge for supervisor instructions
  (case function
    (0 ; Return to user mode
     (b* ((st (s :eip (g :eax st) st))
          (st (s :supervisor-mode 0 st)))
         st))
    (1 ; load system ESP
     (s :sys-esp  (g :eax st) st))
    (2 ; load user ESP
     (s :user-esp (g :eax st) st))
    (3 ; load system EIP
     (s :sys-eip  (g :eax st) st))
    (4 ; load user EIP
     (s :user-eip (g :eax st) st))
    ;; ...
    (otherwise st)))

(defun y86-svc (st function)
  (if (= 0 (g :supervisor-mode st))
      ;; supervisor call
      (y86-ex-svc st function)
    (y86-ex-function st function)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Step and Run

(defun y86-step (st)
  (b* ((eip         (g :eip st))
       ((when (not (good-08-address-p eip st)))
        (handle-page-fault st))
       (instruction (r08 eip st))
       (opcode      (bits-04 instruction 1))
       (function    (bits-04 instruction 0)))
      (case opcode

            (0                          ; nop
             (y86-nop st))

            (1                          ; halt
             (y86-halt st))

            (2                          ; rrmovl:  rA -> rB
             (y86-rrmovl st))

            (3                          ; irmovl:  imm -> rB
             (y86-irmovl st))

            (4                          ; rmmovl:  rA -> D(rB)
             (y86-rmmovl st))

            (5                          ; mrmovl:  D(rB), rA
             (y86-mrmovl st))

            (6                          ; OPl:  rA op rB -> rB
             (y86-op st function))

            (7                          ; jXX:  Dest -> eip
             (y86-jXX st function))

            (8                          ; call:  eip -> (--esp) ; Dest -> eip
             (y86-call st))

            (9                          ; ret:  (esp++) -> eip
             (y86-ret st))

            (10                         ; pushl:  rA -> (--esp)
             (y86-pushl st))

            (11                         ; popl:  (esp++) -> rA
             (y86-popl st))

            (12                         ; iaddl:  imm + rB -> rB
             (y86-iaddl st))

            (13                         ; leave:  ebp -> esp ; pop ebp
             (y86-leave st))

            (14                         ; unused
             st)

            (15                         ; supervisor instructions
             (y86-svc st function))

            (otherwise st))))

(defun y86 (st n)
  (declare (xargs :measure (acl2-count n)))
  (if (zp n)
      st
    (y86 (y86-step st) (1- n))))

(defthm |(y86-step st)|
  (implies (and (equal eip (g :eip st))
                (equal instruction (r08 eip st))
                (equal opcode (bits-04 instruction 1))
                (equal function (bits-04 instruction 0))
                (syntaxp (quotep opcode))
                (syntaxp (quotep function)))
           (equal (y86-step st)
                  (if (not (good-08-address-p eip st))
                      (handle-page-fault st)
                    (case opcode

                          (0            ; nop
                           (y86-nop st))

                          (1            ; halt
                           (y86-halt st))

                          (2            ; rrmovl:  rA -> rB
                           (y86-rrmovl st))

                          (3            ; irmovl:  imm -> rB
                           (y86-irmovl st))

                          (4            ; rmmovl:  rA -> D(rB)
                           (y86-rmmovl st))

                          (5            ; mrmovl:  D(rB), rA
                           (y86-mrmovl st))

                          (6            ; OPl:  rA op rB -> rB
                           (y86-op st function))

                          (7            ; jXX:  Dest -> eip
                           (y86-jXX st function))

                          (8     ; call:  eip -> (--esp) ; Dest -> eip
                           (y86-call st))

                          (9            ; ret:  (esp++) -> eip
                           (y86-ret st))

                          (10           ; pushl:  rA -> (--esp)
                           (y86-pushl st))

                          (11           ; popl:  (esp++) -> rA
                           (y86-popl st))

                          (12           ; iaddl:  imm + rB -> rB
                           (y86-iaddl st))

                          (13           ; leave:  ebp -> esp ; pop ebp
                           (y86-leave st))

                          (14           ; unused
                           st)

                          (15           ; supervisor instructions
                           (y86-svc st function))

                          (otherwise st))))))

(in-theory (disable y86-step
                    y86))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; We conclude with a couple utilities to make printing prettier

(defun update-regs-fn (args)
  (cond ((endp args)
         ;; shouldn't happen
         '())
        ((endp (cdr args))
         ;; regs to be updated
         (car args))
        (t
         ;; assume 2n+1 args
         (list 'S (car args) (cadr args)
               (update-regs-fn (cddr args))))))

(defmacro update-regs (&rest args)
  (update-regs-fn args))


(defun update-mem-fn (args)
  (cond ((endp args)
         ;; shouldn't happen
         '())
        ((endp (cdr args))
         ;; mem to be updated
         (car args))
        (t
         ;; assume 2n+1 args
         (list 'W32 (car args) (cadr args)
               (update-mem-fn (cddr args))))))

(defmacro update-mem (&rest args)
  (update-mem-fn args))



(defun untrans-update-regs-1 (term-list)
  (cond ((endp term-list)
         ;; shouldn't happen
         '())
        ((equal (fn-symb (caddr term-list))
                'S)
         (cons (car term-list)  ; field
               (cons (cadr term-list) ; value
                     (untrans-update-regs-1 (cdr (caddr term-list))))))
        (t
         term-list)))

(defun untrans-update-mem-1 (term-list)
  (cond ((endp term-list)
         ;; shouldn't happen
         '())
        ((equal (fn-symb (caddr term-list))
                'W32)
         (cons (car term-list)  ; field
               (cons (cadr term-list) ; value
                     (untrans-update-mem-1 (cdr (caddr term-list))))))
        (t
         term-list)))

(defun untrans-update-mem/regs (term world)
  (declare (ignore world))
  (cond ((equal (fn-symb term) 'S)
         (cons 'update-regs
               (untrans-update-regs-1 (cdr term))))
        ((equal (fn-symb term) 'W32)
         (cons 'update-mem
               (untrans-update-mem-1 (cdr term))))
        (t
         'NIL)))

(table user-defined-functions-table
       'untranslate-preprocess
       'untrans-update-mem/regs)
