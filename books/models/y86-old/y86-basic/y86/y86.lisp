
; y86.lisp                                    Warren A. Hunt, Jr.

; NOTES:  Semantics of MRMOVL changed from D(rB) -> rA to D(rA) -> rB.

(in-package "ACL2")

(include-book "std/util/bstar" :dir :system)

(include-book "../common/misc-events")
(include-book "../common/operations")
(include-book "../common/constants")

; Increase ACL2 memory to model full 2^32 byte memory.
(include-book "centaur/misc/memory-mgmt-logic" :dir :system)
(value-triple (set-max-mem (* 6 (expt 2 30))))

(local (include-book "centaur/gl/gl" :dir :system))
(include-book "../common/x86-state")

; We define a "classic" ACL2 instruction interpreter.
; First, we define the update functions for each instruction.
; Finally, we have a step function.

; Flag access and update functions.

(defun y86-of (eflags)
  (declare (xargs :guard (n32p eflags)))
  ;; We use X86 EFLAGS register, Overflow Flag: bit 11.
  (x86-eflags :of eflags))

(defthm integerp-y86-of
  (and (integerp (y86-of eflags))
       (<= 0 (y86-of eflags)))
  :rule-classes :type-prescription)

(defthm y86-of-less-than-2
  (< (y86-of eflags) 2)
  :rule-classes :linear)

(in-theory (disable y86-of))

(defun !y86-of (eflags bit)
  (declare (xargs :guard (and (n32p eflags) (n01p bit))))
  (x86-update-eflags :of bit eflags))

(defthm integerp-!y86-of
  (and (integerp (!y86-of eflags bit))
       (<= 0 (!y86-of eflags bit))))

(defthm !y86-of-less-than-expt-2-32
  (< (!y86-of eflags bit) 4294967296)
  :rule-classes :linear)

(in-theory (disable !y86-of))


(defun y86-sf (eflags)
  (declare (xargs :guard (n32p eflags)))
  ;; We use X86 EFLAGS register, Sign Flag: bit 7.
  (x86-eflags :sf eflags))

(defthm integerp-y86-sf
  (and (integerp (y86-sf eflags))
       (<= 0 (y86-sf eflags)))
  :rule-classes :type-prescription)

(defthm y86-sf-less-than-2
  (< (y86-sf eflags) 2)
  :rule-classes :linear)

(in-theory (disable y86-sf))

(defun !y86-sf (eflags bit)
  (declare (xargs :guard (and (n32p eflags) (n01p bit))))
  (x86-update-eflags :sf bit eflags))

(defthm !y86-sf-less-than-expt-2-32
  (< (!y86-sf eflags bit) 4294967296)
  :rule-classes :linear)

(defthm integerp-!y86-sf
  (and (integerp (!y86-sf eflags bit))
       (<= 0 (!y86-sf eflags bit)))
  :rule-classes :type-prescription)

(in-theory (disable !y86-sf))


(defun y86-zf (eflags)
  (declare (xargs :guard (n32p eflags)))
  ;; We use X86 EFLAGS register, Sign Flag: bit 6.
  (x86-eflags :zf eflags))

(defthm integerp-y86-zf
  (and (integerp (y86-zf eflags))
       (<= 0 (y86-zf eflags)))
    :rule-classes :type-prescription)

(defthm y86-zf-less-than-2
  (< (y86-zf eflags) 2)
  :rule-classes :linear)

(in-theory (disable y86-zf))

(defun !y86-zf (eflags bit)
  (declare (xargs :guard (and (n32p eflags) (n01p bit))))
  (x86-update-eflags :zf bit eflags))

(defthm integerp-!y86-zf
  (and (integerp (!y86-zf eflags bit))
       (<= 0 (!y86-zf eflags bit)))
  :rule-classes :type-prescription)

(defthm !y86-zf-less-than-expt-2-32
  (< (!y86-zf eflags bit) (expt 2 32))
  :rule-classes :linear)

(in-theory (disable !y86-zf))


(defun y86-condition (x86-32 condition)
  (declare (xargs :guard (and (natp condition)
                              (< condition 7))
                  :stobjs (x86-32)))
  (if (= condition 0)
      1 ;; Minor optimization
    (b* ((eflags (flg x86-32))
         (of (y86-of eflags))
         (sf (y86-sf eflags))
         (zf (y86-zf eflags)))
        (case condition
          ;; Yes
          ;; (0 1) ; See above
          ;; less-equal (le)
          (1 (logior (logxor sf of) zf))
          ;; less (l)
          (2 (logxor sf of))
          ;; equal (e,z)
          (3 zf)
          ;; not equal (ne,nz)
          (4 (n01 (lognot zf)))
          ;; greater-equal (ge)
          (5 (n01 (lognot (logxor sf of))))
          ;; greater (g)
          (6 (n01 (lognot (logior (logxor sf of) zf))))
          (t 0)))))

(defthm integerp-y86-condition
  (and (integerp (y86-condition x86-32 condition-index))
       (<= 0 (y86-condition x86-32 condition-index)))
  :rule-classes :type-prescription)

(defthm y86-condition-less
  (< (y86-condition x86-32 condition-index) 2)
  :rule-classes :linear)

(in-theory (disable y86-condition))


; The Y86 simulator

; Before we execute each instruction, we check to see that the entire
; instruction can be read and :EIP updated (and eventually stored)
; without breaking any addressing invariant (meaning what range of
; addresses can be stored in machine registers).  Generally, we don't
; allow reads and/or writes to memory to "wrap around" -- not that
; this doesn't make sense from a hardware perspective, but when
; programming with a system that include memory management it can't be
; relied on to work.

; Each instruction is defined individually, and afterwards, there is
; an instruction dispatch function.

(defund y86-halt (x86-32)
  (declare (xargs :guard t
                  :stobjs (x86-32)))
    (b* ((pc (eip x86-32)))
        (!ms (list :halt-at-location pc) x86-32)))


(defund y86-nop (x86-32)
  (declare (xargs :guard t
                  :stobjs (x86-32)))
  (b* ((pc (eip x86-32))

       ;; Memory Probe
       ((if (< *2^32-2* pc))
        (!ms (list :at-location pc
                   :instruction 'nop
                   :memory-probe nil)
             x86-32))

       ;; Update PC
       (x86-32 (!eip (+ pc 1) x86-32)))
      x86-32))


(defund y86-cmove (x86-32 condition)
  (declare (xargs :guard (and (natp condition)
                              (< condition 7))
                  :stobjs (x86-32)))
  (b* ((pc (eip x86-32))

       ;; Memory Probe
       ((if (< *2^32-3* pc))
        (!ms (list :at-location pc
                   :instruction 'cmove
                   :memory-probe nil)
             x86-32))

       ;; Decode registers
       (rA-rB (rm08 (+ pc 1) x86-32))
       (rB (n03 rA-rB))
       (rA (n03 (ash rA-rB -4)))
       (b3 (n01 (ash rA-rB -3)))
       (b7 (n01 (ash rA-rB -7)))

       ;; Register decoding problem?
       ((if (= (logior b3 b7) 1))
        (!ms (list :at-location pc
                   :instruction 'cmove
                   :with-condition condition
                   :b7 b7 :b3 b3
                   :ra rA :rb rB)
             x86-32))

       ;; Condition true?
       (move? (y86-condition x86-32 condition))

       ;; When condition true, update register B
       (x86-32 (if (= move? 1)
                   (!rgfi rB
                          (rgfi rA x86-32)
                          x86-32)
                 x86-32))
       ;; Update PC
       (x86-32 (!eip (+ pc 2) x86-32)))
      x86-32))


(defund y86-move-imm (x86-32 condition)
  (declare (xargs :guard (and (natp condition)
                              (< condition 7))
                  :stobjs (x86-32)))
  (b* ((pc (eip x86-32))

       ;; Memory Probe
       ((if (< *2^32-7* pc))
        (!ms (list :at-location pc
                   :instruction 'irmovl
                   :memory-probe nil)
             x86-32))

       ;; Decode registers
       (rA-rB (rm08 (+ pc 1) x86-32))
       (rB (n03 rA-rB))
       (b7-b3 (n05 (ash rA-rB -3)))

       ;; Register decoding problem?
       ((if (not (= b7-b3 #b11110)))
        (!ms (list :at-location pc
                   :instruction 'irmovl
                   :with-condition condition
                   :b7-b3 b7-b3
                   :rb rB)
             x86-32))

       ;; Condition true?  Y86 generalization
       (move? (y86-condition x86-32 condition))

       ;; When condition true, imm -> rb
       (x86-32 (if (= move? 1)
                   (!rgfi rB
                          (rm32 (+ pc 2) x86-32)
                          x86-32)
                 x86-32))
       ;; Update PC
       (x86-32 (!eip (+ pc 6) x86-32)))
      x86-32))

(defund y86-rA-to-mem-at-rb+D (x86-32)
  (declare (xargs :guard t
                  :stobjs (x86-32)))
  (b* ((pc (eip x86-32))

       ;; Memory Probe
       ((if (< *2^32-7* pc))
        (!ms (list :at-location pc
                   :instruction 'rmmovl
                   :memory-probe nil)
             x86-32))

       ;; Decode registers
       (rA-rB (rm08 (+ pc 1) x86-32))
       (rB (n03 rA-rB))
       (rA (n03 (ash rA-rB -4)))
       (b3 (n01 (ash rA-rB -3)))
       (b7 (n01 (ash rA-rB -7)))

       ;; Register decoding problem?
       ((if (or (= b7 1) (= b3 1)))
        (!ms (list :at-location pc
                   :instruction 'rmmovl
                   :b7 b7 :b3 b3
                   :ra rA :rb rB)
             x86-32))

       ;; ra -> D(rb)
       (disp (rm32 (+ pc 2) x86-32))
       (addr (n32+ (rgfi rb x86-32) disp))
       (rA-val (rgfi rA x86-32))
       (x86-32 (wm32 addr rA-val x86-32))
       ;; Update PC
       (x86-32 (!eip (+ pc 6) x86-32)))
      x86-32))

(defund y86-mem-at-rA+D-to-rB (x86-32)
  (declare (xargs :guard t
                  :stobjs (x86-32)))
  (b* ((pc (eip x86-32))

       ;; Memory Probe
       ((if (< *2^32-7* pc))
        (!ms (list :at-location pc
                   :instruction 'mrmovl
                   :memory-probe nil)
             x86-32))

       ;; Decode registers
       (rA-rB (rm08 (+ pc 1) x86-32))
       (rB (n03 rA-rB))
       (rA (n03 (ash rA-rB -4)))
       (b3 (n01 (ash rA-rB -3)))
       (b7 (n01 (ash rA-rB -7)))

       ;; Register decoding problem?
       ((if (or (= b7 1) (= b3 1)))
        (!ms (list :at-location pc
                   :instruction 'mrmovl
                   :b7 b7 :b3 b3
                   :ra rA :rb rB)
             x86-32))

       ;; D(rA) -> rB
       (disp (rm32 (+ pc 2) x86-32))
       (addr (n32+ (rgfi rA x86-32) disp))
       (mem-data (rm32 addr x86-32))
       (x86-32 (!rgfi rB mem-data x86-32))
       ;; Update PC
       (x86-32 (!eip (+ pc 6) x86-32)))
      x86-32))

(defund y86-ALU-results-store-flgs (zf sf of x86-32)
  (declare (xargs :guard (and (n01p zf)
                              (n01p sf)
                              (n01p of))
                  :stobjs (x86-32)))
  (b* ((eflags (flg x86-32))
       (eflags (!y86-zf eflags zf))
       (eflags (!y86-sf eflags sf))
       (eflags (!y86-of eflags of))
       (x86-32 (!flg eflags x86-32)))
      x86-32))

(defund y86-rA-xor-rB-to-rB (x86-32)
  (declare (xargs :guard t
                  :stobjs (x86-32)))
  (b* ((pc (eip x86-32))

       ;; Memory Probe
       ((if (< *2^32-3* pc))
        (!ms (list :at-location pc
                   :instruction 'xorl
                   :memory-probe nil)
             x86-32))

       ;; Decode registers
       (rA-rB (rm08 (+ pc 1) x86-32))
       (rB (n03 rA-rB))
       (rA (n03 (ash rA-rB -4)))
       (b3 (n01 (ash rA-rB -3)))
       (b7 (n01 (ash rA-rB -7)))

       ;; Register decoding problem?
       ((if (= (logior b3 b7) 1))
        (!ms (list :at-location pc
                   :instruction 'xorl
                   :b7 b7 :b3 b3
                   :ra rA :rb rB)
             x86-32))

       (rA-val (rgfi rA x86-32))
       (rB-val (rgfi rB x86-32))

       ;; Calculate result
       (result (logxor rA-val rB-val))
       (zf (if (= result 0) 1 0))
       (sf (if (< result (expt 2 31)) 0 1))
       (of 0)

       ;; Store results
       (x86-32 (!rgfi rB result x86-32))
       (x86-32 (y86-ALU-results-store-flgs zf sf of x86-32))

       ;; Update PC
       (x86-32 (!eip (+ pc 2) x86-32)))
      x86-32))

(defund y86-rA-and-rB-to-rB (x86-32)
  (declare (xargs :guard t
                  :stobjs (x86-32)))
  (b* ((pc (eip x86-32))

       ;; Memory Probe
       ((if (< *2^32-3* pc))
        (!ms (list :at-location pc
                   :instruction 'andl
                   :memory-probe nil)
             x86-32))

       ;; Decode registers
       (rA-rB (rm08 (+ pc 1) x86-32))
       (rB (n03 rA-rB))
       (rA (n03 (ash rA-rB -4)))
       (b3 (n01 (ash rA-rB -3)))
       (b7 (n01 (ash rA-rB -7)))

       ;; Register decoding problem?
       ((if (= (logior b3 b7) 1))
        (!ms (list :at-location pc
                   :instruction 'andl
                   :b7 b7 :b3 b3
                   :ra rA :rb rB)
             x86-32))

       (rA-val (rgfi rA x86-32))
       (rB-val (rgfi rB x86-32))

       ;; Calculate result
       (result (logand rA-val rB-val))
       (zf (if (= result 0) 1 0))
       (sf (if (< result (expt 2 31)) 0 1))
       (of 0)

       ;; Store results
       (x86-32 (!rgfi rB result x86-32))
       (x86-32 (y86-ALU-results-store-flgs zf sf of x86-32))

       ;; Update PC
       (x86-32 (!eip (+ pc 2) x86-32)))
      x86-32))

(defund y86-rA-+-rB-to-rB (x86-32)
  (declare (xargs :guard t
                  :stobjs (x86-32)))
  (b* ((pc (eip x86-32))

       ;; Memory Probe
       ((if (< *2^32-3* pc))
        (!ms (list :at-location pc
                   :instruction 'addl
                   :memory-probe nil)
             x86-32))

       ;; Decode registers
       (rA-rB (rm08 (+ pc 1) x86-32))
       (rB (n03 rA-rB))
       (rA (n03 (ash rA-rB -4)))
       (b3 (n01 (ash rA-rB -3)))
       (b7 (n01 (ash rA-rB -7)))

       ;; Register decoding problem?
       ((if (= (logior b3 b7) 1))
        (!ms (list :at-location pc
                   :instruction 'addl
                   :b7 b7 :b3 b3
                   :ra rA :rb rB)
             x86-32))

       (rA-val (rgfi rA x86-32))
       (rB-val (rgfi rB x86-32))

       ;; Calculate result
       (result (n32+ rA-val rB-val))
       (zf  (if (= result 0) 1 0))
       (sfr (< result (expt 2 31)))
       (sf  (if sfr 0 1))
       (sfa (< rA-val (expt 2 31)))
       (sfb (< rB-val (expt 2 31)))
       (of  (if (eq sfa sfb) ;; If equal sign, then all equal or overflow
                (if (eq sfr sfa) 0 1)
              0))

       ;; Store results
       (x86-32 (!rgfi rB result x86-32))
       (x86-32 (y86-ALU-results-store-flgs zf sf of x86-32))

       ;; Update PC
       (x86-32 (!eip (+ pc 2) x86-32)))
      x86-32))

(defund y86-rB---rA-to-rB (x86-32)
  (declare (xargs :guard t
                  :stobjs (x86-32)))
  (b* ((pc (eip x86-32))

       ;; Memory Probe
       ((if (< *2^32-3* pc))
        (!ms (list :at-location pc
                   :instruction 'subl
                   :memory-probe nil)
             x86-32))

       ;; Decode registers
       (rA-rB (rm08 (+ pc 1) x86-32))
       (rB (n03 rA-rB))
       (rA (n03 (ash rA-rB -4)))
       (b3 (n01 (ash rA-rB -3)))
       (b7 (n01 (ash rA-rB -7)))

       ;; Register decoding problem?
       ((if (= (logior b3 b7) 1))
        (!ms (list :at-location pc
                   :instruction 'subl
                   :b7 b7 :b3 b3
                   :ra rA :rb rB)
             x86-32))

       (rA-val (rgfi rA x86-32))
       (rB-val (rgfi rB x86-32))

       ;; Calculate result
       (rA-val-not (lognot rA-val)) ; Negate rA -- think about overflow flag!
       (rA-val-tc (n32+ rA-val-not 1))
       (result (n32+ rB-val rA-val-tc))
       (zf  (if (= result 0) 1 0))
       (sfr (< result (expt 2 31)))
       (sf  (if sfr 0 1))
       (sfa (< rA-val-tc (expt 2 31))) ; Using twos-complement or rA for test
       (sfb (< rB-val (expt 2 31)))
       (of  (if (eq sfa sfb) ;; If equal sign, then all equal or overflow
                (if (eq sfr sfa) 0 1)
              0))

       ;; Store results
       (x86-32 (!rgfi rB result x86-32))
       (x86-32 (y86-ALU-results-store-flgs zf sf of x86-32))

       ;; Update PC
       (x86-32 (!eip (+ pc 2) x86-32)))
      x86-32))

(defund y86-cjump (x86-32 condition)
  (declare (xargs :guard (and (natp condition)
                              (< condition 7))
                  :stobjs (x86-32)))
  (b* ((pc (eip x86-32))

       ;; Memory Probe
       ((if (< *2^32-6* pc))
        (!ms (list :at-location pc
                   :instruction 'cjump
                   :memory-probe nil)
             x86-32))

       ;; Condition true?
       (jump? (y86-condition x86-32 condition))

       ;; When condition true, update PC; otherwise, PC <- PC + 5
       (x86-32 (if (= jump? 1)
                   (!eip (rm32 (+ pc 1) x86-32) x86-32)
                 (!eip (+ pc 5) x86-32))))
      x86-32))

(defund y86-call (x86-32)
  (declare (xargs :guard t
                  :stobjs (x86-32)))
  (b* ((pc (eip x86-32))

       ;; Memory Probe
       ((if (< *2^32-6* pc))
        (!ms (list :at-location pc
                   :instruction 'call
                   :memory-probe nil)
             x86-32))

       ;; Note, new PC read from stack before stack updated because
       ;; current instruction might be inside the stack!
       (pc+5 (+ pc 5))
       (esp-4 (n32- (rgfi *mr-esp* x86-32) 4))
       (call-addr (rm32 (+ pc 1) x86-32))
       (x86-32 (wm32 esp-4 pc+5 x86-32))
       (x86-32 (!rgfi *mr-esp* esp-4 x86-32))

       ;; Update PC
       (x86-32 (!eip call-addr x86-32)))
      x86-32))

(defund y86-ret (x86-32)
  (declare (xargs :guard t
                  :stobjs (x86-32)))
  (b* (;; No Memory Probe because PC is replaced.
       ;; Get return address and update stack pointer
       (esp (rgfi *mr-esp* x86-32))
       (rtr-addr (rm32 esp x86-32))
       (x86-32 (!rgfi *mr-esp* (n32+ esp 4) x86-32))

       ;; Update PC
       (x86-32 (!eip rtr-addr x86-32)))
      x86-32))

(defund y86-pushl (x86-32)
  (declare (xargs :guard t
                  :stobjs (x86-32)))
  (b* ((pc (eip x86-32))

       ;; Memory Probe
       ((if (< *2^32-3* pc))
        (!ms (list :at-location pc
                   :instruction 'pushl
                   :memory-probe nil)
             x86-32))

       ;; Decode registers
       (rA-rB (rm08 (+ pc 1) x86-32))
       (rA (n03 (ash rA-rB -4)))
       (b3-b0 (n04 rA-rB))
       (b7 (n01 (ash rA-rB -7)))

       ;; Register decoding problem?
       ((if (or (= b7 1) (not (= b3-b0 #b1111))))
        (!ms (list :at-location pc
                   :instruction 'pushl
                   :b3-b0 b3-b0 :b7 b7
                   :ra rA)
             x86-32))

       (esp (rgfi *mr-esp* x86-32))
       (esp-4 (n32- esp 4))
       (valA (rgfi rA x86-32)) ; Read first, as it might be :esp!
       (x86-32 (!rgfi *mr-esp* esp-4 x86-32))
       (x86-32 (wm32 esp-4 valA x86-32))

       ;;  Update PC
       (x86-32 (!eip (+ pc 2) x86-32)))
      x86-32))

(defund y86-popl (x86-32)
  (declare (xargs :guard t
                  :stobjs (x86-32)))
  (b* ((pc (eip x86-32))

       ;; Memory Probe
       ((if (< *2^32-3* pc))
        (!ms (list :at-location pc
                   :instruction 'popl
                   :memory-probe nil)
             x86-32))

       ;; Decode registers
       (rA-rB (rm08 (+ pc 1) x86-32))
       (rA (n03 (ash rA-rB -4)))
       (b3-b0 (n04 rA-rB))
       (b7 (n01 (ash rA-rB -7)))

       ;; Register decoding problem?
       ((if (or (= b7 1) (not (= b3-b0 #b1111))))
        (!ms (list :at-location pc
                   :instruction 'popl
                   :b3-b0 b3-b0 :b7 b7
                   :ra rA)
             x86-32))

       ;; Ordering is critical when :esp is target, if POPL needs to
       ;; overwrite the contents of the :esp register.
       (esp (rgfi *mr-esp* x86-32))
       (esp+4 (n32+ esp 4))
       (MemAtStackPt (rm32 esp x86-32))
       (x86-32 (!rgfi *mr-esp* esp+4 x86-32))
       (x86-32 (!rgfi rA MemAtStackPt x86-32))

       ;; Update PC
       (x86-32 (!eip (+ pc 2) x86-32)))
      x86-32))

(defund y86-imm-add (x86-32 condition)
  (declare (xargs :guard (and (natp condition)
                              (< condition 7))
                  :stobjs (x86-32)))
  (b* ((pc (eip x86-32))

       ;; Memory Probe
       ((if (< *2^32-7* pc))
        (!ms (list :at-location pc
                   :instruction 'imm-add
                   :memory-probe nil)
             x86-32))

       ;; Decode registers
       (rA-rB (rm08 (+ pc 1) x86-32))
       (rB (n03 rA-rB))
       (b7-b3 (n05 (ash rA-rB -4)))

       ;; Register decoding problem?
       ((if (not (= b7-b3 #b1110)))
        (!ms (list :at-location pc
                   :instruction 'imm-add
                   :with-condition condition
                   :b7-b3 b7-b3
                   :rb rB)
             x86-32))

       ;; Condition true?
       (move? (y86-condition x86-32 condition))

       ;; When condition true, imm + rb -> rb
       (x86-32 (if (= move? 1)
                   (!rgfi rB
                          (n32+ (rm32 (+ pc 2) x86-32)
                                (rgfi rB x86-32))
                          x86-32)
                 x86-32))
       ;; Update PC
       (x86-32 (!eip (+ pc 6) x86-32)))
      x86-32))


(defund y86-leave (x86-32)
  (declare (xargs :guard t
                  :stobjs (x86-32)))
  (b* ((pc (eip x86-32))

       ;; Memory Probe
       ((if (< *2^32-2* pc))
        (!ms (list :at-location pc
                   :instruction 'leave
                   :memory-probe nil)
             x86-32))
       ;; :esp <- :ebp
       (x86-32 (!rgfi *mr-esp*
                      (rgfi *mr-ebp* x86-32)
                      x86-32))
       ;; pop :ebp
       (x86-32 (!rgfi *mr-ebp*
                      (rm32 (rgfi *mr-esp* x86-32) x86-32)
                      x86-32))
       ;; Update PC
       (x86-32 (!eip (+ pc 1) x86-32)))
      x86-32))


(defund y86-illegal-opcode (x86-32)
  (declare (xargs :guard t
                  :stobjs (x86-32)))
  (b* ((pc (eip x86-32))
       (byte-at-pc (rm08 pc x86-32)))
      (!ms (list :illegal-opcode byte-at-pc :at-location pc)
           x86-32)))


; Main instruction dispatch.

(defund y86-step (x86-32)
  (declare (xargs :guard t
                  :stobjs (x86-32)))
  (b* ((pc (eip x86-32))
       (byte-at-pc (rm08 pc x86-32))
       (nibble-1 (logand byte-at-pc #xF0)))
      (case nibble-1

        ;; halt:  Stop the machine
        (#x00
         (case byte-at-pc
           (#x00 (y86-halt x86-32))
           (t    (y86-illegal-opcode x86-32))))

        ;; nop:  No-operation
        (#x10
         (case byte-at-pc
           (#x10 (y86-nop x86-32))
           (t    (y86-illegal-opcode x86-32))))

        ;; rrmovl, cmovle, cmovl, cmove, cmovne, cmovge, cmovg:
        ;; Conditional register-to-register move
        (#x20
         (case byte-at-pc
           (#x20 (y86-cmove x86-32 0))
           (#x21 (y86-cmove x86-32 1))
           (#x22 (y86-cmove x86-32 2))
           (#x23 (y86-cmove x86-32 3))
           (#x24 (y86-cmove x86-32 4))
           (#x25 (y86-cmove x86-32 5))
           (#x26 (y86-cmove x86-32 6))
           (t   (y86-illegal-opcode x86-32))))

        ;; irmovl:  Conditional immediate-to-register move
        (#x30
         (case byte-at-pc
           (#x30 (y86-move-imm x86-32 0))
           (#x31 (y86-move-imm x86-32 1))
           (#x32 (y86-move-imm x86-32 2))
           (#x33 (y86-move-imm x86-32 3))
           (#x34 (y86-move-imm x86-32 4))
           (#x35 (y86-move-imm x86-32 5))
           (#x36 (y86-move-imm x86-32 6))
           (t    (y86-illegal-opcode x86-32))))

        ;; rmmovl:  rA -> D(rB))
        (#x40
         (case byte-at-pc
           (#x40 (y86-rA-to-mem-at-rb+D x86-32))
           (t    (y86-illegal-opcode x86-32))))

        ;; mrmovl:  D(rA) -> rB
        (#x50
         (case byte-at-pc
           (#x50 (y86-mem-at-rA+D-to-rB x86-32))
           (t    (y86-illegal-opcode x86-32))))

        ;; Arithmetic operations
        (#x60
         (case byte-at-pc
           ;; ra + rb -> rb
           (#x60 (y86-rA-+-rB-to-rB x86-32))
           ;; rb - ra -> rb
           (#x61 (y86-rB---rA-to-rB x86-32))
           ;; ra & rb -> rb
           (#x62 (y86-rA-and-rB-to-rB x86-32))
           ;; ra ^ rb -> rb
           (#x63 (y86-rA-xor-rB-to-rB x86-32))
           (t    (y86-illegal-opcode x86-32))))

        ;; jmp, jle, jl, je, jne, jge, jg:  Conditional jump
        (#x70
         (case byte-at-pc
           (#x70 (y86-cjump x86-32 0))
           (#x71 (y86-cjump x86-32 1))
           (#x72 (y86-cjump x86-32 2))
           (#x73 (y86-cjump x86-32 3))
           (#x74 (y86-cjump x86-32 4))
           (#x75 (y86-cjump x86-32 5))
           (#x76 (y86-cjump x86-32 6))
           (t    (y86-illegal-opcode x86-32))))

        ;; call:  :eip -> (--esp);  imm -> PC
        (#x80
         (case byte-at-pc
           (#x80 (y86-call x86-32))
           (t    (y86-illegal-opcode x86-32))))

        ;; ret:  (:esp--) -> :eip
        (#x90
         (case byte-at-pc
           (#x90 (y86-ret x86-32))
           (t    (y86-illegal-opcode x86-32))))

        ;; pushl:  rA -> (--esp)
        (#xA0
         (case byte-at-pc
           (#xA0 (y86-pushl x86-32))
           (t    (y86-illegal-opcode x86-32))))

        ;; popl:  (esp--) -> rA
        (#xB0
         (case byte-at-pc
           (#xB0 (y86-popl x86-32))
           (t    (y86-illegal-opcode x86-32))))

        ;; iaddl:  imm + rb -> rb
        (#xC0
         (case byte-at-pc
           (#xC0 (y86-imm-add x86-32 0))
           (#xC1 (y86-imm-add x86-32 1))
           (#xC2 (y86-imm-add x86-32 2))
           (#xC3 (y86-imm-add x86-32 3))
           (#xC4 (y86-imm-add x86-32 4))
           (#xC5 (y86-imm-add x86-32 5))
           (#xC6 (y86-imm-add x86-32 6))
           (t    (y86-illegal-opcode x86-32))))

        (#xD0 (y86-illegal-opcode x86-32))

        (#xE0 (y86-illegal-opcode x86-32))

        ;; noop:  No-operation
        (#xF0
         (case byte-at-pc
           (#xF0 (y86-nop x86-32)) ;; Dispatch performance test.
           (t    (y86-illegal-opcode x86-32))))

        (t (y86-illegal-opcode x86-32)))))



(defund y86 (x86-32 n)
  (declare (xargs :guard (natp n)
                  :measure (acl2-count n)
                  :stobjs (x86-32)))
  (if (mbe :logic (zp n) :exec (= n 0))
      x86-32
    (if (ms x86-32)
        x86-32
      (let ((x86-32 (y86-step x86-32)))
        (y86 x86-32 (1- n))))))


#||
(include-book "misc/defp" :dir :system)

(defp y86-wc (x86-32)
  ; (declare (xargs :stobjs (x86-32)))
  (if (ms x86-32)
      x86-32
    (let ((x86-32 (y86-step x86-32)))
      (y86-wc x86-32))))

||#
