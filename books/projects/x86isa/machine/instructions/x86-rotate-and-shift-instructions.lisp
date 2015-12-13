;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")

;; ======================================================================

(include-book "shifts"
              :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))
(include-book "rotates"
              :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))
(include-book "../x86-decoding-and-spec-utils"
              :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))
(local (include-book "centaur/bitops/ihs-extensions" :dir :system))

;; ======================================================================
;; INSTRUCTION: SAL/SAR/SHL/SHR/RCL/RCR/ROL/ROR
;; ======================================================================

(def-inst x86-sal/sar/shl/shr/rcl/rcr/rol/ror
  :guard (not (equal (mrm-reg modr/m) 6))

  :parents (one-byte-opcodes)

  :returns (x86 x86p :hyp (and (x86p x86)
                               (canonical-address-p temp-rip))
                :hints (("Goal" :in-theory (e/d () (force (force))))))

  :long
  "<p>
  Op/En: MI<br/>
  C0/0: ROL r/m8, imm8<br/>
  C0/1: ROR r/m8,imm8<br/>
  C0/2: RCL r/m8, imm8<br/>
  C0/3: RCR r/m8, imm8<br/>
  C0/4: SAL/SHL r/m8 imm8<br/>
  C0/5: SHR r/m8 imm8<br/>
  C0/7: SAR r/m8 imm8<br/>
  C1/0: ROL r/m16, r/m32, or r/m64, imm8<br/>
  C1/1: ROR r/m16, r/m32, or r/m64, imm8<br/>
  C1/2: RCL r/m16, r/m32, or r/m64, imm8<br/>
  C1/3: RCR r/m16, r/m32, or r/m64, imm8<br/>
  C1/4: SAL/SHL r/m8 r/m16 or r/m64 imm8<br/>
  C1/5: SHR r/m16 r/m32 or r/m64 imm8<br/>
  C1/7: SAR r/m16 r/m32 or r/m64 imm8<br/>
  </p>

  <p>
  Op/En: M1<br/>
  D0/0: ROL r/m8, 1<br/>
  D0/1: ROR r/m8, 1<br/>
  D0/2: RCL r/m8, 1<br/>
  D0/3: RCR r/m8, 1<br/>
  D0/4: SAL/SHL r/m8 1<br/>
  D0/5: SHR r/m8 1<br/>
  D0/7: SAR r/m8 1<br/>
  D1/0: ROL r/m16, r/m32, or r/m64, 1<br/>
  D1/1: ROR r/m16, r/m32, or r/m64, 1<br/>
  D1/2: RCL r/m16, r/m32, or r/m64, 1<br/>
  D1/3: RCR r/m16, r/m32, or r/m64, 1<br/>
  D1/4: SAL/SHL r/m16 r/m32 or r/m64 1<br/>
  D1/5: SHR r/m16 r/m32 or r/m64 1<br/>
  D1/7: SAR r/m16 r/m32 or r/m64 1<br/>
  </p>

  <p>
  Op/En: MC<br/>
  D2/0: ROL r/m8, CL<br/>
  D2/1: ROR r/m8, CL<br/>
  D2/2: RCL r/m8, CL<br/>
  D2/3: RCR r/m8, CL<br/>
  D2/4: SAL/SHL r/m8 CL<br/>
  D2/5: SHR r/m8 CL<br/>
  D2/7: SAR r/m8, CL<br/>
  D3/0: ROL r/m16, r/m32, or r/m64, CL<br/>
  D3/1: ROR r/m16, r/m32, or r/m64, CL<br/>
  D3/2: RCL r/m16, r/m32, or r/m64, CL<br/>
  D3/3: RCR r/m16, r/m32, or r/m64, CL<br/>
  D3/4: SAL/SHL r/m16 r/m32 or r/m64 CL<br/>
  D3/5: SHR r/m16 r/m32 or r/m64 CL<br/>
  D3/7: SAR r/m16 r/m32 or r/m64 CL<br/>
  </p>"

  :implemented
  (progn
    (add-to-implemented-opcodes-table 'ROL #xC0 '(:reg 0)
                                      'x86-sal/sar/shl/shr/rcl/rcr/rol/ror)
    (add-to-implemented-opcodes-table 'ROR #xC0 '(:reg 1)
                                      'x86-sal/sar/shl/shr/rcl/rcr/rol/ror)
    (add-to-implemented-opcodes-table 'RCL #xC0 '(:reg 2)
                                      'x86-sal/sar/shl/shr/rcl/rcr/rol/ror)
    (add-to-implemented-opcodes-table 'RCR #xC0 '(:reg 3)
                                      'x86-sal/sar/shl/shr/rcl/rcr/rol/ror)
    (add-to-implemented-opcodes-table 'SAL #xC0 '(:reg 4)
                                      'x86-sal/sar/shl/shr/rcl/rcr/rol/ror)
    (add-to-implemented-opcodes-table 'SHR #xC0 '(:reg 5)
                                      'x86-sal/sar/shl/shr/rcl/rcr/rol/ror)
    (add-to-implemented-opcodes-table 'SAR #xC0 '(:reg 7)
                                      'x86-sal/sar/shl/shr/rcl/rcr/rol/ror)

    (add-to-implemented-opcodes-table 'ROL #xC1 '(:reg 0)
                                      'x86-sal/sar/shl/shr/rcl/rcr/rol/ror)
    (add-to-implemented-opcodes-table 'ROR #xC1 '(:reg 1)
                                      'x86-sal/sar/shl/shr/rcl/rcr/rol/ror)
    (add-to-implemented-opcodes-table 'RCL #xC1 '(:reg 2)
                                      'x86-sal/sar/shl/shr/rcl/rcr/rol/ror)
    (add-to-implemented-opcodes-table 'RCR #xC1 '(:reg 3)
                                      'x86-sal/sar/shl/shr/rcl/rcr/rol/ror)
    (add-to-implemented-opcodes-table 'SAL #xC1 '(:reg 4)
                                      'x86-sal/sar/shl/shr/rcl/rcr/rol/ror)
    (add-to-implemented-opcodes-table 'SHR #xC1 '(:reg 5)
                                      'x86-sal/sar/shl/shr/rcl/rcr/rol/ror)
    (add-to-implemented-opcodes-table 'SAR #xC1 '(:reg 7)
                                      'x86-sal/sar/shl/shr/rcl/rcr/rol/ror)

    (add-to-implemented-opcodes-table 'ROL #xD0 '(:reg 0)
                                      'x86-sal/sar/shl/shr/rcl/rcr/rol/ror)
    (add-to-implemented-opcodes-table 'ROR #xD0 '(:reg 1)
                                      'x86-sal/sar/shl/shr/rcl/rcr/rol/ror)
    (add-to-implemented-opcodes-table 'RCL #xD0 '(:reg 2)
                                      'x86-sal/sar/shl/shr/rcl/rcr/rol/ror)
    (add-to-implemented-opcodes-table 'RCR #xD0 '(:reg 3)
                                      'x86-sal/sar/shl/shr/rcl/rcr/rol/ror)
    (add-to-implemented-opcodes-table 'SAL #xD0 '(:reg 4)
                                      'x86-sal/sar/shl/shr/rcl/rcr/rol/ror)
    (add-to-implemented-opcodes-table 'SHR #xD0 '(:reg 5)
                                      'x86-sal/sar/shl/shr/rcl/rcr/rol/ror)
    (add-to-implemented-opcodes-table 'SAR #xD0 '(:reg 7)
                                      'x86-sal/sar/shl/shr/rcl/rcr/rol/ror)

    (add-to-implemented-opcodes-table 'ROL #xD1 '(:reg 0)
                                      'x86-sal/sar/shl/shr/rcl/rcr/rol/ror)
    (add-to-implemented-opcodes-table 'ROR #xD1 '(:reg 1)
                                      'x86-sal/sar/shl/shr/rcl/rcr/rol/ror)
    (add-to-implemented-opcodes-table 'RCL #xD1 '(:reg 2)
                                      'x86-sal/sar/shl/shr/rcl/rcr/rol/ror)
    (add-to-implemented-opcodes-table 'RCR #xD1 '(:reg 3)
                                      'x86-sal/sar/shl/shr/rcl/rcr/rol/ror)
    (add-to-implemented-opcodes-table 'SAL #xD1 '(:reg 4)
                                      'x86-sal/sar/shl/shr/rcl/rcr/rol/ror)
    (add-to-implemented-opcodes-table 'SHR #xD1 '(:reg 5)
                                      'x86-sal/sar/shl/shr/rcl/rcr/rol/ror)
    (add-to-implemented-opcodes-table 'SAR #xD1 '(:reg 7)
                                      'x86-sal/sar/shl/shr/rcl/rcr/rol/ror)

    (add-to-implemented-opcodes-table 'ROL #xD2 '(:reg 0)
                                      'x86-sal/sar/shl/shr/rcl/rcr/rol/ror)
    (add-to-implemented-opcodes-table 'ROR #xD2 '(:reg 1)
                                      'x86-sal/sar/shl/shr/rcl/rcr/rol/ror)
    (add-to-implemented-opcodes-table 'RCL #xD2 '(:reg 2)
                                      'x86-sal/sar/shl/shr/rcl/rcr/rol/ror)
    (add-to-implemented-opcodes-table 'RCR #xD2 '(:reg 3)
                                      'x86-sal/sar/shl/shr/rcl/rcr/rol/ror)
    (add-to-implemented-opcodes-table 'SAL #xD2 '(:reg 4)
                                      'x86-sal/sar/shl/shr/rcl/rcr/rol/ror)
    (add-to-implemented-opcodes-table 'SHR #xD2 '(:reg 5)
                                      'x86-sal/sar/shl/shr/rcl/rcr/rol/ror)
    (add-to-implemented-opcodes-table 'SAR #xD2 '(:reg 7)
                                      'x86-sal/sar/shl/shr/rcl/rcr/rol/ror)

    (add-to-implemented-opcodes-table 'ROL #xD3 '(:reg 0)
                                      'x86-sal/sar/shl/shr/rcl/rcr/rol/ror)
    (add-to-implemented-opcodes-table 'ROR #xD3 '(:reg 1)
                                      'x86-sal/sar/shl/shr/rcl/rcr/rol/ror)
    (add-to-implemented-opcodes-table 'RCL #xD3 '(:reg 2)
                                      'x86-sal/sar/shl/shr/rcl/rcr/rol/ror)
    (add-to-implemented-opcodes-table 'RCR #xD3 '(:reg 3)
                                      'x86-sal/sar/shl/shr/rcl/rcr/rol/ror)
    (add-to-implemented-opcodes-table 'SAL #xD3 '(:reg 4)
                                      'x86-sal/sar/shl/shr/rcl/rcr/rol/ror)
    (add-to-implemented-opcodes-table 'SHR #xD3 '(:reg 5)
                                      'x86-sal/sar/shl/shr/rcl/rcr/rol/ror)
    (add-to-implemented-opcodes-table 'SAR #xD3 '(:reg 7)
                                      'x86-sal/sar/shl/shr/rcl/rcr/rol/ror))

  :body

  (b* ((ctx 'x86-sal/sar/shl/shr/rcl/rcr/rol/ror)
       (lock (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock)
        (!!ms-fresh :lock-prefix prefixes))
       (r/m (mrm-r/m modr/m))
       (mod (mrm-mod modr/m))
       (reg (mrm-reg modr/m))
       (p2 (prefixes-slice :group-2-prefix prefixes))
       (p4 (equal #.*addr-size-override*
                  (prefixes-slice :group-4-prefix prefixes)))

       (select-byte-operand (or (equal opcode #xC0)
                                (equal opcode #xD0)
                                (equal opcode #xD2)))
       ((the (integer 0 8) ?reg/mem-size)
        (select-operand-size select-byte-operand rex-byte nil
                             prefixes))

       (inst-ac? t)
       ((mv flg0 ?reg/mem (the (unsigned-byte 3) increment-RIP-by)
            (the (signed-byte #.*max-linear-address-size*) v-addr) x86)
        (x86-operand-from-modr/m-and-sib-bytes
         #.*rgf-access* reg/mem-size inst-ac? p2 p4 temp-rip rex-byte r/m mod sib 0 x86))
       ((when flg0)
        (!!ms-fresh :x86-operand-from-modr/m-and-sib-bytes flg0))

       ((the (signed-byte #.*max-linear-address-size+1*) temp-rip)
        (+ increment-RIP-by temp-rip))
       ((when (mbe :logic (not (canonical-address-p temp-rip))
                   :exec (<= #.*2^47*
                             (the (signed-byte
                                   #.*max-linear-address-size+1*)
                               temp-rip))))
        (!!ms-fresh :temp-rip-not-canonical temp-rip))

       ((mv flg1 shift/rotate-by x86)
        (case opcode
          ((#xD0 #xD1)
           (mv nil 1 x86))
          ((#xD2 #xD3)
           (mv nil (rr08 *rcx* rex-byte x86) x86))
          ((#xC0 #xC1)
           (rm-size 1 temp-rip :x x86))
          (otherwise ;; will not be reached
           (mv nil 0 x86))))
       ((when flg1)
        (!!ms-fresh :rm-size-error flg1))

       (countMask (if (logbitp #.*w* rex-byte)
                      #x3F
                    #x1F))
       (shift/rotate-by (logand countMask shift/rotate-by))

       ((the (signed-byte #.*max-linear-address-size+1*) temp-rip)
        (if (or (equal opcode #xC0)
                (equal opcode #xC1))
            (+ temp-rip 1)
          temp-rip))
       ((when (mbe :logic (not (canonical-address-p temp-rip))
                   :exec (<= #.*2^47*
                             (the (signed-byte
                                   #.*max-linear-address-size+1*)
                               temp-rip))))
        (!!ms-fresh :virtual-memory-error temp-rip))

       ((the (signed-byte #.*max-linear-address-size+1*) addr-diff)
        (-
         (the (signed-byte #.*max-linear-address-size*)
           temp-rip)
         (the (signed-byte #.*max-linear-address-size*)
           start-rip)))
       ((when (< 15 addr-diff))
        (!!ms-fresh :instruction-length addr-diff))

       ;; Computing the flags and the result:
       (input-rflags (the (unsigned-byte 32) (rflags x86)))

       ((mv result
            (the (unsigned-byte 32) output-rflags)
            (the (unsigned-byte 32) undefined-flags))
        (case reg
          (0
           ;; ROL
           (rol-spec reg/mem-size reg/mem shift/rotate-by input-rflags))
          (1
           ;; ROR
           (ror-spec reg/mem-size reg/mem shift/rotate-by input-rflags))
          (2
           ;; RCL
           (rcl-spec reg/mem-size reg/mem shift/rotate-by input-rflags))
          (3
           ;; RCR
           (rcr-spec reg/mem-size reg/mem shift/rotate-by input-rflags))
          (4
           ;; SAL/SHL
           (sal/shl-spec reg/mem-size reg/mem shift/rotate-by input-rflags))
          (5
           ;; SHR
           (shr-spec reg/mem-size reg/mem shift/rotate-by input-rflags))
          (7
           ;; SAR
           (sar-spec reg/mem-size reg/mem shift/rotate-by input-rflags))
          ;; The guard for this function will ensure that we don't
          ;; reach here.
          (otherwise
           (mv 0 0 0))))

       ;; Update the x86 state:

       (x86 (write-user-rflags output-rflags undefined-flags x86))

       ((mv flg2 x86)
        (x86-operand-to-reg/mem
         reg/mem-size inst-ac?
         ;; TO-DO@Shilpi: Remove this trunc.
         (trunc reg/mem-size result)
         (the (signed-byte #.*max-linear-address-size*) v-addr)
         rex-byte r/m mod x86))
       ;; Note: If flg2 is non-nil, we bail out without changing the x86 state.
       ((when flg2)
        (!!ms-fresh :x86-operand-to-reg/mem flg2))
       (x86 (!rip temp-rip x86)))
    x86))

;; ======================================================================
