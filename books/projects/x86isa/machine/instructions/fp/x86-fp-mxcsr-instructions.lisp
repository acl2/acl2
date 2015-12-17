;; AUTHOR:
;; Cuong Kim Chau <ckcuong@cs.utexas.edu>

(in-package "X86ISA")

;; ======================================================================

(include-book "../../x86-decoding-and-spec-utils"
              :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))
(include-book "fp-base"
              :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))
(local (include-book "centaur/bitops/ihs-extensions" :dir :system))

; =============================================================================
; INSTRUCTION: MXCSR State Management Instructions
; =============================================================================

(def-inst x86-ldmxcsr/stmxcsr-Op/En-M

  :parents (two-byte-opcodes fp-opcodes)

  :short "Load/Store MXCSR register"

  :long
  "<h3>Op/En = M: \[OP M\]</h3>
  0F AE /2: LDMXCSR m32<br/>
  0F AE /3: STMXCSR m32<br/>"

  :returns (x86 x86p :hyp (x86p x86))

  :body
  (b* ((ctx 'x86-ldmxcsr/stmxcsr-Op/En-M)
       (r/m (the (unsigned-byte 3) (mrm-r/m  modr/m)))
       (mod (the (unsigned-byte 2) (mrm-mod  modr/m)))
       (reg (the (unsigned-byte 3) (mrm-reg  modr/m)))
       (lock (eql #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock)
        (!!ms-fresh :lock-prefix prefixes))

       (p2 (prefixes-slice :group-2-prefix prefixes))
       (p4? (eql #.*addr-size-override*
                 (prefixes-slice :group-4-prefix prefixes)))
       (inst-ac? ;; Exceptions Type 5
        t)

       ((mv flg0
            (the (unsigned-byte 32) mem)
            (the (integer 0 4) increment-RIP-by)
            (the (signed-byte 64) v-addr)
            x86)
        (x86-operand-from-modr/m-and-sib-bytes
         #.*rgf-access* 4 inst-ac? p2 p4? temp-rip rex-byte r/m mod sib 0 x86))

       ((when flg0)
        (!!ms-fresh :x86-operand-from-modr/m-and-sib-bytes flg0))

       ((the (signed-byte #.*max-linear-address-size+1*) temp-rip)
        (+ temp-rip increment-RIP-by))

       ((when (mbe :logic (not (canonical-address-p temp-rip))
                   :exec (<= #.*2^47*
                             (the (signed-byte
                                   #.*max-linear-address-size+1*)
                               temp-rip))))
        (!!ms-fresh :temp-rip-not-canonical temp-rip))

       ((when (not (canonical-address-p v-addr)))
        (!!ms-fresh :v-addr-not-canonical v-addr))

       ((the (signed-byte #.*max-linear-address-size+1*) addr-diff)
        (-
         (the (signed-byte #.*max-linear-address-size*)
           temp-rip)
         (the (signed-byte #.*max-linear-address-size*)
           start-rip)))
       ((when (< 15 addr-diff))
        (!!ms-fresh :instruction-length addr-diff))

       ;; Update the x86 state:
       (x86
        (case reg
          (2 ;; LDMXCSR
           (!mxcsr mem x86))
          (3 ;; STMXCSR
           (b* ((mxcsr (the (unsigned-byte 32) (mxcsr x86)))
                ((mv flg1 x86)
                 (x86-operand-to-reg/mem
                  4 inst-ac? mxcsr v-addr rex-byte r/m mod x86))
                ;; Note: If flg1 is non-nil, we bail out without changing the
                ;; x86 state.
                ((when flg1)
                 (!!ms-fresh :x86-operand-to-reg/mem flg1)))
             x86))
          (otherwise ;; Should never be reached, unimplemented.
           x86)))

       (x86 (!rip temp-rip x86)))
    x86)

  :implemented
  (progn
    (add-to-implemented-opcodes-table 'LDMXCSR #x0FAE
                                      '(:misc (eql (mrm-reg modr/m) 2))
                                      'x86-ldmxcsr/stmxcsr-Op/En-M)
    (add-to-implemented-opcodes-table 'STMXCSR #x0FAE
                                      '(:misc (eql (mrm-reg modr/m) 3))
                                      'x86-ldmxcsr/stmxcsr-Op/En-M)))

;; ======================================================================
