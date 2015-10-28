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
; INSTRUCTION: Bit Scan
; =============================================================================

(encapsulate
 ()

 (local (in-theory (e/d* (ihsext-inductions
                          ihsext-recursive-redefs)
                         ())))

 (define bsf ((index natp)
              (x natp))
   :hints (("Goal" :in-theory (enable logtail)))
   :returns (index natp :hyp (natp index)
                   :rule-classes :type-prescription)
   (if (zp x)
       0
     (if (logbitp 0 x)
         index
       (bsf (1+ index) (ash x -1))))
   ///
   (defthm bsf-64
     (implies (n64p x)
              (< (bsf 0 x) 64))
     :rule-classes :linear)))

(def-inst x86-bsf-Op/En-RM

  :parents (two-byte-opcodes fp-opcodes)
  :implemented
  (progn
    (add-to-implemented-opcodes-table 'BSF #x0FBC '(:nil nil) 'x86-bsf-Op/En-RM)
    (add-to-implemented-opcodes-table 'BSF #x0FBC '(:misc (logbitp *w* rex-byte)) 'x86-bsf-Op/En-RM))

  :short "Bit scan forward"

  :long
  "<h3>Op/En = RM: \[OP REG, R/M\]</h3>
          0F BC: BSF r16, r/m16<br/>
          0F BC: BSF r32, r/m32<br/>
  REX.W + 0F BC: BSF r64, r/m64<br/>"

  :guard-hints (("Goal" :in-theory (enable reg-index)))

  :returns (x86 x86p :hyp (x86p x86))

  :body
  (b* ((ctx 'x86-bsf-Op/En-RM)
       (r/m (the (unsigned-byte 3) (mrm-r/m  modr/m)))
       (mod (the (unsigned-byte 2) (mrm-mod  modr/m)))
       (reg (the (unsigned-byte 3) (mrm-reg  modr/m)))
       (lock (eql #.*lock*
                  (prefixes-slice :group-1-prefix prefixes)))
       ((when lock)
        (!!ms-fresh :lock-prefix prefixes))

       (p3 (equal #.*operand-size-override*
                  (prefixes-slice :group-3-prefix prefixes)))

       ((the (integer 2 8) operand-size)
        (if (logbitp *w* rex-byte)
            8
          (if p3
              ;; See Table 3-4, P. 3-26, Intel Vol. 1.
              2 ; 16-bit operand-size
            4)))

       ((the (unsigned-byte 4) rgf-index)
        (reg-index reg rex-byte #.*r*))

       (p2 (prefixes-slice :group-2-prefix prefixes))

       (p4? (eql #.*addr-size-override*
                 (prefixes-slice :group-4-prefix prefixes)))

       ((mv flg0 reg/mem
            (the (integer 0 4) increment-RIP-by)
            (the (signed-byte 64) ?v-addr)
            x86)
        (x86-operand-from-modr/m-and-sib-bytes #.*rgf-access* operand-size
                                               p2 p4? temp-rip
                                               rex-byte r/m mod sib 0 x86))

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

       ((the (signed-byte #.*max-linear-address-size+1*) addr-diff)
        (-
         (the (signed-byte #.*max-linear-address-size*)
           temp-rip)
         (the (signed-byte #.*max-linear-address-size*)
           start-rip)))
       ((when (< 15 addr-diff))
        (!!ms-fresh :instruction-length addr-diff))

       ;; Update the x86 state:
       (zf (if (int= reg/mem 0) 1 0))
       (x86 (!flgi #.*zf* zf x86))

       (x86 (!rip temp-rip x86))

       ((when (int= reg/mem 0))
        x86)

       (index (the (unsigned-byte 6) (bsf 0 reg/mem)))
       (x86 (!rgfi-size operand-size rgf-index index rex-byte x86)))
      x86))

;; ======================================================================
