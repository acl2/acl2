;; AUTHOR:
;; Cuong Kim Chau <ckcuong@cs.utexas.edu>

(in-package "X86ISA")

;; ======================================================================

(include-book "../../x86-decoding-and-spec-utils"
              :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))
(include-book "fp-base"
              :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))
(include-book "centaur/bitops/merge" :dir :system)

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))

; =============================================================================
; INSTRUCTION: SSE2 64-Bit SIMD Integer Instructions
; =============================================================================

(def-inst x86-pcmpeqb-Op/En-RM

  :parents (two-byte-opcodes fp-opcodes)

  :short "Compare packed bytes for equal"

  :long
  "<h3>Op/En = RM: \[OP XMM, XMM/M\]</h3>
  66 0F 74: PCMPEQB xmm1, xmm2/m128<br/>"

  :returns (x86 x86p :hyp (x86p x86))

  :prepwork

  ((define pcmpeqb32 ((xmm n32p)
                      (xmm/mem n32p))
     :inline t

     (let* ((xmm0 (mbe :logic (part-select xmm :low 0 :high 7)
                       :exec  (the (unsigned-byte 8)
                                (logand #xFF xmm))))
            (xmm/mem0 (mbe :logic (part-select xmm/mem :low 0 :high 7)
                           :exec  (the (unsigned-byte 8)
                                    (logand #xFF xmm/mem))))

            (xmm1 (mbe :logic (part-select xmm :low 8 :high 15)
                       :exec  (the (unsigned-byte 8)
                                (logand #xFF (ash xmm -8)))))
            (xmm/mem1 (mbe :logic (part-select xmm/mem :low 8 :high 15)
                           :exec  (the (unsigned-byte 8)
                                    (logand #xFF (ash xmm/mem -8)))))

            (xmm2 (mbe :logic (part-select xmm :low 16 :high 23)
                       :exec  (the (unsigned-byte 8)
                                (logand #xFF (ash xmm -16)))))
            (xmm/mem2 (mbe :logic (part-select xmm/mem :low 16 :high 23)
                           :exec  (the (unsigned-byte 8)
                                    (logand #xFF (ash xmm/mem -16)))))

            (xmm3 (mbe :logic (part-select xmm :low 24 :high 31)
                       :exec  (the (unsigned-byte 8)
                                (logand #xFF (ash xmm -24)))))
            (xmm/mem3 (mbe :logic (part-select xmm/mem :low 24 :high 31)
                           :exec  (the (unsigned-byte 8)
                                    (logand #xFF (ash xmm/mem -24)))))

            (byte0 (the (unsigned-byte 8)
                     (if (int= xmm0 xmm/mem0) #xFF 0)))
            (byte1 (the (unsigned-byte 8)
                     (if (int= xmm1 xmm/mem1) #xFF 0)))
            (byte2 (the (unsigned-byte 8)
                     (if (int= xmm2 xmm/mem2) #xFF 0)))
            (byte3 (the (unsigned-byte 8)
                     (if (int= xmm3 xmm/mem3) #xFF 0)))

            (dword (merge-4-u8s byte3 byte2 byte1 byte0)))
       dword)

     ///

     (defthm-usb n32p-pcmpeqb32
       :bound 32
       :concl (pcmpeqb32 xmm xmm/mem)
       :gen-type t
       :gen-linear t)))

  :body
  (b* ((ctx 'x86-pcmpeqb-Op/En-RM)
       (r/m (the (unsigned-byte 3) (mrm-r/m  modr/m)))
       (mod (the (unsigned-byte 2) (mrm-mod  modr/m)))
       (reg (the (unsigned-byte 3) (mrm-reg  modr/m)))
       ;; [Shilpi]: The Intel manual doesn't mention that a lock
       ;; prefix causes an exception for this opcode. Should the
       ;; following be removed then?
       (lock (eql #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock)
        (!!ms-fresh :lock-prefix prefixes))

       ((the (unsigned-byte 4) xmm-index)
        (reg-index reg rex-byte #.*r*))

       ((the (unsigned-byte 128) xmm)
        (xmmi-size 16 xmm-index x86))

       (p2 (prefixes-slice :group-2-prefix prefixes))

       (p4? (eql #.*addr-size-override*
                 (prefixes-slice :group-4-prefix prefixes)))

       ((mv flg0
            (the (unsigned-byte 128) xmm/mem)
            (the (integer 0 4) increment-RIP-by)
            (the (signed-byte 64) ?v-addr) x86)
        (x86-operand-from-modr/m-and-sib-bytes
         #.*xmm-access* 16 p2 p4? temp-rip rex-byte r/m mod sib 0 x86))

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

       ;; Raise an error if v-addr is not 16-byte aligned.
       ;; In case the second operand is an XMM register, v-addr = 0.
       ((when (not (eql (mod v-addr 16) 0)))
        (!!ms-fresh :memory-address-is-not-16-byte-aligned v-addr))

       (xmm0 (mbe :logic (part-select xmm :low 0 :high 31)
                  :exec  (the (unsigned-byte 32)
                           (logand #uxFFFF_FFFF xmm))))
       (xmm/mem0 (mbe :logic (part-select xmm/mem :low 0 :high 31)
                      :exec  (the (unsigned-byte 32)
                               (logand #uxFFFF_FFFF xmm/mem))))

       (xmm1 (mbe :logic (part-select xmm :low 32 :high 63)
                  :exec  (the (unsigned-byte 32)
                           (logand #uxFFFF_FFFF (ash xmm -32)))))
       (xmm/mem1 (mbe :logic (part-select xmm/mem :low 32 :high 63)
                      :exec  (the (unsigned-byte 32)
                               (logand #uxFFFF_FFFF (ash xmm/mem -32)))))

       (xmm2 (mbe :logic (part-select xmm :low 64 :high 95)
                  :exec  (the (unsigned-byte 32)
                           (logand #uxFFFF_FFFF (ash xmm -64)))))
       (xmm/mem2 (mbe :logic (part-select xmm/mem :low 64 :high 95)
                      :exec  (the (unsigned-byte 32)
                               (logand #uxFFFF_FFFF (ash xmm/mem -64)))))

       (xmm3 (mbe :logic (part-select xmm :low 96 :high 127)
                  :exec  (the (unsigned-byte 32)
                           (logand #uxFFFF_FFFF (ash xmm -96)))))
       (xmm/mem3 (mbe :logic (part-select xmm/mem :low 96 :high 127)
                      :exec  (the (unsigned-byte 32)
                               (logand #uxFFFF_FFFF (ash xmm/mem -96)))))

       (dword0 (the (unsigned-byte 32)
                 (pcmpeqb32 xmm0 xmm/mem0)))
       (dword1 (the (unsigned-byte 32)
                 (pcmpeqb32 xmm1 xmm/mem1)))
       (dword2 (the (unsigned-byte 32)
                 (pcmpeqb32 xmm2 xmm/mem2)))
       (dword3 (the (unsigned-byte 32)
                 (pcmpeqb32 xmm3 xmm/mem3)))

       (result (merge-4-u32s dword3 dword2 dword1 dword0))

       ;; Update the x86 state:
       (x86 (!xmmi-size 16 xmm-index result x86))

       (x86 (!rip temp-rip x86)))
      x86)

  :implemented
  (add-to-implemented-opcodes-table 'PCMPEQB #x0F74
                                    '(:misc
                                      (eql #.*mandatory-66h* (prefixes-slice :group-3-prefix prefixes)))
                                    'x86-pcmpeqb-Op/En-RM))

(def-inst x86-pmovmskb-Op/En-RM

  :parents (two-byte-opcodes fp-opcodes)

  :short "Move byte mask"

  :long
  "<h3>Op/En = RM: \[OP REG, XMM\]</h3>
  66 0F D7: PMOVMSKB reg, xmm<br/>"

  :guard-hints (("Goal" :in-theory (enable reg-index merge-2-u8s)))

  :returns (x86 x86p :hyp (x86p x86))

  :prepwork

  ((define pmovmskb8 ((xmm n64p))
     :inline t

     (let* ((bit0  (logbit   7 xmm))
            (bit1  (logbit  15 xmm))
            (bit2  (logbit  23 xmm))
            (bit3  (logbit  31 xmm))
            (bit4  (logbit  39 xmm))
            (bit5  (logbit  47 xmm))
            (bit6  (logbit  55 xmm))
            (bit7  (logbit  63 xmm))

            (two-bit0 (the (unsigned-byte 2)
                        (logior (the (unsigned-byte 2) (ash bit1 1))
                                bit0)))
            (two-bit1 (the (unsigned-byte 2)
                        (logior (the (unsigned-byte 2) (ash bit3 1))
                                bit2)))
            (two-bit2 (the (unsigned-byte 2)
                        (logior (the (unsigned-byte 2) (ash bit5 1))
                                bit4)))
            (two-bit3 (the (unsigned-byte 2)
                        (logior (the (unsigned-byte 2) (ash bit7 1))
                                bit6)))

            (four-bit0 (the (unsigned-byte 4)
                         (logior (the (unsigned-byte 4) (ash two-bit1 2))
                                 two-bit0)))
            (four-bit1 (the (unsigned-byte 4)
                         (logior (the (unsigned-byte 4) (ash two-bit3 2))
                                 two-bit2)))

            (byte (the (unsigned-byte 8)
                    (logior (the (unsigned-byte 8) (ash four-bit1 4))
                            four-bit0))))
       byte)

     ///

     (defthm-usb n08p-pmovmskb8
       :bound 8
       :concl (pmovmskb8 xmm)
       :gen-type t
       :gen-linear t)))

  :body
  (b* ((ctx 'x86-pmovmskb-Op/En-RM)
       (r/m (the (unsigned-byte 3) (mrm-r/m  modr/m)))
       (mod (the (unsigned-byte 2) (mrm-mod  modr/m)))
       (reg (the (unsigned-byte 3) (mrm-reg  modr/m)))
       ;; [Shilpi]: The Intel manual doesn't mention that a lock
       ;; prefix causes an exception for this opcode. Should the
       ;; following be removed then?
       (lock (eql #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock)
        (!!ms-fresh :lock-prefix prefixes))

       ((the (unsigned-byte 4) rgf-index)
        (reg-index reg rex-byte #.*r*))

       (p2 (prefixes-slice :group-2-prefix prefixes))

       (p4? (eql #.*addr-size-override*
                 (prefixes-slice :group-4-prefix prefixes)))

       ((mv flg0
            (the (unsigned-byte 128) xmm)
            (the (integer 0 4) increment-RIP-by)
            (the (signed-byte 64) ?v-addr) x86)
        (x86-operand-from-modr/m-and-sib-bytes #.*xmm-access* 16
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

       (xmm0 (mbe :logic (part-select xmm :low 0 :high 63)
                  :exec  (the (unsigned-byte 64)
                           (logand #uxFFFF_FFFF_FFFF_FFFF xmm))))
       (xmm1 (mbe :logic (part-select xmm :low 64 :high 127)
                  :exec  (the (unsigned-byte 64)
                           (logand #uxFFFF_FFFF_FFFF_FFFF
                                   (ash xmm -64)))))

       (byte0 (the (unsigned-byte 8) (pmovmskb8 xmm0)))
       (byte1 (the (unsigned-byte 8) (pmovmskb8 xmm1)))

       (result (merge-2-u8s byte1 byte0))

       ;; Update the x86 state:
       (x86 (!rgfi-size 8 rgf-index result rex-byte x86))

       (x86 (!rip temp-rip x86)))
      x86)

  :implemented
  (add-to-implemented-opcodes-table 'PMOVMSKB #x0FD7
                                    '(:misc
                                      (eql #.*mandatory-66h* (prefixes-slice :group-3-prefix prefixes)))
                                    'x86-pmovmskb-Op/En-RM))

;; ======================================================================
