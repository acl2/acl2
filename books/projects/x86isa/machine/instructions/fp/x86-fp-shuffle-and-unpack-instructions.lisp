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
; INSTRUCTION: SSE/SSE2 Shuffle and Unpack Instructions
; =============================================================================

(define extract-32-bits ((x (n128p x))
                         (n (n02p n)))
  :inline t
  :returns (result (unsigned-byte-p 32 result)
                   :rule-classes (:rewrite :type-prescription))
  (case n
    (0 (mbe :logic (part-select x :low 0 :high 31)
            :exec  (the (unsigned-byte 32)
                     (logand #uxFFFF_FFFF x))))
    (1 (mbe :logic (part-select x :low 32 :high 63)
            :exec  (the (unsigned-byte 32)
                     (logand #uxFFFF_FFFF (ash x -32)))))
    (2 (mbe :logic (part-select x :low 64 :high 95)
            :exec  (the (unsigned-byte 32)
                     (logand #uxFFFF_FFFF (ash x -64)))))
    (otherwise (mbe :logic (part-select x :low 96 :high 127)
                    :exec  (the (unsigned-byte 32)
                             (logand #uxFFFF_FFFF (ash x -96)))))))

(define extract-64-bits ((x (n128p x))
                         (n (n01p n)))
  :inline t
  :returns (result (unsigned-byte-p 64 result)
                   :rule-classes (:rewrite :type-prescription))
  (case n
    (0 (mbe :logic (part-select x :low 0 :high 63)
            :exec  (the (unsigned-byte 64)
                     (logand #uxFFFF_FFFF_FFFF_FFFF x))))
    (otherwise (mbe :logic (part-select x :low 64 :high 127)
                    :exec  (the (unsigned-byte 64)
                             (logand #uxFFFF_FFFF_FFFF_FFFF
                                     (ash x -64)))))))

(def-inst x86-shufps-Op/En-RMI

  :parents (two-byte-opcodes fp-opcodes)

  :short "Shuffle packed single-precision floating-point values"

  :long
  "<h3>Op/En = RMI: \[OP XMM, XMM/M, IMM\]</h3>
  0F C6: SHUFPS xmm1, xmm2/m128, imm8<br/>"

  :returns (x86 x86p :hyp (x86p x86))

  :body
  (b* ((ctx 'x86-shufps-Op/En-RMI)
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
         #.*xmm-access* 16 p2 p4? temp-rip rex-byte r/m mod sib 1 x86))

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

       ((mv flg1 (the (unsigned-byte 8) imm) x86)
        (rm-size 1 (the (signed-byte #.*max-linear-address-size*)
                     temp-rip) :x x86))

       ((when flg1)
        (!!ms-fresh :rm-size-error flg1))

       ((the (signed-byte #.*max-linear-address-size+1*) temp-rip)
        (1+ temp-rip))
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
       ;; Although this requirement is not specified in the Intel manual, I got
       ;; a segmentation fault when trying with non 16-byte aligned addresses
       ;; on a real machine.
       ((when (not (eql (mod v-addr 16) 0)))
        (!!ms-fresh :memory-address-is-not-16-byte-aligned v-addr))

       (imm0 (mbe :logic (part-select imm :low 0 :high 1)
                  :exec  (the (unsigned-byte 2)
                           (logand #x3 imm))))
       (imm1 (mbe :logic (part-select imm :low 2 :high 3)
                  :exec  (the (unsigned-byte 2)
                           (logand #x3 (ash imm -2)))))
       (imm2 (mbe :logic (part-select imm :low 4 :high 5)
                  :exec  (the (unsigned-byte 2)
                           (logand #x3 (ash imm -4)))))
       (imm3 (mbe :logic (part-select imm :low 6 :high 7)
                  :exec  (the (unsigned-byte 2)
                           (logand #x3 (ash imm -6)))))

       (dword0 (extract-32-bits xmm imm0))
       (dword1 (extract-32-bits xmm imm1))

       (dword2 (extract-32-bits xmm/mem imm2))
       (dword3 (extract-32-bits xmm/mem imm3))

       (result (merge-4-u32s dword3 dword2 dword1 dword0))

       ;; Update the x86 state:
       (x86 (!xmmi-size 16 xmm-index result x86))

       (x86 (!rip temp-rip x86)))
      x86)

  :implemented
  (add-to-implemented-opcodes-table 'SHUFPS #x0FC6
                                    '(:nil nil)
                                    'x86-shufps-Op/En-RMI))

(def-inst x86-shufpd-Op/En-RMI

  :parents (two-byte-opcodes fp-opcodes)

  :short "Shuffle packed double-precision floating-point values"

  :long
  "<h3>Op/En = RMI: \[OP XMM, XMM/M, IMM\]</h3>
  66 0F C6: SHUFPD xmm1, xmm2/m128, imm8<br/>"

  :returns (x86 x86p :hyp (x86p x86))

  :body
  (b* ((ctx 'x86-shufpd-Op/En-RMI)
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
         #.*xmm-access* 16 p2 p4? temp-rip rex-byte r/m mod sib 1 x86))

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

       ((mv flg1 (the (unsigned-byte 8) imm) x86)
        (rm-size 1 (the (signed-byte #.*max-linear-address-size*)
                     temp-rip) :x x86))

       ((when flg1)
        (!!ms-fresh :rm-size-error flg1))

       ((the (signed-byte #.*max-linear-address-size+1*) temp-rip)
        (1+ temp-rip))
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
       ;; Although this requirement is not specified in the Intel manual, I got
       ;; a segmentation fault when trying with non 16-byte aligned addresses
       ;; on a real machine.
       ((when (not (eql (mod v-addr 16) 0)))
        (!!ms-fresh :memory-address-is-not-16-byte-aligned v-addr))

       (imm0 (logbit 0 imm))
       (imm1 (logbit 1 imm))

       (qword0 (extract-64-bits xmm imm0))
       (qword1 (extract-64-bits xmm/mem imm1))

       (result (merge-2-u64s qword1 qword0))

       ;; Update the x86 state:
       (x86 (!xmmi-size 16 xmm-index result x86))

       (x86 (!rip temp-rip x86)))
      x86)

  :implemented
  (add-to-implemented-opcodes-table 'SHUFPD #x0FC6
                                    '(:misc
                                      (eql #.*mandatory-66h* (prefixes-slice :group-3-prefix prefixes)))
                                    'x86-shufpd-Op/En-RMI))

(def-inst x86-unpck?ps-Op/En-RM

  :parents (two-byte-opcodes fp-opcodes)

  :short "Unpack and interleave low/high packed single-precision floating-point
  values"

  :long
  "<h3>Op/En = RM: \[OP XMM, XMM/M\]</h3>
  0F 14: UNPCKLPS xmm1, xmm2/m128<br/>
  0F 15: UNPCKHPS xmm1, xmm2/m128<br/>"

  :high/low t

  :returns (x86 x86p :hyp (x86p x86))

  :prepwork
  ;; This is one of those cases where without this dumb lemma
  ;; logtail-96-of-usb-128, the guard proof succeeds if :guard-debug t
  ;; is provided.
  ((local
    (defthm-usb logtail-96-of-usb-128
      :hyp (unsigned-byte-p 128 x)
      :bound 32
      :concl (logtail 96 x)
      :hints (("Goal" :in-theory (e/d* (bitops::ihsext-recursive-redefs
                                        bitops::ihsext-inductions)
                                       (unsigned-byte-p))))
      :gen-linear t
      :hints-l (("Goal" :in-theory (e/d* ()
                                         (unsigned-byte-p-of-logtail)))))))

  :body
  (b* ((ctx 'x86-unpck?ps-Op/En-RM)
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

       (dword0 (if (int= high/low #.*HIGH-PACK*)
                   (mbe :logic (part-select xmm :low 64 :high 95)
                        :exec  (the (unsigned-byte 32)
                                 (logand #uxFFFF_FFFF (ash xmm -64))))
                 (mbe :logic (part-select xmm :low 0 :high 31)
                      :exec  (the (unsigned-byte 32)
                               (logand #uxFFFF_FFFF xmm)))))

       (dword1 (if (int= high/low #.*HIGH-PACK*)
                   (mbe :logic (part-select xmm/mem :low 64 :high 95)
                        :exec  (the (unsigned-byte 32)
                                 (logand #uxFFFF_FFFF (ash xmm/mem -64))))
                 (mbe :logic (part-select xmm/mem :low 0 :high 31)
                      :exec  (the (unsigned-byte 32)
                               (logand #uxFFFF_FFFF xmm/mem)))))

       (dword2 (if (int= high/low #.*HIGH-PACK*)
                   (mbe :logic (part-select xmm :low 96 :high 127)
                        :exec  (the (unsigned-byte 32)
                                 (logand #uxFFFF_FFFF (ash xmm -96))))
                 (mbe :logic (part-select xmm :low 32 :high 63)
                      :exec  (the (unsigned-byte 32)
                               (logand #uxFFFF_FFFF (ash xmm -32))))))

       (dword3 (if (int= high/low #.*HIGH-PACK*)
                   (mbe :logic (part-select xmm/mem :low 96 :high 127)
                        :exec  (the (unsigned-byte 32)
                                 (logand #uxFFFF_FFFF (ash xmm/mem -96))))
                 (mbe :logic (part-select xmm/mem :low 32 :high 63)
                      :exec  (the (unsigned-byte 32)
                               (logand #uxFFFF_FFFF (ash xmm/mem -32))))))

       (result (merge-4-u32s dword3 dword2 dword1 dword0))

       ;; Update the x86 state:
       (x86 (!xmmi-size 16 xmm-index result x86))

       (x86 (!rip temp-rip x86)))
      x86)
  :implemented
  (progn
    (add-to-implemented-opcodes-table 'UNPCKLPS #x0F14
                                      '(:nil nil)
                                      'x86-unpck?ps-Op/En-RM)
    (add-to-implemented-opcodes-table 'UNPCKHPS #x0F15
                                      '(:nil nil)
                                      'x86-unpck?ps-Op/En-RM)))

(def-inst x86-unpck?pd-Op/En-RM

  :parents (two-byte-opcodes fp-opcodes)

  :short "Unpack and interleave low/high packed double-precision floating-point
  values"

  :long
  "<h3>Op/En = RM: \[OP XMM, XMM/M\]</h3>
  66 0F 14: UNPCKLPD xmm1, xmm2/m128<br/>
  66 0F 15: UNPCKHPD xmm1, xmm2/m128<br/>"

  :high/low t

  :returns (x86 x86p :hyp (x86p x86))

  :prepwork
  ;; This is one of those cases where without this dumb lemma
  ;; x86-unpck?pd-Op/En-RM, the guard proof succeeds if :guard-debug t
  ;; is provided.
  ((local
    (defthm-usb logtail-64-of-usb-128
      :hyp (unsigned-byte-p 128 x)
      :bound 64
      :concl (logtail 64 x)
      :hints (("Goal" :in-theory (e/d* (bitops::ihsext-recursive-redefs
                                        bitops::ihsext-inductions)
                                       (unsigned-byte-p))))
      :gen-linear t
      :hints-l (("Goal" :in-theory (e/d* ()
                                         (unsigned-byte-p-of-logtail)))))))

  :body
  (b* ((ctx 'x86-unpck?pd-Op/En-RM)
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

       (qword0 (if (int= high/low #.*HIGH-PACK*)
                   (mbe :logic (part-select xmm :low 64 :high 127)
                        :exec  (the (unsigned-byte 64)
                                 (logand #uxFFFF_FFFF_FFFF_FFFF
                                         (ash xmm -64))))
                 (mbe :logic (part-select xmm :low 0 :high 63)
                      :exec  (the (unsigned-byte 64)
                               (logand #uxFFFF_FFFF_FFFF_FFFF xmm)))))

       (qword1 (if (int= high/low #.*HIGH-PACK*)
                   (mbe :logic (part-select xmm/mem :low 64 :high 127)
                        :exec  (the (unsigned-byte 64)
                                 (logand #uxFFFF_FFFF_FFFF_FFFF
                                         (ash xmm/mem -64))))
                 (mbe :logic (part-select xmm/mem :low 0 :high 63)
                      :exec  (the (unsigned-byte 64)
                               (logand #uxFFFF_FFFF_FFFF_FFFF xmm/mem)))))

       (result (merge-2-u64s qword1 qword0))

       ;; Update the x86 state:
       (x86 (!xmmi-size 16 xmm-index result x86))

       (x86 (!rip temp-rip x86)))
      x86)

  :implemented
  (progn
    (add-to-implemented-opcodes-table 'UNPCKLPD #x0F14
                                      '(:misc
                                        (eql #.*mandatory-66h* (prefixes-slice :group-3-prefix prefixes)))
                                      'x86-unpck?pd-Op/En-RM)
    (add-to-implemented-opcodes-table 'UNPCKHPD #x0F15
                                      '(:misc
                                        (eql #.*mandatory-66h* (prefixes-slice :group-3-prefix prefixes)))
                                      'x86-unpck?pd-Op/En-RM)))

;; ======================================================================
