(in-package "X86ISA")

;; ======================================================================

(include-book "../decoding-and-spec-utils"
	      :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))

(skip-proofs (def-inst x86-invlpg

                       ;; Op/En: M
                       ;; 0F 01/7

                       :parents (two-byte-opcodes)

                       :guard-hints (("Goal" :in-theory (e/d (riml08 riml32) ())))

                       :returns (x86 x86p :hyp (x86p x86))

                       :modr/m t

                       :body

                       (b* ((p4? (equal #.*addr-size-override*
                                        (prefixes->adr prefixes)))

                            ((mv flg0
                                 (the (signed-byte 64) addr)
                                 (the (unsigned-byte 3) increment-RIP-by)
                                 x86)
                             (if (equal mod #b11)
                               (mv nil 0 0 x86)
                               (x86-effective-addr proc-mode p4?
                                                   temp-rip
                                                   rex-byte
                                                   r/m
                                                   mod
                                                   sib
                                                   0 ;; No immediate operand
                                                   x86)))
                            ((when flg0)
                             (!!ms-fresh :x86-effective-addr flg0))

                            (vpn (ash addr -12))
                            (tlb (tlb x86))
                            (tlb (hons-acons (logior (ash vpn 3)
                                                     (ash 0 2)
                                                     0) nil tlb))
                            (tlb (hons-acons (logior (ash vpn 3)
                                                     (ash 0 2)
                                                     1) nil tlb))
                            (tlb (hons-acons (logior (ash vpn 3)
                                                     (ash 0 2)
                                                     2) nil tlb))
                            (tlb (hons-acons (logior (ash vpn 3)
                                                     (ash 1 2)
                                                     0) nil tlb))
                            (tlb (hons-acons (logior (ash vpn 3)
                                                     (ash 1 2)
                                                     1) nil tlb))
                            (tlb (hons-acons (logior (ash vpn 3)
                                                     (ash 1 2)
                                                     2) nil tlb))
                            (x86 (!tlb tlb x86))

                            ((mv flg (the (signed-byte #.*max-linear-address-size*) temp-rip))
                             (add-to-*ip proc-mode temp-rip increment-RIP-by x86))
                            ((when flg) (!!ms-fresh :next-rip-invalid temp-rip))

                            (badlength? (check-instruction-length start-rip temp-rip 0))
                            ((when badlength?)
                             (!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

                            ;; Update the x86 state:
                            (x86 (write-*ip proc-mode temp-rip x86)))
                           x86)))
