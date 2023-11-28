(in-package "X86ISA")

(include-book "../decoding-and-spec-utils"
	      :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))
(include-book "../top-level-memory")

;; TODO use some macros to make this nicer
;; tbf this was written with the help of macros -- just nvim macros, not lisp macros

(skip-proofs (def-inst x86-fxsave/fxsave64

		       ;; Op/En: M
		       ;; 0F AE /0: fxsave
		       ;; REX.W + 00F AE /0: fxsave64

		       :parents (two-byte-opcodes)

		       :guard-hints (("Goal" :in-theory (e/d () ())))

		       :returns (x86 x86p :hyp (x86p x86))

           :modr/m t

		       :body

           (b* ((p2 (prefixes->seg prefixes))
                (p4? (equal #.*addr-size-override*
                            (prefixes->adr prefixes)))
                ;; TODO this should always be a memory address size, right?
                ((the (integer 1 8) operand-size)
                 (select-operand-size proc-mode nil rex-byte nil prefixes nil nil nil x86))
                (seg-reg (select-segment-register proc-mode p2 p4? mod r/m sib x86))
                (inst-ac? nil) ;; TODO check 16 byte alignment requirement
                ((mv flg & (the (unsigned-byte 3) increment-RIP-by) (the (signed-byte 64) dest-addr) x86)
                 (x86-operand-from-modr/m-and-sib-bytes proc-mode
                                                        0
                                                        operand-size
                                                        inst-ac?
                                                        t ;; Memory ptr operand
                                                        seg-reg
                                                        p4?
                                                        temp-rip
                                                        rex-byte
                                                        r/m
                                                        mod
                                                        sib
                                                        0 ;; No immediate operand
                                                        x86))
                ((when flg) (!!ms-fresh :x86-operand-from-modr/m-and-sib-bytes flg))
                ((mv flg (the (signed-byte #.*max-linear-address-size*) temp-rip))
                 (add-to-*ip proc-mode temp-rip increment-RIP-by x86))
                ((when flg) (!!ms-fresh :rip-increment-error temp-rip))

                ;; Most of the first 32 bytes of the output have to do with the x87 state,
                ;; which has not been implemented
                ;; The only thing we output for now in this region is mxcsr and mxcsr mask
                ;; TODO update this if more of the x87 is implemented
                ((mv flg x86) (wme128 proc-mode (+ 24 dest-addr) seg-reg (mxcsr x86) inst-ac?  x86))
                ((when flg) (!!ms-fresh :wme128 proc-mode flg))
                ((mv flg x86) (wme128 proc-mode (+ 28 dest-addr) seg-reg #xFFFF inst-ac? x86))
                ((when flg) (!!ms-fresh :wme128 proc-mode flg))
                ;; We don't have MMX registers, so we don't save those
                ((mv flg x86) (wme128 proc-mode (+ 160 0 dest-addr) seg-reg (rx128 0 x86) inst-ac? x86))
                ((when flg) (!!ms-fresh :wme128 proc-mode flg))
                ((mv flg x86) (wme128 proc-mode (+ 160 16 dest-addr) seg-reg (rx128 1 x86) inst-ac? x86))
                ((when flg) (!!ms-fresh :wme128 proc-mode flg))
                ((mv flg x86) (wme128 proc-mode (+ 160 32 dest-addr) seg-reg (rx128 2 x86) inst-ac? x86))
                ((when flg) (!!ms-fresh :wme128 proc-mode flg))
                ((mv flg x86) (wme128 proc-mode (+ 160 48 dest-addr) seg-reg (rx128 3 x86) inst-ac? x86))
                ((when flg) (!!ms-fresh :wme128 proc-mode flg))
                ((mv flg x86) (wme128 proc-mode (+ 160 64 dest-addr) seg-reg (rx128 4 x86) inst-ac? x86))
                ((when flg) (!!ms-fresh :wme128 proc-mode flg))
                ((mv flg x86) (wme128 proc-mode (+ 160 80 dest-addr) seg-reg (rx128 5 x86) inst-ac? x86))
                ((when flg) (!!ms-fresh :wme128 proc-mode flg))
                ((mv flg x86) (wme128 proc-mode (+ 160 96 dest-addr) seg-reg (rx128 6 x86) inst-ac? x86))
                ((when flg) (!!ms-fresh :wme128 proc-mode flg))
                ((mv flg x86) (wme128 proc-mode (+ 160 112 dest-addr) seg-reg (rx128 7 x86) inst-ac? x86))
                ((when flg) (!!ms-fresh :wme128 proc-mode flg))
                (x86 (if (equal operand-size *64-bit-mode*)
                         (b* (((mv flg x86) (wme128 proc-mode (+ 288 0 dest-addr) seg-reg (rx128 8 x86) inst-ac? x86))
                              ((when flg) (!!ms-fresh :wme128 proc-mode flg))
                              ((mv flg x86) (wme128 proc-mode (+ 288 16 dest-addr) seg-reg (rx128 9 x86) inst-ac? x86))
                              ((when flg) (!!ms-fresh :wme128 proc-mode flg))
                              ((mv flg x86) (wme128 proc-mode (+ 288 32 dest-addr) seg-reg (rx128 10 x86) inst-ac? x86))
                              ((when flg) (!!ms-fresh :wme128 proc-mode flg))
                              ((mv flg x86) (wme128 proc-mode (+ 288 48 dest-addr) seg-reg (rx128 11 x86) inst-ac? x86))
                              ((when flg) (!!ms-fresh :wme128 proc-mode flg))
                              ((mv flg x86) (wme128 proc-mode (+ 288 64 dest-addr) seg-reg (rx128 12 x86) inst-ac? x86))
                              ((when flg) (!!ms-fresh :wme128 proc-mode flg))
                              ((mv flg x86) (wme128 proc-mode (+ 288 80 dest-addr) seg-reg (rx128 13 x86) inst-ac? x86))
                              ((when flg) (!!ms-fresh :wme128 proc-mode flg))
                              ((mv flg x86) (wme128 proc-mode (+ 288 96 dest-addr) seg-reg (rx128 14 x86) inst-ac? x86))
                              ((when flg) (!!ms-fresh :wme128 proc-mode flg))
                              ((mv flg x86) (wme128 proc-mode (+ 288 112 dest-addr) seg-reg (rx128 15 x86) inst-ac? x86))
                              ((when flg) (!!ms-fresh :wme128 proc-mode flg)))
                             x86)
                         x86)))
               (write-*ip proc-mode temp-rip x86))))

(skip-proofs (def-inst x86-fxrstor/fxrstor64

		       ;; Op/En: M
		       ;; 0F AE /0: fxrstor
		       ;; REX.W + 00F AE /0: fxrstor64

		       :parents (two-byte-opcodes)

		       :guard-hints (("Goal" :in-theory (e/d (riml08 riml32) ())))

		       :returns (x86 x86p :hyp (x86p x86))

           :modr/m t

		       :body

           (b* ((p2 (prefixes->seg prefixes))
                (p4? (equal #.*addr-size-override*
                            (prefixes->adr prefixes)))
                ;; TODO this should always be a memory address size, right?
                ((the (integer 1 8) operand-size)
                 (select-operand-size proc-mode nil rex-byte nil prefixes nil nil nil x86))
                (seg-reg (select-segment-register proc-mode p2 p4? mod r/m sib x86))
                (inst-ac? nil) ;; TODO check 16 byte alignment requirement
                ((mv flg & (the (unsigned-byte 3) increment-RIP-by) (the (signed-byte 64) src-addr) x86)
                 (x86-operand-from-modr/m-and-sib-bytes proc-mode
                                                        0
                                                        operand-size
                                                        inst-ac?
                                                        t ;; Memory ptr operand
                                                        seg-reg
                                                        p4?
                                                        temp-rip
                                                        rex-byte
                                                        r/m
                                                        mod
                                                        sib
                                                        0 ;; No immediate operand
                                                        x86))
                ((when flg) (!!ms-fresh :x86-operand-from-modr/m-and-sib-bytes flg))
                ((mv flg (the (signed-byte #.*max-linear-address-size*) temp-rip))
                 (add-to-*ip proc-mode temp-rip increment-RIP-by x86))
                ((when flg) (!!ms-fresh :rip-increment-error temp-rip))

                ;; Most of the first 32 bytes of the output have to do with the x87 state,
                ;; which has not been implemented
                ;; The only thing we read for now in this region is mxcsr and mxcsr mask
                ;; TODO update this if more of the x87 is implemented
                ((mv flg mxcsr x86) (rime32 proc-mode (+ 24 src-addr) seg-reg :r inst-ac? x86))
                ((when flg) (!!ms-fresh :rime32 proc-mode flg))
                ;; TODO check if we're supposed to read the mxcsr-mask or not
                ((mv flg mxcsr-mask x86) (rime32 proc-mode (+ 28 src-addr) seg-reg :r inst-ac? x86))
                ((when flg) (!!ms-fresh :rime32 proc-mode flg))
                (mxcsr (logand mxcsr mxcsr-mask))
                ((when (not (equal (logand mxcsr #xFFFF0000) 0)))
                 (!!fault-fresh :gp 0 :mxcsr-error mxcsr))
                (x86 (!mxcsr mxcsr x86))

                ;; We don't have MMX registers, so we don't restore those
                ((mv flg val x86) (rme128 proc-mode (+ 160 0 src-addr) seg-reg :r inst-ac? x86))
                ((when flg) (!!ms-fresh :rme128 proc-mode flg))
                (x86 (wx128 0 val x86))
                ((mv flg val x86) (rme128 proc-mode (+ 160 16 src-addr) seg-reg :r inst-ac? x86))
                ((when flg) (!!ms-fresh :rme128 proc-mode flg))
                (x86 (wx128 1 val x86))
                ((mv flg val x86) (rme128 proc-mode (+ 160 32 src-addr) seg-reg :r inst-ac? x86))
                ((when flg) (!!ms-fresh :rme128 proc-mode flg))
                (x86 (wx128 2 val x86))
                ((mv flg val x86) (rme128 proc-mode (+ 160 48 src-addr) seg-reg :r inst-ac? x86))
                ((when flg) (!!ms-fresh :rme128 proc-mode flg))
                (x86 (wx128 3 val x86))
                ((mv flg val x86) (rme128 proc-mode (+ 160 64 src-addr) seg-reg :r inst-ac? x86))
                ((when flg) (!!ms-fresh :rme128 proc-mode flg))
                (x86 (wx128 4 val x86))
                ((mv flg val x86) (rme128 proc-mode (+ 160 80 src-addr) seg-reg :r inst-ac? x86))
                ((when flg) (!!ms-fresh :rme128 proc-mode flg))
                (x86 (wx128 5 val x86))
                ((mv flg val x86) (rme128 proc-mode (+ 160 96 src-addr) seg-reg :r inst-ac? x86))
                ((when flg) (!!ms-fresh :rme128 proc-mode flg))
                (x86 (wx128 6 val x86))
                ((mv flg val x86) (rme128 proc-mode (+ 160 112 src-addr) seg-reg :r inst-ac? x86))
                ((when flg) (!!ms-fresh :rme128 proc-mode flg))
                (x86 (wx128 7 val x86))
                (x86 (if (equal operand-size *64-bit-mode*)
                       (b* (((mv flg val x86) (rme128 proc-mode (+ 288 0 src-addr) seg-reg :r inst-ac? x86))
                            ((when flg) (!!ms-fresh :rme128 proc-mode flg))
                            (x86 (wx128 8 val x86))
                            ((mv flg val x86) (rme128 proc-mode (+ 288 16 src-addr) seg-reg :r inst-ac? x86))
                            ((when flg) (!!ms-fresh :rme128 proc-mode flg))
                            (x86 (wx128 9 val x86))
                            ((mv flg val x86) (rme128 proc-mode (+ 288 32 src-addr) seg-reg :r inst-ac? x86))
                            ((when flg) (!!ms-fresh :rme128 proc-mode flg))
                            (x86 (wx128 10 val x86))
                            ((mv flg val x86) (rme128 proc-mode (+ 288 48 src-addr) seg-reg :r inst-ac? x86))
                            ((when flg) (!!ms-fresh :rme128 proc-mode flg))
                            (x86 (wx128 11 val x86))
                            ((mv flg val x86) (rme128 proc-mode (+ 288 64 src-addr) seg-reg :r inst-ac? x86))
                            ((when flg) (!!ms-fresh :rme128 proc-mode flg))
                            (x86 (wx128 12 val x86))
                            ((mv flg val x86) (rme128 proc-mode (+ 288 80 src-addr) seg-reg :r inst-ac? x86))
                            ((when flg) (!!ms-fresh :rme128 proc-mode flg))
                            (x86 (wx128 13 val x86))
                            ((mv flg val x86) (rme128 proc-mode (+ 288 96 src-addr) seg-reg :r inst-ac? x86))
                            ((when flg) (!!ms-fresh :rme128 proc-mode flg))
                            (x86 (wx128 14 val x86))
                            ((mv flg val x86) (rme128 proc-mode (+ 288 112 src-addr) seg-reg :r inst-ac? x86))
                            ((when flg) (!!ms-fresh :rme128 proc-mode flg))
                            (x86 (wx128 15 val x86)))
                           x86)
                       x86)))
           (write-*ip proc-mode temp-rip x86))))
