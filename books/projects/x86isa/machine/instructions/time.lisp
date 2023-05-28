(in-package "X86ISA")

(include-book "../decoding-and-spec-utils"
	      :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))

;; ======================================================================
;; INSTRUCTION: RDTSC
;; ======================================================================

(skip-proofs (def-inst x86-rdtsc

  ;; Op/En: ZO
  ;; 0F 31

  :parents (one-byte-opcodes)

  :guard-hints (("Goal" :in-theory (e/d (riml08 riml32) ())))

  :returns (x86 x86p :hyp (x86p x86))

  :body


  ;; Loads the time stamp counter into EDX:EAX
  (b* ((time-stamp-counter (time-stamp-counter x86))
       (x86 (wr32 *eax* (logand (1- (ash 1 32)) time-stamp-counter) x86))
       (x86 (wr32 *edx* (logand (1- (ash 1 32)) (ash time-stamp-counter -32)) x86)))
      (write-*ip proc-mode temp-rip x86))))
