(in-package "X86ISA")

(include-book "../decoding-and-spec-utils"
	      :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))

;; ======================================================================
;; INSTRUCTION: RDTSC
;; ======================================================================

(def-inst x86-rdtsc

          ;; Op/En: ZO
          ;; 0F 31

          :parents (one-byte-opcodes)

          :guard-hints (("Goal" :in-theory (e/d () ())))

          :returns (x86 x86p :hyp (x86p x86))

          :prepwork
          ((local (defthm integerp-natp (implies (natp x)
                                                 (integerp x)))))

          :body


          ;; Loads the time stamp counter into EDX:EAX
          (b* ((time-stamp-counter (time-stamp-counter x86))
               (x86 (wr32 *eax* (loghead 32 time-stamp-counter) x86))
               (x86 (wr32 *edx* (loghead 32 (logtail 32 time-stamp-counter)) x86)))
              (write-*ip proc-mode temp-rip x86)))
