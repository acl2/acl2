(in-package "X86ISA")

;; ======================================================================

(include-book "std/util/defaggregate" :dir :system)
(include-book "../decoding-and-spec-utils"
	      :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))

;; ======================================================================

;; ======================================================================
;; INSTRUCTION: STI
;; ======================================================================

;; machine/cpuid.lisp seems to have some info already, but I think it was WIP
;; and never completed (and hence the instruction was never implemented),
;; so I write my own set of cpuid info here

(defaggregate cpuid-info
              (eax ebx ecx edx))

(defconst *cpuid-basic-info* (list (make-cpuid-info
                                     ;; Model and version info 
                                     :eax 0
                                     ;; Brand index, CLFLUSH line size, Max addressable IDs for logical processors,
                                     ;; initial APIC ID
                                     ;; I think we can leave this 0 without issue
                                     :ebx 0
                                     ;; Some features
                                     ;; From a cursory glance, I think we don't support any of these features
                                     :ecx 0
                                     ;; Some more features
                                     :edx (logior (ash 1 3) ;; 4MB pages
                                                  (ash 1 5) ;; RDMSR and WRMSR
                                                  (ash 1 6) ;; PAE
                                                  (ash 1 17) ;; 36-bit page size extension
                                                  ))))
(defconst *cpuid-extended-info* nil)

;; Determine the correct cpu info for the given index and info set
(skip-proofs (defun get-cpu-info (idx relevant-info)
               (declare (xargs :verify-guards t))
               (b* (((when (not relevant-info)) nil)
                    ((when (equal idx 1)) (car relevant-info))
                    (cpu-info (get-cpu-info (1- idx) (cdr relevant-info)))
                    ((when (not cpu-info)) (car relevant-info)))
                   cpu-info)))

(skip-proofs (def-inst x86-cpuid

           ;; Op/En: ZO
           ;; 0f A2

           :parents (two-byte-opcodes)

           :guard-hints (("Goal" :in-theory (e/d (riml08 riml32) ())))

           :returns (x86 x86p :hyp (x86p x86))

           :body

           (b* ((requested-info (rr32 *eax* x86))
                ;; Choose between basic and extended data
                (basic-info? (< requested-info #x80000000))
                (relevant-info (if basic-info?
                                   *cpuid-basic-info*
                                   *cpuid-extended-info*))
                ;; This essentially removes the information about whether to use basic or extended data
                ;; and lets us use this value to index into the separate lists
                (info-idx (mod requested-info #x80000000))
                (info (if (or (not relevant-info)
                              (equal info-idx 0)) 
                          ;; Handle the case when the index is 0 separately
                          (make-cpuid-info :eax (+ (len relevant-info)
                                                   (if basic-info?
                                                       0
                                                       #x80000000))
                                           :ebx 0
                                           :ecx 0
                                           :edx 0)
                          (get-cpu-info info-idx relevant-info)))
                (x86 (wr32 *eax* (cpuid-info->eax info) x86))
                (x86 (wr32 *ebx* (cpuid-info->ebx info) x86))
                (x86 (wr32 *ecx* (cpuid-info->ecx info) x86))
                (x86 (wr32 *edx* (cpuid-info->edx info) x86)))
               (write-*ip proc-mode temp-rip x86))))
