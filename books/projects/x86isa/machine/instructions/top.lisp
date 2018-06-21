;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")

;; ======================================================================

(include-book "arith-and-logic"
              :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))
(include-book "bit"
              :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))
(include-book "conditional"
              :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))
(include-book "divide"
              :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))
(include-book "exchange"
              :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))
(include-book "jump-and-loop"
              :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))
(include-book "move"
              :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))
(include-book "multiply"
              :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))
(include-book "push-and-pop"
              :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))
(include-book "rotate-and-shift"
              :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))
(include-book "segmentation"
              :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))
(include-book "signextend"
              :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))
(include-book "string"
              :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))
(include-book "syscall"
              :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))
(include-book "subroutine"
              :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))
(include-book "fp/top"
              :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))

;; ======================================================================

(defsection instructions
  :parents (machine)
  )

(defsection one-byte-opcodes
  :parents (instructions)
  )

(defsection two-byte-opcodes
  :parents (instructions)
  )

(defsection fp-opcodes
  :parents (instructions)
  )

(defsection privileged-opcodes
  :parents (instructions)
  )

(defsection instruction-semantic-functions
  :parents (instructions)
  :short "Instruction Semantic Functions"
  :long "<p>The instruction semantic functions have dual roles:</p>

<ol>
 <li>They fetch the instruction's operands, as dictated by the decoded
  components of the instruction \(like the prefixes, SIB byte, etc.\)
  provided as input; these decoded components are provided by our x86
  decoder function @(see x86-fetch-decode-execute).</li>

  <li> They contain or act as the functional specification of the
  instructions.  For example, the functional specification function of
  the ADD instruction returns two values: the appropriately truncated
  sum of the operands and the modified flags. We do not deal with the
  x86 state in these specifications.</li>
</ol>

<p>Each semantic function takes, among other arguments, the value
@('start-rip') of the instruction pointer at the beginning of the
instruction, and the value @('temp-rip') of the instruction pointer
after the decoding of the prefixes, REX byte, opcode, ModR/M byte, and
SIB byte (some of these bytes may not be present).  The semantic
function may further increment the instruction pointer beyond
@('temp-rip') to read the ending bytes of the instruction, e.g. to
read a displacement or an immediate.  The semantic function eventually
writes the final value of the instruction pointer into RIP.</p>")

;; Misc. instructions not categorized yet into the books included above or not
;; yet placed in their own separate books follow.

;; ======================================================================
;; INSTRUCTION: HLT
;; ======================================================================

;; [Shilpi]: I haven't specified the halt instruction accurately --- halt can
;; be called only in the supervisor mode.  For now, we use the HALT instruction
;; for convenience, e.g., when we want to stop program execution.

; Extended to 32-bit mode by Alessandro Coglio <coglio@kestrel.edu>
(def-inst x86-hlt

  ;; Op/En: NP
  ;; F4

  :parents (one-byte-opcodes)
  :guard-hints (("Goal" :in-theory (e/d (riml08 riml32) ())))

  :returns (x86 x86p :hyp (and (x86p x86)
                               (canonical-address-p temp-rip)))
  :implemented
  (add-to-implemented-opcodes-table 'HLT #xF4 '(:nil nil) 'x86-hlt)

  :body

  (b* ((ctx 'x86-hlt)
       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock?) (!!fault-fresh :ud nil :lock-prefix prefixes)) ;; #UD

       ;; Update the x86 state:

       ;; Intel Vol. 2A, HLT specification: Instruction pointer is saved.
       ;; "If an interrupt ... is used to resume execution after a HLT
       ;; instruction, the saved instruction pointer points to the instruction
       ;; following the HLT instruction."
       (x86 (write-*ip temp-rip x86)))
    (!!ms-fresh :legal-halt :hlt)))

;; ======================================================================
;; INSTRUCTION: CMC/CLC/STC/CLD/STD
;; ======================================================================

; Extended to 32-bit mode by Alessandro Coglio <coglio@kestrel.edu>
(def-inst x86-cmc/clc/stc/cld/std

  ;; Op/En: NP
  ;; F5: CMC (CF complemented, all other flags are unaffected)
  ;; F8: CLC (CF cleared, all other flags are unaffected)
  ;; F9: STC (CF set, all other flags are unaffected)
  ;; FC: CLD (DF cleared, all other flags are unaffected)
  ;; FD: STD (DF set, all other flags are unaffected)

  :parents (one-byte-opcodes)
  :guard-hints (("Goal" :in-theory (e/d (riml08 riml32) ())))

  :returns (x86 x86p :hyp (and (x86p x86)
                               (canonical-address-p temp-rip)))
  :implemented
  (progn
    (add-to-implemented-opcodes-table 'CMC #xF5 '(:nil nil)
                                      'x86-cmc/clc/stc/cld/std)
    (add-to-implemented-opcodes-table 'CLC #xF8 '(:nil nil)
                                      'x86-cmc/clc/stc/cld/std)
    (add-to-implemented-opcodes-table 'STC #xF9 '(:nil nil)
                                      'x86-cmc/clc/stc/cld/std)
    (add-to-implemented-opcodes-table 'CLD #xFC '(:nil nil)
                                      'x86-cmc/clc/stc/cld/std)
    (add-to-implemented-opcodes-table 'STD #xFD '(:nil nil)
                                      'x86-cmc/clc/stc/cld/std))

  :body

  (b* ((ctx 'x86-cmc/clc/stc/cld/std)

       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock?) (!!fault-fresh :ud nil :lock-prefix prefixes)) ;; #UD

       (x86 (case opcode
              (#xF5 ;; CMC
               (let* ((cf (the (unsigned-byte 1)
                            (flgi #.*cf* x86)))
                      (not-cf (if (equal cf 1) 0 1)))
                 (!flgi #.*cf* not-cf x86)))
              (#xF8 ;; CLC
               (!flgi #.*cf* 0 x86))
              (#xF9 ;; STC
               (!flgi #.*cf* 1 x86))
              (#xFC ;; CLD
               (!flgi #.*df* 0 x86))
              (otherwise ;; #xFD STD
               (!flgi #.*df* 1 x86))))

       (x86 (write-*ip temp-rip x86)))
      x86))

;; ======================================================================
;; INSTRUCTION: SAHF
;; ======================================================================

; Extended to 32-bit mode by Alessandro Coglio <coglio@kestrel.edu>
(def-inst x86-sahf

  ;; Opcode: #x9E

  ;; TO-DO@Shilpi: The following instruction is valid in 64-bit mode
  ;; only if the CPUID.80000001H:ECX.LAHF-SAHF[bit0] = 1.

  :parents (one-byte-opcodes)
  :guard-hints (("Goal" :in-theory (e/d (riml08 riml32) ())))

  :returns (x86 x86p :hyp (and (x86p x86)
                               (canonical-address-p temp-rip)))
  :implemented
  (add-to-implemented-opcodes-table 'SAHF #x9E '(:nil nil) 'x86-sahf)

  :body

  (b* ((ctx 'x86-sahf)
       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock?) (!!fault-fresh :ud nil :lock-prefix prefixes)) ;; #UD
       ((the (unsigned-byte 16) ax)
        (mbe :logic (rgfi-size 2 *rax* rex-byte x86)
             :exec (rr16 *rax* x86)))
       ((the (unsigned-byte 8) ah) (ash ax -8))
       ;; Bits 1, 3, and 5 of eflags are unaffected, with the values remaining
       ;; 1, 0, and 0, respectively.
       ((the (unsigned-byte 8) ah) (logand #b11010111 (logior #b10 ah)))
       ;; Update the x86 state:
       (x86 (!rflags ah x86))
       (x86 (write-*ip temp-rip x86)))
      x86))

;; ======================================================================
;; INSTRUCTION: LAHF
;; ======================================================================

; Extended to 32-bit mode by Alessandro Coglio <coglio@kestrel.edu>
(def-inst x86-lahf

  ;; Opcode: #x9F

  ;; TO-DO@Shilpi: The following instruction is valid in 64-bit mode
  ;; only if the CPUID.80000001H:ECX.LAHF-LAHF[bit0] = 1.

  :parents (one-byte-opcodes)
  :guard-hints (("Goal" :in-theory (e/d (riml08 riml32) ())))

  :returns (x86 x86p :hyp (and (x86p x86)
                               (canonical-address-p temp-rip)))
  :implemented
  (add-to-implemented-opcodes-table 'LAHF #x9F '(:nil nil) 'x86-lahf)

  :body

  (b* ((ctx 'x86-lahf)
       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock?) (!!fault-fresh :ud nil :lock-prefix prefixes)) ;; #UD
       ((the (unsigned-byte 8) ah)
        (logand #xff (the (unsigned-byte 32) (rflags x86))))
       ((the (unsigned-byte 16) ax)
        (mbe :logic (rgfi-size 2 *rax* rex-byte x86)
             :exec (rr16 *rax* x86)))
       ((the (unsigned-byte 16) ax) (logior (logand #xff00 ax) ah))
       ;; Update the x86 state:
       (x86 (mbe :logic (!rgfi-size 2 *rax* ax rex-byte x86)
                 :exec (wr16 *rax* ax x86)))
       (x86 (write-*ip temp-rip x86)))
      x86))

;; ======================================================================
;; INSTRUCTION: RDRAND
;; ======================================================================

; Extended to 32-bit mode by Alessandro Coglio <coglio@kestrel.edu>
(def-inst x86-rdrand

  ;; 0F C7:
  ;; Opcode Extensions:
  ;; Bits 5,4,3 of the ModR/M byte (reg): 110
  ;; Bits 7,6 of the ModR/M byte (mod):    11

  :parents (two-byte-opcodes)

  :returns (x86 x86p :hyp (and (x86p x86)
                               (canonical-address-p temp-rip))
                :hints (("Goal" :in-theory (e/d (hw_rnd_gen
                                                 hw_rnd_gen-logic)
                                                (force (force))))))
  :implemented
  (add-to-implemented-opcodes-table 'RDRAND #x0FC7 '(:reg 6 :mod 3)
                                    'x86-rdrand)

  :long
  "<p>Note from the Intel Manual (March 2017, Vol. 1, Section 7.3.17):</p>

<p><em>Under heavy load, with multiple cores executing RDRAND in
parallel, it is possible, though unlikely, for the demand of random
numbers by software processes or threads to exceed the rate at which
the random number generator hardware can supply them. This will lead
to the RDRAND instruction returning no data transitorily. The RDRAND
instruction indicates the occurrence of this rare situation by
clearing the CF flag.</em></p>

<p>See <a
href='http://software.intel.com/en-us/articles/intel-digital-random-number-generator-drng-software-implementation-guide/'>Intel's
Digital Random Number Generator Guide</a> for more details.</p>"

  :body

  (b* ((ctx 'x86-rdrand)
       (reg (the (unsigned-byte 3) (mrm-reg  modr/m)))

       ;; TODO: throw #UD if CPUID.01H:ECX.RDRAND[bit 30] = 0
       ;; (see Intel manual, Mar'17, Vol 2, RDRAND)

       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       (rep (prefixes-slice :group-2-prefix prefixes))
       (rep-p (or (equal #.*repe* rep)
                  (equal #.*repne* rep)))
       ((when (or lock? rep-p))
        (!!fault-fresh :ud nil :lock-prefix-or-rep-p prefixes)) ;; #UD

       ((the (integer 1 8) operand-size)
        (select-operand-size nil rex-byte nil prefixes x86))

       ((mv cf rand x86)
        (HW_RND_GEN operand-size x86))

       ;; (- (cw "~%~%HW_RND_GEN: If RDRAND does not return the result you ~
       ;;         expected (or returned an error), then you might want ~
       ;;         to check whether these ~
       ;;         books were compiled using x86isa_exec set to t. See ~
       ;;         :doc x86isa-build-instructions.~%~%"))

       ((when (ms x86))
        (!!ms-fresh :x86-rdrand (ms x86)))
       ((when (or (not (unsigned-byte-p 1 cf))
                  (not (unsigned-byte-p (ash operand-size 3) rand))))
        (!!ms-fresh :x86-rdrand-ill-formed-outputs (ms x86)))

       ;; Update the x86 state:
       (x86 (!rgfi-size operand-size (reg-index reg rex-byte #.*r*)
                        rand rex-byte x86))
       (x86 (let* ((x86 (!flgi #.*cf* cf x86))
                   (x86 (!flgi #.*pf* 0 x86))
                   (x86 (!flgi #.*af* 0 x86))
                   (x86 (!flgi #.*zf* 0 x86))
                   (x86 (!flgi #.*sf* 0 x86))
                   (x86 (!flgi #.*of* 0 x86)))
              x86))
       (x86 (write-*ip temp-rip x86)))
      x86))

;; ======================================================================

;; To see the rules in the instruction-decoding-and-spec-rules
;; ruleset:

(define show-inst-decoding-and-spec-fn
  ((state))
  :mode :program
  (let ((world (w state)))
    (ruleset-theory 'instruction-decoding-and-spec-rules)))

(defmacro show-inst-decoding-and-spec-ruleset ()
  `(show-inst-decoding-and-spec-fn state))

;; ======================================================================
