; X86ISA Library

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2015, Regents of the University of Texas
; Copyright (C) 2018, Kestrel Technology, LLC
; All rights reserved.

; Redistribution and use in source and binary forms, with or without
; modification, are permitted provided that the following conditions are
; met:

; o Redistributions of source code must retain the above copyright
;   notice, this list of conditions and the following disclaimer.

; o Redistributions in binary form must reproduce the above copyright
;   notice, this list of conditions and the following disclaimer in the
;   documentation and/or other materials provided with the distribution.

; o Neither the name of the copyright holders nor the names of its
;   contributors may be used to endorse or promote products derived
;   from this software without specific prior written permission.

; THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
; "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
; LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
; A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
; HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
; SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
; LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
; DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
; THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
; (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
; OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

; Original Author(s):
; Shilpi Goel         <shigoel@cs.utexas.edu>
; Contributing Author(s):
; Alessandro Coglio   <coglio@kestrel.edu>

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
  :short "Umbrella topic for specification of Intel's x86 instructions"
  )

(defsection one-byte-opcodes
  :parents (instructions)
  :short "Instruction semantic functions for Intel's instructions with a
  one-byte opcode" )

(defsection two-byte-opcodes
  :parents (instructions)
  :short "Instruction semantic functions for Intel's instructions with two-byte
  opcodes" )

(defsection fp-opcodes
  :parents (instructions)
  :short "Instruction semantic functions for Intel's floating-point instructions"
  )

(defsection privileged-opcodes
  :parents (instructions)
  :short "Instruction semantic functions for Intel's privileged instructions"
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

(def-inst x86-hlt

  ;; Op/En: NP
  ;; F4

  :parents (one-byte-opcodes)

  :guard-hints (("Goal" :in-theory (e/d (riml08 riml32) ())))

  :returns (x86 x86p :hyp (x86p x86))

  :body

  (b* (;; Update the x86 state:
       ;; Intel Vol. 2A, HLT specification: Instruction pointer is saved.
       ;; "If an interrupt ... is used to resume execution after a HLT
       ;; instruction, the saved instruction pointer points to the instruction
       ;; following the HLT instruction."
       (x86 (write-*ip proc-mode temp-rip x86)))
    (!!ms-fresh :legal-halt :hlt)))

;; ======================================================================
;; INSTRUCTION: CMC/CLC/STC/CLD/STD
;; ======================================================================

(def-inst x86-cmc/clc/stc/cld/std

  ;; Op/En: NP
  ;; F5: CMC (CF complemented, all other flags are unaffected)
  ;; F8: CLC (CF cleared, all other flags are unaffected)
  ;; F9: STC (CF set, all other flags are unaffected)
  ;; FC: CLD (DF cleared, all other flags are unaffected)
  ;; FD: STD (DF set, all other flags are unaffected)

  :parents (one-byte-opcodes)

  :guard-hints (("Goal" :in-theory (e/d (riml08 riml32) ())))

  :returns (x86 x86p :hyp (x86p x86))

  :body

  (b* ((x86 (case opcode
              (#xF5 ;; CMC
               (let* ((cf (the (unsigned-byte 1)
                            (flgi :cf x86)))
                      (not-cf (if (equal cf 1) 0 1)))
                 (!flgi :cf not-cf x86)))
              (#xF8 ;; CLC
               (!flgi :cf 0 x86))
              (#xF9 ;; STC
               (!flgi :cf 1 x86))
              (#xFC ;; CLD
               (!flgi :df 0 x86))
              (otherwise ;; #xFD STD
               (!flgi :df 1 x86))))

       (x86 (write-*ip proc-mode temp-rip x86)))
      x86))

;; ======================================================================
;; INSTRUCTION: SAHF
;; ======================================================================

(def-inst x86-sahf

  ;; Opcode: #x9E

  :parents (one-byte-opcodes)

  :guard-hints (("Goal" :in-theory (e/d (riml08 riml32) ())))

  :returns (x86 x86p :hyp (x86p x86))

  :body

  (b* (((the (unsigned-byte 16) ax) (rr16 #.*rax* x86))
       ((the (unsigned-byte 8) ah) (ash ax -8))
       ((the (unsigned-byte 32) rflags) (rflags x86))
       ;; Bits 1, 3, and 5 of eflags are unaffected, with the values remaining
       ;; 1, 0, and 0, respectively.
       (cf (rflagsBits->cf ah))
       (pf (rflagsBits->pf ah))
       (af (rflagsBits->af ah))
       (zf (rflagsBits->zf ah))
       (sf (rflagsBits->sf ah))
       ((the (unsigned-byte 32) new-rflags)
        (!rflagsBits->cf
         cf
         (!rflagsBits->pf
          pf
          (!rflagsBits->af
           af
           (!rflagsBits->zf
            zf
            (!rflagsBits->sf
             sf
             rflags))))))
       ;; Update the x86 state:
       (x86 (!rflags new-rflags x86))
       (x86 (write-*ip proc-mode temp-rip x86)))
    x86))

;; ======================================================================
;; INSTRUCTION: LAHF
;; ======================================================================

(def-inst x86-lahf

  ;; Opcode: #x9F

  :parents (one-byte-opcodes)

  :guard-hints (("Goal" :in-theory (e/d* (rflag-RoWs-enables
                                          riml08 riml32)
                                         ((tau-system)))))

  :returns (x86 x86p :hyp (x86p x86))

  :prepwork
  ((local
    (defthm unsigned-byte-p-8-of-rflagsBits-for-lahf
      (< (rflagsbits cf 1 pf 0 af 0 zf sf 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
         256)
      :hints (("Goal" :in-theory (e/d* (rflagsbits
                                        bitops::ihsext-inductions
                                        bitops::ihsext-recursive-redefs)
                                       ()))))))

  :body

  (b* (((the (unsigned-byte 32) rflags) (rflags x86))
       (cf (rflagsBits->cf rflags))
       (pf (rflagsBits->pf rflags))
       (af (rflagsBits->af rflags))
       (zf (rflagsBits->zf rflags))
       (sf (rflagsBits->sf rflags))

       ((the (unsigned-byte 8) new-ah)
        (!rflagsBits->cf
         cf
         (!rflagsBits->res1
          1
          (!rflagsBits->pf
           pf
           (!rflagsBits->res2
            0
            (!rflagsBits->af
             af
             (!rflagsBits->res3
              0
              (!rflagsBits->zf
               zf
               (!rflagsBits->sf
                sf
                0)))))))))

       ((the (unsigned-byte 16) ax) (rr16 #.*rax* x86))
       ((the (unsigned-byte 16) new-ax)
        (logior (logand #xFF ax) (ash new-ah 8)))
       ;; Update the x86 state:
       (x86 (wr16 #.*rax* new-ax x86))
       (x86 (write-*ip proc-mode temp-rip x86)))
    x86))

;; ======================================================================
;; INSTRUCTION: RDRAND
;; ======================================================================

(def-inst x86-rdrand

  ;; 0F C7:
  ;; Opcode Extensions:
  ;; Bits 5,4,3 of the ModR/M byte (reg): 110
  ;; Bits 7,6 of the ModR/M byte (mod):    11

  :parents (two-byte-opcodes)

  :returns (x86 x86p :hyp (x86p x86)
                :hints (("Goal" :in-theory (e/d ()
                                                (force (force))))))

  :long
  "<p>Note from the Intel Manual (March 2017, Vol. 1, Section 7.3.17):</p>

 <p><em>Under heavy load, with multiple cores executing RDRAND in parallel, it
 is possible, though unlikely, for the demand of random numbers by software
 processes or threads to exceed the rate at which the random number generator
 hardware can supply them. This will lead to the RDRAND instruction returning
 no data transitorily. The RDRAND instruction indicates the occurrence of this
 rare situation by clearing the CF flag.</em></p>

 <p>See <a
 href='http://software.intel.com/en-us/articles/intel-digital-random-number-generator-drng-software-implementation-guide/'>Intel's
 Digital Random Number Generator Guide</a> for more details.</p>"

  :modr/m t

  :body

  (b* (((the (integer 1 8) operand-size)
        (select-operand-size
         proc-mode nil rex-byte nil prefixes nil nil nil x86))

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
       (x86 (let* ((x86 (!flgi :cf cf x86))
                   (x86 (!flgi :pf 0 x86))
                   (x86 (!flgi :af 0 x86))
                   (x86 (!flgi :zf 0 x86))
                   (x86 (!flgi :sf 0 x86))
                   (x86 (!flgi :of 0 x86)))
              x86))
       (x86 (write-*ip proc-mode temp-rip x86)))
      x86))

;; ----------------------------------------------------------------------

(define x86-step-unimplemented (message x86)
  :parents (instructions)
  :short "Semantic function corresponding to Intel's instructions unsupported
  in the @('x86isa') books"
  :long "<p>Note that the @('ms') field is populated with @('message') here
  because this function is called when a model-related error occurs.</p>"
  :returns (x86 x86p :hyp (x86p x86))
  (b* ((ctx 'x86-step-unimplemented))
    (!!ms-fresh :message message)))

(define x86-illegal-instruction
  (message
   (start-rip :type (signed-byte   #.*max-linear-address-size*))
   (temp-rip  :type (signed-byte   #.*max-linear-address-size*))
   x86)
  :parents (instructions)
  :short "Semantic function corresponding to opcodes that Intel deems to be
  illegal or reserved"
  :long "<p>Note that the @('#UD') (undefined operation) exception should be
  thrown here, which is why the @('fault') field is populated with
  @('message').</p>"
  :returns (x86 x86p :hyp (x86p x86))
  (b* ((ctx 'x86-illegal-instruction)
       ;; We update the RIP to point to the next instruction --- in case we
       ;; ever get to the point that we can recover from #UD exceptions, this
       ;; may be the right thing to do.
       (x86 (!rip temp-rip x86)))
    (!!fault-fresh :ud message :instruction-address start-rip)))

(define x86-general-protection
  (message
   (start-rip :type (signed-byte   #.*max-linear-address-size*))
   (temp-rip  :type (signed-byte   #.*max-linear-address-size*))
   x86)
  :parents (instructions)
  :short "Semantic function corresponding to a general protection fault"
  :long "<p>Note that the @('#GP') (general protection) exception should be
  thrown here, which is why the @('fault') field is populated with
  @('message').</p>"
  :returns (x86 x86p :hyp (x86p x86))
  (b* ((ctx 'x86-general-protection)
       ;; We update the RIP to point to the next instruction --- in case we
       ;; ever get to the point that we can recover from #GP exceptions, this
       ;; may be the right thing to do.
       (x86 (!rip temp-rip x86)))
    (!!fault-fresh :gp message :instruction-address start-rip)))

(define x86-device-not-available
  (message
   (start-rip :type (signed-byte   #.*max-linear-address-size*))
   (temp-rip  :type (signed-byte   #.*max-linear-address-size*))
   x86)
  :parents (instructions)
  :short "Semantic function corresponding to a device not available (no math coprocessor) fault"
  :long "<p>Note that the @('#NM') (device not available) exception should be
  thrown here, which is why the @('fault') field is populated with
  @('message').</p>"
  :returns (x86 x86p :hyp (x86p x86))
  (b* ((ctx 'x86-device-not-available)
       ;; We update the RIP to point to the next instruction --- in case we
       ;; ever get to the point that we can recover from #NM exceptions, this
       ;; may be the right thing to do.
       (x86 (!rip temp-rip x86)))
    (!!fault-fresh :nm message :instruction-address start-rip)))

(add-to-ruleset instruction-decoding-and-spec-rules
                '(x86-step-unimplemented
                  x86-illegal-instruction
                  x86-general-protection
                  x86-device-not-available))

(in-theory (e/d () (rip-guard-okp)))

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
