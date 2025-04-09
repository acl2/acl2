; X86ISA Library

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2015, Regents of the University of Texas
; Copyright (C) 2024, Kestrel Technology, LLC
; All rights reserved.

; Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:

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
; Alessandro Coglio (www.alessandrocoglio.info)

(in-package "X86ISA")

;; ======================================================================

(include-book "arith-and-logic"
              :ttags (:undef-flg))
(include-book "bit"
              :ttags (:undef-flg))
(include-book "conditional"
              :ttags (:undef-flg))
(include-book "divide"
              :ttags (:undef-flg))
(include-book "endbranch"
              :ttags (:undef-flg))
(include-book "exchange"
              :ttags (:undef-flg))
(include-book "flags"
              :ttags (:undef-flg))
(include-book "halt"
              :ttags (:undef-flg))
(include-book "jump-and-loop"
              :ttags (:undef-flg))
(include-book "move"
              :ttags (:undef-flg))
(include-book "multiply"
              :ttags (:undef-flg))
(include-book "padd"
              :ttags (:undef-flg))
(include-book "psub"
              :ttags (:undef-flg))
(include-book "push-and-pop"
              :ttags (:undef-flg))
(include-book "rand"
              :ttags (:other-non-det :undef-flg))
(include-book "rotate-and-shift"
              :ttags (:undef-flg))
(include-book "segmentation"
              :ttags (:undef-flg))
(include-book "signextend"
              :ttags (:undef-flg))
(include-book "string"
              :ttags (:undef-flg))
(include-book "syscall"
              :ttags (:syscall-exec :undef-flg))
(include-book "subroutine"
              :ttags (:undef-flg))
(include-book "fp/top"
              :ttags (:undef-flg))
(include-book "interrupts"
              :ttags (:undef-flg))
(include-book "cpuid"
              :ttags (:undef-flg))
(include-book "msrs"
              :ttags (:undef-flg))
(include-book "x87"
              :ttags (:undef-flg))
(include-book "time"
              :ttags (:undef-flg))
(include-book "pio"
              :ttags (:undef-flg))
(include-book "cache"
              :ttags (:undef-flg))
(include-book "punpck"
              :ttags (:undef-flg))
(include-book "pcmp"
              :ttags (:undef-flg))
(include-book "pshuf"
              :ttags (:undef-flg))

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

(defsection three-byte-opcodes
  :parents (instructions)
  :short "Instruction semantic functions for Intel's instructions with three-byte
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

;; ----------------------------------------------------------------------

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
