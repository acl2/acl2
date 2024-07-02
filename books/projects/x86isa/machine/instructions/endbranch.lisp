; X86ISA Library

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2024, Kestrel Technology, LLC
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
; Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X86ISA")

(include-book "../decoding-and-spec-utils"
              :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-inst x86-endbr32/endbr64

  :returns (x86 x86p :hyp (x86p x86))

  :parents (two-byte-opcodes)

  :short "Terminate indirect branch."

  :long

  "<p>For now we model ENDBR32 and ENDBR64 as no-ops,
   effectively assuming no CET support
   (see Intel manual Volume 1 Chapter 17 of Dec 2023).
   In the future, we will add proper support
   (conditional under CPU features).</p>

   <p>These are instructions with two-byte opcodes,
   according to their specification in Intel manual Volume 2 of Dec 2023.
   However, Table A-3 of the same manual
   shows \"Reserved-NOP\" for <tt>F3 0F 1E</tt>.
   Perhaps that table has not been updated yet,
   but note that the `NOP' is consistent with the fact that
   ENDBR32 and ENDBR64 are no-ops in legacy platforms.
   It seems that the <tt>FB</tt> (for ENDBR32) and <tt>FA</tt> (for ENDBR64)
   are opcode extensions, which differentiate between the two.</p>

   <p>This ACL2 function is called when
   the bytes <tt>0F 1E</tt> are encountered during decoding,
   possibly with prefixes.
   Since the <tt>F3</tt> prefix is mandatory for these instructions,
   in this ACL2 function we check that it is present.</p>

   <p>It is not clear whether the presence of other prefixes is allowed.
   For now we allow and ignore them, but we may revise this</p>

   <p>Then we ensure that there is at least one more byte,
   which must be either <tt>FB</tt> or <tt>FA</tt>.
   Otherwise, the throw a #UD, which seems appropriate,
   although it is not immediately clear from the Intel manual
   whether there are other instructions that also start with <tt>F3 0F 1E</tt>.
   Also this may be revised in the future.</p>

   <p>It is not clear from the Intel manual what should happen
   if ENDBR32 is used in 64-bit mode or ENDBR64 is used in 32-bit mode.
   For now, we allow them, since we treat them as no-op anyhow.</p>

   <p>For generality, we may want to rename this ACL2 function
   to something like @('x86-reserved-nop-1e'),
   so that it can accommodate potentially other (future?)
   instructions besides ENDBR32 and ENDBR64.</p>"

  :modr/m t

  :body
  (b* ((p1 (prefixes->rep prefixes))
       ((unless (= p1 #.*repe*))
        (!!fault-fresh :ud nil ;; #UD
                       :no-mandatory-f3))
       (p2 (prefixes->seg prefixes))
       (p4? (equal #.*addr-size-override* (prefixes->adr prefixes)))
       (seg-reg (select-segment-register proc-mode p2 p4? mod r/m sib x86))
       ((mv flg next-byte x86)
        (rme08 proc-mode temp-rip seg-reg :x x86))
       ((when flg)
        (!!ms-fresh :no-next-byte-in-instruction))
       ((unless (or (= next-byte #xfb)   ; ENDBR32
                    (= next-byte #xfa))) ; ENDBR64
        (!!fault-fresh :ud nil ;; #UD
                       :no-following-fb-or-fa))
       ((mv flg temp-rip) (add-to-*ip proc-mode temp-rip 1 x86))
       ((when flg)
        (!!ms-fresh :add-to-*ip temp-rip))
       (x86 (write-*ip proc-mode temp-rip x86)))
    x86))
