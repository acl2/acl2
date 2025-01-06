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

(include-book "../decoding-and-spec-utils"
              :ttags (:undef-flg))

(include-book "../other-non-det"
              :ttags (:undef-flg :other-non-det))

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
