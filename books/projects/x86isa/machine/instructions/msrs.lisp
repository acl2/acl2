; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) May - August 2023, Regents of the University of Texas
; Copyright (C) August 2023 - May 2024, Yahya Sohail
; Copyright (C) May 2024 - August 2024, Intel Corporation

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
; Yahya Sohail        <yahya.sohail@intel.com>

(in-package "X86ISA")

;; ======================================================================

(include-book "../decoding-and-spec-utils"
	      :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))

;; ======================================================================

;; ======================================================================
;; INSTRUCTION: RDMSR
;; ======================================================================

(def-inst x86-rdmsr

          ;; Op/En: ZO
          ;; 0F 32

          :parents (two-byte-opcodes)

          :returns (x86 x86p :hyp (x86p x86))

          ;; Why do we need to enable msra? Why doesn't ACL2 appeal to
          ;; n64p-of-msra? We should ask Shilpi
          :guard-hints (("Goal" :in-theory (e/d* (msra) ())))

          :body

          (b* ((msr-addr (rr32 *ecx* x86))
               ((unless (valid-msr-addr-p msr-addr)) (!!fault-fresh :gp 0 :invalid-msr msr-addr))
               (msr-val (msra msr-addr x86))
               (x86 (wr32 *eax* (loghead 32 msr-val) x86))
               (x86 (wr32 *edx* (logtail 32 msr-val) x86))
               (x86 (write-*ip proc-mode temp-rip x86)))
              x86))

(def-inst x86-wrmsr

          ;; Op/En: ZO
          ;; 0F 30

          :parents (two-byte-opcodes)

          :returns (x86 x86p :hyp (x86p x86))

          :body

          (b* ((msr-addr (rr32 *ecx* x86))
               ((when (not (valid-msr-addr-p msr-addr))) (!!fault-fresh :gp 0 :invalid-msr msr-addr))
               (lower (rr32 *eax* x86))
               (upper (rr32 *edx* x86))
               (msr-val (logapp 32 lower upper))
               (x86 (!msra msr-addr msr-val x86))
               (x86 (write-*ip proc-mode temp-rip x86)))
              x86))
