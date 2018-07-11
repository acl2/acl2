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

(include-book "../decoding-and-spec-utils"
              :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))
(local (include-book "centaur/bitops/ihs-extensions" :dir :system))

;; ======================================================================
;; INSTRUCTION: CBW/CWDE/CDQE/CLTQ
;; ======================================================================

; Extended to 32-bit mode by Alessandro Coglio <coglio@kestrel.edu>
(def-inst x86-cbw/cwd/cdqe

  ;; Op/En: NP

  ;; #x98: CBW:   AX  := Sign-extended AL
  ;; #x98: CWDE:  EAX := Sign-extended AX
  ;; #x98: CDQE:  RAX := Sign-extended EAX

  :parents (one-byte-opcodes)
  :returns (x86 x86p :hyp (and (x86p x86)
                               (canonical-address-p temp-rip)))
  :guard-hints (("Goal" :in-theory (e/d (n08-to-i08
                                         n16-to-i16
                                         n32-to-i32
                                         n64-to-i64)
                                        ())))
  :implemented
  (add-to-implemented-opcodes-table 'CBW #x98 '(:nil nil)
                                    'x86-cbw/cwd/cdqe)

  :body

  (b* ((ctx 'x86-cbw/cwd/cdqe)

       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock?) (!!fault-fresh :ud nil :lock-prefix prefixes)) ;; #UD

       (badlength? (check-instruction-length start-rip temp-rip 0))
       ((when badlength?)
        (!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       ((the (integer 1 8) register-size)
        (select-operand-size nil rex-byte nil prefixes x86))
       ((the (integer 1 4) src-size) (ash register-size -1))

       ((the (unsigned-byte 32) src)
        (mbe :logic
             (rgfi-size src-size *rax* rex-byte x86)
             :exec
             (case src-size
               (1 (rr08 *rax* rex-byte x86))
               (2 (rr16 *rax* x86))
               (4 (rr32 *rax* x86))
               (otherwise 0))))

       (dst (if (logbitp (the (integer 0 32)
                           (1- (the (integer 0 32) (ash src-size 3))))
                         src)
                (trunc register-size (case src-size
                                       (1 (n08-to-i08 src))
                                       (2 (n16-to-i16 src))
                                       (t (n32-to-i32 src))))
              src))

       ;; Update the x86 state:
       (x86 (!rgfi-size register-size *rax* dst rex-byte x86))
       (x86 (write-*ip temp-rip x86)))

    x86))

;; ======================================================================
;; INSTRUCTION: CWD/CDQ/CQO
;; ======================================================================

; Extended to 32-bit mode by Alessandro Coglio <coglio@kestrel.edu>
(def-inst x86-cwd/cdq/cqo

  ;; Op/En: NP

  ;; #x99: CWD:  DX:AX   := Sign-extended AX
  ;; #x99: CDQ:  EDX:EAX := Sign-extended EAX
  ;; #x99: CQO:  RDX:RAX := Sign-extended RAX

  :parents (one-byte-opcodes)

  :returns (x86 x86p :hyp (and (x86p x86)
                               (canonical-address-p temp-rip)))
  :implemented
  (add-to-implemented-opcodes-table 'CWD #x99 '(:nil nil) 'x86-cwd/cdq/cqo)

  :body

  (b* ((ctx 'x86-cwd/cdq/cqo)

       (lock? (equal #.*lock* (prefixes-slice :group-1-prefix prefixes)))
       ((when lock?) (!!fault-fresh :ud nil :lock-prefix prefixes)) ;; #UD

       (badlength? (check-instruction-length start-rip temp-rip 0))
       ((when badlength?)
        (!!fault-fresh :gp 0 :instruction-length badlength?)) ;; #GP(0)

       ((the (integer 1 8) src-size)
        (select-operand-size nil rex-byte nil prefixes x86))

       (src (rgfi-size src-size *rax* rex-byte x86))

       (rDX (if (logbitp (1- (ash src-size 3)) src)
                (trunc src-size -1)
              0))

       ;; Update the x86 state:
       (x86 (!rgfi-size src-size *rdx* rDX rex-byte x86))
       (x86 (write-*ip temp-rip x86)))

      x86))

;; ======================================================================
