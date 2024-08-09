; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) May - August 2023, Regents of the University of Texas
; Copyright (C) August 2023 - May 2024, Yahya Sohail

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
; Yahya Sohail        <ysohail@cs.utexas.edu>

(in-package "X86ISA")

(include-book "../decoding-and-spec-utils"
	      :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))
(local (include-book "centaur/bitops/ihs-extensions" :dir :system))

;; ======================================================================
;; INSTRUCTION: OUT
;; ======================================================================

(define read-cstr-from-memory1 ((addr :type (signed-byte #.*max-linear-address-size*))
                                x86
                                (acc character-listp))
  :measure (nfix (- *max-linear-address-space* addr))
  :returns (mv (char-list character-listp :hyp (character-listp acc))
               (x86 x86p :hyp (x86p x86)))
  (b* (((mv flg byt x86) (rml08 addr :r x86))
       ((when flg) (mv nil x86))
       ((when (equal byt 0)) (mv acc x86))
       (addr+1 (1+ addr))
       ((unless (canonical-address-p addr+1)) (mv nil x86)))
      (read-cstr-from-memory1 (1+ addr) x86 (cons (code-char byt) acc))))

(defmacro read-cstr-from-memory (addr x86)
  `(b* (((mv bytes x86) (read-cstr-from-memory1 ,addr ,x86 nil)))
       (mv (coerce (reverse bytes) 'string) x86)))

(define modelcall-printk (x86)
  :returns (x86 x86p :hyp (x86p x86))
  :prepwork
  ((local (defthm character-listp-reverse-of-character-listp
                  (implies (character-listp x)
                           (character-listp (reverse x))))))
  (b* ((addr (rgfi *rbx* x86))
       ((unless (canonical-address-p addr)) x86)
       ((mv str x86) (read-cstr-from-memory addr x86))
       (- (cw str)))
      x86))

(defxdoc modelcalls
         :parents (x86isa)
         :short "Modelcalls, like syscalls, but instead of calling into the OS, we call into the model."
         :long "<p>A modelcall is like a syscall, but it calls into the model
         asking it to do something. Model calls are done by calling the @(tsee
         x86-out) instruction. On a real processor this would write to the IO
         bus, but our processor doesn't support that.</p>

         <p>At the moment, one model call is supported. Writing any byte to
         port 1 results in printing out the null terminated string of one byte
         characters pointed to by @('rbx').</p>")

(def-inst x86-out

          ;; Op/En: I
          ;; E6 ib

          :long "<p>This isn't actually implemented because we don't have any port
          I/O peripherals modeled. Instead, we use this instruction to perform
          what are essentially modelcalls (i.e. calls from the software running
          on the model into the model). See @(tsee modelcalls) for more
          information.</p>"

          :parents (one-byte-opcodes modelcalls)

          :guard-hints (("Goal" :in-theory (e/d (riml08 riml32) ())))

          :returns (x86 x86p :hyp (x86p x86))

          :body

          (b* (((mv flg port-number x86) (rme-size-opt proc-mode 1 temp-rip #.*cs* :x nil x86))
               ((when flg) (!!ms-fresh :rme-size-error flg))
               ((mv flg (the (signed-byte #.*max-linear-address-size*) temp-rip))
                (add-to-*ip proc-mode temp-rip 1 x86))
               ((when flg) (!!ms-fresh :increment-error flg))
               (x86 (case port-number
                      (1 (modelcall-printk x86))
                      (otherwise (!!ms-fresh :unhandled-port port-number)))))
              (write-*ip proc-mode temp-rip x86)))
