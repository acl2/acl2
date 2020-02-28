; X86ISA Library

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2015, Regents of the University of Texas
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

(in-package "X86ISA")

(include-book "../../top" :ttags :all)
(include-book "std/testing/assert" :dir :system)

(defsection nop-cosim
  :parents (concrete-simulation-examples)

  :short "Test to see if the <i>Recommended multi-byte sequence of NOP
  Instruction</i> (Intel Vol. 2B, NOP Instruction-Set Reference) is supported
  by the @('x86isa') model"
  )

(local (xdoc::set-default-parents nop-cosim))

;; ======================================================================

;; Recommended NOP Sequence:

;; 1. #x66 #x90
;; 2. #x0F #x1F #x00
;; 3. #x0F #x1F #x40 #x00
;; 4. #x0F #x1F #x44 #x00 #x00
;; 5. #x66 #x0F #x1F #x44 #x00 #x00
;; 6. #x0F #x1F #x80 #x00 #x00 #x00 #x00
;; 7. #x0F #x1F #x84 #x00 #x00 #x00 #x00 #x00
;; 8. #x66 #x0F #x1F #x84 #x00 #x00 #x00 #x00 #x00

(defconst *nop*
  '(
    ;; RIP: 0
    #x66 #x90
    ;; RIP: 2
    #x0F #x1F #x00
    ;; RIP: 5
    #x0F #x1F #x40 #x00
    ;; RIP: 9
    #x0F #x1F #x44 #x00 #x00
    ;; RIP: 0E
    #x66 #x0F #x1F #x44 #x00 #x00
    ;; RIP: 14
    #x0F #x1F #x80 #x00 #x00 #x00 #x00
    ;; RIP: 1B
    #x0F #x1F #x84 #x00 #x00 #x00 #x00 #x00
    ;; The following instruction is the odd one out. Note #x67 prefix.
    ;; RIP: 23
    #x67 #x66 #x0F #x1F #x84 #x00 #x00 #x00 #x00 #x00
    ;; RIP: 2D
    #x66 #x0F #x1F #x84 #x00 #x00 #x00 #x00 #x00))

(defconst *nop-xrun-limit* #u_500)

(define check-nop-output
  ((halt-address :type (signed-byte #.*max-linear-address-size*))
   (x86 "Output x86 State"))

  (cond ((or (fault x86)
             (not (equal (ms x86)
                         `((x86-fetch-decode-execute-halt
                            :rip ,halt-address)))))

         (cw "~|(ms x86) = ~x0 (fault x86) = ~x1~%"
             (ms x86) (fault x86)))

        (t

         (if (and (equal (rgfi *rax* x86) 0)
                  (equal (rgfi *rbx* x86) 0)
                  (equal (rgfi *rcx* x86) 0)
                  (equal (rgfi *rdx* x86) 0)
                  (equal (rgfi *rsi* x86) 0)
                  (equal (rgfi *rdi* x86) 0)
                  (equal (rgfi *rsp* x86) 0)
                  (equal (rgfi *r8*  x86) 0)
                  (equal (rgfi *r9*  x86) 0)
                  (equal (rgfi *r10* x86) 0)
                  (equal (rgfi *r11* x86) 0)
                  (equal (rgfi *r12* x86) 0)
                  (equal (rgfi *r13* x86) 0)
                  (equal (rgfi *r14* x86) 0)
                  (equal (rgfi *r15* x86) 0)
                  (equal (rflags x86) 2))

             (prog2$
              (cw "~|NOP sequences behave as expected.~%")
              t)

           (cw "~|NOP sequences DO NOT behave as expected!~%")))))

(acl2::assert!-stobj

 (b* ((start-address 0)
      (halt-address  (len *nop*))
      (x86           (!app-view t x86))

      ((mv flg x86)
       ;; Initialize the x86 state:
       (init-x86-state-64
        ;; Status (MS and fault field)
        nil
        ;; Start Address --- set the RIP to this address
        start-address
        ;; Initial values of General-Purpose Registers
        nil
        ;; Control Registers
        nil
        ;; Model-Specific Registers
        nil
        ;; seg-visibles
        nil
        ;; seg-hiddens
        nil nil nil
        ;; Rflags Register
        2
        ;; Memory image
        (pairlis$
         (create-canonical-address-list (len *nop*) 0)
         *nop*)
        ;; x86 state
        x86))
      ((when flg)
       (cw "~%Error in initializing x86-64 state!~%")
       (mv flg x86))

      (x86 (time$ (x86-run-halt halt-address *nop-xrun-limit* x86)))
      (ok? (check-nop-output halt-address x86)))

   (mv ok? x86))

 x86)

;; To create a log file:

;; Halt Address --- overwrites this address by #xF4 (HLT)
;; (wme08 *64-bit-mode* (len *nop*) *cs* #xf4 x86)
;; (!log-file-name "nop.log")
;; (log_instr)

;; ----------------------------------------------------------------------

;; Checking the XCHG functionality:

(defconst *xchg*
  '(
    ;; #x48 #xc7 #xc0 #x01 #x00 #x00 #x00 ;; movq	$0x1, %rax
    ;; #x49 #xb8 #xff #xff #xff #xff #x00 #x00 #x00 #x00 ;; movabsq	$0xffffffff, %r8
    ;; #x49 #x90 ;; xchgq	%r8, %rax

    #x48 #xc7 #xc0 #x01 #x00 #x00 #x00                ; movq	$0x1, %rax
    #x49 #xb8 #xff #xff #xff #xff #x00 #x00 #x00 #x00 ; movabsq	$0xffffffff, %r8
    #x66 #x41 #x90                                    ; xchgw	%r8w, %ax

    ))

(defconst *xchg-xrun-limit* #u_500)

(define check-xchg-output
  ((halt-address :type (signed-byte #.*max-linear-address-size*))
   (x86 "Output x86 State"))

  (cond ((or (fault x86)
             (not (equal (ms x86)
                         `((x86-fetch-decode-execute-halt
                            :rip ,halt-address)))))

         (cw "~|(ms x86) = ~x0 (fault x86) = ~x1~%"
             (ms x86) (fault x86)))

        (t

         (if (and (equal (rgfi *rax* x86) #xffff)
                  (equal (rgfi *rbx* x86) 0)
                  (equal (rgfi *rcx* x86) 0)
                  (equal (rgfi *rdx* x86) 0)
                  (equal (rgfi *rsi* x86) 0)
                  (equal (rgfi *rdi* x86) 0)
                  (equal (rgfi *rsp* x86) 0)
                  (equal (rgfi *r8*  x86) #uxffff_0001)
                  (equal (rgfi *r9*  x86) 0)
                  (equal (rgfi *r10* x86) 0)
                  (equal (rgfi *r11* x86) 0)
                  (equal (rgfi *r12* x86) 0)
                  (equal (rgfi *r13* x86) 0)
                  (equal (rgfi *r14* x86) 0)
                  (equal (rgfi *r15* x86) 0)
                  (equal (rflags x86) 2))

             (prog2$
              (cw "~|XCHG behaves as expected.~%")
              t)

           (cw "~|XCHG DOES NOT behave as expected!~%")))))

(acl2::assert!-stobj

 (b* ((start-address 0)
      (halt-address  (len *xchg*))
      (x86           (!app-view t x86))

      ((mv flg x86)
       ;; Initialize the x86 state:
       (init-x86-state-64
        ;; Status (MS and fault field)
        nil
        ;; Start Address --- set the RIP to this address
        start-address
        ;; Initial values of General-Purpose Registers
        nil
        ;; Control Registers
        nil
        ;; Model-Specific Registers
        nil
        ;; seg-visibles
        nil
        ;; seg-hiddens
        nil nil nil
        ;; Rflags Register
        2
        ;; Memory image
        (pairlis$
         (create-canonical-address-list (len *xchg*) 0)
         *xchg*)
        ;; x86 state
        x86))
      ((when flg)
       (cw "~%Error in initializing x86-64 state!~%")
       (mv flg x86))

      (x86 (time$ (x86-run-halt halt-address *xchg-xrun-limit* x86)))
      (ok? (check-xchg-output halt-address x86)))

   (mv ok? x86))

 x86)

;; To create a log file:
;; Halt Address --- overwrites this address by #xF4 (HLT)
;; (wme08 (len *xchg*) *cs* #xf4 x86)
;; (!log-file-name "xchg.log")
;; (log_instr)

;; ----------------------------------------------------------------------
