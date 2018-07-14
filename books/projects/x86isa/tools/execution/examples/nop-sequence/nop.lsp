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

;; Checking if the "Recommended multi-byte sequence of NOP
;; Instruction" (Intel Vol. 2B, NOP Instruction-Set Reference) is
;; supported by the x86isa model:

(in-package "X86ISA")

(include-book "../../top" :ttags :all)

;; ======================================================================

;; Set the OS-Info:
(!app-view t x86)

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

;; Initialize the x86 state:
(init-x86-state
 ;; Status (MS and fault field)
 nil
 ;; Start Address --- set the RIP to this address
 0
 ;; Halt Address --- overwrites this address by #xF4 (HLT)
 (len *nop*)
 ;; Initial values of General-Purpose Registers
 nil
 ;; Control Registers
 nil
 ;; Model-Specific Registers
 nil
 ;; Rflags Register
 2
 ;; Memory image
 (pairlis$
  (create-canonical-address-list (len *nop*) 0)
  *nop*)
 ;; x86 state
 x86)

(!log-file-name "nop.log")
(log_instr)

;; Run the program for up to 1000000 steps or till the machine halts, whatever comes first:
;; (x86-run-steps 1000000 x86)

;; ======================================================================

(defconst *xchg*
  '(
    ;;     #x48 #xc7 #xc0 #x01 #x00 #x00 #x00 ;; movq	$0x1, %rax
    ;;     #x49 #xb8 #xff #xff #xff #xff #x00 #x00 #x00 #x00 ;; movabsq	$0xffffffff, %r8
    ;;     #x49 #x90 ;; xchgq	%r8, %rax

    #x48 #xc7 #xc0 #x01 #x00 #x00 #x00 ; movq	$0x1, %rax
    #x49 #xb8 #xff #xff #xff #xff #x00 #x00 #x00 #x00 ; movabsq	$0xffffffff, %r8
    #x66 #x41 #x90 ; xchgw	%r8w, %ax

    ))


;; Initialize the x86 state:
(init-x86-state
 ;; Status (MS and fault field)
 nil
 ;; Start Address --- set the RIP to this address
 0
 ;; Halt Address --- overwrites this address by #xF4 (HLT)
 (len *xchg*)
 ;; Initial values of General-Purpose Registers
 nil
 ;; Control Registers
 nil
 ;; Model-Specific Registers
 nil
 ;; Rflags Register
 2
 ;; Memory image
 (pairlis$
  (create-canonical-address-list (len *xchg*) 0)
  *xchg*)
 ;; x86 state
 x86)

(!log-file-name "xchg.log")
(log_instr)

;; Run the program for up to 1000000 steps or till the machine halts, whatever comes first:
;; (x86-run-steps 1000000 x86)

;; ----------------------------------------------------------------------
