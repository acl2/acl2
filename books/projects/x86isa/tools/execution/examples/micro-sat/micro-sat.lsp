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

;; The source program, called micro-sat.c (authored by Marijn Heule)
;; can be found in the current directory.

;; The ACL2 representation of the micro-sat binary, called
;; *micro-sat*, can also be found in the current directory.
(ld "micro-sat-addr-byte.lsp")

;; ======================================================================

;; Initializing the x86 state:

(init-x86-state
 ;; MS and Fault
 nil
 ;; Start address
 #x402874
 ;; Halt address
 #x4028e7
 ;; Registers
 '((#.*RAX* . #x7FFFF7DD6548)
   (#.*RBX* . #x0)
   (#.*RCX* . #x4028F0)
   (#.*RDX* . #x7FFFFFFFE918)
   (#.*RSI* . #x7FFFFFFFE908)
   (#.*RDI* . #x1)
   (#.*RBP* . #x0)
   (#.*RSP* . #x7FFFFFFFE828)
   (#.*R8*  . #x402980)
   (#.*R9*  . #x7FFFF7DE9740)
   (#.*R10* . #x7FFFFFFFE680)
   (#.*R11* . #x7FFFF7A3D680)
   (#.*R12* . #x4003D0)
   (#.*R13* . #x7FFFFFFFE900)
   (#.*R14* . #x0)
   (#.*R15* . #x0))
 ;; Control Registers
 '((#.*cr0* . 2147483648) ;; (!cr0-slice :cr0-pg  1 0)
   (#.*cr4* . 32)         ;; (!cr4-slice :cr4-pae 1 0)
   (#.*cr3* . #x0))
 ;; Model-Specific Registers
 ;; (!ia32-efer-slice :lme 1 (!ia32-efer-slice :lma 1 (!ia32-efer-slice :sce 1 0)))
 '((#.*ia32_efer-idx* . 2561))
 ;; Flags
 #x246
 ;; Memory
 *micro-sat*
 x86
 )

;; Setting up the page tables:
(!app-view nil x86)
(load-qwords-into-physical-memory-list *1-gig-page-tables* x86)

;; ======================================================================

(set-print-radix t state)

(set-print-base 16 state)

;; Uncomment the following if you wish to trace the memory
;; reads/writes as well.

;; (trace-all-reads)
;; (trace-all-writes)
;; ;; Note that the following will send all trace output, including
;; ;; the memory trace, to micro-sat-memory-trace.log.
;; (trace-to-file "micro-sat-memory-trace.log")

(!log-file-name "micro-sat-instrument.log")
(log_instr) ;; See log output in micro-sat-instrument.log

;; ======================================================================
