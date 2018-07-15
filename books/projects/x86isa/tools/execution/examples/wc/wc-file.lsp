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

;; Simulation of a program that illustrates support for various SYSCALLs in the
;; programmer-level mode of the x86isa model. For a simpler program, see
;; wc-input.c and wc-input.lsp.

;; This program takes in the name of a file as input and prints out the number
;; of characters, words, and lines in it.

(in-package "X86ISA")

(include-book "../../top" :ttags :all)

;; ======================================================================

;; Read and load binary into the x86 model's memory:
(binary-file-load "wc-file.o")

;; Set the OS-Info:
(!app-view t x86)
;; Change :darwin to :linux if you're on a linux machine. Unfortunately, no
;; other OSes are supported.
(!os-info :darwin x86)

;; Initialize the x86 state:
(init-x86-state
 ;; Status (MS and fault field)
 nil
 ;; Start Address --- set the RIP to this address
 #x100000910
 ;; Halt Address --- overwrites this address by #xF4 (HLT)
 #x100000f4a
 ;; Initial values of General-Purpose Registers
 '((#.*RAX* . #x100000910)
   (#.*RBX* . #x0)
   (#.*RCX* . #x7FFF5FBFF578)
   (#.*RDX* . #x7FFF5FBFF4B0)
   (#.*RSI* . #x7FFF5FBFF4A0)
   (#.*RDI* . #x1)
   (#.*RBP* . #x7FFF5FBFF490)
   (#.*RSP* . #x7FFF5FBFF488)
   (#.*R8*  . #x0)
   (#.*R9*  . #x7FFF5FBFE548)
   (#.*R10* . #x32)
   (#.*R11* . #x246)
   (#.*R12* . #x0)
   (#.*R13* . #x0)
   (#.*R14* . #x0)
   (#.*R15* . #x0))
 ;; Control Registers
 nil
 ;; Model-Specific Registers
 '((#.*ia32_efer-idx* . #x401)) ;; (!ia32_efer-slice :ia32_efer-lma 1 (!ia32_efer-slice :ia32_efer-sce 1 0))
 ;; Rflags Register
 #xF6
 ;; Memory image: a value of nil will not nullify existing values.
 nil
 ;; x86 state
 x86)

;; (log_instr)

;; Run the program for up to 1000000 steps or till the machine halts, whatever comes first:
(x86-run-steps 1000000 x86)

;; ======================================================================
