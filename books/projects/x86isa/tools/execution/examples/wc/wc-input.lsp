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

;; Simulation of a small program that illustrates SYSCALL support in the
;; programmer-level mode of the x86isa model

;; This program reads input from stdin and computes the number of lines, words,
;; and characters in it till a # character is encountered.

(in-package "X86ISA")

(include-book "../../top" :ttags :all)

;; ======================================================================

;; Read and load binary into the x86 model's memory:
(binary-file-load "wc-input.o")

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
 #x100000ed0
 ;; Halt Address --- overwrites this address by #xF4 (HLT)
 #x100000f94
 ;; Initial values of General-Purpose Registers
 '((#.*RSP* . #x7FFFFFFFE5D8))
 ;; Control Registers: a value of nil will not nullify existing
 ;; values.
 nil
 ;; Model-Specific Registers: a value of nil will not nullify existing
 ;; values.
 '((#.*ia32_efer-idx* . #x401)) ;; (!ia32_efer-slice :ia32_efer-lma 1 (!ia32_efer-slice :ia32_efer-sce 1 0))
 ;; Rflags Register
 2
 ;; Memory image: a value of nil will not nullify existing values.
 nil
 ;; x86 state
 x86)


;; Run the program for up to 100000 or till the machine halts, whatever comes first:
(x86-run-steps 1000000 x86)

;; ======================================================================
;; Inspect the output:

(set-print-base 10 state)

;; The NL, NW, and NC counters might be located at a different memory address
;; for you. See wc-print.lsp if you don't want to be bothered with figuring out
;; where these counters are located in the memory.

;; NL
(rm32 (+ #x-C  (- #x7FFFFFFFE5D8 8)) :r x86)
;; NW:
(rm32 (+ #x-10 (- #x7FFFFFFFE5D8 8)) :r x86)
;; NC:
(rm32 (+ #x-14 (- #x7FFFFFFFE5D8 8)) :r x86)


;; ======================================================================
