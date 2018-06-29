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

;; A simple program that copies data from one location to another.

(in-package "X86ISA")

(include-book "../../top" :ttags :all)

;; ======================================================================

;; Read and load binary into the x86 model's memory:
(binary-file-load "dataCopy.o")

;; 0000000100000d80 <_copyData>:
;;    100000d80:	55                      push   %rbp
;;    100000d81:	48 89 e5                mov    %rsp,%rbp
;;    100000d84:	85 d2                   test   %edx,%edx
;;    100000d86:	74 1a                   je     100000da2 <_copyData+0x22>
;;    100000d88:	48 63 c2                movslq %edx,%rax
;;    100000d8b:	48 c1 e0 02             shl    $0x2,%rax
;;    100000d8f:	90                      nop
;;    100000d90:	8b 0f                   mov    (%rdi),%ecx
;;    100000d92:	48 83 c7 04             add    $0x4,%rdi
;;    100000d96:	89 0e                   mov    %ecx,(%rsi)
;;    100000d98:	48 83 c6 04             add    $0x4,%rsi
;;    100000d9c:	48 83 c0 fc             add    $0xfffffffffffffffc,%rax
;;    100000da0:	75 ee                   jne    100000d90 <_copyData+0x10>
;;    100000da2:	5d                      pop    %rbp
;;    100000da3:	c3                      retq

(!app-view t x86)

;; Initialize the x86 state:
(init-x86-state
 ;; Status (MS and fault field)
 nil
 ;; Start Address --- set the RIP to this address
 #x100000d80
 ;; Halt Address --- overwrites this address by #xF4 (HLT)
 #x100000da3
 ;; Initial values of General-Purpose Registers
 '((#.*RAX* . #x1)
   (#.*RBX* . #x0)
   (#.*RCX* . #x4B00345618D749B7)
   (#.*RDX* . #x5)            ;; n
   (#.*RSI* . #x7FFF5FBFF430) ;; destination
   (#.*RDI* . #x7FFF5FBFF450) ;; source
   (#.*RBP* . 0)
   (#.*RSP* . #x7FFF5FBFF400)
   (#.*R8*  . 0)
   (#.*R9*  . 0)
   (#.*R10* . #xA)
   (#.*R11* . #x246)
   (#.*R12* . #x0)
   (#.*R13* . #x0)
   (#.*R14* . #x0)
   (#.*R15* . #x0))
 ;; Control Registers: a value of nil will not nullify existing
 ;; values.
 nil
 ;; Model-Specific Registers: a value of nil will not nullify existing
 ;; values.
 nil ;; (!ia32_efer-slice :ia32_efer-lma 1 (!ia32_efer-slice :ia32_efer-sce 1 0))
 ;; Rflags Register
 #x202
 ;; Source Array
 '((#x7FFF5FBFF450 . 6)
   (#x7FFF5FBFF454 . 7)
   (#x7FFF5FBFF458 . 8)
   (#x7FFF5FBFF45C . 9)
   (#x7FFF5FBFF460 . 10))
 ;; x86 state
 x86)

;; Sanity checks:
(rm08 #x7FFF5FBFF450 :r x86)
(rm08 #x7FFF5FBFF460 :r x86)

(rm08 #x100000da3 :r x86)

(trace$ x86-hlt)
(trace-write-memory (wm08 wm16 wm32 wm64))

;; Run the program for up to (2^60 - 1) steps or till the machine
;; halts, whatever comes first. Results logged in acl2-instrument.log.
(log_instr)

;; ======================================================================
;; Inspect the output:

(set-print-base 10 state)

;; Destination Array:
(rb
 '(#x7FFF5FBFF430
   #x7FFF5FBFF434
   #x7FFF5FBFF438
   #x7FFF5FBFF43C
   #x7FFF5FBFF440)
 :r x86)

;; Source Array:
(rb
 '(#x7FFF5FBFF450
   #x7FFF5FBFF454
   #x7FFF5FBFF458
   #x7FFF5FBFF45C
   #x7FFF5FBFF460)
 :r x86)

;; ======================================================================
