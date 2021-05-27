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
(include-book "std/testing/assert-bang-stobj" :dir :system)

(defsection dataCopy-cosim
  :parents (concrete-simulation-examples)
  :short "Test to check if an array copy program works as expected")

(local (xdoc::set-default-parents dataCopy-cosim))

;; ----------------------------------------------------------------------

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

(defconst *copyData*
  '(#x55
    #x48 #x89 #xe5
    #x85 #xd2
    #x74 #x1a
    #x48 #x63 #xc2
    #x48 #xc1 #xe0 #x02
    #x90
    #x8b #x0f
    #x48 #x83 #xc7 #x04
    #x89 #x0e
    #x48 #x83 #xc6 #x04
    #x48 #x83 #xc0 #xfc
    #x75 #xee
    #x5d
    #xc3))

(defconst *start-address* #x100000d80)
(defconst *halt-address*  #x100000da3)
(defconst *datacopy-xrun-limit* #u_500)

(acl2::assert!-stobj

 (b* ((start-address *start-address*)
      (halt-address  *halt-address*)

      (x86 (!app-view t x86))
      ((mv flg x86)
       ;; Initialize the x86 state:
       (init-x86-state-64
        ;; Status (MS and fault field)
        nil
        ;; Start Address --- set the RIP to this address
        start-address
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
        ;; Control Registers
        nil
        ;; Model-Specific Registers
        nil
        ;; seg-visibles
        nil
        ;; seg-hiddens
        nil nil nil
        ;; Rflags Register
        #x202
        (append
         ;; Program binary
         (pairlis$
          (create-canonical-address-list (len *copyData*) start-address)
          *copyData*)
         ;; Source Array
         '((#x7FFF5FBFF450 . 6)
           (#x7FFF5FBFF454 . 7)
           (#x7FFF5FBFF458 . 8)
           (#x7FFF5FBFF45C . 9)
           (#x7FFF5FBFF460 . 10)))
        ;; x86 state
        x86))
      ((when flg)
       (cw "~%Error in initializing x86-64 state!~%")
       (mv flg x86))

      (x86 (time$ (x86-run-halt halt-address *datacopy-xrun-limit* x86)))
      ((mv ok? x86)
       (b* (((mv flg dst x86)
             (rb (1+ (- #x7FFF5FBFF440 #x7FFF5FBFF430))
                 #x7FFF5FBFF430
                 :r x86))
            ((when flg)
             (cw "~%Error in reading the destination array!~%")
             (mv nil x86))
            ((mv flg src x86)
             (rb (1+ (- #x7FFF5FBFF460 #x7FFF5FBFF450))
                 #x7FFF5FBFF450
                 :r x86))
            ((when flg)
             (cw "~%Error in reading the source array!~%")
             (mv nil x86)))
         (mv (equal dst src) x86))))
   (mv ok? x86))

 x86)

;; ----------------------------------------------------------------------

;; To create a log file:

#||

;; Read and load binary into the x86 model's memory:
(binary-file-load "dataCopy.o" :elf t)

;; Fill these in by inspecting the object file:
(make-event
 `(defconst *start-address* ;; address of the first instruction of copyData routine 
    ,(exld::get-label-address "copyData" exld::elf)))
(defconst *halt-address*  #ux400805) ;; address of the ret instruction of copyData routine

(b* ((start-address *start-address*)

     (x86 (!app-view t x86))
     ((mv flg x86)
       ;; Initialize the x86 state:
      (init-x86-state-64
        ;; Status (MS and fault field)
       nil
        ;; Start Address --- set the RIP to this address
       start-address
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
        ;; Control Registers
       nil
        ;; Model-Specific Registers
       nil
        ;; seg-visibles
       nil
        ;; seg-hiddens
       nil nil nil
        ;; Rflags Register
       #x202

       (append
         ;; Halt address
        (list (cons *halt-address* #xF4))
        ;; Source Array
        '((#x7FFF5FBFF450 . 6)
          (#x7FFF5FBFF454 . 7)
          (#x7FFF5FBFF458 . 8)
          (#x7FFF5FBFF45C . 9)
          (#x7FFF5FBFF460 . 10)))
        ;; x86 state
       x86))
     ((when flg)
      (cw "~%Error in initializing x86-64 state!~%")
      x86))
  x86)

;; Run the program for up to (2^60 - 1) steps or till the machine
;; halts, whatever comes first. Results logged in acl2-instrument.log.

(trace-all-reads)
(trace-all-writes)

(!log-file-name "dataCopy.log")
(set-print-base 16 state)

(log_instr)

;; Inspect the output:

;; Destination Array:
(rb 20 #x7FFF5FBFF430 :r x86)

;; Source Array:
(rb 20 #x7FFF5FBFF450 :r x86)

||#
;; ----------------------------------------------------------------------
