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

;; GCC Optimization level: -default-opt

(in-package "X86ISA")

;; ======================================================================

;; Program details:

;; 50 assembly instructions
;; 51 bytes of GC, 115 bytes of main, 166 bytes total.

(defconst *newline* #x0a) ;; 10
(defconst *space*   #x20) ;; 32
(defconst *tab*     #x09) ;;  9
(defconst *eof*     #x23) ;; 35
(defconst *OUT*       0 )
(defconst *IN*        1 )

(defconst *gc*
  ;; Bytes corresponding to the GC procedure:
  '(#x55 #x48 #x89 #xe5 #x53 #x48 #x8d #x45 #xf7 #x48 #x89 #x45 #xe0
         #x48 #xc7 #xc0 #x00 #x00 #x00 #x00 #x48 #x31 #xff #x48 #x8b #x75
         #xe0 #x48 #xc7 #xc2 #x01 #x00 #x00 #x00 #x0f #x05 #x89 #xc3 #x89
         #x5d #xf0 #x0f #xb6 #x45 #xf7 #x0f #xb6 #xc0 #x5b #x5d #xc3))

(defconst *gc-len* (len *gc*))

(defconst *wc-main*
  ;; Bytes corresponding to MAIN:
  '(#x55 #x48 #x89 #xe5 #x48 #x83 #xec #x20 #xc7 #x45 #xf8 #x00 #x00 #x00
         #x00 #xc7 #x45 #xf4 #x00 #x00 #x00 #x00 #x8b #x45 #xf4 #x89 #x45 #xf0
         #x8b #x45 #xf0 #x89 #x45 #xec #xeb #x3a #x83 #x45 #xf4 #x01 #x83 #x7d
         #xfc #x0a #x75 #x04 #x83 #x45 #xec #x01 #x83 #x7d #xfc #x20 #x74 #x0c
         #x83 #x7d #xfc #x0a #x74 #x06 #x83 #x7d #xfc #x09 #x75 #x09 #xc7 #x45
         #xf8 #x00 #x00 #x00 #x00 #xeb #x11 #x83 #x7d #xf8 #x00 #x75 #x0b #xc7
         #x45 #xf8 #x01 #x00 #x00 #x00 #x83 #x45 #xf0 #x01 #xe8 #x6a #xff #xff
         #xff #x89 #x45 #xfc #x83 #x7d #xfc #x23 #x75 #xb8 #xb8 #x00 #x00 #x00
         #x00 #xc9 #xc3))

(defconst *wc-main-len* (len *wc-main*))

(defconst *wc*
  ;; Bytes corresponding to WC (GC + Main):
  (append *gc* *wc-main*))

(defconst *wc-len* (len *wc*))

#||

WC Pseudo-code:


(#x4004e7):             Main begins here

(#x400509):             jmp to #x400545

Loop Begins:

(#x400545):             Call GC (#x4004b4 to #x4004e6)

(#x40054a to #x400551): Check for EOF (#): if # encountered, proceed
                        till Ret (#x400559) else jump to #x40050b

(#x40050b):             Check for newline, space, and tab and
                        increment counters appropriately.

(#x400559):             Call GC (#x4004b4 to #x4004e6)


||#

;; (defconst *wc*
;;   (list

;;    ;; Section: <gc>:

;;    (cons #x4004b4 #x55) ;; push %rbp
;;    (cons #x4004b5 #x48) ;; mov %rsp,%rbp
;;    (cons #x4004b6 #x89) ;;
;;    (cons #x4004b7 #xe5) ;;
;;    (cons #x4004b8 #x53) ;; push %rbx
;;    (cons #x4004b9 #x48) ;; lea -0x9(%rbp),%rax
;;    (cons #x4004ba #x8d) ;;
;;    (cons #x4004bb #x45) ;;
;;    (cons #x4004bc #xf7) ;;
;;    (cons #x4004bd #x48) ;; mov %rax,-0x20(%rbp)
;;    (cons #x4004be #x89) ;;
;;    (cons #x4004bf #x45) ;;
;;    (cons #x4004c0 #xe0) ;;
;;    (cons #x4004c1 #x48) ;; mov $0x0,%rax
;;    (cons #x4004c2 #xc7) ;;
;;    (cons #x4004c3 #xc0) ;;
;;    (cons #x4004c4 #x00) ;;
;;    (cons #x4004c5 #x00) ;;
;;    (cons #x4004c6 #x00) ;;
;;    (cons #x4004c7 #x00) ;;
;;    (cons #x4004c8 #x48) ;; xor %rdi,%rdi
;;    (cons #x4004c9 #x31) ;;
;;    (cons #x4004ca #xff) ;;
;;    (cons #x4004cb #x48) ;; mov -0x20(%rbp),%rsi
;;    (cons #x4004cc #x8b) ;;
;;    (cons #x4004cd #x75) ;;
;;    (cons #x4004ce #xe0) ;;
;;    (cons #x4004cf #x48) ;; mov $0x1,%rdx
;;    (cons #x4004d0 #xc7) ;;
;;    (cons #x4004d1 #xc2) ;;
;;    (cons #x4004d2 #x01) ;;
;;    (cons #x4004d3 #x00) ;;
;;    (cons #x4004d4 #x00) ;;
;;    (cons #x4004d5 #x00) ;;
;;    (cons #x4004d6 #x0f) ;; syscall
;;    (cons #x4004d7 #x05) ;;
;;    (cons #x4004d8 #x89) ;; mov %eax,%ebx
;;    (cons #x4004d9 #xc3) ;;
;;    (cons #x4004da #x89) ;; mov %ebx,-0x10(%rbp)
;;    (cons #x4004db #x5d) ;;
;;    (cons #x4004dc #xf0) ;;
;;    (cons #x4004dd #x0f) ;; movzbl -0x9(%rbp),%eax
;;    (cons #x4004de #xb6) ;;
;;    (cons #x4004df #x45) ;;
;;    (cons #x4004e0 #xf7) ;;
;;    (cons #x4004e1 #x0f) ;; movzbl %al,%eax
;;    (cons #x4004e2 #xb6) ;;
;;    (cons #x4004e3 #xc0) ;;
;;    (cons #x4004e4 #x5b) ;; pop %rbx
;;    (cons #x4004e5 #x5d) ;; pop %rbp
;;    (cons #x4004e6 #xc3) ;; retq

;;    ;; Section: <main>:


;;    (cons #x4004e7 #x55) ;; push %rbp
;;    (cons #x4004e8 #x48) ;; mov %rsp,%rbp
;;    (cons #x4004e9 #x89) ;;
;;    (cons #x4004ea #xe5) ;;
;;    (cons #x4004eb #x48) ;; sub $0x20,%rsp
;;    (cons #x4004ec #x83) ;;
;;    (cons #x4004ed #xec) ;;
;;    (cons #x4004ee #x20) ;;
;;    (cons #x4004ef #xc7) ;; movl $0x0,-0x8(%rbp)
;;    (cons #x4004f0 #x45) ;;
;;    (cons #x4004f1 #xf8) ;;
;;    (cons #x4004f2 #x00) ;;
;;    (cons #x4004f3 #x00) ;;
;;    (cons #x4004f4 #x00) ;;
;;    (cons #x4004f5 #x00) ;;
;;    (cons #x4004f6 #xc7) ;; movl $0x0,-0xc(%rbp)
;;    (cons #x4004f7 #x45) ;;
;;    (cons #x4004f8 #xf4) ;;
;;    (cons #x4004f9 #x00) ;;
;;    (cons #x4004fa #x00) ;;
;;    (cons #x4004fb #x00) ;;
;;    (cons #x4004fc #x00) ;;
;;    (cons #x4004fd #x8b) ;; mov -0xc(%rbp),%eax
;;    (cons #x4004fe #x45) ;;
;;    (cons #x4004ff #xf4) ;;
;;    (cons #x400500 #x89) ;; mov %eax,-0x10(%rbp)
;;    (cons #x400501 #x45) ;;
;;    (cons #x400502 #xf0) ;;
;;    (cons #x400503 #x8b) ;; mov -0x10(%rbp),%eax
;;    (cons #x400504 #x45) ;;
;;    (cons #x400505 #xf0) ;;
;;    (cons #x400506 #x89) ;; mov %eax,-0x14(%rbp)
;;    (cons #x400507 #x45) ;;
;;    (cons #x400508 #xec) ;;
;;    (cons #x400509 #xeb) ;; jmp 400545 <main+0x5e>
;;    (cons #x40050a #x3a) ;;
;;    (cons #x40050b #x83) ;; addl $0x1,-0xc(%rbp)
;;    (cons #x40050c #x45) ;;
;;    (cons #x40050d #xf4) ;;
;;    (cons #x40050e #x01) ;;
;;    (cons #x40050f #x83) ;; cmpl $0xa,-0x4(%rbp)
;;    (cons #x400510 #x7d) ;;
;;    (cons #x400511 #xfc) ;;
;;    (cons #x400512 #x0a) ;;
;;    (cons #x400513 #x75) ;; jne 400519 <main+0x32>
;;    (cons #x400514 #x04) ;;
;;    (cons #x400515 #x83) ;; addl $0x1,-0x14(%rbp)
;;    (cons #x400516 #x45) ;;
;;    (cons #x400517 #xec) ;;
;;    (cons #x400518 #x01) ;;
;;    (cons #x400519 #x83) ;; cmpl $0x20,-0x4(%rbp)
;;    (cons #x40051a #x7d) ;;
;;    (cons #x40051b #xfc) ;;
;;    (cons #x40051c #x20) ;;
;;    (cons #x40051d #x74) ;; je 40052b <main+0x44>
;;    (cons #x40051e #x0c) ;;
;;    (cons #x40051f #x83) ;; cmpl $0xa,-0x4(%rbp)
;;    (cons #x400520 #x7d) ;;
;;    (cons #x400521 #xfc) ;;
;;    (cons #x400522 #x0a) ;;
;;    (cons #x400523 #x74) ;; je 40052b <main+0x44>
;;    (cons #x400524 #x06) ;;
;;    (cons #x400525 #x83) ;; cmpl $0x9,-0x4(%rbp)
;;    (cons #x400526 #x7d) ;;
;;    (cons #x400527 #xfc) ;;
;;    (cons #x400528 #x09) ;;
;;    (cons #x400529 #x75) ;; jne 400534 <main+0x4d>
;;    (cons #x40052a #x09) ;;
;;    (cons #x40052b #xc7) ;; movl $0x0,-0x8(%rbp)
;;    (cons #x40052c #x45) ;;
;;    (cons #x40052d #xf8) ;;
;;    (cons #x40052e #x00) ;;
;;    (cons #x40052f #x00) ;;
;;    (cons #x400530 #x00) ;;
;;    (cons #x400531 #x00) ;;
;;    (cons #x400532 #xeb) ;; jmp 400545 <main+0x5e>
;;    (cons #x400533 #x11) ;;
;;    (cons #x400534 #x83) ;; cmpl $0x0,-0x8(%rbp)
;;    (cons #x400535 #x7d) ;;
;;    (cons #x400536 #xf8) ;;
;;    (cons #x400537 #x00) ;;
;;    (cons #x400538 #x75) ;; jne 400545 <main+0x5e>
;;    (cons #x400539 #x0b) ;;
;;    (cons #x40053a #xc7) ;; movl $0x1,-0x8(%rbp)
;;    (cons #x40053b #x45) ;;
;;    (cons #x40053c #xf8) ;;
;;    (cons #x40053d #x01) ;;
;;    (cons #x40053e #x00) ;;
;;    (cons #x40053f #x00) ;;
;;    (cons #x400540 #x00) ;;
;;    (cons #x400541 #x83) ;; addl $0x1,-0x10(%rbp)
;;    (cons #x400542 #x45) ;;
;;    (cons #x400543 #xf0) ;;
;;    (cons #x400544 #x01) ;;
;;    (cons #x400545 #xe8) ;; callq 4004b4 <gc>
;;    (cons #x400546 #x6a) ;;
;;    (cons #x400547 #xff) ;;
;;    (cons #x400548 #xff) ;;
;;    (cons #x400549 #xff) ;;
;;    (cons #x40054a #x89) ;; mov %eax,-0x4(%rbp)
;;    (cons #x40054b #x45) ;;
;;    (cons #x40054c #xfc) ;;
;;    (cons #x40054d #x83) ;; cmpl $0x23,-0x4(%rbp)
;;    (cons #x40054e #x7d) ;;
;;    (cons #x40054f #xfc) ;;
;;    (cons #x400550 #x23) ;;
;;    (cons #x400551 #x75) ;; jne 40050b <main+0x24>
;;    (cons #x400552 #xb8) ;;
;;    (cons #x400553 #xb8) ;; mov $0x0,%eax
;;    (cons #x400554 #x00) ;;
;;    (cons #x400555 #x00) ;;
;;    (cons #x400556 #x00) ;;
;;    (cons #x400557 #x00) ;;
;;    (cons #x400558 #xc9) ;; leaveq
;;    (cons #x400559 #xc3) ;; retq
;;    (cons #x40055a #x90) ;; nop
;;    (cons #x40055b #x90) ;; nop
;;    (cons #x40055c #x90) ;; nop
;;    (cons #x40055d #x90) ;; nop
;;    (cons #x40055e #x90) ;; nop
;;    (cons #x40055f #x90) ;; nop
;;    ))
