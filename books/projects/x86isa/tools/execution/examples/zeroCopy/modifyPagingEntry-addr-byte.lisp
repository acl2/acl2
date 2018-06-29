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

(defconst *modifyPagingEntry*
  (list

   ;; Section: <part_select>:

   (cons #x4004ed #x55) ;; push %rbp
   (cons #x4004ee #x48) ;; mov %rsp,%rbp
   (cons #x4004ef #x89) ;;
   (cons #x4004f0 #xe5) ;;
   (cons #x4004f1 #x48) ;; mov %rdi,-0x28(%rbp)
   (cons #x4004f2 #x89) ;;
   (cons #x4004f3 #x7d) ;;
   (cons #x4004f4 #xd8) ;;
   (cons #x4004f5 #x89) ;; mov %esi,-0x2c(%rbp)
   (cons #x4004f6 #x75) ;;
   (cons #x4004f7 #xd4) ;;
   (cons #x4004f8 #x89) ;; mov %edx,-0x30(%rbp)
   (cons #x4004f9 #x55) ;;
   (cons #x4004fa #xd0) ;;
   (cons #x4004fb #x8b) ;; mov -0x2c(%rbp),%eax
   (cons #x4004fc #x45) ;;
   (cons #x4004fd #xd4) ;;
   (cons #x4004fe #x8b) ;; mov -0x30(%rbp),%edx
   (cons #x4004ff #x55) ;;
   (cons #x400500 #xd0) ;;
   (cons #x400501 #x29) ;; sub %eax,%edx
   (cons #x400502 #xc2) ;;
   (cons #x400503 #x89) ;; mov %edx,%eax
   (cons #x400504 #xd0) ;;
   (cons #x400505 #x83) ;; add $0x1,%eax
   (cons #x400506 #xc0) ;;
   (cons #x400507 #x01) ;;
   (cons #x400508 #x89) ;; mov %eax,%eax
   (cons #x400509 #xc0) ;;
   (cons #x40050a #x48) ;; mov %rax,-0x18(%rbp)
   (cons #x40050b #x89) ;;
   (cons #x40050c #x45) ;;
   (cons #x40050d #xe8) ;;
   (cons #x40050e #x48) ;; mov -0x18(%rbp),%rax
   (cons #x40050f #x8b) ;;
   (cons #x400510 #x45) ;;
   (cons #x400511 #xe8) ;;
   (cons #x400512 #xba) ;; mov $0x1,%edx
   (cons #x400513 #x01) ;;
   (cons #x400514 #x00) ;;
   (cons #x400515 #x00) ;;
   (cons #x400516 #x00) ;;
   (cons #x400517 #x89) ;; mov %eax,%ecx
   (cons #x400518 #xc1) ;;
   (cons #x400519 #x48) ;; shl %cl,%rdx
   (cons #x40051a #xd3) ;;
   (cons #x40051b #xe2) ;;
   (cons #x40051c #x48) ;; mov %rdx,%rax
   (cons #x40051d #x89) ;;
   (cons #x40051e #xd0) ;;
   (cons #x40051f #x48) ;; sub $0x1,%rax
   (cons #x400520 #x83) ;;
   (cons #x400521 #xe8) ;;
   (cons #x400522 #x01) ;;
   (cons #x400523 #x48) ;; mov %rax,-0x10(%rbp)
   (cons #x400524 #x89) ;;
   (cons #x400525 #x45) ;;
   (cons #x400526 #xf0) ;;
   (cons #x400527 #x8b) ;; mov -0x2c(%rbp),%eax
   (cons #x400528 #x45) ;;
   (cons #x400529 #xd4) ;;
   (cons #x40052a #x48) ;; mov -0x28(%rbp),%rdx
   (cons #x40052b #x8b) ;;
   (cons #x40052c #x55) ;;
   (cons #x40052d #xd8) ;;
   (cons #x40052e #x89) ;; mov %eax,%ecx
   (cons #x40052f #xc1) ;;
   (cons #x400530 #x48) ;; shr %cl,%rdx
   (cons #x400531 #xd3) ;;
   (cons #x400532 #xea) ;;
   (cons #x400533 #x48) ;; mov %rdx,%rax
   (cons #x400534 #x89) ;;
   (cons #x400535 #xd0) ;;
   (cons #x400536 #x48) ;; and -0x10(%rbp),%rax
   (cons #x400537 #x23) ;;
   (cons #x400538 #x45) ;;
   (cons #x400539 #xf0) ;;
   (cons #x40053a #x48) ;; mov %rax,-0x8(%rbp)
   (cons #x40053b #x89) ;;
   (cons #x40053c #x45) ;;
   (cons #x40053d #xf8) ;;
   (cons #x40053e #x48) ;; mov -0x8(%rbp),%rax
   (cons #x40053f #x8b) ;;
   (cons #x400540 #x45) ;;
   (cons #x400541 #xf8) ;;
   (cons #x400542 #x5d) ;; pop %rbp
   (cons #x400543 #xc3) ;; retq

   ;; Section: <part_install>:


   (cons #x400544 #x55) ;; push %rbp
   (cons #x400545 #x48) ;; mov %rsp,%rbp
   (cons #x400546 #x89) ;;
   (cons #x400547 #xe5) ;;
   (cons #x400548 #x48) ;; mov %rdi,-0x28(%rbp)
   (cons #x400549 #x89) ;;
   (cons #x40054a #x7d) ;;
   (cons #x40054b #xd8) ;;
   (cons #x40054c #x48) ;; mov %rsi,-0x30(%rbp)
   (cons #x40054d #x89) ;;
   (cons #x40054e #x75) ;;
   (cons #x40054f #xd0) ;;
   (cons #x400550 #x89) ;; mov %edx,-0x34(%rbp)
   (cons #x400551 #x55) ;;
   (cons #x400552 #xcc) ;;
   (cons #x400553 #x89) ;; mov %ecx,-0x38(%rbp)
   (cons #x400554 #x4d) ;;
   (cons #x400555 #xc8) ;;
   (cons #x400556 #x8b) ;; mov -0x34(%rbp),%eax
   (cons #x400557 #x45) ;;
   (cons #x400558 #xcc) ;;
   (cons #x400559 #x8b) ;; mov -0x38(%rbp),%edx
   (cons #x40055a #x55) ;;
   (cons #x40055b #xc8) ;;
   (cons #x40055c #x29) ;; sub %eax,%edx
   (cons #x40055d #xc2) ;;
   (cons #x40055e #x89) ;; mov %edx,%eax
   (cons #x40055f #xd0) ;;
   (cons #x400560 #x83) ;; add $0x1,%eax
   (cons #x400561 #xc0) ;;
   (cons #x400562 #x01) ;;
   (cons #x400563 #x89) ;; mov %eax,%eax
   (cons #x400564 #xc0) ;;
   (cons #x400565 #x48) ;; mov %rax,-0x18(%rbp)
   (cons #x400566 #x89) ;;
   (cons #x400567 #x45) ;;
   (cons #x400568 #xe8) ;;
   (cons #x400569 #x48) ;; mov -0x18(%rbp),%rax
   (cons #x40056a #x8b) ;;
   (cons #x40056b #x45) ;;
   (cons #x40056c #xe8) ;;
   (cons #x40056d #xba) ;; mov $0x1,%edx
   (cons #x40056e #x01) ;;
   (cons #x40056f #x00) ;;
   (cons #x400570 #x00) ;;
   (cons #x400571 #x00) ;;
   (cons #x400572 #x89) ;; mov %eax,%ecx
   (cons #x400573 #xc1) ;;
   (cons #x400574 #x48) ;; shl %cl,%rdx
   (cons #x400575 #xd3) ;;
   (cons #x400576 #xe2) ;;
   (cons #x400577 #x48) ;; mov %rdx,%rax
   (cons #x400578 #x89) ;;
   (cons #x400579 #xd0) ;;
   (cons #x40057a #x48) ;; sub $0x1,%rax
   (cons #x40057b #x83) ;;
   (cons #x40057c #xe8) ;;
   (cons #x40057d #x01) ;;
   (cons #x40057e #x48) ;; mov %rax,-0x10(%rbp)
   (cons #x40057f #x89) ;;
   (cons #x400580 #x45) ;;
   (cons #x400581 #xf0) ;;
   (cons #x400582 #x8b) ;; mov -0x34(%rbp),%eax
   (cons #x400583 #x45) ;;
   (cons #x400584 #xcc) ;;
   (cons #x400585 #x48) ;; mov -0x10(%rbp),%rdx
   (cons #x400586 #x8b) ;;
   (cons #x400587 #x55) ;;
   (cons #x400588 #xf0) ;;
   (cons #x400589 #x89) ;; mov %eax,%ecx
   (cons #x40058a #xc1) ;;
   (cons #x40058b #x48) ;; shl %cl,%rdx
   (cons #x40058c #xd3) ;;
   (cons #x40058d #xe2) ;;
   (cons #x40058e #x48) ;; mov %rdx,%rax
   (cons #x40058f #x89) ;;
   (cons #x400590 #xd0) ;;
   (cons #x400591 #x48) ;; not %rax
   (cons #x400592 #xf7) ;;
   (cons #x400593 #xd0) ;;
   (cons #x400594 #x48) ;; and -0x30(%rbp),%rax
   (cons #x400595 #x23) ;;
   (cons #x400596 #x45) ;;
   (cons #x400597 #xd0) ;;
   (cons #x400598 #x48) ;; mov %rax,%rdx
   (cons #x400599 #x89) ;;
   (cons #x40059a #xc2) ;;
   (cons #x40059b #x8b) ;; mov -0x34(%rbp),%eax
   (cons #x40059c #x45) ;;
   (cons #x40059d #xcc) ;;
   (cons #x40059e #x48) ;; mov -0x28(%rbp),%rsi
   (cons #x40059f #x8b) ;;
   (cons #x4005a0 #x75) ;;
   (cons #x4005a1 #xd8) ;;
   (cons #x4005a2 #x89) ;; mov %eax,%ecx
   (cons #x4005a3 #xc1) ;;
   (cons #x4005a4 #x48) ;; shl %cl,%rsi
   (cons #x4005a5 #xd3) ;;
   (cons #x4005a6 #xe6) ;;
   (cons #x4005a7 #x48) ;; mov %rsi,%rax
   (cons #x4005a8 #x89) ;;
   (cons #x4005a9 #xf0) ;;
   (cons #x4005aa #x48) ;; or %rdx,%rax
   (cons #x4005ab #x09) ;;
   (cons #x4005ac #xd0) ;;
   (cons #x4005ad #x48) ;; mov %rax,-0x8(%rbp)
   (cons #x4005ae #x89) ;;
   (cons #x4005af #x45) ;;
   (cons #x4005b0 #xf8) ;;
   (cons #x4005b1 #x48) ;; mov -0x8(%rbp),%rax
   (cons #x4005b2 #x8b) ;;
   (cons #x4005b3 #x45) ;;
   (cons #x4005b4 #xf8) ;;
   (cons #x4005b5 #x5d) ;; pop %rbp
   (cons #x4005b6 #xc3) ;; retq

   ;; Section: <pml4e_paddr>:


   (cons #x4005b7 #x55) ;; push %rbp
   (cons #x4005b8 #x48) ;; mov %rsp,%rbp
   (cons #x4005b9 #x89) ;;
   (cons #x4005ba #xe5) ;;
   (cons #x4005bb #x48) ;; sub $0x20,%rsp
   (cons #x4005bc #x83) ;;
   (cons #x4005bd #xec) ;;
   (cons #x4005be #x20) ;;
   (cons #x4005bf #x48) ;; mov %rdi,-0x18(%rbp)
   (cons #x4005c0 #x89) ;;
   (cons #x4005c1 #x7d) ;;
   (cons #x4005c2 #xe8) ;;
   (cons #x4005c3 #x48) ;; mov %rsi,-0x20(%rbp)
   (cons #x4005c4 #x89) ;;
   (cons #x4005c5 #x75) ;;
   (cons #x4005c6 #xe0) ;;
   (cons #x4005c7 #x48) ;; mov -0x18(%rbp),%rax
   (cons #x4005c8 #x8b) ;;
   (cons #x4005c9 #x45) ;;
   (cons #x4005ca #xe8) ;;
   (cons #x4005cb #x48) ;; and $0xfffffffffffff000,%rax
   (cons #x4005cc #x25) ;;
   (cons #x4005cd #x00) ;;
   (cons #x4005ce #xf0) ;;
   (cons #x4005cf #xff) ;;
   (cons #x4005d0 #xff) ;;
   (cons #x4005d1 #x48) ;; mov %rax,-0x10(%rbp)
   (cons #x4005d2 #x89) ;;
   (cons #x4005d3 #x45) ;;
   (cons #x4005d4 #xf0) ;;
   (cons #x4005d5 #x48) ;; mov -0x20(%rbp),%rax
   (cons #x4005d6 #x8b) ;;
   (cons #x4005d7 #x45) ;;
   (cons #x4005d8 #xe0) ;;
   (cons #x4005d9 #xba) ;; mov $0x2f,%edx
   (cons #x4005da #x2f) ;;
   (cons #x4005db #x00) ;;
   (cons #x4005dc #x00) ;;
   (cons #x4005dd #x00) ;;
   (cons #x4005de #xbe) ;; mov $0x27,%esi
   (cons #x4005df #x27) ;;
   (cons #x4005e0 #x00) ;;
   (cons #x4005e1 #x00) ;;
   (cons #x4005e2 #x00) ;;
   (cons #x4005e3 #x48) ;; mov %rax,%rdi
   (cons #x4005e4 #x89) ;;
   (cons #x4005e5 #xc7) ;;
   (cons #x4005e6 #xe8) ;; callq 4004ed <part_select>
   (cons #x4005e7 #x02) ;;
   (cons #x4005e8 #xff) ;;
   (cons #x4005e9 #xff) ;;
   (cons #x4005ea #xff) ;;
   (cons #x4005eb #x48) ;; mov -0x10(%rbp),%rsi
   (cons #x4005ec #x8b) ;;
   (cons #x4005ed #x75) ;;
   (cons #x4005ee #xf0) ;;
   (cons #x4005ef #xb9) ;; mov $0xb,%ecx
   (cons #x4005f0 #x0b) ;;
   (cons #x4005f1 #x00) ;;
   (cons #x4005f2 #x00) ;;
   (cons #x4005f3 #x00) ;;
   (cons #x4005f4 #xba) ;; mov $0x3,%edx
   (cons #x4005f5 #x03) ;;
   (cons #x4005f6 #x00) ;;
   (cons #x4005f7 #x00) ;;
   (cons #x4005f8 #x00) ;;
   (cons #x4005f9 #x48) ;; mov %rax,%rdi
   (cons #x4005fa #x89) ;;
   (cons #x4005fb #xc7) ;;
   (cons #x4005fc #xe8) ;; callq 400544 <part_install>
   (cons #x4005fd #x43) ;;
   (cons #x4005fe #xff) ;;
   (cons #x4005ff #xff) ;;
   (cons #x400600 #xff) ;;
   (cons #x400601 #x48) ;; mov %rax,-0x8(%rbp)
   (cons #x400602 #x89) ;;
   (cons #x400603 #x45) ;;
   (cons #x400604 #xf8) ;;
   (cons #x400605 #x48) ;; mov -0x8(%rbp),%rax
   (cons #x400606 #x8b) ;;
   (cons #x400607 #x45) ;;
   (cons #x400608 #xf8) ;;
   (cons #x400609 #xc9) ;; leaveq
   (cons #x40060a #xc3) ;; retq

   ;; Section: <pdpte_paddr>:


   (cons #x40060b #x55) ;; push %rbp
   (cons #x40060c #x48) ;; mov %rsp,%rbp
   (cons #x40060d #x89) ;;
   (cons #x40060e #xe5) ;;
   (cons #x40060f #x48) ;; sub $0x30,%rsp
   (cons #x400610 #x83) ;;
   (cons #x400611 #xec) ;;
   (cons #x400612 #x30) ;;
   (cons #x400613 #x48) ;; mov %rdi,-0x28(%rbp)
   (cons #x400614 #x89) ;;
   (cons #x400615 #x7d) ;;
   (cons #x400616 #xd8) ;;
   (cons #x400617 #x48) ;; mov %rsi,-0x30(%rbp)
   (cons #x400618 #x89) ;;
   (cons #x400619 #x75) ;;
   (cons #x40061a #xd0) ;;
   (cons #x40061b #x48) ;; mov -0x28(%rbp),%rax
   (cons #x40061c #x8b) ;;
   (cons #x40061d #x45) ;;
   (cons #x40061e #xd8) ;;
   (cons #x40061f #x48) ;; mov (%rax),%rax
   (cons #x400620 #x8b) ;;
   (cons #x400621 #x00) ;;
   (cons #x400622 #x48) ;; mov %rax,-0x18(%rbp)
   (cons #x400623 #x89) ;;
   (cons #x400624 #x45) ;;
   (cons #x400625 #xe8) ;;
   (cons #x400626 #x48) ;; mov -0x18(%rbp),%rax
   (cons #x400627 #x8b) ;;
   (cons #x400628 #x45) ;;
   (cons #x400629 #xe8) ;;
   (cons #x40062a #x83) ;; and $0x1,%eax
   (cons #x40062b #xe0) ;;
   (cons #x40062c #x01) ;;
   (cons #x40062d #x48) ;; test %rax,%rax
   (cons #x40062e #x85) ;;
   (cons #x40062f #xc0) ;;
   (cons #x400630 #x75) ;; jne 40063b <pdpte_paddr+0x30>
   (cons #x400631 #x09) ;;
   (cons #x400632 #x48) ;; mov $0xffffffffffffffff,%rax
   (cons #x400633 #xc7) ;;
   (cons #x400634 #xc0) ;;
   (cons #x400635 #xff) ;;
   (cons #x400636 #xff) ;;
   (cons #x400637 #xff) ;;
   (cons #x400638 #xff) ;;
   (cons #x400639 #xeb) ;; jmp 40068d <pdpte_paddr+0x82>
   (cons #x40063a #x52) ;;
   (cons #x40063b #x48) ;; mov -0x18(%rbp),%rax
   (cons #x40063c #x8b) ;;
   (cons #x40063d #x45) ;;
   (cons #x40063e #xe8) ;;
   (cons #x40063f #xba) ;; mov $0x33,%edx
   (cons #x400640 #x33) ;;
   (cons #x400641 #x00) ;;
   (cons #x400642 #x00) ;;
   (cons #x400643 #x00) ;;
   (cons #x400644 #xbe) ;; mov $0xc,%esi
   (cons #x400645 #x0c) ;;
   (cons #x400646 #x00) ;;
   (cons #x400647 #x00) ;;
   (cons #x400648 #x00) ;;
   (cons #x400649 #x48) ;; mov %rax,%rdi
   (cons #x40064a #x89) ;;
   (cons #x40064b #xc7) ;;
   (cons #x40064c #xe8) ;; callq 4004ed <part_select>
   (cons #x40064d #x9c) ;;
   (cons #x40064e #xfe) ;;
   (cons #x40064f #xff) ;;
   (cons #x400650 #xff) ;;
   (cons #x400651 #x48) ;; shl $0xc,%rax
   (cons #x400652 #xc1) ;;
   (cons #x400653 #xe0) ;;
   (cons #x400654 #x0c) ;;
   (cons #x400655 #x48) ;; mov %rax,-0x10(%rbp)
   (cons #x400656 #x89) ;;
   (cons #x400657 #x45) ;;
   (cons #x400658 #xf0) ;;
   (cons #x400659 #x48) ;; mov -0x30(%rbp),%rax
   (cons #x40065a #x8b) ;;
   (cons #x40065b #x45) ;;
   (cons #x40065c #xd0) ;;
   (cons #x40065d #xba) ;; mov $0x26,%edx
   (cons #x40065e #x26) ;;
   (cons #x40065f #x00) ;;
   (cons #x400660 #x00) ;;
   (cons #x400661 #x00) ;;
   (cons #x400662 #xbe) ;; mov $0x1e,%esi
   (cons #x400663 #x1e) ;;
   (cons #x400664 #x00) ;;
   (cons #x400665 #x00) ;;
   (cons #x400666 #x00) ;;
   (cons #x400667 #x48) ;; mov %rax,%rdi
   (cons #x400668 #x89) ;;
   (cons #x400669 #xc7) ;;
   (cons #x40066a #xe8) ;; callq 4004ed <part_select>
   (cons #x40066b #x7e) ;;
   (cons #x40066c #xfe) ;;
   (cons #x40066d #xff) ;;
   (cons #x40066e #xff) ;;
   (cons #x40066f #x48) ;; mov -0x10(%rbp),%rsi
   (cons #x400670 #x8b) ;;
   (cons #x400671 #x75) ;;
   (cons #x400672 #xf0) ;;
   (cons #x400673 #xb9) ;; mov $0xb,%ecx
   (cons #x400674 #x0b) ;;
   (cons #x400675 #x00) ;;
   (cons #x400676 #x00) ;;
   (cons #x400677 #x00) ;;
   (cons #x400678 #xba) ;; mov $0x3,%edx
   (cons #x400679 #x03) ;;
   (cons #x40067a #x00) ;;
   (cons #x40067b #x00) ;;
   (cons #x40067c #x00) ;;
   (cons #x40067d #x48) ;; mov %rax,%rdi
   (cons #x40067e #x89) ;;
   (cons #x40067f #xc7) ;;
   (cons #x400680 #xe8) ;; callq 400544 <part_install>
   (cons #x400681 #xbf) ;;
   (cons #x400682 #xfe) ;;
   (cons #x400683 #xff) ;;
   (cons #x400684 #xff) ;;
   (cons #x400685 #x48) ;; mov %rax,-0x8(%rbp)
   (cons #x400686 #x89) ;;
   (cons #x400687 #x45) ;;
   (cons #x400688 #xf8) ;;
   (cons #x400689 #x48) ;; mov -0x8(%rbp),%rax
   (cons #x40068a #x8b) ;;
   (cons #x40068b #x45) ;;
   (cons #x40068c #xf8) ;;
   (cons #x40068d #xc9) ;; leaveq
   (cons #x40068e #xc3) ;; retq

   ;; Section: <paddr>:


   (cons #x40068f #x55) ;; push %rbp
   (cons #x400690 #x48) ;; mov %rsp,%rbp
   (cons #x400691 #x89) ;;
   (cons #x400692 #xe5) ;;
   (cons #x400693 #x48) ;; sub $0x30,%rsp
   (cons #x400694 #x83) ;;
   (cons #x400695 #xec) ;;
   (cons #x400696 #x30) ;;
   (cons #x400697 #x48) ;; mov %rdi,-0x28(%rbp)
   (cons #x400698 #x89) ;;
   (cons #x400699 #x7d) ;;
   (cons #x40069a #xd8) ;;
   (cons #x40069b #x48) ;; mov %rsi,-0x30(%rbp)
   (cons #x40069c #x89) ;;
   (cons #x40069d #x75) ;;
   (cons #x40069e #xd0) ;;
   (cons #x40069f #x48) ;; mov -0x28(%rbp),%rax
   (cons #x4006a0 #x8b) ;;
   (cons #x4006a1 #x45) ;;
   (cons #x4006a2 #xd8) ;;
   (cons #x4006a3 #x48) ;; mov (%rax),%rax
   (cons #x4006a4 #x8b) ;;
   (cons #x4006a5 #x00) ;;
   (cons #x4006a6 #x48) ;; mov %rax,-0x18(%rbp)
   (cons #x4006a7 #x89) ;;
   (cons #x4006a8 #x45) ;;
   (cons #x4006a9 #xe8) ;;
   (cons #x4006aa #x48) ;; mov -0x18(%rbp),%rax
   (cons #x4006ab #x8b) ;;
   (cons #x4006ac #x45) ;;
   (cons #x4006ad #xe8) ;;
   (cons #x4006ae #x83) ;; and $0x1,%eax
   (cons #x4006af #xe0) ;;
   (cons #x4006b0 #x01) ;;
   (cons #x4006b1 #x48) ;; test %rax,%rax
   (cons #x4006b2 #x85) ;;
   (cons #x4006b3 #xc0) ;;
   (cons #x4006b4 #x74) ;; je 4006d1 <paddr+0x42>
   (cons #x4006b5 #x1b) ;;
   (cons #x4006b6 #x48) ;; mov -0x18(%rbp),%rax
   (cons #x4006b7 #x8b) ;;
   (cons #x4006b8 #x45) ;;
   (cons #x4006b9 #xe8) ;;
   (cons #x4006ba #xba) ;; mov $0x7,%edx
   (cons #x4006bb #x07) ;;
   (cons #x4006bc #x00) ;;
   (cons #x4006bd #x00) ;;
   (cons #x4006be #x00) ;;
   (cons #x4006bf #xbe) ;; mov $0x7,%esi
   (cons #x4006c0 #x07) ;;
   (cons #x4006c1 #x00) ;;
   (cons #x4006c2 #x00) ;;
   (cons #x4006c3 #x00) ;;
   (cons #x4006c4 #x48) ;; mov %rax,%rdi
   (cons #x4006c5 #x89) ;;
   (cons #x4006c6 #xc7) ;;
   (cons #x4006c7 #xe8) ;; callq 4004ed <part_select>
   (cons #x4006c8 #x21) ;;
   (cons #x4006c9 #xfe) ;;
   (cons #x4006ca #xff) ;;
   (cons #x4006cb #xff) ;;
   (cons #x4006cc #x48) ;; test %rax,%rax
   (cons #x4006cd #x85) ;;
   (cons #x4006ce #xc0) ;;
   (cons #x4006cf #x75) ;; jne 4006da <paddr+0x4b>
   (cons #x4006d0 #x09) ;;
   (cons #x4006d1 #x48) ;; mov $0xffffffffffffffff,%rax
   (cons #x4006d2 #xc7) ;;
   (cons #x4006d3 #xc0) ;;
   (cons #x4006d4 #xff) ;;
   (cons #x4006d5 #xff) ;;
   (cons #x4006d6 #xff) ;;
   (cons #x4006d7 #xff) ;;
   (cons #x4006d8 #xeb) ;; jmp 40072c <paddr+0x9d>
   (cons #x4006d9 #x52) ;;
   (cons #x4006da #x48) ;; mov -0x18(%rbp),%rax
   (cons #x4006db #x8b) ;;
   (cons #x4006dc #x45) ;;
   (cons #x4006dd #xe8) ;;
   (cons #x4006de #xba) ;; mov $0x33,%edx
   (cons #x4006df #x33) ;;
   (cons #x4006e0 #x00) ;;
   (cons #x4006e1 #x00) ;;
   (cons #x4006e2 #x00) ;;
   (cons #x4006e3 #xbe) ;; mov $0x1e,%esi
   (cons #x4006e4 #x1e) ;;
   (cons #x4006e5 #x00) ;;
   (cons #x4006e6 #x00) ;;
   (cons #x4006e7 #x00) ;;
   (cons #x4006e8 #x48) ;; mov %rax,%rdi
   (cons #x4006e9 #x89) ;;
   (cons #x4006ea #xc7) ;;
   (cons #x4006eb #xe8) ;; callq 4004ed <part_select>
   (cons #x4006ec #xfd) ;;
   (cons #x4006ed #xfd) ;;
   (cons #x4006ee #xff) ;;
   (cons #x4006ef #xff) ;;
   (cons #x4006f0 #x48) ;; shl $0x1e,%rax
   (cons #x4006f1 #xc1) ;;
   (cons #x4006f2 #xe0) ;;
   (cons #x4006f3 #x1e) ;;
   (cons #x4006f4 #x48) ;; mov %rax,-0x10(%rbp)
   (cons #x4006f5 #x89) ;;
   (cons #x4006f6 #x45) ;;
   (cons #x4006f7 #xf0) ;;
   (cons #x4006f8 #x48) ;; mov -0x30(%rbp),%rax
   (cons #x4006f9 #x8b) ;;
   (cons #x4006fa #x45) ;;
   (cons #x4006fb #xd0) ;;
   (cons #x4006fc #xba) ;; mov $0x1d,%edx
   (cons #x4006fd #x1d) ;;
   (cons #x4006fe #x00) ;;
   (cons #x4006ff #x00) ;;
   (cons #x400700 #x00) ;;
   (cons #x400701 #xbe) ;; mov $0x0,%esi
   (cons #x400702 #x00) ;;
   (cons #x400703 #x00) ;;
   (cons #x400704 #x00) ;;
   (cons #x400705 #x00) ;;
   (cons #x400706 #x48) ;; mov %rax,%rdi
   (cons #x400707 #x89) ;;
   (cons #x400708 #xc7) ;;
   (cons #x400709 #xe8) ;; callq 4004ed <part_select>
   (cons #x40070a #xdf) ;;
   (cons #x40070b #xfd) ;;
   (cons #x40070c #xff) ;;
   (cons #x40070d #xff) ;;
   (cons #x40070e #x48) ;; mov -0x10(%rbp),%rsi
   (cons #x40070f #x8b) ;;
   (cons #x400710 #x75) ;;
   (cons #x400711 #xf0) ;;
   (cons #x400712 #xb9) ;; mov $0x1d,%ecx
   (cons #x400713 #x1d) ;;
   (cons #x400714 #x00) ;;
   (cons #x400715 #x00) ;;
   (cons #x400716 #x00) ;;
   (cons #x400717 #xba) ;; mov $0x0,%edx
   (cons #x400718 #x00) ;;
   (cons #x400719 #x00) ;;
   (cons #x40071a #x00) ;;
   (cons #x40071b #x00) ;;
   (cons #x40071c #x48) ;; mov %rax,%rdi
   (cons #x40071d #x89) ;;
   (cons #x40071e #xc7) ;;
   (cons #x40071f #xe8) ;; callq 400544 <part_install>
   (cons #x400720 #x20) ;;
   (cons #x400721 #xfe) ;;
   (cons #x400722 #xff) ;;
   (cons #x400723 #xff) ;;
   (cons #x400724 #x48) ;; mov %rax,-0x8(%rbp)
   (cons #x400725 #x89) ;;
   (cons #x400726 #x45) ;;
   (cons #x400727 #xf8) ;;
   (cons #x400728 #x48) ;; mov -0x8(%rbp),%rax
   (cons #x400729 #x8b) ;;
   (cons #x40072a #x45) ;;
   (cons #x40072b #xf8) ;;
   (cons #x40072c #xc9) ;; leaveq
   (cons #x40072d #xc3) ;; retq

   ;; Section: <copy_pdpte>:


   (cons #x40072e #x55) ;; push %rbp
   (cons #x40072f #x48) ;; mov %rsp,%rbp
   (cons #x400730 #x89) ;;
   (cons #x400731 #xe5) ;;
   (cons #x400732 #x48) ;; sub $0x30,%rsp
   (cons #x400733 #x83) ;;
   (cons #x400734 #xec) ;;
   (cons #x400735 #x30) ;;
   (cons #x400736 #x48) ;; mov %rdi,-0x28(%rbp)
   (cons #x400737 #x89) ;;
   (cons #x400738 #x7d) ;;
   (cons #x400739 #xd8) ;;
   (cons #x40073a #x48) ;; mov %rsi,-0x30(%rbp)
   (cons #x40073b #x89) ;;
   (cons #x40073c #x75) ;;
   (cons #x40073d #xd0) ;;
   (cons #x40073e #x48) ;; mov -0x28(%rbp),%rax
   (cons #x40073f #x8b) ;;
   (cons #x400740 #x45) ;;
   (cons #x400741 #xd8) ;;
   (cons #x400742 #x48) ;; mov (%rax),%rax
   (cons #x400743 #x8b) ;;
   (cons #x400744 #x00) ;;
   (cons #x400745 #x48) ;; mov %rax,-0x20(%rbp)
   (cons #x400746 #x89) ;;
   (cons #x400747 #x45) ;;
   (cons #x400748 #xe0) ;;
   (cons #x400749 #x48) ;; mov -0x20(%rbp),%rax
   (cons #x40074a #x8b) ;;
   (cons #x40074b #x45) ;;
   (cons #x40074c #xe0) ;;
   (cons #x40074d #x83) ;; and $0x1,%eax
   (cons #x40074e #xe0) ;;
   (cons #x40074f #x01) ;;
   (cons #x400750 #x48) ;; test %rax,%rax
   (cons #x400751 #x85) ;;
   (cons #x400752 #xc0) ;;
   (cons #x400753 #x74) ;; je 400770 <copy_pdpte+0x42>
   (cons #x400754 #x1b) ;;
   (cons #x400755 #x48) ;; mov -0x20(%rbp),%rax
   (cons #x400756 #x8b) ;;
   (cons #x400757 #x45) ;;
   (cons #x400758 #xe0) ;;
   (cons #x400759 #xba) ;; mov $0x7,%edx
   (cons #x40075a #x07) ;;
   (cons #x40075b #x00) ;;
   (cons #x40075c #x00) ;;
   (cons #x40075d #x00) ;;
   (cons #x40075e #xbe) ;; mov $0x7,%esi
   (cons #x40075f #x07) ;;
   (cons #x400760 #x00) ;;
   (cons #x400761 #x00) ;;
   (cons #x400762 #x00) ;;
   (cons #x400763 #x48) ;; mov %rax,%rdi
   (cons #x400764 #x89) ;;
   (cons #x400765 #xc7) ;;
   (cons #x400766 #xe8) ;; callq 4004ed <part_select>
   (cons #x400767 #x82) ;;
   (cons #x400768 #xfd) ;;
   (cons #x400769 #xff) ;;
   (cons #x40076a #xff) ;;
   (cons #x40076b #x48) ;; test %rax,%rax
   (cons #x40076c #x85) ;;
   (cons #x40076d #xc0) ;;
   (cons #x40076e #x75) ;; jne 400779 <copy_pdpte+0x4b>
   (cons #x40076f #x09) ;;
   (cons #x400770 #x48) ;; mov $0xffffffffffffffff,%rax
   (cons #x400771 #xc7) ;;
   (cons #x400772 #xc0) ;;
   (cons #x400773 #xff) ;;
   (cons #x400774 #xff) ;;
   (cons #x400775 #xff) ;;
   (cons #x400776 #xff) ;;
   (cons #x400777 #xeb) ;; jmp 4007cc <copy_pdpte+0x9e>
   (cons #x400778 #x53) ;;
   (cons #x400779 #x48) ;; mov -0x20(%rbp),%rax
   (cons #x40077a #x8b) ;;
   (cons #x40077b #x45) ;;
   (cons #x40077c #xe0) ;;
   (cons #x40077d #xba) ;; mov $0x33,%edx
   (cons #x40077e #x33) ;;
   (cons #x40077f #x00) ;;
   (cons #x400780 #x00) ;;
   (cons #x400781 #x00) ;;
   (cons #x400782 #xbe) ;; mov $0x1e,%esi
   (cons #x400783 #x1e) ;;
   (cons #x400784 #x00) ;;
   (cons #x400785 #x00) ;;
   (cons #x400786 #x00) ;;
   (cons #x400787 #x48) ;; mov %rax,%rdi
   (cons #x400788 #x89) ;;
   (cons #x400789 #xc7) ;;
   (cons #x40078a #xe8) ;; callq 4004ed <part_select>
   (cons #x40078b #x5e) ;;
   (cons #x40078c #xfd) ;;
   (cons #x40078d #xff) ;;
   (cons #x40078e #xff) ;;
   (cons #x40078f #x48) ;; mov %rax,-0x18(%rbp)
   (cons #x400790 #x89) ;;
   (cons #x400791 #x45) ;;
   (cons #x400792 #xe8) ;;
   (cons #x400793 #x48) ;; mov -0x30(%rbp),%rax
   (cons #x400794 #x8b) ;;
   (cons #x400795 #x45) ;;
   (cons #x400796 #xd0) ;;
   (cons #x400797 #x48) ;; mov (%rax),%rax
   (cons #x400798 #x8b) ;;
   (cons #x400799 #x00) ;;
   (cons #x40079a #x48) ;; mov %rax,-0x10(%rbp)
   (cons #x40079b #x89) ;;
   (cons #x40079c #x45) ;;
   (cons #x40079d #xf0) ;;
   (cons #x40079e #x48) ;; mov -0x10(%rbp),%rsi
   (cons #x40079f #x8b) ;;
   (cons #x4007a0 #x75) ;;
   (cons #x4007a1 #xf0) ;;
   (cons #x4007a2 #x48) ;; mov -0x18(%rbp),%rax
   (cons #x4007a3 #x8b) ;;
   (cons #x4007a4 #x45) ;;
   (cons #x4007a5 #xe8) ;;
   (cons #x4007a6 #xb9) ;; mov $0x33,%ecx
   (cons #x4007a7 #x33) ;;
   (cons #x4007a8 #x00) ;;
   (cons #x4007a9 #x00) ;;
   (cons #x4007aa #x00) ;;
   (cons #x4007ab #xba) ;; mov $0x1e,%edx
   (cons #x4007ac #x1e) ;;
   (cons #x4007ad #x00) ;;
   (cons #x4007ae #x00) ;;
   (cons #x4007af #x00) ;;
   (cons #x4007b0 #x48) ;; mov %rax,%rdi
   (cons #x4007b1 #x89) ;;
   (cons #x4007b2 #xc7) ;;
   (cons #x4007b3 #xe8) ;; callq 400544 <part_install>
   (cons #x4007b4 #x8c) ;;
   (cons #x4007b5 #xfd) ;;
   (cons #x4007b6 #xff) ;;
   (cons #x4007b7 #xff) ;;
   (cons #x4007b8 #x48) ;; mov %rax,-0x8(%rbp)
   (cons #x4007b9 #x89) ;;
   (cons #x4007ba #x45) ;;
   (cons #x4007bb #xf8) ;;
   (cons #x4007bc #x48) ;; mov -0x30(%rbp),%rax
   (cons #x4007bd #x8b) ;;
   (cons #x4007be #x45) ;;
   (cons #x4007bf #xd0) ;;
   (cons #x4007c0 #x48) ;; mov -0x8(%rbp),%rdx
   (cons #x4007c1 #x8b) ;;
   (cons #x4007c2 #x55) ;;
   (cons #x4007c3 #xf8) ;;
   (cons #x4007c4 #x48) ;; mov %rdx,(%rax)
   (cons #x4007c5 #x89) ;;
   (cons #x4007c6 #x10) ;;
   (cons #x4007c7 #xb8) ;; mov $0x0,%eax
   (cons #x4007c8 #x00) ;;
   (cons #x4007c9 #x00) ;;
   (cons #x4007ca #x00) ;;
   (cons #x4007cb #x00) ;;
   (cons #x4007cc #xc9) ;; leaveq
   (cons #x4007cd #xc3) ;; retq

   ;; Section: <rewire_dst_to_src>:


   (cons #x4007ce #x55) ;; push %rbp
   (cons #x4007cf #x48) ;; mov %rsp,%rbp
   (cons #x4007d0 #x89) ;;
   (cons #x4007d1 #xe5) ;;
   (cons #x4007d2 #x48) ;; sub $0x50,%rsp
   (cons #x4007d3 #x83) ;;
   (cons #x4007d4 #xec) ;;
   (cons #x4007d5 #x50) ;;
   (cons #x4007d6 #x48) ;; mov %rdi,-0x48(%rbp)
   (cons #x4007d7 #x89) ;;
   (cons #x4007d8 #x7d) ;;
   (cons #x4007d9 #xb8) ;;
   (cons #x4007da #x48) ;; mov %rsi,-0x50(%rbp)
   (cons #x4007db #x89) ;;
   (cons #x4007dc #x75) ;;
   (cons #x4007dd #xb0) ;;
   (cons #x4007de #x0f) ;; mov %cr3,%rax
   (cons #x4007df #x20) ;;
   (cons #x4007e0 #xd8) ;;
   (cons #x4007e1 #x48) ;; mov %rax,-0x40(%rbp)
   (cons #x4007e2 #x89) ;;
   (cons #x4007e3 #x45) ;;
   (cons #x4007e4 #xc0) ;;
   (cons #x4007e5 #x48) ;; mov -0x40(%rbp),%rax
   (cons #x4007e6 #x8b) ;;
   (cons #x4007e7 #x45) ;;
   (cons #x4007e8 #xc0) ;;
   (cons #x4007e9 #x48) ;; mov -0x48(%rbp),%rdx
   (cons #x4007ea #x8b) ;;
   (cons #x4007eb #x55) ;;
   (cons #x4007ec #xb8) ;;
   (cons #x4007ed #x48) ;; mov %rdx,%rsi
   (cons #x4007ee #x89) ;;
   (cons #x4007ef #xd6) ;;
   (cons #x4007f0 #x48) ;; mov %rax,%rdi
   (cons #x4007f1 #x89) ;;
   (cons #x4007f2 #xc7) ;;
   (cons #x4007f3 #xe8) ;; callq 4005b7 <pml4e_paddr>
   (cons #x4007f4 #xbf) ;;
   (cons #x4007f5 #xfd) ;;
   (cons #x4007f6 #xff) ;;
   (cons #x4007f7 #xff) ;;
   (cons #x4007f8 #x48) ;; mov %rax,-0x38(%rbp)
   (cons #x4007f9 #x89) ;;
   (cons #x4007fa #x45) ;;
   (cons #x4007fb #xc8) ;;
   (cons #x4007fc #x48) ;; mov -0x48(%rbp),%rdx
   (cons #x4007fd #x8b) ;;
   (cons #x4007fe #x55) ;;
   (cons #x4007ff #xb8) ;;
   (cons #x400800 #x48) ;; mov -0x38(%rbp),%rax
   (cons #x400801 #x8b) ;;
   (cons #x400802 #x45) ;;
   (cons #x400803 #xc8) ;;
   (cons #x400804 #x48) ;; mov %rdx,%rsi
   (cons #x400805 #x89) ;;
   (cons #x400806 #xd6) ;;
   (cons #x400807 #x48) ;; mov %rax,%rdi
   (cons #x400808 #x89) ;;
   (cons #x400809 #xc7) ;;
   (cons #x40080a #xe8) ;; callq 40060b <pdpte_paddr>
   (cons #x40080b #xfc) ;;
   (cons #x40080c #xfd) ;;
   (cons #x40080d #xff) ;;
   (cons #x40080e #xff) ;;
   (cons #x40080f #x48) ;; mov %rax,-0x30(%rbp)
   (cons #x400810 #x89) ;;
   (cons #x400811 #x45) ;;
   (cons #x400812 #xd0) ;;
   (cons #x400813 #x48) ;; cmpq $0xffffffffffffffff,-0x30(%rbp)
   (cons #x400814 #x83) ;;
   (cons #x400815 #x7d) ;;
   (cons #x400816 #xd0) ;;
   (cons #x400817 #xff) ;;
   (cons #x400818 #x75) ;; jne 400826 <rewire_dst_to_src+0x58>
   (cons #x400819 #x0c) ;;
   (cons #x40081a #x48) ;; mov $0xffffffffffffffff,%rax
   (cons #x40081b #xc7) ;;
   (cons #x40081c #xc0) ;;
   (cons #x40081d #xff) ;;
   (cons #x40081e #xff) ;;
   (cons #x40081f #xff) ;;
   (cons #x400820 #xff) ;;
   (cons #x400821 #xe9) ;; jmpq 4008e2 <rewire_dst_to_src+0x114>
   (cons #x400822 #xbc) ;;
   (cons #x400823 #x00) ;;
   (cons #x400824 #x00) ;;
   (cons #x400825 #x00) ;;
   (cons #x400826 #x48) ;; mov -0x48(%rbp),%rdx
   (cons #x400827 #x8b) ;;
   (cons #x400828 #x55) ;;
   (cons #x400829 #xb8) ;;
   (cons #x40082a #x48) ;; mov -0x30(%rbp),%rax
   (cons #x40082b #x8b) ;;
   (cons #x40082c #x45) ;;
   (cons #x40082d #xd0) ;;
   (cons #x40082e #x48) ;; mov %rdx,%rsi
   (cons #x40082f #x89) ;;
   (cons #x400830 #xd6) ;;
   (cons #x400831 #x48) ;; mov %rax,%rdi
   (cons #x400832 #x89) ;;
   (cons #x400833 #xc7) ;;
   (cons #x400834 #xe8) ;; callq 40068f <paddr>
   (cons #x400835 #x56) ;;
   (cons #x400836 #xfe) ;;
   (cons #x400837 #xff) ;;
   (cons #x400838 #xff) ;;
   (cons #x400839 #x48) ;; mov %rax,-0x28(%rbp)
   (cons #x40083a #x89) ;;
   (cons #x40083b #x45) ;;
   (cons #x40083c #xd8) ;;
   (cons #x40083d #x48) ;; cmpq $0xffffffffffffffff,-0x28(%rbp)
   (cons #x40083e #x83) ;;
   (cons #x40083f #x7d) ;;
   (cons #x400840 #xd8) ;;
   (cons #x400841 #xff) ;;
   (cons #x400842 #x75) ;; jne 400850 <rewire_dst_to_src+0x82>
   (cons #x400843 #x0c) ;;
   (cons #x400844 #x48) ;; mov $0xffffffffffffffff,%rax
   (cons #x400845 #xc7) ;;
   (cons #x400846 #xc0) ;;
   (cons #x400847 #xff) ;;
   (cons #x400848 #xff) ;;
   (cons #x400849 #xff) ;;
   (cons #x40084a #xff) ;;
   (cons #x40084b #xe9) ;; jmpq 4008e2 <rewire_dst_to_src+0x114>
   (cons #x40084c #x92) ;;
   (cons #x40084d #x00) ;;
   (cons #x40084e #x00) ;;
   (cons #x40084f #x00) ;;
   (cons #x400850 #x48) ;; mov -0x40(%rbp),%rax
   (cons #x400851 #x8b) ;;
   (cons #x400852 #x45) ;;
   (cons #x400853 #xc0) ;;
   (cons #x400854 #x48) ;; mov -0x50(%rbp),%rdx
   (cons #x400855 #x8b) ;;
   (cons #x400856 #x55) ;;
   (cons #x400857 #xb0) ;;
   (cons #x400858 #x48) ;; mov %rdx,%rsi
   (cons #x400859 #x89) ;;
   (cons #x40085a #xd6) ;;
   (cons #x40085b #x48) ;; mov %rax,%rdi
   (cons #x40085c #x89) ;;
   (cons #x40085d #xc7) ;;
   (cons #x40085e #xe8) ;; callq 4005b7 <pml4e_paddr>
   (cons #x40085f #x54) ;;
   (cons #x400860 #xfd) ;;
   (cons #x400861 #xff) ;;
   (cons #x400862 #xff) ;;
   (cons #x400863 #x48) ;; mov %rax,-0x20(%rbp)
   (cons #x400864 #x89) ;;
   (cons #x400865 #x45) ;;
   (cons #x400866 #xe0) ;;
   (cons #x400867 #x48) ;; mov -0x50(%rbp),%rdx
   (cons #x400868 #x8b) ;;
   (cons #x400869 #x55) ;;
   (cons #x40086a #xb0) ;;
   (cons #x40086b #x48) ;; mov -0x20(%rbp),%rax
   (cons #x40086c #x8b) ;;
   (cons #x40086d #x45) ;;
   (cons #x40086e #xe0) ;;
   (cons #x40086f #x48) ;; mov %rdx,%rsi
   (cons #x400870 #x89) ;;
   (cons #x400871 #xd6) ;;
   (cons #x400872 #x48) ;; mov %rax,%rdi
   (cons #x400873 #x89) ;;
   (cons #x400874 #xc7) ;;
   (cons #x400875 #xe8) ;; callq 40060b <pdpte_paddr>
   (cons #x400876 #x91) ;;
   (cons #x400877 #xfd) ;;
   (cons #x400878 #xff) ;;
   (cons #x400879 #xff) ;;
   (cons #x40087a #x48) ;; mov %rax,-0x18(%rbp)
   (cons #x40087b #x89) ;;
   (cons #x40087c #x45) ;;
   (cons #x40087d #xe8) ;;
   (cons #x40087e #x48) ;; cmpq $0xffffffffffffffff,-0x18(%rbp)
   (cons #x40087f #x83) ;;
   (cons #x400880 #x7d) ;;
   (cons #x400881 #xe8) ;;
   (cons #x400882 #xff) ;;
   (cons #x400883 #x75) ;; jne 40088e <rewire_dst_to_src+0xc0>
   (cons #x400884 #x09) ;;
   (cons #x400885 #x48) ;; mov $0xffffffffffffffff,%rax
   (cons #x400886 #xc7) ;;
   (cons #x400887 #xc0) ;;
   (cons #x400888 #xff) ;;
   (cons #x400889 #xff) ;;
   (cons #x40088a #xff) ;;
   (cons #x40088b #xff) ;;
   (cons #x40088c #xeb) ;; jmp 4008e2 <rewire_dst_to_src+0x114>
   (cons #x40088d #x54) ;;
   (cons #x40088e #x48) ;; mov -0x18(%rbp),%rdx
   (cons #x40088f #x8b) ;;
   (cons #x400890 #x55) ;;
   (cons #x400891 #xe8) ;;
   (cons #x400892 #x48) ;; mov -0x30(%rbp),%rax
   (cons #x400893 #x8b) ;;
   (cons #x400894 #x45) ;;
   (cons #x400895 #xd0) ;;
   (cons #x400896 #x48) ;; mov %rdx,%rsi
   (cons #x400897 #x89) ;;
   (cons #x400898 #xd6) ;;
   (cons #x400899 #x48) ;; mov %rax,%rdi
   (cons #x40089a #x89) ;;
   (cons #x40089b #xc7) ;;
   (cons #x40089c #xe8) ;; callq 40072e <copy_pdpte>
   (cons #x40089d #x8d) ;;
   (cons #x40089e #xfe) ;;
   (cons #x40089f #xff) ;;
   (cons #x4008a0 #xff) ;;
   (cons #x4008a1 #x48) ;; mov %rax,-0x10(%rbp)
   (cons #x4008a2 #x89) ;;
   (cons #x4008a3 #x45) ;;
   (cons #x4008a4 #xf0) ;;
   (cons #x4008a5 #x48) ;; mov -0x50(%rbp),%rdx
   (cons #x4008a6 #x8b) ;;
   (cons #x4008a7 #x55) ;;
   (cons #x4008a8 #xb0) ;;
   (cons #x4008a9 #x48) ;; mov -0x18(%rbp),%rax
   (cons #x4008aa #x8b) ;;
   (cons #x4008ab #x45) ;;
   (cons #x4008ac #xe8) ;;
   (cons #x4008ad #x48) ;; mov %rdx,%rsi
   (cons #x4008ae #x89) ;;
   (cons #x4008af #xd6) ;;
   (cons #x4008b0 #x48) ;; mov %rax,%rdi
   (cons #x4008b1 #x89) ;;
   (cons #x4008b2 #xc7) ;;
   (cons #x4008b3 #xe8) ;; callq 40068f <paddr>
   (cons #x4008b4 #xd7) ;;
   (cons #x4008b5 #xfd) ;;
   (cons #x4008b6 #xff) ;;
   (cons #x4008b7 #xff) ;;
   (cons #x4008b8 #x48) ;; mov %rax,-0x8(%rbp)
   (cons #x4008b9 #x89) ;;
   (cons #x4008ba #x45) ;;
   (cons #x4008bb #xf8) ;;
   (cons #x4008bc #x48) ;; cmpq $0xffffffffffffffff,-0x8(%rbp)
   (cons #x4008bd #x83) ;;
   (cons #x4008be #x7d) ;;
   (cons #x4008bf #xf8) ;;
   (cons #x4008c0 #xff) ;;
   (cons #x4008c1 #x75) ;; jne 4008cc <rewire_dst_to_src+0xfe>
   (cons #x4008c2 #x09) ;;
   (cons #x4008c3 #x48) ;; mov $0xffffffffffffffff,%rax
   (cons #x4008c4 #xc7) ;;
   (cons #x4008c5 #xc0) ;;
   (cons #x4008c6 #xff) ;;
   (cons #x4008c7 #xff) ;;
   (cons #x4008c8 #xff) ;;
   (cons #x4008c9 #xff) ;;
   (cons #x4008ca #xeb) ;; jmp 4008e2 <rewire_dst_to_src+0x114>
   (cons #x4008cb #x16) ;;
   (cons #x4008cc #x48) ;; mov -0x8(%rbp),%rax
   (cons #x4008cd #x8b) ;;
   (cons #x4008ce #x45) ;;
   (cons #x4008cf #xf8) ;;
   (cons #x4008d0 #x48) ;; cmp -0x28(%rbp),%rax
   (cons #x4008d1 #x3b) ;;
   (cons #x4008d2 #x45) ;;
   (cons #x4008d3 #xd8) ;;
   (cons #x4008d4 #x75) ;; jne 4008dd <rewire_dst_to_src+0x10f>
   (cons #x4008d5 #x07) ;;
   (cons #x4008d6 #xb8) ;; mov $0x1,%eax
   (cons #x4008d7 #x01) ;;
   (cons #x4008d8 #x00) ;;
   (cons #x4008d9 #x00) ;;
   (cons #x4008da #x00) ;;
   (cons #x4008db #xeb) ;; jmp 4008e2 <rewire_dst_to_src+0x114>
   (cons #x4008dc #x05) ;;
   (cons #x4008dd #xb8) ;; mov $0x0,%eax
   (cons #x4008de #x00) ;;
   (cons #x4008df #x00) ;;
   (cons #x4008e0 #x00) ;;
   (cons #x4008e1 #x00) ;;
   (cons #x4008e2 #xc9) ;; leaveq
   (cons #x4008e3 #xc3) ;; retq

   ;; Section: <main>:


   (cons #x4008e4 #x55) ;; push %rbp
   (cons #x4008e5 #x48) ;; mov %rsp,%rbp
   (cons #x4008e6 #x89) ;;
   (cons #x4008e7 #xe5) ;;
   (cons #x4008e8 #x48) ;; sub $0x10,%rsp
   (cons #x4008e9 #x83) ;;
   (cons #x4008ea #xec) ;;
   (cons #x4008eb #x10) ;;
   (cons #x4008ec #x48) ;; movabs $0x8c0000000,%rax
   (cons #x4008ed #xb8) ;;
   (cons #x4008ee #x00) ;;
   (cons #x4008ef #x00) ;;
   (cons #x4008f0 #x00) ;;
   (cons #x4008f1 #xc0) ;;
   (cons #x4008f2 #x08) ;;
   (cons #x4008f3 #x00) ;;
   (cons #x4008f4 #x00) ;;
   (cons #x4008f5 #x00) ;;
   (cons #x4008f6 #x48) ;; mov %rax,-0x10(%rbp)
   (cons #x4008f7 #x89) ;;
   (cons #x4008f8 #x45) ;;
   (cons #x4008f9 #xf0) ;;
   (cons #x4008fa #x48) ;; movabs $0x900000000,%rax
   (cons #x4008fb #xb8) ;;
   (cons #x4008fc #x00) ;;
   (cons #x4008fd #x00) ;;
   (cons #x4008fe #x00) ;;
   (cons #x4008ff #x00) ;;
   (cons #x400900 #x09) ;;
   (cons #x400901 #x00) ;;
   (cons #x400902 #x00) ;;
   (cons #x400903 #x00) ;;
   (cons #x400904 #x48) ;; mov %rax,-0x8(%rbp)
   (cons #x400905 #x89) ;;
   (cons #x400906 #x45) ;;
   (cons #x400907 #xf8) ;;
   (cons #x400908 #x48) ;; mov -0x8(%rbp),%rdx
   (cons #x400909 #x8b) ;;
   (cons #x40090a #x55) ;;
   (cons #x40090b #xf8) ;;
   (cons #x40090c #x48) ;; mov -0x10(%rbp),%rax
   (cons #x40090d #x8b) ;;
   (cons #x40090e #x45) ;;
   (cons #x40090f #xf0) ;;
   (cons #x400910 #x48) ;; mov %rdx,%rsi
   (cons #x400911 #x89) ;;
   (cons #x400912 #xd6) ;;
   (cons #x400913 #x48) ;; mov %rax,%rdi
   (cons #x400914 #x89) ;;
   (cons #x400915 #xc7) ;;
   (cons #x400916 #xe8) ;; callq 4007ce <rewire_dst_to_src>
   (cons #x400917 #xb3) ;;
   (cons #x400918 #xfe) ;;
   (cons #x400919 #xff) ;;
   (cons #x40091a #xff) ;;
   (cons #x40091b #xc9) ;; leaveq
   (cons #x40091c #xc3) ;; retq
   (cons #x40091d #x0f) ;; nopl (%rax)
   (cons #x40091e #x1f) ;;
   (cons #x40091f #x00) ;;

   ))
