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

(defconst *pageWalk1G*
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

   ;; Section: <laToPa>:


   (cons #x40072e #x55) ;; push %rbp
   (cons #x40072f #x48) ;; mov %rsp,%rbp
   (cons #x400730 #x89) ;;
   (cons #x400731 #xe5) ;;
   (cons #x400732 #x48) ;; sub $0x28,%rsp
   (cons #x400733 #x83) ;;
   (cons #x400734 #xec) ;;
   (cons #x400735 #x28) ;;
   (cons #x400736 #x48) ;; mov %rdi,-0x28(%rbp)
   (cons #x400737 #x89) ;;
   (cons #x400738 #x7d) ;;
   (cons #x400739 #xd8) ;;
   (cons #x40073a #x0f) ;; mov %cr3,%rax
   (cons #x40073b #x20) ;;
   (cons #x40073c #xd8) ;;
   (cons #x40073d #x48) ;; mov %rax,-0x20(%rbp)
   (cons #x40073e #x89) ;;
   (cons #x40073f #x45) ;;
   (cons #x400740 #xe0) ;;
   (cons #x400741 #x48) ;; mov -0x20(%rbp),%rax
   (cons #x400742 #x8b) ;;
   (cons #x400743 #x45) ;;
   (cons #x400744 #xe0) ;;
   (cons #x400745 #x48) ;; mov -0x28(%rbp),%rdx
   (cons #x400746 #x8b) ;;
   (cons #x400747 #x55) ;;
   (cons #x400748 #xd8) ;;
   (cons #x400749 #x48) ;; mov %rdx,%rsi
   (cons #x40074a #x89) ;;
   (cons #x40074b #xd6) ;;
   (cons #x40074c #x48) ;; mov %rax,%rdi
   (cons #x40074d #x89) ;;
   (cons #x40074e #xc7) ;;
   (cons #x40074f #xe8) ;; callq 4005b7 <pml4e_paddr>
   (cons #x400750 #x63) ;;
   (cons #x400751 #xfe) ;;
   (cons #x400752 #xff) ;;
   (cons #x400753 #xff) ;;
   (cons #x400754 #x48) ;; mov %rax,-0x18(%rbp)
   (cons #x400755 #x89) ;;
   (cons #x400756 #x45) ;;
   (cons #x400757 #xe8) ;;
   (cons #x400758 #x48) ;; mov -0x28(%rbp),%rdx
   (cons #x400759 #x8b) ;;
   (cons #x40075a #x55) ;;
   (cons #x40075b #xd8) ;;
   (cons #x40075c #x48) ;; mov -0x18(%rbp),%rax
   (cons #x40075d #x8b) ;;
   (cons #x40075e #x45) ;;
   (cons #x40075f #xe8) ;;
   (cons #x400760 #x48) ;; mov %rdx,%rsi
   (cons #x400761 #x89) ;;
   (cons #x400762 #xd6) ;;
   (cons #x400763 #x48) ;; mov %rax,%rdi
   (cons #x400764 #x89) ;;
   (cons #x400765 #xc7) ;;
   (cons #x400766 #xe8) ;; callq 40060b <pdpte_paddr>
   (cons #x400767 #xa0) ;;
   (cons #x400768 #xfe) ;;
   (cons #x400769 #xff) ;;
   (cons #x40076a #xff) ;;
   (cons #x40076b #x48) ;; mov %rax,-0x10(%rbp)
   (cons #x40076c #x89) ;;
   (cons #x40076d #x45) ;;
   (cons #x40076e #xf0) ;;
   (cons #x40076f #x48) ;; cmpq $0xffffffffffffffff,-0x10(%rbp)
   (cons #x400770 #x83) ;;
   (cons #x400771 #x7d) ;;
   (cons #x400772 #xf0) ;;
   (cons #x400773 #xff) ;;
   (cons #x400774 #x75) ;; jne 40077f <laToPa+0x51>
   (cons #x400775 #x09) ;;
   (cons #x400776 #x48) ;; mov $0xffffffffffffffff,%rax
   (cons #x400777 #xc7) ;;
   (cons #x400778 #xc0) ;;
   (cons #x400779 #xff) ;;
   (cons #x40077a #xff) ;;
   (cons #x40077b #xff) ;;
   (cons #x40077c #xff) ;;
   (cons #x40077d #xeb) ;; jmp 4007bc <laToPa+0x8e>
   (cons #x40077e #x3d) ;;
   (cons #x40077f #x48) ;; mov -0x28(%rbp),%rdx
   (cons #x400780 #x8b) ;;
   (cons #x400781 #x55) ;;
   (cons #x400782 #xd8) ;;
   (cons #x400783 #x48) ;; mov -0x10(%rbp),%rax
   (cons #x400784 #x8b) ;;
   (cons #x400785 #x45) ;;
   (cons #x400786 #xf0) ;;
   (cons #x400787 #x48) ;; mov %rdx,%rsi
   (cons #x400788 #x89) ;;
   (cons #x400789 #xd6) ;;
   (cons #x40078a #x48) ;; mov %rax,%rdi
   (cons #x40078b #x89) ;;
   (cons #x40078c #xc7) ;;
   (cons #x40078d #xe8) ;; callq 40068f <paddr>
   (cons #x40078e #xfd) ;;
   (cons #x40078f #xfe) ;;
   (cons #x400790 #xff) ;;
   (cons #x400791 #xff) ;;
   (cons #x400792 #x48) ;; mov %rax,-0x8(%rbp)
   (cons #x400793 #x89) ;;
   (cons #x400794 #x45) ;;
   (cons #x400795 #xf8) ;;
   (cons #x400796 #x48) ;; cmpq $0xffffffffffffffff,-0x8(%rbp)
   (cons #x400797 #x83) ;;
   (cons #x400798 #x7d) ;;
   (cons #x400799 #xf8) ;;
   (cons #x40079a #xff) ;;
   (cons #x40079b #x75) ;; jne 4007a6 <laToPa+0x78>
   (cons #x40079c #x09) ;;
   (cons #x40079d #x48) ;; mov $0xffffffffffffffff,%rax
   (cons #x40079e #xc7) ;;
   (cons #x40079f #xc0) ;;
   (cons #x4007a0 #xff) ;;
   (cons #x4007a1 #xff) ;;
   (cons #x4007a2 #xff) ;;
   (cons #x4007a3 #xff) ;;
   (cons #x4007a4 #xeb) ;; jmp 4007bc <laToPa+0x8e>
   (cons #x4007a5 #x16) ;;
   (cons #x4007a6 #x48) ;; mov -0x28(%rbp),%rax
   (cons #x4007a7 #x8b) ;;
   (cons #x4007a8 #x45) ;;
   (cons #x4007a9 #xd8) ;;
   (cons #x4007aa #x48) ;; cmp -0x8(%rbp),%rax
   (cons #x4007ab #x3b) ;;
   (cons #x4007ac #x45) ;;
   (cons #x4007ad #xf8) ;;
   (cons #x4007ae #x75) ;; jne 4007b7 <laToPa+0x89>
   (cons #x4007af #x07) ;;
   (cons #x4007b0 #xb8) ;; mov $0x1,%eax
   (cons #x4007b1 #x01) ;;
   (cons #x4007b2 #x00) ;;
   (cons #x4007b3 #x00) ;;
   (cons #x4007b4 #x00) ;;
   (cons #x4007b5 #xeb) ;; jmp 4007bc <laToPa+0x8e>
   (cons #x4007b6 #x05) ;;
   (cons #x4007b7 #xb8) ;; mov $0x0,%eax
   (cons #x4007b8 #x00) ;;
   (cons #x4007b9 #x00) ;;
   (cons #x4007ba #x00) ;;
   (cons #x4007bb #x00) ;;
   (cons #x4007bc #xc9) ;; leaveq
   (cons #x4007bd #xc3) ;; retq

   ;; Section: <main>:


   (cons #x4007be #x55) ;; push %rbp
   (cons #x4007bf #x48) ;; mov %rsp,%rbp
   (cons #x4007c0 #x89) ;;
   (cons #x4007c1 #xe5) ;;
   (cons #x4007c2 #x48) ;; sub $0x10,%rsp
   (cons #x4007c3 #x83) ;;
   (cons #x4007c4 #xec) ;;
   (cons #x4007c5 #x10) ;;
   (cons #x4007c6 #x48) ;; movq $0x2a,-0x10(%rbp)
   (cons #x4007c7 #xc7) ;;
   (cons #x4007c8 #x45) ;;
   (cons #x4007c9 #xf0) ;;
   (cons #x4007ca #x2a) ;;
   (cons #x4007cb #x00) ;;
   (cons #x4007cc #x00) ;;
   (cons #x4007cd #x00) ;;
   (cons #x4007ce #x48) ;; movq $0x3,-0x8(%rbp)
   (cons #x4007cf #xc7) ;;
   (cons #x4007d0 #x45) ;;
   (cons #x4007d1 #xf8) ;;
   (cons #x4007d2 #x03) ;;
   (cons #x4007d3 #x00) ;;
   (cons #x4007d4 #x00) ;;
   (cons #x4007d5 #x00) ;;
   (cons #x4007d6 #x48) ;; lea -0x10(%rbp),%rax
   (cons #x4007d7 #x8d) ;;
   (cons #x4007d8 #x45) ;;
   (cons #x4007d9 #xf0) ;;
   (cons #x4007da #x48) ;; mov %rax,%rdi
   (cons #x4007db #x89) ;;
   (cons #x4007dc #xc7) ;;
   (cons #x4007dd #xe8) ;; callq 40072e <laToPa>
   (cons #x4007de #x4c) ;;
   (cons #x4007df #xff) ;;
   (cons #x4007e0 #xff) ;;
   (cons #x4007e1 #xff) ;;
   (cons #x4007e2 #xc9) ;; leaveq
   (cons #x4007e3 #xc3) ;; retq
   (cons #x4007e4 #x66) ;; nopw %cs:0x0(%rax,%rax,1)
   (cons #x4007e5 #x2e) ;;
   (cons #x4007e6 #x0f) ;;
   (cons #x4007e7 #x1f) ;;
   (cons #x4007e8 #x84) ;;
   (cons #x4007e9 #x00) ;;
   (cons #x4007ea #x00) ;;
   (cons #x4007eb #x00) ;;
   (cons #x4007ec #x00) ;;
   (cons #x4007ed #x00) ;;
   (cons #x4007ee #x66) ;; xchg %ax,%ax
   (cons #x4007ef #x90) ;;
   ))
