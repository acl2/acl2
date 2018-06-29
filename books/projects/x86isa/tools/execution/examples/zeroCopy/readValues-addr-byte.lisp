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

(defconst *readValues*
  (list

;; Section: <main>:


   (cons #x400400 #x53) ;; push %rbx
   (cons #x400401 #x48) ;; movabs $0x8c0000000,%rax
   (cons #x400402 #xb8) ;;
   (cons #x400403 #x00) ;;
   (cons #x400404 #x00) ;;
   (cons #x400405 #x00) ;;
   (cons #x400406 #xc0) ;;
   (cons #x400407 #x08) ;;
   (cons #x400408 #x00) ;;
   (cons #x400409 #x00) ;;
   (cons #x40040a #x00) ;;
   (cons #x40040b #x48) ;; movabs $0x900000000,%rbx
   (cons #x40040c #xbb) ;;
   (cons #x40040d #x00) ;;
   (cons #x40040e #x00) ;;
   (cons #x40040f #x00) ;;
   (cons #x400410 #x00) ;;
   (cons #x400411 #x09) ;;
   (cons #x400412 #x00) ;;
   (cons #x400413 #x00) ;;
   (cons #x400414 #x00) ;;
   (cons #x400415 #x48) ;; movq $0xf,(%rax)
   (cons #x400416 #xc7) ;;
   (cons #x400417 #x00) ;;
   (cons #x400418 #x0f) ;;
   (cons #x400419 #x00) ;;
   (cons #x40041a #x00) ;;
   (cons #x40041b #x00) ;;
   (cons #x40041c #x48) ;; mov %rbx,%rsi
   (cons #x40041d #x89) ;;
   (cons #x40041e #xde) ;;
   (cons #x40041f #x48) ;; movq $0xa,(%rbx)
   (cons #x400420 #xc7) ;;
   (cons #x400421 #x03) ;;
   (cons #x400422 #x0a) ;;
   (cons #x400423 #x00) ;;
   (cons #x400424 #x00) ;;
   (cons #x400425 #x00) ;;
   (cons #x400426 #x48) ;; movabs $0x8c0000000,%rdi
   (cons #x400427 #xbf) ;;
   (cons #x400428 #x00) ;;
   (cons #x400429 #x00) ;;
   (cons #x40042a #x00) ;;
   (cons #x40042b #xc0) ;;
   (cons #x40042c #x08) ;;
   (cons #x40042d #x00) ;;
   (cons #x40042e #x00) ;;
   (cons #x40042f #x00) ;;
   (cons #x400430 #xe8) ;; callq 400680 <rewire_dst_to_src>
   (cons #x400431 #x4b) ;;
   (cons #x400432 #x02) ;;
   (cons #x400433 #x00) ;;
   (cons #x400434 #x00) ;;
   (cons #x400435 #x31) ;; xor %edx,%edx
   (cons #x400436 #xd2) ;;
   (cons #x400437 #x48) ;; cmp $0x1,%rax
   (cons #x400438 #x83) ;;
   (cons #x400439 #xf8) ;;
   (cons #x40043a #x01) ;;
   (cons #x40043b #x74) ;; je 400441 <main+0x41>
   (cons #x40043c #x04) ;;
   (cons #x40043d #x89) ;; mov %edx,%eax
   (cons #x40043e #xd0) ;;
   (cons #x40043f #x5b) ;; pop %rbx
   (cons #x400440 #xc3) ;; retq
   (cons #x400441 #x31) ;; xor %edx,%edx
   (cons #x400442 #xd2) ;;
   (cons #x400443 #x48) ;; movabs 0x8c0000000,%rax
   (cons #x400444 #xa1) ;;
   (cons #x400445 #x00) ;;
   (cons #x400446 #x00) ;;
   (cons #x400447 #x00) ;;
   (cons #x400448 #xc0) ;;
   (cons #x400449 #x08) ;;
   (cons #x40044a #x00) ;;
   (cons #x40044b #x00) ;;
   (cons #x40044c #x00) ;;
   (cons #x40044d #x48) ;; cmp (%rbx),%rax
   (cons #x40044e #x3b) ;;
   (cons #x40044f #x03) ;;
   (cons #x400450 #x0f) ;; sete %dl
   (cons #x400451 #x94) ;;
   (cons #x400452 #xc2) ;;
   (cons #x400453 #xeb) ;; jmp 40043d <main+0x3d>
   (cons #x400454 #xe8) ;;

;; Section: <part_select>:


   (cons #x400540 #x48) ;; sub %rsi,%rdx
   (cons #x400541 #x29) ;;
   (cons #x400542 #xf2) ;;
   (cons #x400543 #xb8) ;; mov $0x1,%eax
   (cons #x400544 #x01) ;;
   (cons #x400545 #x00) ;;
   (cons #x400546 #x00) ;;
   (cons #x400547 #x00) ;;
   (cons #x400548 #x48) ;; lea 0x1(%rdx),%rcx
   (cons #x400549 #x8d) ;;
   (cons #x40054a #x4a) ;;
   (cons #x40054b #x01) ;;
   (cons #x40054c #x48) ;; shl %cl,%rax
   (cons #x40054d #xd3) ;;
   (cons #x40054e #xe0) ;;
   (cons #x40054f #x89) ;; mov %esi,%ecx
   (cons #x400550 #xf1) ;;
   (cons #x400551 #x48) ;; sub $0x1,%rax
   (cons #x400552 #x83) ;;
   (cons #x400553 #xe8) ;;
   (cons #x400554 #x01) ;;
   (cons #x400555 #x48) ;; shr %cl,%rdi
   (cons #x400556 #xd3) ;;
   (cons #x400557 #xef) ;;
   (cons #x400558 #x48) ;; and %rdi,%rax
   (cons #x400559 #x21) ;;
   (cons #x40055a #xf8) ;;
   (cons #x40055b #xc3) ;; retq
   (cons #x40055c #x0f) ;; nopl 0x0(%rax)
   (cons #x40055d #x1f) ;;
   (cons #x40055e #x40) ;;
   (cons #x40055f #x00) ;;

;; Section: <part_install>:


   (cons #x400560 #x48) ;; sub %rdx,%rcx
   (cons #x400561 #x29) ;;
   (cons #x400562 #xd1) ;;
   (cons #x400563 #xb8) ;; mov $0x1,%eax
   (cons #x400564 #x01) ;;
   (cons #x400565 #x00) ;;
   (cons #x400566 #x00) ;;
   (cons #x400567 #x00) ;;
   (cons #x400568 #x48) ;; add $0x1,%rcx
   (cons #x400569 #x83) ;;
   (cons #x40056a #xc1) ;;
   (cons #x40056b #x01) ;;
   (cons #x40056c #x48) ;; shl %cl,%rax
   (cons #x40056d #xd3) ;;
   (cons #x40056e #xe0) ;;
   (cons #x40056f #x89) ;; mov %edx,%ecx
   (cons #x400570 #xd1) ;;
   (cons #x400571 #x48) ;; sub $0x1,%rax
   (cons #x400572 #x83) ;;
   (cons #x400573 #xe8) ;;
   (cons #x400574 #x01) ;;
   (cons #x400575 #x48) ;; shl %cl,%rdi
   (cons #x400576 #xd3) ;;
   (cons #x400577 #xe7) ;;
   (cons #x400578 #x48) ;; shl %cl,%rax
   (cons #x400579 #xd3) ;;
   (cons #x40057a #xe0) ;;
   (cons #x40057b #x48) ;; not %rax
   (cons #x40057c #xf7) ;;
   (cons #x40057d #xd0) ;;
   (cons #x40057e #x48) ;; and %rsi,%rax
   (cons #x40057f #x21) ;;
   (cons #x400580 #xf0) ;;
   (cons #x400581 #x48) ;; or %rdi,%rax
   (cons #x400582 #x09) ;;
   (cons #x400583 #xf8) ;;
   (cons #x400584 #xc3) ;; retq
   (cons #x400585 #x66) ;; data32 nopw %cs:0x0(%rax,%rax,1)
   (cons #x400586 #x66) ;;
   (cons #x400587 #x2e) ;;
   (cons #x400588 #x0f) ;;
   (cons #x400589 #x1f) ;;
   (cons #x40058a #x84) ;;
   (cons #x40058b #x00) ;;
   (cons #x40058c #x00) ;;
   (cons #x40058d #x00) ;;
   (cons #x40058e #x00) ;;
   (cons #x40058f #x00) ;;

;; Section: <pml4e_paddr>:


   (cons #x400590 #x48) ;; mov %rsi,%rax
   (cons #x400591 #x89) ;;
   (cons #x400592 #xf0) ;;
   (cons #x400593 #x48) ;; and $0xfffffffffffff000,%rdi
   (cons #x400594 #x81) ;;
   (cons #x400595 #xe7) ;;
   (cons #x400596 #x00) ;;
   (cons #x400597 #xf0) ;;
   (cons #x400598 #xff) ;;
   (cons #x400599 #xff) ;;
   (cons #x40059a #x48) ;; shr $0x24,%rax
   (cons #x40059b #xc1) ;;
   (cons #x40059c #xe8) ;;
   (cons #x40059d #x24) ;;
   (cons #x40059e #x25) ;; and $0xff8,%eax
   (cons #x40059f #xf8) ;;
   (cons #x4005a0 #x0f) ;;
   (cons #x4005a1 #x00) ;;
   (cons #x4005a2 #x00) ;;
   (cons #x4005a3 #x48) ;; or %rdi,%rax
   (cons #x4005a4 #x09) ;;
   (cons #x4005a5 #xf8) ;;
   (cons #x4005a6 #xc3) ;; retq
   (cons #x4005a7 #x66) ;; nopw 0x0(%rax,%rax,1)
   (cons #x4005a8 #x0f) ;;
   (cons #x4005a9 #x1f) ;;
   (cons #x4005aa #x84) ;;
   (cons #x4005ab #x00) ;;
   (cons #x4005ac #x00) ;;
   (cons #x4005ad #x00) ;;
   (cons #x4005ae #x00) ;;
   (cons #x4005af #x00) ;;

;; Section: <pdpte_paddr>:


   (cons #x4005b0 #x48) ;; mov (%rdi),%rdx
   (cons #x4005b1 #x8b) ;;
   (cons #x4005b2 #x17) ;;
   (cons #x4005b3 #x48) ;; mov $0xffffffffffffffff,%rax
   (cons #x4005b4 #xc7) ;;
   (cons #x4005b5 #xc0) ;;
   (cons #x4005b6 #xff) ;;
   (cons #x4005b7 #xff) ;;
   (cons #x4005b8 #xff) ;;
   (cons #x4005b9 #xff) ;;
   (cons #x4005ba #xf6) ;; test $0x1,%dl
   (cons #x4005bb #xc2) ;;
   (cons #x4005bc #x01) ;;
   (cons #x4005bd #x75) ;; jne 4005c8 <pdpte_paddr+0x18>
   (cons #x4005be #x09) ;;
   (cons #x4005bf #xf3) ;; repz retq
   (cons #x4005c0 #xc3) ;;
   (cons #x4005c1 #x0f) ;; nopl 0x0(%rax)
   (cons #x4005c2 #x1f) ;;
   (cons #x4005c3 #x80) ;;
   (cons #x4005c4 #x00) ;;
   (cons #x4005c5 #x00) ;;
   (cons #x4005c6 #x00) ;;
   (cons #x4005c7 #x00) ;;
   (cons #x4005c8 #x48) ;; shr $0x1b,%rsi
   (cons #x4005c9 #xc1) ;;
   (cons #x4005ca #xee) ;;
   (cons #x4005cb #x1b) ;;
   (cons #x4005cc #x48) ;; movabs $0xffffffffff000,%rax
   (cons #x4005cd #xb8) ;;
   (cons #x4005ce #x00) ;;
   (cons #x4005cf #xf0) ;;
   (cons #x4005d0 #xff) ;;
   (cons #x4005d1 #xff) ;;
   (cons #x4005d2 #xff) ;;
   (cons #x4005d3 #xff) ;;
   (cons #x4005d4 #x0f) ;;
   (cons #x4005d5 #x00) ;;
   (cons #x4005d6 #x48) ;; and %rdx,%rax
   (cons #x4005d7 #x21) ;;
   (cons #x4005d8 #xd0) ;;
   (cons #x4005d9 #x81) ;; and $0xff8,%esi
   (cons #x4005da #xe6) ;;
   (cons #x4005db #xf8) ;;
   (cons #x4005dc #x0f) ;;
   (cons #x4005dd #x00) ;;
   (cons #x4005de #x00) ;;
   (cons #x4005df #x48) ;; or %rsi,%rax
   (cons #x4005e0 #x09) ;;
   (cons #x4005e1 #xf0) ;;
   (cons #x4005e2 #xc3) ;; retq
   (cons #x4005e3 #x66) ;; data32 data32 data32 nopw %cs:0x0(%rax,%rax,1)
   (cons #x4005e4 #x66) ;;
   (cons #x4005e5 #x66) ;;
   (cons #x4005e6 #x66) ;;
   (cons #x4005e7 #x2e) ;;
   (cons #x4005e8 #x0f) ;;
   (cons #x4005e9 #x1f) ;;
   (cons #x4005ea #x84) ;;
   (cons #x4005eb #x00) ;;
   (cons #x4005ec #x00) ;;
   (cons #x4005ed #x00) ;;
   (cons #x4005ee #x00) ;;
   (cons #x4005ef #x00) ;;

;; Section: <paddr>:


   (cons #x4005f0 #x48) ;; mov (%rdi),%rdx
   (cons #x4005f1 #x8b) ;;
   (cons #x4005f2 #x17) ;;
   (cons #x4005f3 #x48) ;; mov $0xffffffffffffffff,%rax
   (cons #x4005f4 #xc7) ;;
   (cons #x4005f5 #xc0) ;;
   (cons #x4005f6 #xff) ;;
   (cons #x4005f7 #xff) ;;
   (cons #x4005f8 #xff) ;;
   (cons #x4005f9 #xff) ;;
   (cons #x4005fa #x48) ;; mov %rdx,%rcx
   (cons #x4005fb #x89) ;;
   (cons #x4005fc #xd1) ;;
   (cons #x4005fd #x81) ;; and $0x81,%ecx
   (cons #x4005fe #xe1) ;;
   (cons #x4005ff #x81) ;;
   (cons #x400600 #x00) ;;
   (cons #x400601 #x00) ;;
   (cons #x400602 #x00) ;;
   (cons #x400603 #x48) ;; cmp $0x81,%rcx
   (cons #x400604 #x81) ;;
   (cons #x400605 #xf9) ;;
   (cons #x400606 #x81) ;;
   (cons #x400607 #x00) ;;
   (cons #x400608 #x00) ;;
   (cons #x400609 #x00) ;;
   (cons #x40060a #x74) ;; je 400610 <paddr+0x20>
   (cons #x40060b #x04) ;;
   (cons #x40060c #xf3) ;; repz retq
   (cons #x40060d #xc3) ;;
   (cons #x40060e #x66) ;; xchg %ax,%ax
   (cons #x40060f #x90) ;;
   (cons #x400610 #x48) ;; movabs $0xfffffc0000000,%rax
   (cons #x400611 #xb8) ;;
   (cons #x400612 #x00) ;;
   (cons #x400613 #x00) ;;
   (cons #x400614 #x00) ;;
   (cons #x400615 #xc0) ;;
   (cons #x400616 #xff) ;;
   (cons #x400617 #xff) ;;
   (cons #x400618 #x0f) ;;
   (cons #x400619 #x00) ;;
   (cons #x40061a #x81) ;; and $0x3fffffff,%esi
   (cons #x40061b #xe6) ;;
   (cons #x40061c #xff) ;;
   (cons #x40061d #xff) ;;
   (cons #x40061e #xff) ;;
   (cons #x40061f #x3f) ;;
   (cons #x400620 #x48) ;; and %rdx,%rax
   (cons #x400621 #x21) ;;
   (cons #x400622 #xd0) ;;
   (cons #x400623 #x48) ;; or %rsi,%rax
   (cons #x400624 #x09) ;;
   (cons #x400625 #xf0) ;;
   (cons #x400626 #xc3) ;; retq
   (cons #x400627 #x66) ;; nopw 0x0(%rax,%rax,1)
   (cons #x400628 #x0f) ;;
   (cons #x400629 #x1f) ;;
   (cons #x40062a #x84) ;;
   (cons #x40062b #x00) ;;
   (cons #x40062c #x00) ;;
   (cons #x40062d #x00) ;;
   (cons #x40062e #x00) ;;
   (cons #x40062f #x00) ;;

;; Section: <copy_pdpte>:


   (cons #x400630 #x48) ;; mov (%rdi),%rdx
   (cons #x400631 #x8b) ;;
   (cons #x400632 #x17) ;;
   (cons #x400633 #x48) ;; mov $0xffffffffffffffff,%rax
   (cons #x400634 #xc7) ;;
   (cons #x400635 #xc0) ;;
   (cons #x400636 #xff) ;;
   (cons #x400637 #xff) ;;
   (cons #x400638 #xff) ;;
   (cons #x400639 #xff) ;;
   (cons #x40063a #x48) ;; mov %rdx,%rcx
   (cons #x40063b #x89) ;;
   (cons #x40063c #xd1) ;;
   (cons #x40063d #x81) ;; and $0x81,%ecx
   (cons #x40063e #xe1) ;;
   (cons #x40063f #x81) ;;
   (cons #x400640 #x00) ;;
   (cons #x400641 #x00) ;;
   (cons #x400642 #x00) ;;
   (cons #x400643 #x48) ;; cmp $0x81,%rcx
   (cons #x400644 #x81) ;;
   (cons #x400645 #xf9) ;;
   (cons #x400646 #x81) ;;
   (cons #x400647 #x00) ;;
   (cons #x400648 #x00) ;;
   (cons #x400649 #x00) ;;
   (cons #x40064a #x74) ;; je 400650 <copy_pdpte+0x20>
   (cons #x40064b #x04) ;;
   (cons #x40064c #xf3) ;; repz retq
   (cons #x40064d #xc3) ;;
   (cons #x40064e #x66) ;; xchg %ax,%ax
   (cons #x40064f #x90) ;;
   (cons #x400650 #x48) ;; movabs $0xfffffc0000000,%rax
   (cons #x400651 #xb8) ;;
   (cons #x400652 #x00) ;;
   (cons #x400653 #x00) ;;
   (cons #x400654 #x00) ;;
   (cons #x400655 #xc0) ;;
   (cons #x400656 #xff) ;;
   (cons #x400657 #xff) ;;
   (cons #x400658 #x0f) ;;
   (cons #x400659 #x00) ;;
   (cons #x40065a #x48) ;; and %rax,%rdx
   (cons #x40065b #x21) ;;
   (cons #x40065c #xc2) ;;
   (cons #x40065d #x48) ;; movabs $0xfff000003fffffff,%rax
   (cons #x40065e #xb8) ;;
   (cons #x40065f #xff) ;;
   (cons #x400660 #xff) ;;
   (cons #x400661 #xff) ;;
   (cons #x400662 #x3f) ;;
   (cons #x400663 #x00) ;;
   (cons #x400664 #x00) ;;
   (cons #x400665 #xf0) ;;
   (cons #x400666 #xff) ;;
   (cons #x400667 #x48) ;; and (%rsi),%rax
   (cons #x400668 #x23) ;;
   (cons #x400669 #x06) ;;
   (cons #x40066a #x48) ;; or %rax,%rdx
   (cons #x40066b #x09) ;;
   (cons #x40066c #xc2) ;;
   (cons #x40066d #x31) ;; xor %eax,%eax
   (cons #x40066e #xc0) ;;
   (cons #x40066f #x48) ;; mov %rdx,(%rsi)
   (cons #x400670 #x89) ;;
   (cons #x400671 #x16) ;;
   (cons #x400672 #xc3) ;; retq
   (cons #x400673 #x66) ;; data32 data32 data32 nopw %cs:0x0(%rax,%rax,1)
   (cons #x400674 #x66) ;;
   (cons #x400675 #x66) ;;
   (cons #x400676 #x66) ;;
   (cons #x400677 #x2e) ;;
   (cons #x400678 #x0f) ;;
   (cons #x400679 #x1f) ;;
   (cons #x40067a #x84) ;;
   (cons #x40067b #x00) ;;
   (cons #x40067c #x00) ;;
   (cons #x40067d #x00) ;;
   (cons #x40067e #x00) ;;
   (cons #x40067f #x00) ;;

;; Section: <rewire_dst_to_src>:


   (cons #x400680 #x0f) ;; mov %cr3,%rax
   (cons #x400681 #x20) ;;
   (cons #x400682 #xd8) ;;
   (cons #x400683 #x48) ;; mov %rax,-0x18(%rsp)
   (cons #x400684 #x89) ;;
   (cons #x400685 #x44) ;;
   (cons #x400686 #x24) ;;
   (cons #x400687 #xe8) ;;
   (cons #x400688 #x48) ;; mov -0x18(%rsp),%rdx
   (cons #x400689 #x8b) ;;
   (cons #x40068a #x54) ;;
   (cons #x40068b #x24) ;;
   (cons #x40068c #xe8) ;;
   (cons #x40068d #x48) ;; mov %rdi,%rax
   (cons #x40068e #x89) ;;
   (cons #x40068f #xf8) ;;
   (cons #x400690 #x48) ;; shr $0x24,%rax
   (cons #x400691 #xc1) ;;
   (cons #x400692 #xe8) ;;
   (cons #x400693 #x24) ;;
   (cons #x400694 #x25) ;; and $0xff8,%eax
   (cons #x400695 #xf8) ;;
   (cons #x400696 #x0f) ;;
   (cons #x400697 #x00) ;;
   (cons #x400698 #x00) ;;
   (cons #x400699 #x48) ;; and $0xfffffffffffff000,%rdx
   (cons #x40069a #x81) ;;
   (cons #x40069b #xe2) ;;
   (cons #x40069c #x00) ;;
   (cons #x40069d #xf0) ;;
   (cons #x40069e #xff) ;;
   (cons #x40069f #xff) ;;
   (cons #x4006a0 #x48) ;; or %rdx,%rax
   (cons #x4006a1 #x09) ;;
   (cons #x4006a2 #xd0) ;;
   (cons #x4006a3 #x48) ;; mov (%rax),%rax
   (cons #x4006a4 #x8b) ;;
   (cons #x4006a5 #x00) ;;
   (cons #x4006a6 #xa8) ;; test $0x1,%al
   (cons #x4006a7 #x01) ;;
   (cons #x4006a8 #x0f) ;; je 400780 <rewire_dst_to_src+0x100>
   (cons #x4006a9 #x84) ;;
   (cons #x4006aa #xd2) ;;
   (cons #x4006ab #x00) ;;
   (cons #x4006ac #x00) ;;
   (cons #x4006ad #x00) ;;
   (cons #x4006ae #x48) ;; shr $0xc,%rax
   (cons #x4006af #xc1) ;;
   (cons #x4006b0 #xe8) ;;
   (cons #x4006b1 #x0c) ;;
   (cons #x4006b2 #x49) ;; movabs $0xffffffffff,%r8
   (cons #x4006b3 #xb8) ;;
   (cons #x4006b4 #xff) ;;
   (cons #x4006b5 #xff) ;;
   (cons #x4006b6 #xff) ;;
   (cons #x4006b7 #xff) ;;
   (cons #x4006b8 #xff) ;;
   (cons #x4006b9 #x00) ;;
   (cons #x4006ba #x00) ;;
   (cons #x4006bb #x00) ;;
   (cons #x4006bc #x48) ;; mov %rdi,%rcx
   (cons #x4006bd #x89) ;;
   (cons #x4006be #xf9) ;;
   (cons #x4006bf #x4c) ;; and %r8,%rax
   (cons #x4006c0 #x21) ;;
   (cons #x4006c1 #xc0) ;;
   (cons #x4006c2 #x48) ;; shr $0x1b,%rcx
   (cons #x4006c3 #xc1) ;;
   (cons #x4006c4 #xe9) ;;
   (cons #x4006c5 #x1b) ;;
   (cons #x4006c6 #x81) ;; and $0xff8,%ecx
   (cons #x4006c7 #xe1) ;;
   (cons #x4006c8 #xf8) ;;
   (cons #x4006c9 #x0f) ;;
   (cons #x4006ca #x00) ;;
   (cons #x4006cb #x00) ;;
   (cons #x4006cc #x48) ;; shl $0xc,%rax
   (cons #x4006cd #xc1) ;;
   (cons #x4006ce #xe0) ;;
   (cons #x4006cf #x0c) ;;
   (cons #x4006d0 #x48) ;; or %rcx,%rax
   (cons #x4006d1 #x09) ;;
   (cons #x4006d2 #xc8) ;;
   (cons #x4006d3 #x48) ;; mov (%rax),%rax
   (cons #x4006d4 #x8b) ;;
   (cons #x4006d5 #x00) ;;
   (cons #x4006d6 #x48) ;; mov %rax,%rcx
   (cons #x4006d7 #x89) ;;
   (cons #x4006d8 #xc1) ;;
   (cons #x4006d9 #x81) ;; and $0x81,%ecx
   (cons #x4006da #xe1) ;;
   (cons #x4006db #x81) ;;
   (cons #x4006dc #x00) ;;
   (cons #x4006dd #x00) ;;
   (cons #x4006de #x00) ;;
   (cons #x4006df #x48) ;; cmp $0x81,%rcx
   (cons #x4006e0 #x81) ;;
   (cons #x4006e1 #xf9) ;;
   (cons #x4006e2 #x81) ;;
   (cons #x4006e3 #x00) ;;
   (cons #x4006e4 #x00) ;;
   (cons #x4006e5 #x00) ;;
   (cons #x4006e6 #x0f) ;; jne 400780 <rewire_dst_to_src+0x100>
   (cons #x4006e7 #x85) ;;
   (cons #x4006e8 #x94) ;;
   (cons #x4006e9 #x00) ;;
   (cons #x4006ea #x00) ;;
   (cons #x4006eb #x00) ;;
   (cons #x4006ec #x48) ;; mov %rsi,%rcx
   (cons #x4006ed #x89) ;;
   (cons #x4006ee #xf1) ;;
   (cons #x4006ef #x49) ;; movabs $0xfffffc0000000,%r9
   (cons #x4006f0 #xb9) ;;
   (cons #x4006f1 #x00) ;;
   (cons #x4006f2 #x00) ;;
   (cons #x4006f3 #x00) ;;
   (cons #x4006f4 #xc0) ;;
   (cons #x4006f5 #xff) ;;
   (cons #x4006f6 #xff) ;;
   (cons #x4006f7 #x0f) ;;
   (cons #x4006f8 #x00) ;;
   (cons #x4006f9 #x48) ;; shr $0x24,%rcx
   (cons #x4006fa #xc1) ;;
   (cons #x4006fb #xe9) ;;
   (cons #x4006fc #x24) ;;
   (cons #x4006fd #x49) ;; and %rax,%r9
   (cons #x4006fe #x21) ;;
   (cons #x4006ff #xc1) ;;
   (cons #x400700 #x81) ;; and $0xff8,%ecx
   (cons #x400701 #xe1) ;;
   (cons #x400702 #xf8) ;;
   (cons #x400703 #x0f) ;;
   (cons #x400704 #x00) ;;
   (cons #x400705 #x00) ;;
   (cons #x400706 #x48) ;; or %rdx,%rcx
   (cons #x400707 #x09) ;;
   (cons #x400708 #xd1) ;;
   (cons #x400709 #x48) ;; mov (%rcx),%rax
   (cons #x40070a #x8b) ;;
   (cons #x40070b #x01) ;;
   (cons #x40070c #xa8) ;; test $0x1,%al
   (cons #x40070d #x01) ;;
   (cons #x40070e #x74) ;; je 400780 <rewire_dst_to_src+0x100>
   (cons #x40070f #x70) ;;
   (cons #x400710 #x48) ;; shr $0xc,%rax
   (cons #x400711 #xc1) ;;
   (cons #x400712 #xe8) ;;
   (cons #x400713 #x0c) ;;
   (cons #x400714 #x48) ;; mov %rsi,%rdx
   (cons #x400715 #x89) ;;
   (cons #x400716 #xf2) ;;
   (cons #x400717 #x4c) ;; and %r8,%rax
   (cons #x400718 #x21) ;;
   (cons #x400719 #xc0) ;;
   (cons #x40071a #x48) ;; shr $0x1b,%rdx
   (cons #x40071b #xc1) ;;
   (cons #x40071c #xea) ;;
   (cons #x40071d #x1b) ;;
   (cons #x40071e #x81) ;; and $0xff8,%edx
   (cons #x40071f #xe2) ;;
   (cons #x400720 #xf8) ;;
   (cons #x400721 #x0f) ;;
   (cons #x400722 #x00) ;;
   (cons #x400723 #x00) ;;
   (cons #x400724 #x48) ;; shl $0xc,%rax
   (cons #x400725 #xc1) ;;
   (cons #x400726 #xe0) ;;
   (cons #x400727 #x0c) ;;
   (cons #x400728 #x48) ;; or %rdx,%rax
   (cons #x400729 #x09) ;;
   (cons #x40072a #xd0) ;;
   (cons #x40072b #x48) ;; movabs $0xfff000003fffffff,%rdx
   (cons #x40072c #xba) ;;
   (cons #x40072d #xff) ;;
   (cons #x40072e #xff) ;;
   (cons #x40072f #xff) ;;
   (cons #x400730 #x3f) ;;
   (cons #x400731 #x00) ;;
   (cons #x400732 #x00) ;;
   (cons #x400733 #xf0) ;;
   (cons #x400734 #xff) ;;
   (cons #x400735 #x48) ;; and (%rax),%rdx
   (cons #x400736 #x23) ;;
   (cons #x400737 #x10) ;;
   (cons #x400738 #x4c) ;; or %r9,%rdx
   (cons #x400739 #x09) ;;
   (cons #x40073a #xca) ;;
   (cons #x40073b #x48) ;; mov %rdx,(%rax)
   (cons #x40073c #x89) ;;
   (cons #x40073d #x10) ;;
   (cons #x40073e #x48) ;; mov %rdx,%rax
   (cons #x40073f #x89) ;;
   (cons #x400740 #xd0) ;;
   (cons #x400741 #x25) ;; and $0x81,%eax
   (cons #x400742 #x81) ;;
   (cons #x400743 #x00) ;;
   (cons #x400744 #x00) ;;
   (cons #x400745 #x00) ;;
   (cons #x400746 #x48) ;; cmp $0x81,%rax
   (cons #x400747 #x3d) ;;
   (cons #x400748 #x81) ;;
   (cons #x400749 #x00) ;;
   (cons #x40074a #x00) ;;
   (cons #x40074b #x00) ;;
   (cons #x40074c #x75) ;; jne 400780 <rewire_dst_to_src+0x100>
   (cons #x40074d #x32) ;;
   (cons #x40074e #x48) ;; movabs $0xfffffc0000000,%rax
   (cons #x40074f #xb8) ;;
   (cons #x400750 #x00) ;;
   (cons #x400751 #x00) ;;
   (cons #x400752 #x00) ;;
   (cons #x400753 #xc0) ;;
   (cons #x400754 #xff) ;;
   (cons #x400755 #xff) ;;
   (cons #x400756 #x0f) ;;
   (cons #x400757 #x00) ;;
   (cons #x400758 #x81) ;; and $0x3fffffff,%esi
   (cons #x400759 #xe6) ;;
   (cons #x40075a #xff) ;;
   (cons #x40075b #xff) ;;
   (cons #x40075c #xff) ;;
   (cons #x40075d #x3f) ;;
   (cons #x40075e #x81) ;; and $0x3fffffff,%edi
   (cons #x40075f #xe7) ;;
   (cons #x400760 #xff) ;;
   (cons #x400761 #xff) ;;
   (cons #x400762 #xff) ;;
   (cons #x400763 #x3f) ;;
   (cons #x400764 #x48) ;; and %rax,%rdx
   (cons #x400765 #x21) ;;
   (cons #x400766 #xc2) ;;
   (cons #x400767 #x4c) ;; or %r9,%rdi
   (cons #x400768 #x09) ;;
   (cons #x400769 #xcf) ;;
   (cons #x40076a #x31) ;; xor %eax,%eax
   (cons #x40076b #xc0) ;;
   (cons #x40076c #x48) ;; or %rsi,%rdx
   (cons #x40076d #x09) ;;
   (cons #x40076e #xf2) ;;
   (cons #x40076f #x48) ;; cmp %rdx,%rdi
   (cons #x400770 #x39) ;;
   (cons #x400771 #xd7) ;;
   (cons #x400772 #x0f) ;; sete %al
   (cons #x400773 #x94) ;;
   (cons #x400774 #xc0) ;;
   (cons #x400775 #xc3) ;; retq
   (cons #x400776 #x66) ;; nopw %cs:0x0(%rax,%rax,1)
   (cons #x400777 #x2e) ;;
   (cons #x400778 #x0f) ;;
   (cons #x400779 #x1f) ;;
   (cons #x40077a #x84) ;;
   (cons #x40077b #x00) ;;
   (cons #x40077c #x00) ;;
   (cons #x40077d #x00) ;;
   (cons #x40077e #x00) ;;
   (cons #x40077f #x00) ;;
   (cons #x400780 #x48) ;; mov $0xffffffffffffffff,%rax
   (cons #x400781 #xc7) ;;
   (cons #x400782 #xc0) ;;
   (cons #x400783 #xff) ;;
   (cons #x400784 #xff) ;;
   (cons #x400785 #xff) ;;
   (cons #x400786 #xff) ;;
   (cons #x400787 #xc3) ;; retq
   (cons #x400788 #x0f) ;; nopl 0x0(%rax,%rax,1)
   (cons #x400789 #x1f) ;;
   (cons #x40078a #x84) ;;
   (cons #x40078b #x00) ;;
   (cons #x40078c #x00) ;;
   (cons #x40078d #x00) ;;
   (cons #x40078e #x00) ;;
   (cons #x40078f #x00) ;;

   ))
