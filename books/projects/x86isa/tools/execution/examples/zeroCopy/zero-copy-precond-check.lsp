;; Author: Shilpi Goel <shigoel@cs.utexas.edu>

;; Checking the preconditions stated in the proof of correctness of
;; the zero-copy program (proof in proofs/zeroCopy/zeroCopy.lisp).

(in-package "X86ISA")

(include-book "../../top" :ttags :all)
;; For all-xlation-governing-entries-paddrs:
(include-book "../../../../proofs/utilities/sys-view/top" :ttags :all)
(include-book "readValues-addr-byte" :ttags :all)

;; For the guard proof of the new function introduced by
;; (x86-debug). The sys-view/top book disabled
;; unsigned-byte-p, which causes this failure.
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))

;; ======================================================================

;; Initialize the system-level mode of operation
;; 1. Set the programmer-level mode to nil
;; 2. Set CR0.PG  = 1
;; 3. Set CR4.PAE = 1
;; 4. Set CR3.PDB = (logtail 12 address-of-pml4-table)
(init-sys-view
 ;; Address of PML4 Table
 0
 x86)

(!marking-view nil x86)

;; The default paging structures occupy 2,101,248 bytes (#x201000) and
;; are located at address 0. Since the program below exists in the
;; #x400*** space, there should be no overlap between the structures
;; and the program.

;; A simple sanity check:
(assert-event (equal (app-view x86) nil))

;; Set CPL = 0 (actually, it's 0 by default, which should change, maybe)
(!seg-visiblei *cs* (!seg-sel-layout-slice :rpl 0 (seg-visiblei *cs* x86)) x86)

;; Initialize the x86 state:
(init-x86-state
 ;; Status (MS and fault field)
 nil
 ;; Start Address --- set the RIP to this address
 #x400400
 ;; Halt Address --- overwrites this address by #xF4 (HLT)
 #x400440
 ;; Initial values of General-Purpose Registers
 '((#.*RSP* . #x7FFF5FBFF488))
 ;; Control Registers
 nil
 ;; Model-Specific Registers
 nil
 ;; Rflags Register
 #x2
 ;; Memory image
 *readValues*
 ;; x86 state
 x86)

;; Poised to execute rewire_dst_to_src:
(x86-break '(equal (rip x86) #x400680))
(x86-debug)
(!ms nil x86)
(!fault nil x86)
(assert-event (equal (rip x86) #x400680))

;; ======================================================================

(defconst *rewire_dst_to-src-addr-bytes*
  ;; This section has been pulled out from *readValues*.

  (list
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

(defconst *rewire_dst_to-src*
  (strip-cdrs *rewire_dst_to-src-addr-bytes*))

(define pml4-table-base-addr (x86)
  :enabled t
  ;; From proofs/zeroCopy/zeroCopy.lisp
  (ash (cr3-slice :cr3-pdb (ctri *cr3* x86)) 12))

(define page-dir-ptr-table-base-addr (lin-addr x86)
  ;; Taken from proofs/zeroCopy/zeroCopy.lisp, but modified to be executable.
  :guard (and (signed-byte-p 48 lin-addr)
              (canonical-address-p
               (pml4-table-entry-addr lin-addr (ash (loghead 40 (logtail 12 (xr :ctr *cr3* x86))) 12)))
              (canonical-address-p
               (+ 8 (pml4-table-entry-addr lin-addr (ash (loghead 40 (logtail 12 (xr :ctr *cr3* x86))) 12)))))
  (b* (((mv flg byte-list x86)
        (rb
         (create-canonical-address-list
          8 (pml4-table-entry-addr lin-addr (pml4-table-base-addr x86))) :r x86)))
    (mv flg
        (ash (loghead 40 (logtail 12 (combine-bytes byte-list))) 12)
        x86)))

;; ======================================================================

;; Tests begin here.

;; Tests related to the program.
(and
 (x86p x86)
 (not (app-view x86))
 (not (marking-view x86))
 (not (alignment-checking-enabled-p x86))

 ;; CR3's reserved bits must be zero (MBZ).
 (equal (logtail 40 (ctri *cr3* x86)) 0)

 ;; Source address is canonical.
 (canonical-address-p (xr :rgf *rdi* x86))
 (canonical-address-p (+ -1 *2^30* (xr :rgf *rdi* x86)))
 ;; Source address is 1G-aligned.
 (equal (loghead 30 (xr :rgf *rdi* x86)) 0)
 ;; Destination address is canonical.
 (canonical-address-p (xr :rgf *rsi* x86))
 (canonical-address-p (+ -1 *2^30* (xr :rgf *rsi* x86)))
 ;; Destination address is 1G-aligned.
 (equal (loghead 30 (xr :rgf *rsi* x86)) 0)
 ;; Program addresses are canonical.
 (canonical-address-p (+ (len *rewire_dst_to-src*) (xr :rip 0 x86)))
 ;; (canonical-address-p (xr :rip 0 x86))
 ;; Stack addresses are canonical.
 (canonical-address-p (+ -24 (xr :rgf *rsp* x86)))
 ;; (canonical-address-p (xr :rgf *rsp* x86))
 (canonical-address-p (+ 8 (xr :rgf *rsp* x86)))
 (equal (xr :ms 0 x86) nil)
 (equal (xr :fault 0 x86) nil)
 (equal (cpl x86) 0)
 ;; (program-at (create-canonical-address-list (len *rewire_dst_to-src*) (xr :rip 0 x86))
 ;;             *rewire_dst_to-src* x86)
 ;; No errors encountered while translating the linear
 ;; addresses where the program is located.
 ;; (not (mv-nth 0 (las-to-pas
 ;;                 (create-canonical-address-list (len *rewire_dst_to-src*) (xr :rip 0 x86))
 ;;                 :x (cpl x86) x86)))

 (b*
     ((prog-laddrs (create-canonical-address-list (len *rewire_dst_to-src*) (xr :rip 0 x86)))
      ((mv top-prog-flg program-bytes x86) (rb prog-laddrs :x x86))
      ((mv xlate-prog-flg ?prog-paddrs x86)
       (las-to-pas prog-laddrs :x (cpl x86) x86)))
   (if
       (and (equal top-prog-flg nil)
            (equal program-bytes *rewire_dst_to-src*)
            (equal xlate-prog-flg nil)
            ;; !!! How do I check whether the output x86 from rb (and
            ;; !!! las-to-pas) is the same as the input x86 to rb?
            ;; !!! But I'm not too worried about this. I've already
            ;; !!! proved
            ;; !!! mv-nth-2-rb-in-system-level-non-marking-view, which
            ;; !!! states that if the model is in non-marking mode and
            ;; !!! rb returns no error, then the output x86 from that
            ;; !!! rb is the same as the input x86.
            )
       (mv :PASSED x86)

     (mv :FAILED x86))))


;; Tests related to the stack:
(b*
    ((prog-laddrs (create-canonical-address-list (len *rewire_dst_to-src*) (xr :rip 0 x86)))
     ((mv ?xlate-prog-flg prog-paddrs x86)
      (las-to-pas prog-laddrs :x (cpl x86) x86))
     (stack-laddrs (create-canonical-address-list 8 (+ -24 (xr :rgf *rsp* x86))))
     ((mv stack-write-flg stack-paddrs-from-write x86)
      (las-to-pas stack-laddrs :w (cpl x86) x86))
     ((mv stack-read-flg stack-paddrs-from-read x86)
      (las-to-pas stack-laddrs :r (cpl x86) x86)))


  (if
      (and
       ;; Writing to stack: No errors encountered while
       ;; translating the linear addresses corresponding to the
       ;; program stack.
       ;; (not (mv-nth 0 (las-to-pas
       ;;                 (create-canonical-address-list
       ;;                  8
       ;;                  (+ -24 (xr :rgf *rsp* x86)))
       ;;                 :w (cpl x86) x86)))
       (equal stack-write-flg nil)

       ;; Reading from stack: No errors encountered while
       ;; translating the linear addresses corresponding to the
       ;; stack.
       ;; (not (mv-nth 0 (las-to-pas
       ;;                 (create-canonical-address-list
       ;;                  8 (+ -24 (xr :rgf *rsp* x86)))
       ;;                 :r (cpl x86) x86)))
       (equal stack-read-flg nil)

       ;; !!! Extra check.
       (equal stack-paddrs-from-write stack-paddrs-from-read)

       ;; Reading from stack: The stack is located in a
       ;; contiguous region of memory --- no overlaps among
       ;; physical addresses of the stack. I need this hypothesis
       ;; so that rb-wb-equal-in-system-level-non-marking-view
       ;; can fire.
       ;; (no-duplicates-p
       ;;  (mv-nth 1 (las-to-pas
       ;;             (create-canonical-address-list
       ;;              8 (+ -24 (xr :rgf *rsp* x86)))
       ;;             :r (cpl x86) x86)))
       (no-duplicates-p stack-paddrs-from-read)

       ;; The physical addresses corresponding to the program and
       ;; stack are disjoint.
       ;; (disjoint-p
       ;;  (mv-nth 1 (las-to-pas
       ;;             (create-canonical-address-list (len *rewire_dst_to-src*) (xr :rip 0 x86))
       ;;             :x (cpl x86) x86))
       ;;  (mv-nth 1
       ;;          (las-to-pas
       ;;           (create-canonical-address-list
       ;;            8 (+ -24 (xr :rgf *rsp* x86)))
       ;;           :w (cpl x86) x86)))
       (disjoint-p prog-paddrs stack-paddrs-from-write)

       ;; Translation-governing addresses of the program are
       ;; disjoint from the physical addresses of the stack.
       ;; (disjoint-p
       ;;  (all-xlation-governing-entries-paddrs
       ;;   (create-canonical-address-list (len *rewire_dst_to-src*) (xr :rip 0 x86))
       ;;   x86)
       ;;  (mv-nth 1 (las-to-pas
       ;;             (create-canonical-address-list
       ;;              8 (+ -24 (xr :rgf *rsp* x86)))
       ;;             :w (cpl x86) x86)))
       (disjoint-p
        (all-xlation-governing-entries-paddrs prog-laddrs x86)
        stack-paddrs-from-write)

       ;; Translation-governing addresses of the stack are
       ;; disjoint from the physical addresses of the stack.
       ;; (disjoint-p
       ;;  (all-xlation-governing-entries-paddrs
       ;;   (create-canonical-address-list
       ;;    8 (+ -24 (xr :rgf *rsp* x86)))
       ;;   x86)
       ;;  (mv-nth 1 (las-to-pas
       ;;             (create-canonical-address-list
       ;;              8 (+ -24 (xr :rgf *rsp* x86)))
       ;;             :w (cpl x86) x86)))
       (disjoint-p
        (all-xlation-governing-entries-paddrs stack-laddrs x86)
        stack-paddrs-from-write))

      (mv :PASSED x86)

    (mv :FAILED x86)))

;; Tests related to the source PML4TE:
(b* ((pml4-table-entry-addr
      (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86)))
     (src-pml4-laddrs (create-canonical-address-list 8 pml4-table-entry-addr))
     ((mv src-pml4-laddrs-flg src-pml4-paddrs x86)
      (las-to-pas src-pml4-laddrs :r (cpl x86) x86))
     ((mv src-pml4-entry-flg src-pml4-entry x86)
      (rb src-pml4-laddrs :r x86))
     (stack-laddrs (create-canonical-address-list 8 (+ -24 (xr :rgf *rsp* x86))))
     ((mv ?stack-write-flg stack-paddrs-from-write x86)
      (las-to-pas stack-laddrs :w (cpl x86) x86)))
  (if
      (and

       ;; Assumptions about the source PML4TE:

       ;; PML4TE linear addresses are canonical.
       ;; (canonical-address-p
       ;;  (+ 7 (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86))))
       (canonical-address-p (+ 7 pml4-table-entry-addr))

       ;; No errors encountered while translating the PML4TE linear addresses.
       ;; (not (mv-nth 0 (las-to-pas
       ;;                 (create-canonical-address-list
       ;;                  8 (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86)))
       ;;                 :r (cpl x86) x86)))
       (equal src-pml4-laddrs-flg nil)

       ;; The translation-governing addresses of PML4TE addresses
       ;; are disjoint from the physical addresses corresponding
       ;; to the stack.
       ;; (disjoint-p
       ;;  (all-xlation-governing-entries-paddrs
       ;;   (create-canonical-address-list
       ;;    8 (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86)))
       ;;   x86)
       ;;  (mv-nth 1 (las-to-pas
       ;;             (create-canonical-address-list
       ;;              8 (+ -24 (xr :rgf *rsp* x86))) :w (cpl x86) x86)))
       (disjoint-p
        (all-xlation-governing-entries-paddrs src-pml4-laddrs x86)
        stack-paddrs-from-write)

       ;; The PML4TE physical addresses are disjoint from the
       ;; stack physical addresses.
       ;; (disjoint-p
       ;;             (mv-nth 1 (las-to-pas
       ;;                        (create-canonical-address-list
       ;;                         8
       ;;                         (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86)))
       ;;                        :r (cpl x86) x86))
       ;;             (mv-nth 1 (las-to-pas
       ;;                        (create-canonical-address-list 8 (+ -24 (xr :rgf *rsp* x86))) :w (cpl x86) x86)))

       (disjoint-p src-pml4-paddrs stack-paddrs-from-write)

       ;; PML4TE has P = 1 (i.e., it is present).
       ;; (equal
       ;;  (loghead
       ;;   1
       ;;   (logext
       ;;    64
       ;;    (combine-bytes
       ;;     (mv-nth
       ;;      1
       ;;      (rb
       ;;       (create-canonical-address-list
       ;;        8
       ;;        (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86)))
       ;;       :r x86)))))
       ;;  1)
       ;; !! Extra check:
       (equal src-pml4-entry-flg nil)
       (equal (loghead 1 (logext 64 (combine-bytes src-pml4-entry))) 1))

      (mv :PASSED x86)

    (mv :FAILED x86)))

;; Tests related to the source PDPTE:
(b* (((mv page-dir-ptr-table-base-addr-flg page-dir-ptr-table-base-addr x86)
      (page-dir-ptr-table-base-addr (xr :rgf *rdi* x86) x86))
     (page-dir-ptr-table-entry-addr
      (page-dir-ptr-table-entry-addr (xr :rgf *rdi* x86) page-dir-ptr-table-base-addr))
     (src-page-dir-ptr-laddrs (create-canonical-address-list 8 page-dir-ptr-table-entry-addr))
     ((mv src-page-dir-ptr-laddrs-flg src-page-dir-ptr-paddrs x86)
      (las-to-pas src-page-dir-ptr-laddrs :r (cpl x86) x86))
     ((mv src-page-dir-ptr-entry-flg src-page-dir-ptr-entry x86)
      (rb src-page-dir-ptr-laddrs :r x86))
     (stack-laddrs (create-canonical-address-list 8 (+ -24 (xr :rgf *rsp* x86))))
     ((mv ?stack-write-flg stack-paddrs-from-write x86)
      (las-to-pas stack-laddrs :w (cpl x86) x86)))

  (if
      (and

       ;; Assumptions about the source PDPTE:

       ;; !! Extra check:
       (equal page-dir-ptr-table-base-addr-flg nil)

       ;; PDPTE linear addresses are canonical.
       ;; (canonical-address-p
       ;;  (+ 7 (page-dir-ptr-table-entry-addr
       ;;        (xr :rgf *rdi* x86)
       ;;        (page-dir-ptr-table-base-addr (xr :rgf *rdi* x86) x86))))
       (canonical-address-p (+ 7 page-dir-ptr-table-entry-addr))

       ;; No errors encountered while translating the PDPTE linear addresses.
       ;; (not (mv-nth 0 (las-to-pas
       ;;                 (create-canonical-address-list
       ;;                  8
       ;;                  (page-dir-ptr-table-entry-addr
       ;;                   (xr :rgf *rdi* x86)
       ;;                   (page-dir-ptr-table-base-addr (xr :rgf *rdi* x86) x86)))
       ;;                 :r (cpl x86) x86)))
       (equal src-page-dir-ptr-laddrs-flg nil)

       ;; The translation-governing addresses of PDPTE addresses
       ;; are disjoint from the physical addresses corresponding
       ;; to the stack.
       ;; (disjoint-p
       ;;  (all-xlation-governing-entries-paddrs
       ;;   (create-canonical-address-list
       ;;    8
       ;;    (page-dir-ptr-table-entry-addr
       ;;     (xr :rgf *rdi* x86)
       ;;     (page-dir-ptr-table-base-addr (xr :rgf *rdi* x86) x86)))
       ;;   x86)
       ;;  (mv-nth 1 (las-to-pas
       ;;             (create-canonical-address-list
       ;;              8 (+ -24 (xr :rgf *rsp* x86))) :w (cpl x86) x86)))
       (disjoint-p
        (all-xlation-governing-entries-paddrs src-page-dir-ptr-laddrs x86)
        stack-paddrs-from-write)

       ;; The PDPTE physical addresses are disjoint from the
       ;; stack physical addresses.
       ;; (disjoint-p
       ;;  (mv-nth 1 (las-to-pas
       ;;             (create-canonical-address-list
       ;;              8
       ;;              (page-dir-ptr-table-entry-addr
       ;;               (xr :rgf *rdi* x86)
       ;;               (page-dir-ptr-table-base-addr (xr :rgf *rdi* x86) x86)))
       ;;             :r (cpl x86) x86))
       ;;  (mv-nth 1 (las-to-pas
       ;;             (create-canonical-address-list
       ;;              8 (+ -24 (xr :rgf *rsp* x86))) :w (cpl x86) x86)))
       (disjoint-p src-page-dir-ptr-paddrs stack-paddrs-from-write)

       ;; PDPTE does not have the P or PS bit cleared (i.e., the
       ;; entry is present and it points to a 1G page).
       ;; (equal (part-select
       ;;         (combine-bytes
       ;;          (mv-nth 1
       ;;                  (rb
       ;;                   (create-canonical-address-list
       ;;                    8
       ;;                    (page-dir-ptr-table-entry-addr
       ;;                     (xr :rgf *rdi* x86)
       ;;                     (page-dir-ptr-table-base-addr (xr :rgf *rdi* x86) x86)))
       ;;                   :r x86)))
       ;;         :low 0 :width 1)
       ;;        1)
       ;; (equal (part-select
       ;;         (combine-bytes
       ;;          (mv-nth 1
       ;;                  (rb
       ;;                   (create-canonical-address-list
       ;;                    8
       ;;                    (page-dir-ptr-table-entry-addr
       ;;                     (xr :rgf *rdi* x86)
       ;;                     (page-dir-ptr-table-base-addr (xr :rgf *rdi* x86) x86)))
       ;;                   :r x86)))
       ;;         :low 7 :width 1)
       ;;        1)
       ;; !! Extra check:
       (equal src-page-dir-ptr-entry-flg nil)
       (equal (part-select (combine-bytes src-page-dir-ptr-entry) :low 0 :width 1) 1)
       (equal (part-select (combine-bytes src-page-dir-ptr-entry) :low 7 :width 1) 1))

      (mv :PASSED x86)
    (mv :FAILED x86)))

;; Tests related to the destination PML4TE:
(b* ((pml4-table-entry-addr
      (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86)))
     (dst-pml4-laddrs (create-canonical-address-list 8 pml4-table-entry-addr))
     ((mv dst-pml4-laddrs-flg dst-pml4-paddrs x86)
      (las-to-pas dst-pml4-laddrs :r (cpl x86) x86))
     ((mv dst-pml4-entry-flg dst-pml4-entry x86)
      (rb dst-pml4-laddrs :r x86))
     (stack-laddrs (create-canonical-address-list 8 (+ -24 (xr :rgf *rsp* x86))))
     ((mv ?stack-write-flg stack-paddrs-from-write x86)
      (las-to-pas stack-laddrs :w (cpl x86) x86)))
  (if
      (and

       ;; Assumptions about the destination PML4TE:

       ;; PML4TE linear addresses are canonical.
       ;; (canonical-address-p
       ;;  (+ 7 (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86))))
       (canonical-address-p (+ 7 pml4-table-entry-addr))

       ;; No errors encountered while translating the PML4TE linear addresses.
       ;; (not (mv-nth 0 (las-to-pas
       ;;                 (create-canonical-address-list
       ;;                  8 (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86)))
       ;;                 :r (cpl x86) x86)))
       (equal dst-pml4-laddrs-flg nil)

       ;; The translation-governing addresses of PML4TE addresses
       ;; are disjoint from the physical addresses corresponding
       ;; to the stack.
       ;; (disjoint-p
       ;;  (all-xlation-governing-entries-paddrs
       ;;   (create-canonical-address-list
       ;;    8 (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86)))
       ;;   x86)
       ;;  (mv-nth 1 (las-to-pas
       ;;             (create-canonical-address-list
       ;;              8 (+ -24 (xr :rgf *rsp* x86))) :w (cpl x86) x86)))
       (disjoint-p
        (all-xlation-governing-entries-paddrs dst-pml4-laddrs x86)
        stack-paddrs-from-write)

       ;; The PML4TE physical addresses are disjoint from the
       ;; stack physical addresses.
       ;; (disjoint-p
       ;;             (mv-nth 1 (las-to-pas
       ;;                        (create-canonical-address-list
       ;;                         8
       ;;                         (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86)))
       ;;                        :r (cpl x86) x86))
       ;;             (mv-nth 1 (las-to-pas
       ;;                        (create-canonical-address-list 8 (+ -24 (xr :rgf *rsp* x86))) :w (cpl x86) x86)))

       (disjoint-p dst-pml4-paddrs stack-paddrs-from-write)

       ;; PML4TE has P = 1 (i.e., it is present).
       ;; (equal
       ;;  (loghead
       ;;   1
       ;;   (logext
       ;;    64
       ;;    (combine-bytes
       ;;     (mv-nth
       ;;      1
       ;;      (rb
       ;;       (create-canonical-address-list
       ;;        8
       ;;        (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86)))
       ;;       :r x86)))))
       ;;  1)
       ;; !! Extra check:
       (equal dst-pml4-entry-flg nil)
       (equal (loghead 1 (logext 64 (combine-bytes dst-pml4-entry))) 1))

      (mv :PASSED x86)

    (mv :FAILED x86)))

;; Tests related to the destination PDPTE:
(b* ((prog-laddrs (create-canonical-address-list (len *rewire_dst_to-src*) (xr :rip 0 x86)))
     ((mv ?xlate-prog-flg prog-paddrs x86)
      (las-to-pas prog-laddrs :x (cpl x86) x86))
     ((mv page-dir-ptr-table-base-addr-flg page-dir-ptr-table-base-addr x86)
      (page-dir-ptr-table-base-addr (xr :rgf *rsi* x86) x86))
     (page-dir-ptr-table-entry-addr
      (page-dir-ptr-table-entry-addr (xr :rgf *rsi* x86) page-dir-ptr-table-base-addr))
     (dst-page-dir-ptr-laddrs (create-canonical-address-list 8 page-dir-ptr-table-entry-addr))
     ((mv dst-page-dir-ptr-laddrs-flg-read dst-page-dir-ptr-paddrs x86)
      (las-to-pas dst-page-dir-ptr-laddrs :r (cpl x86) x86))
     ((mv dst-page-dir-ptr-laddrs-flg-write & x86)
      (las-to-pas dst-page-dir-ptr-laddrs :w (cpl x86) x86))
     ((mv dst-page-dir-ptr-entry-flg dst-page-dir-ptr-entry x86)
      (rb dst-page-dir-ptr-laddrs :r x86))
     (stack-laddrs (create-canonical-address-list 8 (+ -24 (xr :rgf *rsp* x86))))
     ((mv ?stack-write-flg stack-paddrs-from-write x86)
      (las-to-pas stack-laddrs :w (cpl x86) x86)))

  (if
      (and

       ;; Assumptions about the destination PDPTE:

       ;; !! Extra check:
       (equal page-dir-ptr-table-base-addr-flg nil)

       ;; PDPTE linear addresses are canonical.
       ;; (canonical-address-p
       ;;  (page-dir-ptr-table-entry-addr
       ;;   (xr :rgf *rsi* x86)
       ;;   (page-dir-ptr-table-base-addr (xr :rgf *rsi* x86) x86)))
       ;; (canonical-address-p
       ;;  (+ 7 (page-dir-ptr-table-entry-addr
       ;;        (xr :rgf *rsi* x86)
       ;;        (page-dir-ptr-table-base-addr (xr :rgf *rsi* x86) x86))))
       (canonical-address-p page-dir-ptr-table-entry-addr)
       (canonical-address-p (+ 7 page-dir-ptr-table-entry-addr))

       ;; No errors encountered while translating the PDPTE
       ;; linear addresses on behalf of a read.
       ;; (not (mv-nth 0 (las-to-pas
       ;;                 (create-canonical-address-list
       ;;                  8
       ;;                  (page-dir-ptr-table-entry-addr
       ;;                   (xr :rgf *rsi* x86)
       ;;                   (page-dir-ptr-table-base-addr (xr :rgf *rsi* x86) x86)))
       ;;                 :r (cpl x86) x86)))
       (equal dst-page-dir-ptr-laddrs-flg-read nil)

       ;; No errors encountered while translating the PDPTE
       ;; linear addresses on behalf of a write.
       ;; (not (mv-nth 0 (las-to-pas
       ;;                 (create-canonical-address-list
       ;;                  8
       ;;                  (page-dir-ptr-table-entry-addr
       ;;                   (xr :rgf *rsi* x86)
       ;;                   (page-dir-ptr-table-base-addr (xr :rgf *rsi* x86) x86)))
       ;;                 :w (cpl x86) x86)))
       (equal dst-page-dir-ptr-laddrs-flg-write nil)


       ;; The translation-governing addresses of PDPTE addresses
       ;; are disjoint from the physical addresses corresponding
       ;; to the stack.
       ;; (disjoint-p
       ;;  (all-xlation-governing-entries-paddrs
       ;;   (create-canonical-address-list
       ;;    8
       ;;    (page-dir-ptr-table-entry-addr
       ;;     (xr :rgf *rsi* x86)
       ;;     (page-dir-ptr-table-base-addr (xr :rgf *rsi* x86) x86)))
       ;;   x86)
       ;;  (mv-nth 1 (las-to-pas
       ;;             (create-canonical-address-list
       ;;              8 (+ -24 (xr :rgf *rsp* x86))) :w (cpl x86) x86)))
       (disjoint-p
        (all-xlation-governing-entries-paddrs dst-page-dir-ptr-laddrs x86)
        stack-paddrs-from-write)

       ;; The PDPTE physical addresses are disjoint from the
       ;; stack physical addresses.
       ;; (disjoint-p
       ;;  (mv-nth 1 (las-to-pas
       ;;             (create-canonical-address-list
       ;;              8
       ;;              (page-dir-ptr-table-entry-addr
       ;;               (xr :rgf *rsi* x86)
       ;;               (page-dir-ptr-table-base-addr (xr :rgf *rsi* x86) x86)))
       ;;             :r (cpl x86) x86))
       ;;  (mv-nth 1 (las-to-pas
       ;;             (create-canonical-address-list
       ;;              8 (+ -24 (xr :rgf *rsp* x86))) :w (cpl x86) x86)))
       (disjoint-p dst-page-dir-ptr-paddrs stack-paddrs-from-write)

       ;; The physical addresses corresponding to the program are
       ;; disjoint from those of the PDPTE (on behalf of a
       ;; write).
       ;; (disjoint-p
       ;;  (mv-nth 1 (las-to-pas
       ;;             (create-canonical-address-list (len *rewire_dst_to-src*) (xr :rip 0 x86))
       ;;             :x (cpl x86) x86))
       ;;  (mv-nth 1 (las-to-pas
       ;;             (create-canonical-address-list
       ;;              8
       ;;              (page-dir-ptr-table-entry-addr
       ;;               (xr :rgf *rsi* x86)
       ;;               (page-dir-ptr-table-base-addr (xr :rgf *rsi* x86) x86)))
       ;;             :w (cpl x86) x86)))
       (disjoint-p prog-paddrs dst-page-dir-ptr-paddrs)

       ;; Translation-governing addresses of the program are
       ;; disjoint from the PDPTE physical addresses (on behalf
       ;; of a write).
       ;; (disjoint-p
       ;;  (all-xlation-governing-entries-paddrs
       ;;   (create-canonical-address-list (len *rewire_dst_to-src*) (xr :rip 0 x86))
       ;;   x86)
       ;;  (mv-nth 1 (las-to-pas
       ;;             (create-canonical-address-list
       ;;              8
       ;;              (page-dir-ptr-table-entry-addr
       ;;               (xr :rgf *rsi* x86)
       ;;               (page-dir-ptr-table-base-addr (xr :rgf *rsi* x86) x86)))
       ;;             :w (cpl x86) x86)))
       (disjoint-p (all-xlation-governing-entries-paddrs prog-laddrs x86)
                   dst-page-dir-ptr-paddrs)


       ;; PDPTE does not have the P or PS bit cleared (i.e., the
       ;; entry is present and it points to a 1G page).
       ;; (equal (part-select
       ;;         (combine-bytes
       ;;          (mv-nth 1
       ;;                  (rb
       ;;                   (create-canonical-address-list
       ;;                    8
       ;;                    (page-dir-ptr-table-entry-addr
       ;;                     (xr :rgf *rsi* x86)
       ;;                     (page-dir-ptr-table-base-addr (xr :rgf *rsi* x86) x86)))
       ;;                   :r x86)))
       ;;         :low 0 :width 1)
       ;;        1)
       ;; (equal (part-select
       ;;         (combine-bytes
       ;;          (mv-nth 1
       ;;                  (rb
       ;;                   (create-canonical-address-list
       ;;                    8
       ;;                    (page-dir-ptr-table-entry-addr
       ;;                     (xr :rgf *rsi* x86)
       ;;                     (page-dir-ptr-table-base-addr (xr :rgf *rsi* x86) x86)))
       ;;                   :r x86)))
       ;;         :low 7 :width 1)
       ;;        1)
       ;; !! Extra check:
       (equal dst-page-dir-ptr-entry-flg nil)
       (equal (part-select (combine-bytes dst-page-dir-ptr-entry) :low 0 :width 1) 1)
       (equal (part-select (combine-bytes dst-page-dir-ptr-entry) :low 7 :width 1) 1))

      (mv :PASSED x86)
    (mv :FAILED x86)))

;; Tests for the final ret instruction:
(b* ((ret-laddrs (create-canonical-address-list 8 (xr :rgf *rsp* x86)))
     ((mv ret-paddrs-flg ret-paddrs x86)
      (las-to-pas ret-laddrs :r (cpl x86) x86))
     ((mv ret-value-flg ret-value x86)
      (rb ret-laddrs :r x86))
     ((mv & page-dir-ptr-table-base-addr x86)
      (page-dir-ptr-table-base-addr (xr :rgf *rsi* x86) x86))
     (page-dir-ptr-table-entry-addr
      (page-dir-ptr-table-entry-addr (xr :rgf *rsi* x86) page-dir-ptr-table-base-addr))
     (dst-page-dir-ptr-laddrs (create-canonical-address-list 8 page-dir-ptr-table-entry-addr))
     ((mv & dst-page-dir-ptr-paddrs x86)
      (las-to-pas dst-page-dir-ptr-laddrs :r (cpl x86) x86))
     (stack-laddrs (create-canonical-address-list 8 (+ -24 (xr :rgf *rsp* x86))))
     ((mv ?stack-write-flg stack-paddrs-from-write x86)
      (las-to-pas stack-laddrs :w (cpl x86) x86)))

  (if
      (and
       ;; For the final ret instruction:

       ;; Reading from stack for the final ret instruction
       ;; doesn't cause errors.
       ;; (not (mv-nth 0 (las-to-pas
       ;;                 (create-canonical-address-list
       ;;                  8 (xr :rgf *rsp* x86))
       ;;                 :r (cpl x86) x86)))
       (equal ret-paddrs-flg nil)

       ;; The translation-governing addresses of the ret address
       ;; are disjoint from the destination PDPTE.
       ;; (disjoint-p
       ;;  (all-xlation-governing-entries-paddrs
       ;;   (create-canonical-address-list 8 (xr :rgf *rsp* x86)) x86)
       ;;  (mv-nth 1 (las-to-pas
       ;;             (create-canonical-address-list
       ;;              8
       ;;              (page-dir-ptr-table-entry-addr
       ;;               (xr :rgf *rsi* x86)
       ;;               (page-dir-ptr-table-base-addr (xr :rgf *rsi* x86) x86)))
       ;;             :r (cpl x86) x86)))
       (disjoint-p
        (all-xlation-governing-entries-paddrs ret-laddrs x86)
        dst-page-dir-ptr-paddrs)

       ;; The destination PDPTE is disjoint from the ret address
       ;; on the stack.
       ;; (disjoint-p
       ;;  (mv-nth 1 (las-to-pas
       ;;             (create-canonical-address-list 8 (xr :rgf *rsp* x86))
       ;;             :r (cpl x86) x86))
       ;;  (mv-nth 1 (las-to-pas
       ;;             (create-canonical-address-list
       ;;              8
       ;;              (page-dir-ptr-table-entry-addr
       ;;               (xr :rgf *rsi* x86)
       ;;               (page-dir-ptr-table-base-addr (xr :rgf *rsi* x86) x86)))
       ;;             :r (cpl x86) x86)))
       (disjoint-p ret-paddrs dst-page-dir-ptr-paddrs)

       ;; The destination PDPTE is disjoint from the rest of the stack.
       ;; (disjoint-p
       ;;  (mv-nth 1 (las-to-pas
       ;;             (create-canonical-address-list
       ;;              8
       ;;              (page-dir-ptr-table-entry-addr
       ;;               (xr :rgf *rsi* x86)
       ;;               (page-dir-ptr-table-base-addr (xr :rgf *rsi* x86) x86)))
       ;;             :r (cpl x86) x86))
       ;;  (mv-nth 1 (las-to-pas
       ;;             (create-canonical-address-list
       ;;              8 (+ -24 (xr :rgf *rsp* x86))) :w (cpl x86) x86)))
       (disjoint-p dst-page-dir-ptr-paddrs stack-paddrs-from-write)

       ;; The ret address on the stack is disjoint from the rest
       ;; of the stack.
       ;; (disjoint-p
       ;;  (mv-nth 1 (las-to-pas
       ;;             (create-canonical-address-list 8 (xr :rgf *rsp* x86))
       ;;             :r (cpl x86) x86))
       ;;  (mv-nth 1 (las-to-pas
       ;;             (create-canonical-address-list 8 (+ -24 (xr :rgf *rsp* x86))) :w (cpl x86) x86)))
       (disjoint-p ret-paddrs stack-paddrs-from-write)

       ;; The translation-governing addresses of the return
       ;; address on the stack are disjoint from the physical
       ;; addresses of the rest of the stack.
       ;; (disjoint-p
       ;;  (all-xlation-governing-entries-paddrs
       ;;   (create-canonical-address-list 8 (xr :rgf *rsp* x86)) x86)
       ;;  (mv-nth 1
       ;;          (las-to-pas (create-canonical-address-list
       ;;                       8 (+ -24 (xr :rgf *rsp* x86)))
       ;;                      :w (cpl x86) x86)))
       (disjoint-p
        (all-xlation-governing-entries-paddrs ret-laddrs x86)
        stack-paddrs-from-write)

       ;; Return address on the stack is canonical.
       ;; (canonical-address-p
       ;;  (logext 64
       ;;          (combine-bytes
       ;;           (mv-nth 1
       ;;                   (rb (create-canonical-address-list
       ;;                        8 (xr :rgf *rsp* x86))
       ;;                       :r x86)))))
       ;; !! Extra check
       (equal ret-value-flg nil)
       (canonical-address-p
        (logext 64 (combine-bytes ret-value))))

      (mv :PASSED x86)

    (mv :FAILED x86)))

;; Tests for the direct mapping.
(b* ((src-pml4-table-entry-addr
      (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86)))
     (src-pml4-laddrs (create-canonical-address-list 8 src-pml4-table-entry-addr))
     ((mv & src-pml4-paddrs x86)
      (las-to-pas src-pml4-laddrs :r (cpl x86) x86))

     ((mv & src-page-dir-ptr-table-base-addr x86)
      (page-dir-ptr-table-base-addr (xr :rgf *rdi* x86) x86))
     (src-page-dir-ptr-table-entry-addr
      (page-dir-ptr-table-entry-addr (xr :rgf *rdi* x86) src-page-dir-ptr-table-base-addr))
     (src-page-dir-ptr-laddrs (create-canonical-address-list 8 src-page-dir-ptr-table-entry-addr))
     ((mv & src-page-dir-ptr-paddrs x86)
      (las-to-pas src-page-dir-ptr-laddrs :r (cpl x86) x86))

     (dst-pml4-table-entry-addr
      (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86)))
     (dst-pml4-laddrs (create-canonical-address-list 8 dst-pml4-table-entry-addr))
     ((mv & dst-pml4-paddrs x86)
      (las-to-pas dst-pml4-laddrs :r (cpl x86) x86))

     ((mv & dst-page-dir-ptr-table-base-addr x86)
      (page-dir-ptr-table-base-addr (xr :rgf *rsi* x86) x86))
     (dst-page-dir-ptr-table-entry-addr
      (page-dir-ptr-table-entry-addr (xr :rgf *rsi* x86) dst-page-dir-ptr-table-base-addr))
     (dst-page-dir-ptr-laddrs (create-canonical-address-list 8 dst-page-dir-ptr-table-entry-addr))
     ((mv & dst-page-dir-ptr-paddrs x86)
      (las-to-pas dst-page-dir-ptr-laddrs :r (cpl x86) x86)))


  (if
      (and

       ;; Direct map for paging structures, specifically
       ;; destination and source PML4E and PDPTE.
       ;; (equal (mv-nth 1 (las-to-pas
       ;;                   (create-canonical-address-list
       ;;                    8
       ;;                    (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86)))
       ;;                   :r (cpl x86) x86))
       ;;        (addr-range
       ;;         8
       ;;         (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86))))
       (equal src-pml4-paddrs (addr-range 8 src-pml4-table-entry-addr))

       ;; (equal (mv-nth 1 (las-to-pas
       ;;                   (create-canonical-address-list
       ;;                    8
       ;;                    (page-dir-ptr-table-entry-addr
       ;;                     (xr :rgf *rdi* x86)
       ;;                     (page-dir-ptr-table-base-addr (xr :rgf *rdi* x86) x86)))
       ;;                   :r 0 x86))
       ;;        (addr-range
       ;;         8
       ;;         (page-dir-ptr-table-entry-addr
       ;;          (xr :rgf *rdi* x86)
       ;;          (page-dir-ptr-table-base-addr (xr :rgf *rdi* x86) x86))))
       (equal src-page-dir-ptr-paddrs (addr-range 8 src-page-dir-ptr-table-entry-addr))

       ;; (equal (mv-nth 1 (las-to-pas
       ;;                   (create-canonical-address-list
       ;;                    8
       ;;                    (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86)))
       ;;                   :r (cpl x86) x86))
       ;;        (addr-range
       ;;         8
       ;;         (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86))))
       (equal dst-pml4-paddrs (addr-range 8 dst-pml4-table-entry-addr))

       ;; (equal (mv-nth 1 (las-to-pas
       ;;                   (create-canonical-address-list
       ;;                    8
       ;;                    (page-dir-ptr-table-entry-addr
       ;;                     (xr :rgf *rsi* x86)
       ;;                     (page-dir-ptr-table-base-addr (xr :rgf *rsi* x86) x86)))
       ;;                   :r 0 x86))
       ;;        (addr-range
       ;;         8
       ;;         (page-dir-ptr-table-entry-addr
       ;;          (xr :rgf *rsi* x86)
       ;;          (page-dir-ptr-table-base-addr (xr :rgf *rsi* x86) x86))))
       (equal dst-page-dir-ptr-paddrs (addr-range 8 dst-page-dir-ptr-table-entry-addr))

       ;; ======================================================================

       ;; TO-DO: Check these preconditions. Also, change
       ;; rm-low-64 to rb. We have a direct map after all.

       ;; The destination PML4E and PDPTE are disjoint.
       ;; (disjoint-p
       ;;  (addr-range 8 (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86)))
       ;;  (addr-range 8 (page-dir-ptr-table-entry-addr
       ;;                 (xr :rgf *rsi* x86)
       ;;                 (page-dir-ptr-table-base-addr (xr :rgf *rsi* x86) x86))))
       (disjoint-p
        (addr-range 8 dst-pml4-table-entry-addr)
        (addr-range 8 src-page-dir-ptr-table-entry-addr)))

      (mv :PASSED x86)

    (mv :FAILED x86)))

;; @@@ Tests for 1G regions: It's difficult to compare 1G regions, so
;; until I figure out how to do that, I'll just compare a quadword.

;; The source physical addresses are disjoint from the the
;; physical addresses of the destination PDPTE.
;; (disjoint-p
;;  (addr-range *2^30*
;;              (ash (loghead 22 (logtail 30
;;                                        (rm-low-64
;;                                         (page-dir-ptr-table-entry-addr
;;                                          (xr :rgf *rdi* x86)
;;                                          (page-dir-ptr-table-base-addr (xr :rgf *rdi* x86) x86))
;;                                         x86)))
;;                   30))
;;  (addr-range 8
;;              (page-dir-ptr-table-entry-addr
;;               (xr :rgf *rsi* x86)
;;               (page-dir-ptr-table-base-addr (xr :rgf *rsi* x86) x86))))
(b*
    (((mv & src-page-dir-ptr-table-base-addr x86)
      (page-dir-ptr-table-base-addr (xr :rgf *rdi* x86) x86))
     (src-page-dir-ptr-table-entry-addr
      (page-dir-ptr-table-entry-addr (xr :rgf *rdi* x86) src-page-dir-ptr-table-base-addr))

     ((mv & dst-page-dir-ptr-table-base-addr x86)
      (page-dir-ptr-table-base-addr (xr :rgf *rsi* x86) x86))
     (dst-page-dir-ptr-table-entry-addr
      (page-dir-ptr-table-entry-addr (xr :rgf *rsi* x86) dst-page-dir-ptr-table-base-addr)))

  (if
      (disjoint-p
       (addr-range 8 ;; @@@ This really ought to be *2^30*.
                   (ash (loghead 22 (logtail 30 (rm-low-64 dst-page-dir-ptr-table-entry-addr x86)))
                        30))
       (addr-range 8 ;; This is fine; it should be 8.
                   src-page-dir-ptr-table-entry-addr))
      (mv :PASSED x86)
    (mv :FAILED x86)))


;; The translation-governing addresses of the destination
;; are disjoint from the physical addresses corresponding
;; to the stack.
;; (disjoint-p
;;  (all-xlation-governing-entries-paddrs
;;   (create-canonical-address-list *2^30* (xr :rgf *rsi* x86)) x86)
;;  (mv-nth 1 (las-to-pas
;;             (create-canonical-address-list
;;              8 (+ -24 (xr :rgf *rsp* x86))) :w (cpl x86) x86)))
(b*
    ((stack-laddrs (create-canonical-address-list 8 (+ -24 (xr :rgf *rsp* x86))))
     ((mv & stack-paddrs-from-write x86)
      (las-to-pas stack-laddrs :w (cpl x86) x86)))
  (if (disjoint-p
       (all-xlation-governing-entries-paddrs
        (create-canonical-address-list
         8 ;; @@@ This really ought to be *2^30*.
         (xr :rgf *rsi* x86)) x86)
       stack-paddrs-from-write)
      (mv :PASSED x86)
    (mv :FAILED x86)))


;; No errors encountered while translating the destination
;; linear addresses.
;; (not
;;  (mv-nth 0
;;          (las-to-pas (create-canonical-address-list
;;                       *2^30* (xr :rgf *rsi* x86))
;;                      :r (cpl x86) x86)))
(b* (((mv flg & x86)
      (las-to-pas (create-canonical-address-list
                   8 ;;; @@@ This really ought to be *2^30*.
                   (xr :rgf *rsi* x86))
                  :r (cpl x86) x86)))
  (mv (if flg :FAILED :PASSED) x86))

;; The source addresses are disjoint from the physical
;; addresses corresponding to the stack.
;; (disjoint-p
;;  (addr-range
;;   *2^30*
;;   (ash
;;    (loghead
;;     22
;;     (logtail
;;      30
;;      (rm-low-64 (page-dir-ptr-table-entry-addr
;;                  (xr :rgf *rdi* x86)
;;                  (page-dir-ptr-table-base-addr (xr :rgf *rdi* x86) x86))
;;                 x86)))
;;    30))
;;  (mv-nth
;;   1
;;   (las-to-pas (create-canonical-address-list
;;                8 (+ -24 (xr :rgf *rsp* x86)))
;;               :w (cpl x86) x86)))
(b* (((mv & src-page-dir-ptr-table-base-addr x86)
      (page-dir-ptr-table-base-addr (xr :rgf *rdi* x86) x86))
     (src-page-dir-ptr-table-entry-addr
      (page-dir-ptr-table-entry-addr (xr :rgf *rdi* x86) src-page-dir-ptr-table-base-addr))
     (stack-laddrs (create-canonical-address-list 8 (+ -24 (xr :rgf *rsp* x86))))
     ((mv & stack-paddrs-from-write x86)
      (las-to-pas stack-laddrs :w (cpl x86) x86)))
  (if (disjoint-p
       (addr-range
        8 ;; @@@ This really ought to be *2^30*.
        (ash (loghead 22 (logtail 30 (rm-low-64 src-page-dir-ptr-table-entry-addr x86))) 30))
       stack-paddrs-from-write)
      (mv :PASSED x86)
    (mv :FAILED x86)))

;; No errors encountered while translating the source
;; linear addresses.
;; (not
;;  (mv-nth 0
;;          (las-to-pas (create-canonical-address-list
;;                       *2^30* (xr :rgf *rdi* x86))
;;                      :r (cpl x86) x86)))
(b* (((mv flg & x86)
      (las-to-pas (create-canonical-address-list
                   8 ;; @@@ This really ought to be *2^30*.
                   (xr :rgf *rdi* x86))
                  :r (cpl x86) x86)))
  (mv (if flg :FAILED :PASSED) x86))
