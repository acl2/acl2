;; Author: Shilpi Goel <shigoel@cs.utexas.edu>

;; Simulation of a program that illustrates zero-copy --- the
;; destination linear address is mapped to the same physical address
;; as the source linear address.

(in-package "X86ISA")

(include-book "../../top" :ttags :all)
(include-book "modifyPagingEntry-addr-byte" :ttags :all)

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
 #x4008e4
 ;; Halt Address --- overwrites this address by #xF4 (HLT)
 #x40091c
 ;; Initial values of General-Purpose Registers
 '((#.*RSP* . #x7FFF5FBFF488))
 ;; Control Registers
 nil
 ;; Model-Specific Registers
 nil
 ;; Rflags Register
 #x2
 ;; Memory image
 *modifyPagingEntry*
 ;; x86 state
 x86)

;; A simple sanity check (should use rm08 here but memi works because
;; of the direct map from LA to PA):
(assert-event (equal (memi #x4007d2 x86) #x48))

;; part-select:
(x86-break '(equal (rip x86) #x4004ed))
;; part-install:
(x86-break '(equal (rip x86) #x400544))
;; pml4e_paddr:
(x86-break '(equal (rip x86) #x4005b7))
;; pdpte_paddr:
(x86-break '(equal (rip x86) #x40060b))
;; paddr:
(x86-break '(equal (rip x86) #x40068f))
;; rewire_dst_to_src:
(x86-break '(equal (rip x86) #x4007ce))
;; Return from rewire_dst_to_src:
(x86-break '(equal (rip x86) #x4008e3))

(!log-file-name "modifyPagingEntry.log")
;; Record the x86 state at a breakpoint in the log file above and then continue:
(x86-debug!)

;; If *rax* == 1, Success (la == pa).
(rgfi *rax* x86)

;; ======================================================================
