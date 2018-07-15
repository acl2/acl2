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

(in-package "X86ISA")

(include-book "sys-view/marking-view-top" :dir :proof-utils)
(include-book "zeroCopy-part-1")
(include-book "zeroCopy-part-2")
(include-book "read-page-after-write-to-page-table")

(include-book "centaur/bitops/ihs-extensions" :dir :system)
(include-book "centaur/bitops/signed-byte-p" :dir :system)
(include-book "arithmetic/top-with-meta" :dir :system)
(include-book "centaur/gl/gl" :dir :system)

;; ======================================================================

(local
 (in-theory
  ;; For the effects theorems:
  (e/d* (instruction-decoding-and-spec-rules
         shr-spec
         shr-spec-64
         sal/shl-spec
         sal/shl-spec-64
         gpr-and-spec-1
         gpr-and-spec-4
         gpr-and-spec-8
         gpr-sub-spec-8
         gpr-or-spec-8
         gpr-xor-spec-4
         jcc/cmovcc/setcc-spec
         top-level-opcode-execute
         two-byte-opcode-decode-and-execute
         x86-operand-from-modr/m-and-sib-bytes
         x86-operand-from-modr/m-and-sib-bytes$
         x86-effective-addr
         x86-effective-addr-from-sib
         x86-operand-to-reg/mem
         x86-operand-to-reg/mem$
         rr08 rr32 rr64 wr08 wr32 wr64
         rme-size wme-size
         rime-size wime-size
         riml08 riml32 riml64
         !flgi-undefined
         write-user-rflags

         pos
         mv-nth-0-las-to-pas-subset-p
         member-p
         subset-p

         rb-alt-wb-equal-in-sys-view)

        (rewire_dst_to_src-disable
         rewire_dst_to_src-disable-more))))

;; Argh, ACL2's default ancestors-check is killing me --- it prevents
;; x86-fetch-decode-execute from opening up (because the first hyp of
;; get-prefixes-alt-opener-lemma-no-prefix-byte is judged more
;; complicated than its ancestors --- why?). So I'm going to use Sol's
;; trivial ancestors-check version.
(local (include-book "tools/trivial-ancestors-check" :dir :system))
(local (acl2::use-trivial-ancestors-check))

(defthmd rewrite-to-pml4-table-entry-addr
  (implies
   (and (x86-state-okp x86)
        (source-addresses-ok-p x86)
        (destination-addresses-ok-p x86))

   (and
    (equal
     (logior (logand -4096 (logext 64 (xr :ctr *cr3* x86)))
             (logand 4088
                     (loghead 28 (logtail 36 (xr :rgf *rdi* x86)))))
     (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86)))
    (equal
     (logior (logand -4096 (logext 64 (xr :ctr *cr3* x86)))
             (logand 4088
                     (loghead 28 (logtail 36 (xr :rgf *rsi* x86)))))
     (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86))))))

(defthmd rewrite-to-page-dir-ptr-table-entry-addr
  (implies
   (and (x86-state-okp x86)
        (source-addresses-ok-p x86)
        (source-pml4te-ok-p x86)
        (destination-addresses-ok-p x86)
        (destination-pml4te-ok-p x86))
   (and
    (equal
     (logior
      (logand 4088
              (loghead 32 (logtail 27 (xr :rgf *rdi* x86))))
      (ash
       (loghead
        40
        (logtail
         12
         (mv-nth
          1
          (rb
           8
           (logior
            (logand -4096 (logext 64 (xr :ctr *cr3* x86)))
            (logand 4088
                    (loghead 28 (logtail 36 (xr :rgf *rdi* x86)))))
           :r x86))))
       12))
     (page-dir-ptr-table-entry-addr
      (xr :rgf *rdi* x86)
      (pdpt-base-addr (xr :rgf *rdi* x86) x86)))
    (equal
     (logior
      (logand 4088
              (loghead 32 (logtail 27 (xr :rgf *rsi* x86))))
      (ash
       (loghead
        40
        (logtail
         12
         (mv-nth
          1
          (rb
           8
           (logior
            (logand -4096 (logext 64 (xr :ctr *cr3* x86)))
            (logand 4088
                    (loghead 28 (logtail 36 (xr :rgf *rsi* x86)))))
           :r x86))))
       12))
     (page-dir-ptr-table-entry-addr
      (xr :rgf *rsi* x86)
      (pdpt-base-addr (xr :rgf *rsi* x86) x86))))))

(defun-nx rewire_dst_to_src-effects-preconditions (x86)
  (and
   (x86-state-okp x86)
   (program-ok-p x86)
   (stack-ok-p x86)
   (program-and-stack-no-interfere-p x86)
   (source-addresses-ok-p x86)
   (source-PML4TE-ok-p x86)
   (source-PDPTE-ok-p x86)
   (source-PML4TE-and-stack-no-interfere-p x86)
   (source-PML4TE-and-program-no-interfere-p x86)
   (source-PDPTE-and-stack-no-interfere-p x86)
   (source-PDPTE-and-program-no-interfere-p x86)
   (source-PDPTE-and-source-PML4E-no-interfere-p x86)
   (destination-addresses-ok-p x86)
   (destination-PML4TE-ok-p x86)
   (destination-PDPTE-ok-p x86)
   (destination-PML4TE-and-stack-no-interfere-p x86)
   (destination-PML4TE-and-program-no-interfere-p x86)
   (destination-PML4TE-and-source-PML4TE-no-interfere-p x86)
   (destination-PML4TE-and-source-PDPTE-no-interfere-p x86)
   (destination-PDPTE-and-source-PML4E-no-interfere-p x86)
   (destination-PDPTE-and-source-PDPTE-no-interfere-p x86)
   (destination-PDPTE-and-destination-PML4TE-no-interfere-p x86)
   (destination-PDPTE-and-stack-no-interfere-p x86)
   (destination-PDPTE-and-program-no-interfere-p x86)
   (return-address-ok-p x86)
   (stack-containing-return-address-ok-p x86)
   (stack-containing-return-address-and-program-no-interfere-p x86)
   (stack-containing-return-address-and-source-PML4E-no-interfere-p x86)
   (stack-containing-return-address-and-source-PDPTE-no-interfere-p x86)
   (stack-containing-return-address-and-destination-PML4E-no-interfere-p x86)
   (stack-containing-return-address-and-destination-PDPTE-no-interfere-p x86)
   (stack-containing-return-address-and-rest-of-the-stack-no-interfere-p x86)

   (direct-map-p
    8
    (page-dir-ptr-table-entry-addr
     (xr :rgf *rsi* x86)
     (pdpt-base-addr (xr :rgf *rsi* x86) x86))
    :w x86)))

(def-ruleset rewire_dst_to_src-effects-preconditions-defs
  '(x86-state-okp
    program-ok-p
    stack-ok-p
    program-and-stack-no-interfere-p
    source-addresses-ok-p
    source-pml4te-ok-p source-pdpte-ok-p
    source-pml4te-and-stack-no-interfere-p
    source-pml4te-and-program-no-interfere-p
    source-pdpte-and-stack-no-interfere-p
    source-pdpte-and-program-no-interfere-p
    source-pdpte-and-source-pml4e-no-interfere-p
    destination-addresses-ok-p
    destination-pml4te-ok-p
    destination-pdpte-ok-p
    destination-pml4te-and-stack-no-interfere-p
    destination-pml4te-and-program-no-interfere-p
    destination-pml4te-and-source-pml4te-no-interfere-p
    destination-pml4te-and-source-pdpte-no-interfere-p
    destination-pdpte-and-source-pml4e-no-interfere-p
    destination-pdpte-and-source-pdpte-no-interfere-p
    destination-pdpte-and-destination-pml4te-no-interfere-p
    destination-pdpte-and-stack-no-interfere-p
    destination-pdpte-and-program-no-interfere-p
    return-address-ok-p
    stack-containing-return-address-ok-p
    stack-containing-return-address-and-program-no-interfere-p
    stack-containing-return-address-and-source-pml4e-no-interfere-p
    stack-containing-return-address-and-source-pdpte-no-interfere-p
    stack-containing-return-address-and-destination-pml4e-no-interfere-p
    stack-containing-return-address-and-destination-pdpte-no-interfere-p
    stack-containing-return-address-and-rest-of-the-stack-no-interfere-p))

;; ----------------------------------------------------------------------

;; Some more preconditions:

(defun-nx more-stack-containing-return-address-and-source-PML4E-no-interfere-p (x86)
  ;; Physical addresses corresponding to source PML4TE are disjoint
  ;; from the translation-governing addresses of the stack containing
  ;; the return address.
  (disjoint-p
   (mv-nth 1 (las-to-pas
              8
              (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86))
              :r x86))
   (all-xlation-governing-entries-paddrs
    8 (xr :rgf *rsp* x86) x86)))

(defun-nx more-destination-PDPTE-and-source-PML4E-no-interfere-p (x86)
  (and
   (disjoint-p
    (mv-nth 1 (las-to-pas
               8
               (page-dir-ptr-table-entry-addr
                (xr :rgf *rsi* x86)
                (pdpt-base-addr (xr :rgf *rsi* x86) x86))
               :w x86))
    (mv-nth 1 (las-to-pas
               8
               (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86))
               :r x86)))
   (disjoint-p
    (mv-nth 1 (las-to-pas
               8
               (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86))
               :r  x86))
    (all-xlation-governing-entries-paddrs
     8
     (page-dir-ptr-table-entry-addr
      (xr :rgf *rsi* x86)
      (pdpt-base-addr (xr :rgf *rsi* x86) x86))
     x86))))

(defun-nx more-destination-PML4TE-and-source-PML4TE-no-interfere-p (x86)
  (disjoint-p
   (mv-nth
    1
    (las-to-pas 8
                (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86))
                :r  x86))
   (all-xlation-governing-entries-paddrs
    8
    (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86))
    x86)))

(defun-nx more-source-PDPTE-and-source-PML4E-no-interfere-p (x86)
  (disjoint-p
   (mv-nth 1 (las-to-pas
              8
              (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86))
              :r  x86))
   (all-xlation-governing-entries-paddrs
    8
    (page-dir-ptr-table-entry-addr
     (xr :rgf *rdi* x86)
     (pdpt-base-addr (xr :rgf *rdi* x86) x86))
    x86)))

(defun-nx more-stack-containing-return-address-and-destination-PML4E-no-interfere-p (x86)
  (disjoint-p
   (mv-nth
    1
    (las-to-pas
     8
     (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86))
     :r  x86))
   (all-xlation-governing-entries-paddrs
    8 (xr :rgf *rsp* x86)
    x86)))

(defun-nx more-destination-PDPTE-and-destination-PML4TE-no-interfere-p (x86)
  (and
   (disjoint-p
    (mv-nth
     1
     (las-to-pas
      8
      (page-dir-ptr-table-entry-addr
       (xr :rgf *rsi* x86)
       (pdpt-base-addr (xr :rgf *rsi* x86) x86))
      :w  x86))
    (mv-nth
     1
     (las-to-pas
      8
      (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86))
      :r  x86)))
   (disjoint-p
    (mv-nth
     1
     (las-to-pas
      8
      (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86))
      :r  x86))
    (all-xlation-governing-entries-paddrs
     8
     (page-dir-ptr-table-entry-addr
      (xr :rgf *rsi* x86)
      (pdpt-base-addr (xr :rgf *rsi* x86) x86))
     x86))))


(defun-nx throwaway-hyps-for-source-entries-from-final-state (x86)
  (and
   ;; From source-pml4te-ok-p:
   (disjoint-p
    (mv-nth 1 (las-to-pas
               8
               (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86))
               :r  x86))
    (all-xlation-governing-entries-paddrs
     8
     (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86))
     x86))

   ;; Derived from destination-PDPTE-and-source-PML4E-no-interfere-p.
   (disjoint-p
    (mv-nth 1 (las-to-pas
               8
               (page-dir-ptr-table-entry-addr
                (xr :rgf *rsi* x86)
                (pdpt-base-addr (xr :rgf *rsi* x86) x86))
               :w  x86))
    (all-xlation-governing-entries-paddrs
     8
     (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86))
     x86))

   ;; Derived from source-PML4TE-and-stack-no-interfere-p:
   (disjoint-p
    (mv-nth 1 (las-to-pas
               8 (+ -24 (xr :rgf *rsp* x86)) :w  x86))
    (mv-nth 1 (las-to-pas
               8
               (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86))
               :r  x86)))))

(defun-nx throwaway-hyps-for-destination-entries-from-final-state (x86)
  (and
   ;; disjoint-p$ issue:
   ;; Derived from destination-PML4TE-and-source-PDPTE-no-interfere-p:
   (disjoint-p
    (mv-nth
     1
     (las-to-pas
      8
      (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86))
      :r  x86))
    (all-xlation-governing-entries-paddrs
     8
     (page-dir-ptr-table-entry-addr
      (xr :rgf *rdi* x86)
      (pdpt-base-addr (xr :rgf *rdi* x86) x86))
     x86))

   ;; disjoint-p$ issue:
   ;; Derived from destination-PML4TE-and-source-PML4TE-no-interfere-p:
   (disjoint-p
    (mv-nth
     1
     (las-to-pas
      8
      (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86))
      :r  x86))
    (all-xlation-governing-entries-paddrs
     8
     (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86))
     x86))

   ;; disjoint-p$ issue:
   ;; Derived from destination-PML4TE-and-stack-no-interfere-p:
   (disjoint-p
    (mv-nth
     1
     (las-to-pas
      8 (+ -24 (xr :rgf *rsp* x86))
      :w  x86))
    (mv-nth
     1
     (las-to-pas
      8
      (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86))
      :r  x86)))

   ;; disjoint-p$ issue:
   ;; Derived from destination-PML4TE-ok-p:
   (disjoint-p
    (mv-nth
     1
     (las-to-pas 8
                 (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86))
                 :r  x86))
    (all-xlation-governing-entries-paddrs
     8
     (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86))
     x86))

   ;; disjoint-p$ issue:
   ;; Derived from destination-PDPTE-and-destination-PML4TE-no-interfere-p:
   (disjoint-p
    (mv-nth
     1
     (las-to-pas
      8
      (page-dir-ptr-table-entry-addr (xr :rgf *rsi* x86)
                                     (pdpt-base-addr (xr :rgf *rsi* x86) x86))
      :w  x86))
    (all-xlation-governing-entries-paddrs
     8
     (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86))
     x86))))

(defun-nx source-data-preconditions (x86)
  (and
   ;; The physical addresses corresponding to destination
   ;; PDPTE are disjoint from the translation-governing
   ;; addresses of the source linear addresses.  Note
   ;; that this means that the destination PDPTE can't
   ;; serve as the PML4TE or PDPTE of the source.
   (disjoint-p
    (mv-nth
     1
     (las-to-pas
      8
      (page-dir-ptr-table-entry-addr
       (xr :rgf *rsi* x86)
       (pdpt-base-addr (xr :rgf *rsi* x86) x86))
      :w  x86))
    (all-xlation-governing-entries-paddrs *2^30* (xr :rgf *rdi* x86) x86))

   ;; The physical addresses corresponding to destination
   ;; PDPTE are disjoint from the source physical
   ;; addresses.
   (disjoint-p
    (mv-nth
     1
     (las-to-pas
      8
      (page-dir-ptr-table-entry-addr
       (xr :rgf *rsi* x86)
       (pdpt-base-addr (xr :rgf *rsi* x86) x86))
      :w  x86))
    (mv-nth 1 (las-to-pas *2^30* (xr :rgf *rdi* x86) :r  x86)))

   ;; The stack is disjoint from the source physical
   ;; addresses.
   (disjoint-p
    (mv-nth 1 (las-to-pas 8 (+ -24 (xr :rgf *rsp* x86)) :w  x86))
    (mv-nth 1 (las-to-pas *2^30* (xr :rgf *rdi* x86) :r  x86)))
   ;; Source physical addresses are disjoint from the paging
   ;; structures' physical addresses.
   (disjoint-p$
    (mv-nth 1 (las-to-pas *2^30* (xr :rgf *rdi* x86) :r  x86))
    (open-qword-paddr-list
     (gather-all-paging-structure-qword-addresses x86)))
   ;; The source PDPTE physical addresses are disjoint from
   ;; the source PML4TE physical addresses.
   (disjoint-p$
    (mv-nth 1
            (las-to-pas 8
                        (page-dir-ptr-table-entry-addr
                         (xr :rgf *rdi* x86)
                         (pdpt-base-addr (xr :rgf *rdi* x86) x86))
                        :r x86))
    (mv-nth
     1
     (las-to-pas
      8
      (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86))
      :r x86)))
   ;; Source PML4TE is direct-mapped.
   (direct-map-p
    8 (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86))
    :r x86)
   ;; Source PDPTE is direct-mapped.
   (direct-map-p
    8 (page-dir-ptr-table-entry-addr
       (xr :rgf *rdi* x86) (pdpt-base-addr (xr :rgf *rdi* x86) x86))
    :r x86)))

(defun-nx destination-data-preconditions (x86)
  (and
   ;; Source PML4TE is direct-mapped.
   (direct-map-p
    8
    (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86))
    :r  x86)
   ;; Source PDPTE is direct-mapped.
   (direct-map-p
    8
    (page-dir-ptr-table-entry-addr (xr :rgf *rdi* x86)
                                   (pdpt-base-addr (xr :rgf *rdi* x86) x86))
    :r x86)
   ;; Destination PML4TE is direct-mapped.
   (direct-map-p
    8
    (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86))
    :r  x86)

   ;; The destination PML4TE physical addresses are disjoint from the
   ;; translation-governing addresses of the destination PDPTE.
   (disjoint-p
    (mv-nth
     1
     (las-to-pas
      8
      (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86))
      :r  x86))
    (all-xlation-governing-entries-paddrs
     8
     (page-dir-ptr-table-entry-addr (xr :rgf *rsi* x86)
                                    (pdpt-base-addr (xr :rgf *rsi* x86) x86))
     x86))
   ;; Destination PDPTE physical addresses are disjoint from the
   ;; destination PML4TE physical addresses.
   (disjoint-p$
    (mv-nth
     1
     (las-to-pas 8
                 (page-dir-ptr-table-entry-addr
                  (xr :rgf *rsi* x86)
                  (pdpt-base-addr (xr :rgf *rsi* x86) x86))
                 :w  x86))
    (mv-nth
     1
     (las-to-pas
      8
      (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86))
      :r  x86)))


   ;; The source physical addresses are disjoint from the stack physical addresses.
   (disjoint-p
    (addr-range
     *2^30*
     (ash (loghead 22
                   (logtail 30
                            (rm-low-64 (page-dir-ptr-table-entry-addr
                                        (xr :rgf *rdi* x86)
                                        (pdpt-base-addr (xr :rgf *rdi* x86) x86)) x86)))
          30))
    (mv-nth 1 (las-to-pas 8 (+ -24 (xr :rgf *rsp* x86)) :w  x86)))

   ;; The source physical addresses are disjoint from all the paging
   ;; structure physical addresses.
   (disjoint-p$
    (addr-range
     *2^30*
     (ash (loghead 22
                   (logtail
                    30
                    (rm-low-64 (page-dir-ptr-table-entry-addr
                                (xr :rgf *rdi* x86)
                                (pdpt-base-addr (xr :rgf *rdi* x86) x86)) x86)))
          30))
    (open-qword-paddr-list (gather-all-paging-structure-qword-addresses x86)))))

(defun-nx throwaway-destination-data-preconditions (x86)
  (and
   ;; This should follow from the hyp about direct map of destination
   ;; PDPTE, and that the source physical addresses are disjoint from
   ;; all the paging structure physical addresses.
   (disjoint-p
    (addr-range
     *2^30*
     (ash (loghead 22
                   (logtail
                    30
                    (rm-low-64 (page-dir-ptr-table-entry-addr
                                (xr :rgf *rdi* x86)
                                (pdpt-base-addr (xr :rgf *rdi* x86) x86)) x86)))
          30))
    (addr-range
     8 (page-dir-ptr-table-entry-addr
        (xr :rgf *rsi* x86)
        (pdpt-base-addr (xr :rgf *rsi* x86) x86))))

   ;; This should follow from
   ;; destination-PDPTE-and-destination-PML4TE-no-interfere-p
   ;; (disjoint-p$ issue) and direct map of destination PDPTE.
   (disjoint-p
    (addr-range 8
                (page-dir-ptr-table-entry-addr
                 (xr :rgf *rsi* x86)
                 (pdpt-base-addr (xr :rgf *rsi* x86) x86)))
    (all-xlation-governing-entries-paddrs
     8
     (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86)) x86))

   ;; This should follow from
   ;; destination-PDPTE-and-source-PML4E-no-interfere-p (disjoint-p$
   ;; issue) and direct map of destination PDPTE.
   (disjoint-p
    (addr-range 8
                (page-dir-ptr-table-entry-addr
                 (xr :rgf *rsi* x86)
                 (pdpt-base-addr (xr :rgf *rsi* x86) x86)))
    (all-xlation-governing-entries-paddrs
     8 (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86)) x86))

   ;; This should follow from
   ;; destination-PDPTE-and-source-PDPTE-no-interfere-p (disjoint-p$
   ;; issue) and direct map of destination PDPTE.
   (disjoint-p
    (addr-range 8
                (page-dir-ptr-table-entry-addr
                 (xr :rgf *rsi* x86)
                 (pdpt-base-addr (xr :rgf *rsi* x86) x86)))
    (all-xlation-governing-entries-paddrs
     8
     (page-dir-ptr-table-entry-addr
      (xr :rgf *rdi* x86)
      (pdpt-base-addr (xr :rgf *rdi* x86) x86))
     x86))

   ;; disjoint-p$ issue
   ;; Follows from destination-PML4TE-ok-p.
   (disjoint-p
    (mv-nth
     1
     (las-to-pas
      8
      (pml4-table-entry-addr (xr :rgf *rsi* x86)
                             (pml4-table-base-addr x86))
      :r  x86))
    (all-xlation-governing-entries-paddrs
     8
     (pml4-table-entry-addr (xr :rgf *rsi* x86)
                            (pml4-table-base-addr x86))
     x86))

   ;; disjoint-p$ issue
   ;; Follows from destination-PML4TE-and-source-PDPTE-no-interfere-p.
   (disjoint-p
    (mv-nth
     1
     (las-to-pas
      8
      (pml4-table-entry-addr (xr :rgf *rsi* x86)
                             (pml4-table-base-addr x86))
      :r  x86))
    (all-xlation-governing-entries-paddrs
     8
     (page-dir-ptr-table-entry-addr
      (xr :rgf *rdi* x86)
      (pdpt-base-addr (xr :rgf *rdi* x86) x86))
     x86))

   ;; disjoint-p$ issue
   ;; Follows from destination-PML4TE-and-source-PML4TE-no-interfere-p.
   (disjoint-p
    (mv-nth
     1
     (las-to-pas
      8
      (pml4-table-entry-addr (xr :rgf *rsi* x86)
                             (pml4-table-base-addr x86))
      :r  x86))
    (all-xlation-governing-entries-paddrs
     8
     (pml4-table-entry-addr (xr :rgf *rdi* x86)
                            (pml4-table-base-addr x86))
     x86))


   ;; disjoint-p$ issue
   ;; Follows from destination-PML4TE-and-stack-no-interfere-p.
   (disjoint-p
    (mv-nth
     1
     (las-to-pas
      8 (+ -24 (xr :rgf *rsp* x86)) :w  x86))
    (mv-nth 1
            (las-to-pas
             8 (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86))
             :r  x86)))

   ;; disjoint-p$ issue
   ;; Follows from destination-PDPTE-and-stack-no-interfere-p.
   (disjoint-p
    (mv-nth 1 (las-to-pas 8 (+ -24 (xr :rgf *rsp* x86)) :w  x86))
    (mv-nth
     1
     (las-to-pas
      8
      (page-dir-ptr-table-entry-addr (xr :rgf *rsi* x86)
                                     (pdpt-base-addr (xr :rgf *rsi* x86) x86))
      :r  x86)))))

(defun-nx more-destination-data-preconditions (x86)
  (and
   (more-stack-containing-return-address-and-destination-pml4e-no-interfere-p x86)
   (more-destination-pdpte-and-destination-pml4te-no-interfere-p x86)
   (disjoint-p
    (mv-nth 1 (las-to-pas
               8 (+ -24 (xr :rgf *rsp* x86)) :w x86))
    (all-xlation-governing-entries-paddrs
     8
     (page-dir-ptr-table-entry-addr
      (xr :rgf *rsi* x86)
      (pdpt-base-addr (xr :rgf *rsi* x86) x86))
     x86))
   (disjoint-p
    (mv-nth
     1
     (las-to-pas
      8
      (page-dir-ptr-table-entry-addr
       (xr :rgf *rsi* x86)
       (pdpt-base-addr (xr :rgf *rsi* x86) x86))
      :w x86))
    (all-xlation-governing-entries-paddrs
     8
     (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86))
     x86))
   (direct-map-p 8
                 (page-dir-ptr-table-entry-addr
                  (xr :rgf *rsi* x86)
                  (pdpt-base-addr (xr :rgf *rsi* x86) x86))
                 :r x86)
   ;; From destination-PDPTE-and-program-no-interfere-p:
   (disjoint-p
    (mv-nth 1 (las-to-pas
               8
               (page-dir-ptr-table-entry-addr
                (xr :rgf *rsi* x86)
                (pdpt-base-addr (xr :rgf *rsi* x86) x86))
               :w x86))
    (all-xlation-governing-entries-paddrs
     *rewire_dst_to_src-len* (xr :rip 0 x86) x86))
   ;; From destination-PDPTE-ok-p:
   (disjoint-p
    (mv-nth 1 (las-to-pas
               8
               (page-dir-ptr-table-entry-addr
                (xr :rgf *rsi* x86)
                (pdpt-base-addr (xr :rgf *rsi* x86) x86))
               :r x86))
    (all-xlation-governing-entries-paddrs
     8
     (page-dir-ptr-table-entry-addr
      (xr :rgf *rsi* x86)
      (pdpt-base-addr (xr :rgf *rsi* x86) x86))
     x86))
   ;; From destination-PDPTE-and-stack-no-interfere-p:
   ;; (but commuted)
   (disjoint-p
    (mv-nth 1 (las-to-pas
               8
               (page-dir-ptr-table-entry-addr
                (xr :rgf *rsi* x86)
                (pdpt-base-addr (xr :rgf *rsi* x86) x86))
               :r x86))
    (mv-nth 1 (las-to-pas
               8 (+ -24 (xr :rgf *rsp* x86)) :w x86)))
   (direct-map-p 8
                 (page-dir-ptr-table-entry-addr
                  (xr :rgf *rsi* x86)
                  (pdpt-base-addr (xr :rgf *rsi* x86) x86))
                 :r x86)
   ;; From destination-PDPTE-and-program-no-interfere-p:
   (disjoint-p
    (mv-nth 1 (las-to-pas
               8
               (page-dir-ptr-table-entry-addr
                (xr :rgf *rsi* x86)
                (pdpt-base-addr (xr :rgf *rsi* x86) x86))
               :w x86))
    (all-xlation-governing-entries-paddrs
     *rewire_dst_to_src-len* (xr :rip 0 x86) x86))
   ;; From destination-PDPTE-ok-p:
   (disjoint-p
    (mv-nth 1 (las-to-pas
               8
               (page-dir-ptr-table-entry-addr
                (xr :rgf *rsi* x86)
                (pdpt-base-addr (xr :rgf *rsi* x86) x86))
               :r x86))
    (all-xlation-governing-entries-paddrs
     8
     (page-dir-ptr-table-entry-addr
      (xr :rgf *rsi* x86)
      (pdpt-base-addr (xr :rgf *rsi* x86) x86))
     x86))
   ;; From destination-PDPTE-and-stack-no-interfere-p:
   ;; (but commuted)
   (disjoint-p
    (mv-nth 1 (las-to-pas
               8
               (page-dir-ptr-table-entry-addr
                (xr :rgf *rsi* x86)
                (pdpt-base-addr (xr :rgf *rsi* x86) x86))
               :r x86))
    (mv-nth 1 (las-to-pas
               8 (+ -24 (xr :rgf *rsp* x86)) :w x86)))

   ;; !!

   (disjoint-p
    (addr-range
     *2^30*
     (ash (loghead 22
                   (logtail
                    30
                    (rm-low-64
                     (page-dir-ptr-table-entry-addr
                      (xr :rgf *rdi* x86)
                      (pdpt-base-addr (xr :rgf *rdi* x86) x86))
                     x86)))
          30))
    (all-xlation-governing-entries-paddrs
     8 (xr :rgf *rsp* x86) x86))
   (disjoint-p
    (addr-range
     *2^30*
     (ash (loghead 22
                   (logtail
                    30
                    (rm-low-64
                     (page-dir-ptr-table-entry-addr
                      (xr :rgf *rdi* x86)
                      (pdpt-base-addr (xr :rgf *rdi* x86) x86))
                     x86)))
          30))
    (all-xlation-governing-entries-paddrs
     *rewire_dst_to_src-len* (xr :rip 0 x86) x86))

   (disjoint-p
    (addr-range
     *2^30*
     (ash (loghead 22
                   (logtail
                    30
                    (rm-low-64
                     (page-dir-ptr-table-entry-addr
                      (xr :rgf *rdi* x86)
                      (pdpt-base-addr (xr :rgf *rdi* x86) x86))
                     x86)))
          30))
    (mv-nth 1 (las-to-pas
               8
               (page-dir-ptr-table-entry-addr
                (xr :rgf *rsi* x86)
                (pdpt-base-addr (xr :rgf *rsi* x86) x86))
               :r x86)))

   (disjoint-p
    (addr-range
     *2^30*
     (ash (loghead 22
                   (logtail
                    30
                    (rm-low-64
                     (page-dir-ptr-table-entry-addr
                      (xr :rgf *rdi* x86)
                      (pdpt-base-addr (xr :rgf *rdi* x86) x86))
                     x86)))
          30))
    (all-xlation-governing-entries-paddrs
     8
     (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86))
     x86))
   (disjoint-p
    (addr-range
     *2^30*
     (ash (loghead 22
                   (logtail
                    30
                    (rm-low-64
                     (page-dir-ptr-table-entry-addr
                      (xr :rgf *rdi* x86)
                      (pdpt-base-addr (xr :rgf *rdi* x86) x86))
                     x86)))
          30))
    (all-xlation-governing-entries-paddrs
     8
     (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86))
     x86))))

;; ----------------------------------------------------------------------

;; Defining a cumulative effects function:

(defun-nx zeroCopy-state (x86)
  (XW
   :RGF *RAX* 1
   (XW
    :RGF *RCX*
    (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
            (LOGAND 4088
                    (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
    (XW
     :RGF *RDX*
     (LOGAND
      4503598553628672
      (LOGIOR
       (LOGAND
        -4503598553628673
        (LOGEXT
         64
         (MV-NTH
          1
          (RB
           8
           (LOGIOR
            (LOGAND 4088
                    (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
            (ASH
             (LOGHEAD
              40
              (LOGTAIL
               12
               (MV-NTH
                1
                (RB
                 8
                 (LOGIOR
                  (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                  (LOGAND 4088
                          (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
                 :R X86))))
             12))
           :R X86))))
       (LOGAND
        4503598553628672
        (LOGEXT
         64
         (MV-NTH
          1
          (RB
           8
           (LOGIOR
            (LOGAND 4088
                    (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
            (ASH
             (LOGHEAD
              40
              (LOGTAIL
               12
               (MV-NTH
                1
                (RB
                 8
                 (LOGIOR
                  (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                  (LOGAND 4088
                          (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
                 :R X86))))
             12))
           :R X86))))))
     (XW
      :RGF *RSP* (+ 8 (XR :RGF *RSP* X86))
      (XW
       :RGF *RSI* 0
       (XW
        :RGF *RDI*
        (LOGAND
         4503598553628672
         (LOGEXT
          64
          (MV-NTH
           1
           (RB
            8
            (LOGIOR
             (LOGAND 4088
                     (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
             (ASH
              (LOGHEAD
               40
               (LOGTAIL
                12
                (MV-NTH
                 1
                 (RB
                  8
                  (LOGIOR
                   (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                   (LOGAND 4088
                           (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
                  :R X86))))
              12))
            :R X86))))
        (XW
         :RGF *R8* 1099511627775
         (XW
          :RGF *R9*
          (LOGAND
           4503598553628672
           (LOGEXT
            64
            (MV-NTH
             1
             (RB
              8
              (LOGIOR
               (LOGAND 4088
                       (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
               (ASH
                (LOGHEAD
                 40
                 (LOGTAIL
                  12
                  (MV-NTH
                   1
                   (RB
                    8
                    (LOGIOR
                     (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                     (LOGAND 4088
                             (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
                    :R X86))))
                12))
              :R X86))))
          (XW
           :RIP 0
           (LOGEXT 64
                   (MV-NTH 1 (RB 8 (XR :RGF *RSP* X86) :R X86)))
           (XW
            :UNDEF 0 (+ 46 (NFIX (XR :UNDEF 0 X86)))
            (!FLGI
             *CF*
             (BOOL->BIT
              (<
               (LOGAND
                4503598553628672
                (MV-NTH
                 1
                 (RB
                  8
                  (LOGIOR
                   (LOGAND 4088
                           (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
                   (ASH
                    (LOGHEAD
                     40
                     (LOGTAIL
                      12
                      (MV-NTH
                       1
                       (RB
                        8
                        (LOGIOR
                         (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                         (LOGAND
                          4088
                          (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
                        :R X86))))
                    12))
                  :R X86)))
               (LOGAND
                4503598553628672
                (LOGIOR
                 (LOGAND
                  18442240475155922943
                  (MV-NTH
                   1
                   (RB
                    8
                    (LOGIOR
                     (LOGAND 4088
                             (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
                     (ASH
                      (LOGHEAD
                       40
                       (LOGTAIL
                        12
                        (MV-NTH
                         1
                         (RB
                          8
                          (LOGIOR
                           (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                           (LOGAND
                            4088
                            (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
                          :R X86))))
                      12))
                    :R X86)))
                 (LOGAND
                  4503598553628672
                  (MV-NTH
                   1
                   (RB
                    8
                    (LOGIOR
                     (LOGAND 4088
                             (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
                     (ASH
                      (LOGHEAD
                       40
                       (LOGTAIL
                        12
                        (MV-NTH
                         1
                         (RB
                          8
                          (LOGIOR
                           (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                           (LOGAND
                            4088
                            (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
                          :R X86))))
                      12))
                    :R X86)))))))
             (!FLGI
              *PF*
              (PF-SPEC64
               (LOGHEAD
                64
                (+
                 (LOGAND
                  4503598553628672
                  (LOGEXT
                   64
                   (MV-NTH
                    1
                    (RB
                     8
                     (LOGIOR
                      (LOGAND 4088
                              (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
                      (ASH
                       (LOGHEAD
                        40
                        (LOGTAIL
                         12
                         (MV-NTH
                          1
                          (RB
                           8
                           (LOGIOR
                            (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                            (LOGAND
                             4088
                             (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
                           :R X86))))
                       12))
                     :R X86))))
                 (-
                  (LOGAND
                   4503598553628672
                   (LOGIOR
                    (LOGAND
                     -4503598553628673
                     (LOGEXT
                      64
                      (MV-NTH
                       1
                       (RB
                        8
                        (LOGIOR
                         (LOGAND
                          4088
                          (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
                         (ASH
                          (LOGHEAD
                           40
                           (LOGTAIL
                            12
                            (MV-NTH
                             1
                             (RB
                              8
                              (LOGIOR
                               (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                               (LOGAND
                                4088
                                (LOGHEAD
                                 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
                              :R X86))))
                          12))
                        :R X86))))
                    (LOGAND
                     4503598553628672
                     (LOGEXT
                      64
                      (MV-NTH
                       1
                       (RB
                        8
                        (LOGIOR
                         (LOGAND
                          4088
                          (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
                         (ASH
                          (LOGHEAD
                           40
                           (LOGTAIL
                            12
                            (MV-NTH
                             1
                             (RB
                              8
                              (LOGIOR
                               (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                               (LOGAND
                                4088
                                (LOGHEAD
                                 28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
                              :R X86))))
                          12))
                        :R X86))))))))))
              (!FLGI
               *AF*
               (SUB-AF-SPEC64
                (LOGAND
                 4503598553628672
                 (MV-NTH
                  1
                  (RB
                   8
                   (LOGIOR
                    (LOGAND 4088
                            (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
                    (ASH
                     (LOGHEAD
                      40
                      (LOGTAIL
                       12
                       (MV-NTH
                        1
                        (RB
                         8
                         (LOGIOR
                          (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                          (LOGAND
                           4088
                           (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
                         :R X86))))
                     12))
                   :R X86)))
                (LOGAND
                 4503598553628672
                 (LOGIOR
                  (LOGAND
                   18442240475155922943
                   (MV-NTH
                    1
                    (RB
                     8
                     (LOGIOR
                      (LOGAND 4088
                              (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
                      (ASH
                       (LOGHEAD
                        40
                        (LOGTAIL
                         12
                         (MV-NTH
                          1
                          (RB
                           8
                           (LOGIOR
                            (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                            (LOGAND
                             4088
                             (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
                           :R X86))))
                       12))
                     :R X86)))
                  (LOGAND
                   4503598553628672
                   (MV-NTH
                    1
                    (RB
                     8
                     (LOGIOR
                      (LOGAND 4088
                              (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
                      (ASH
                       (LOGHEAD
                        40
                        (LOGTAIL
                         12
                         (MV-NTH
                          1
                          (RB
                           8
                           (LOGIOR
                            (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                            (LOGAND
                             4088
                             (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
                           :R X86))))
                       12))
                     :R X86))))))
               (!FLGI
                *ZF* 1
                (!FLGI
                 *SF*
                 (SF-SPEC64
                  (LOGHEAD
                   64
                   (+
                    (LOGAND
                     4503598553628672
                     (LOGEXT
                      64
                      (MV-NTH
                       1
                       (RB
                        8
                        (LOGIOR
                         (LOGAND
                          4088
                          (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
                         (ASH
                          (LOGHEAD
                           40
                           (LOGTAIL
                            12
                            (MV-NTH
                             1
                             (RB
                              8
                              (LOGIOR
                               (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                               (LOGAND
                                4088
                                (LOGHEAD
                                 28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
                              :R X86))))
                          12))
                        :R X86))))
                    (-
                     (LOGAND
                      4503598553628672
                      (LOGIOR
                       (LOGAND
                        -4503598553628673
                        (LOGEXT
                         64
                         (MV-NTH
                          1
                          (RB
                           8
                           (LOGIOR
                            (LOGAND
                             4088
                             (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
                            (ASH
                             (LOGHEAD
                              40
                              (LOGTAIL
                               12
                               (MV-NTH
                                1
                                (RB
                                 8
                                 (LOGIOR
                                  (LOGAND
                                   -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                                  (LOGAND
                                   4088
                                   (LOGHEAD
                                    28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
                                 :R X86))))
                             12))
                           :R X86))))
                       (LOGAND
                        4503598553628672
                        (LOGEXT
                         64
                         (MV-NTH
                          1
                          (RB
                           8
                           (LOGIOR
                            (LOGAND
                             4088
                             (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
                            (ASH
                             (LOGHEAD
                              40
                              (LOGTAIL
                               12
                               (MV-NTH
                                1
                                (RB
                                 8
                                 (LOGIOR
                                  (LOGAND
                                   -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                                  (LOGAND
                                   4088
                                   (LOGHEAD
                                    28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
                                 :R X86))))
                             12))
                           :R X86))))))))))
                 (!FLGI
                  *OF*
                  (OF-SPEC64
                   (+
                    (LOGAND
                     4503598553628672
                     (LOGEXT
                      64
                      (MV-NTH
                       1
                       (RB
                        8
                        (LOGIOR
                         (LOGAND
                          4088
                          (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
                         (ASH
                          (LOGHEAD
                           40
                           (LOGTAIL
                            12
                            (MV-NTH
                             1
                             (RB
                              8
                              (LOGIOR
                               (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                               (LOGAND
                                4088
                                (LOGHEAD
                                 28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
                              :R X86))))
                          12))
                        :R X86))))
                    (-
                     (LOGAND
                      4503598553628672
                      (LOGIOR
                       (LOGAND
                        -4503598553628673
                        (LOGEXT
                         64
                         (MV-NTH
                          1
                          (RB
                           8
                           (LOGIOR
                            (LOGAND
                             4088
                             (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
                            (ASH
                             (LOGHEAD
                              40
                              (LOGTAIL
                               12
                               (MV-NTH
                                1
                                (RB
                                 8
                                 (LOGIOR
                                  (LOGAND
                                   -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                                  (LOGAND
                                   4088
                                   (LOGHEAD
                                    28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
                                 :R X86))))
                             12))
                           :R X86))))
                       (LOGAND
                        4503598553628672
                        (LOGEXT
                         64
                         (MV-NTH
                          1
                          (RB
                           8
                           (LOGIOR
                            (LOGAND
                             4088
                             (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
                            (ASH
                             (LOGHEAD
                              40
                              (LOGTAIL
                               12
                               (MV-NTH
                                1
                                (RB
                                 8
                                 (LOGIOR
                                  (LOGAND
                                   -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                                  (LOGAND
                                   4088
                                   (LOGHEAD
                                    28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
                                 :R X86))))
                             12))
                           :R X86)))))))))
                  (MV-NTH
                   2
                   (LAS-TO-PAS
                    8 (XR :RGF *RSP* X86)
                    :R
                    (MV-NTH
                     2
                     (LAS-TO-PAS
                      40 (+ 206 (XR :RIP 0 X86))
                      :X
                      (MV-NTH
                       2
                       (LAS-TO-PAS
                        15 (+ 190 (XR :RIP 0 X86))
                        :X
                        (MV-NTH
                         1
                         (WB
                          8
                          (LOGIOR
                           (LOGAND
                            4088
                            (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
                           (ASH
                            (LOGHEAD
                             40
                             (LOGTAIL
                              12
                              (MV-NTH
                               1
                               (RB
                                8
                                (LOGIOR
                                 (LOGAND
                                  -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                                 (LOGAND
                                  4088
                                  (LOGHEAD
                                   28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
                                :R X86))))
                            12))
                          :W
                          (LOGIOR
                           (LOGAND
                            18442240475155922943
                            (MV-NTH
                             1
                             (RB
                              8
                              (LOGIOR
                               (LOGAND
                                4088
                                (LOGHEAD
                                 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
                               (ASH
                                (LOGHEAD
                                 40
                                 (LOGTAIL
                                  12
                                  (MV-NTH
                                   1
                                   (RB
                                    8
                                    (LOGIOR
                                     (LOGAND
                                      -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                                     (LOGAND
                                      4088
                                      (LOGHEAD
                                       28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
                                    :R X86))))
                                12))
                              :R X86)))
                           (LOGAND
                            4503598553628672
                            (MV-NTH
                             1
                             (RB
                              8
                              (LOGIOR
                               (LOGAND
                                4088
                                (LOGHEAD
                                 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
                               (ASH
                                (LOGHEAD
                                 40
                                 (LOGTAIL
                                  12
                                  (MV-NTH
                                   1
                                   (RB
                                    8
                                    (LOGIOR
                                     (LOGAND
                                      -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                                     (LOGAND
                                      4088
                                      (LOGHEAD
                                       28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
                                    :R X86))))
                                12))
                              :R X86))))
                          (MV-NTH
                           2
                           (LAS-TO-PAS
                            6 (+ 184 (XR :RIP 0 X86))
                            :X
                            (MV-NTH
                             2
                             (LAS-TO-PAS
                              8
                              (LOGIOR
                               (LOGAND
                                4088
                                (LOGHEAD
                                 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
                               (ASH
                                (LOGHEAD
                                 40
                                 (LOGTAIL
                                  12
                                  (MV-NTH
                                   1
                                   (RB
                                    8
                                    (LOGIOR
                                     (LOGAND
                                      -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                                     (LOGAND
                                      4088
                                      (LOGHEAD
                                       28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
                                    :R X86))))
                                12))
                              :R
                              (MV-NTH
                               2
                               (LAS-TO-PAS
                                40 (+ 144 (XR :RIP 0 X86))
                                :X
                                (MV-NTH
                                 2
                                 (LAS-TO-PAS
                                  3 (+ 140 (XR :RIP 0 X86))
                                  :X
                                  (MV-NTH
                                   2
                                   (LAS-TO-PAS
                                    8
                                    (LOGIOR
                                     (LOGAND
                                      -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                                     (LOGAND
                                      4088
                                      (LOGHEAD
                                       28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
                                    :R
                                    (MV-NTH
                                     2
                                     (LAS-TO-PAS
                                      32 (+ 108 (XR :RIP 0 X86))
                                      :X
                                      (MV-NTH
                                       2
                                       (LAS-TO-PAS
                                        18 (+ 86 (XR :RIP 0 X86))
                                        :X
                                        (MV-NTH
                                         2
                                         (LAS-TO-PAS
                                          8
                                          (LOGIOR
                                           (LOGAND
                                            4088
                                            (LOGHEAD
                                             32
                                             (LOGTAIL
                                              27 (XR :RGF *RDI* X86))))
                                           (ASH
                                            (LOGHEAD
                                             40
                                             (LOGTAIL
                                              12
                                              (MV-NTH
                                               1
                                               (RB
                                                8
                                                (LOGIOR
                                                 (LOGAND
                                                  -4096
                                                  (LOGEXT
                                                   64 (XR :CTR *CR3* X86)))
                                                 (LOGAND
                                                  4088
                                                  (LOGHEAD
                                                   28
                                                   (LOGTAIL
                                                    36
                                                    (XR :RGF *RDI* X86)))))
                                                :R X86))))
                                            12))
                                          :R
                                          (MV-NTH
                                           2
                                           (LAS-TO-PAS
                                            40 (+ 46 (XR :RIP 0 X86))
                                            :X
                                            (MV-NTH
                                             2
                                             (LAS-TO-PAS
                                              4 (+ 38 (XR :RIP 0 X86))
                                              :X
                                              (MV-NTH
                                               2
                                               (LAS-TO-PAS
                                                8
                                                (LOGIOR
                                                 (LOGAND
                                                  -4096
                                                  (LOGEXT
                                                   64 (XR :CTR *CR3* X86)))
                                                 (LOGAND
                                                  4088
                                                  (LOGHEAD
                                                   28
                                                   (LOGTAIL
                                                    36
                                                    (XR :RGF *RDI* X86)))))
                                                :R
                                                (MV-NTH
                                                 2
                                                 (LAS-TO-PAS
                                                  25 (+ 13 (XR :RIP 0 X86))
                                                  :X
                                                  (MV-NTH
                                                   2
                                                   (LAS-TO-PAS
                                                    8
                                                    (+
                                                     -24 (XR :RGF *RSP* X86))
                                                    :R
                                                    (MV-NTH
                                                     2
                                                     (LAS-TO-PAS
                                                      5 (+ 8 (XR :RIP 0 X86))
                                                      :X
                                                      (MV-NTH
                                                       1
                                                       (WB
                                                        8
                                                        (+
                                                         -24
                                                         (XR :RGF *RSP* X86))
                                                        :W
                                                        (XR :CTR *CR3* X86)
                                                        (MV-NTH
                                                         2
                                                         (LAS-TO-PAS
                                                          8 (XR :RIP 0 X86)
                                                          :X
                                                          X86)))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(defrule 64-bit-modep-of-zerocopy-state
  (equal (64-bit-modep (zerocopy-state x86))
         (64-bit-modep x86)))

(defthmd rewire_dst_to_src-effects
  (implies
   (rewire_dst_to_src-effects-preconditions x86)
   (equal
    (x86-run (rewire_dst_to_src-clk) x86)
    (zeroCopy-state x86)))
  :hints (("Goal"
           :expand ((:free (x) (hide x))
                    (rewire_dst_to_src-effects-preconditions x86))
           :use ((:instance x86-run-plus
                            (n1 (rewire_dst_to_src-clk-1-to-45))
                            (n2 (rewire_dst_to_src-clk-46-to-58)))
                 (:instance rewire_dst_to_src-effects-1-to-45-instructions)
                 (:instance rewire_dst_to_src-effects-46-to-58-instructions)
                 (:instance rewrite-to-pml4-table-entry-addr)
                 (:instance rewrite-to-page-dir-ptr-table-entry-addr))
           :in-theory (union-theories
                       '(zeroCopy-state
                         program-alt-ok-p-and-program-ok-p
                         natp
                         (natp)
                         rewire_dst_to_src-clk
                         rewire_dst_to_src-clk-1-to-45
                         rewire_dst_to_src-clk-46-to-58)
                       (theory 'minimal-theory)))))

(in-theory (e/d () ((rewire_dst_to_src-clk) rewire_dst_to_src-clk)))

;; ASIDE: If I wanted to operate only at the level of physical memory
;; in the system-level marking view, I could do something like the
;; following: define the effects in terms of write-to-physical-memory
;; and read-from-physical-memory, and then prove a theorem like
;; zeroCopy-state-and-zeroCopy-state-physical-memory below.  In this
;; book, I don't use this strategy, but it's worth considering for a
;; future effort.
(defun-nx zeroCopy-state-physical-memory (x86)
  ;; All memory operations in terms of physical memory...
  ;; TODO: Maybe don't convert stack operations to physical memory operations?
  (XW
   :RGF *RAX* 1
   (XW
    :RGF *RCX*
    (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
            (LOGAND 4088
                    (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
    (XW
     :RGF *RDX*
     (LOGAND
      4503598553628672
      (LOGIOR
       (LOGAND
        -4503598553628673
        (LOGEXT
         64
         (READ-FROM-PHYSICAL-MEMORY
          (MV-NTH
           1
           (LAS-TO-PAS
            8
            (LOGIOR
             (LOGAND 4088
                     (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
             (ASH
              (LOGHEAD
               40
               (LOGTAIL
                12
                (READ-FROM-PHYSICAL-MEMORY
                 (MV-NTH
                  1
                  (LAS-TO-PAS
                   8
                   (LOGIOR
                    (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                    (LOGAND 4088
                            (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
                   :R X86))
                 X86)))
              12))
            :W X86))
          X86)))
       (LOGAND
        4503598553628672
        (LOGEXT
         64
         (READ-FROM-PHYSICAL-MEMORY
          (MV-NTH
           1
           (LAS-TO-PAS
            8
            (LOGIOR
             (LOGAND 4088
                     (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
             (ASH
              (LOGHEAD
               40
               (LOGTAIL
                12
                (READ-FROM-PHYSICAL-MEMORY
                 (MV-NTH
                  1
                  (LAS-TO-PAS
                   8
                   (LOGIOR
                    (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                    (LOGAND 4088
                            (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
                   :R X86))
                 X86)))
              12))
            :R X86))
          X86)))))
     (XW
      :RGF *RSP* (+ 8 (XR :RGF *RSP* X86))
      (XW
       :RGF *RSI* 0
       (XW
        :RGF *RDI*
        (LOGAND
         4503598553628672
         (LOGEXT
          64
          (READ-FROM-PHYSICAL-MEMORY
           (MV-NTH
            1
            (LAS-TO-PAS
             8
             (LOGIOR
              (LOGAND 4088
                      (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
              (ASH
               (LOGHEAD
                40
                (LOGTAIL
                 12
                 (READ-FROM-PHYSICAL-MEMORY
                  (MV-NTH
                   1
                   (LAS-TO-PAS
                    8
                    (LOGIOR
                     (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                     (LOGAND 4088
                             (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
                    :R X86))
                  X86)))
               12))
             :R X86))
           X86)))
        (XW
         :RGF *R8* 1099511627775
         (XW
          :RGF *R9*
          (LOGAND
           4503598553628672
           (LOGEXT
            64
            (READ-FROM-PHYSICAL-MEMORY
             (MV-NTH
              1
              (LAS-TO-PAS
               8
               (LOGIOR
                (LOGAND 4088
                        (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
                (ASH
                 (LOGHEAD
                  40
                  (LOGTAIL
                   12
                   (READ-FROM-PHYSICAL-MEMORY
                    (MV-NTH
                     1
                     (LAS-TO-PAS
                      8
                      (LOGIOR
                       (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                       (LOGAND 4088
                               (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
                      :R X86))
                    X86)))
                 12))
               :R X86))
             X86)))
          (XW
           :RIP 0
           (LOGEXT 64
                   (READ-FROM-PHYSICAL-MEMORY
                    (MV-NTH 1
                            (LAS-TO-PAS 8 (XR :RGF *RSP* X86)
                                        :R X86))
                    X86))
           (XW
            :UNDEF 0 (+ 46 (NFIX (XR :UNDEF 0 X86)))
            (!FLGI
             *CF*
             (BOOL->BIT
              (<
               (LOGAND
                4503598553628672
                (READ-FROM-PHYSICAL-MEMORY
                 (MV-NTH
                  1
                  (LAS-TO-PAS
                   8
                   (LOGIOR
                    (LOGAND 4088
                            (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
                    (ASH
                     (LOGHEAD
                      40
                      (LOGTAIL
                       12
                       (READ-FROM-PHYSICAL-MEMORY
                        (MV-NTH
                         1
                         (LAS-TO-PAS
                          8
                          (LOGIOR
                           (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                           (LOGAND
                            4088
                            (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
                          :R X86))
                        X86)))
                     12))
                   :R X86))
                 X86))
               (LOGAND
                4503598553628672
                (LOGIOR
                 (LOGAND
                  18442240475155922943
                  (READ-FROM-PHYSICAL-MEMORY
                   (MV-NTH
                    1
                    (LAS-TO-PAS
                     8
                     (LOGIOR
                      (LOGAND 4088
                              (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
                      (ASH
                       (LOGHEAD
                        40
                        (LOGTAIL
                         12
                         (READ-FROM-PHYSICAL-MEMORY
                          (MV-NTH
                           1
                           (LAS-TO-PAS
                            8
                            (LOGIOR
                             (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                             (LOGAND
                              4088
                              (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
                            :R X86))
                          X86)))
                       12))
                     :W X86))
                   X86))
                 (LOGAND
                  4503598553628672
                  (READ-FROM-PHYSICAL-MEMORY
                   (MV-NTH
                    1
                    (LAS-TO-PAS
                     8
                     (LOGIOR
                      (LOGAND 4088
                              (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
                      (ASH
                       (LOGHEAD
                        40
                        (LOGTAIL
                         12
                         (READ-FROM-PHYSICAL-MEMORY
                          (MV-NTH
                           1
                           (LAS-TO-PAS
                            8
                            (LOGIOR
                             (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                             (LOGAND
                              4088
                              (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
                            :R X86))
                          X86)))
                       12))
                     :R X86))
                   X86))))))
             (!FLGI
              *PF*
              (PF-SPEC64
               (LOGHEAD
                64
                (+
                 (LOGAND
                  4503598553628672
                  (LOGEXT
                   64
                   (READ-FROM-PHYSICAL-MEMORY
                    (MV-NTH
                     1
                     (LAS-TO-PAS
                      8
                      (LOGIOR
                       (LOGAND 4088
                               (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
                       (ASH
                        (LOGHEAD
                         40
                         (LOGTAIL
                          12
                          (READ-FROM-PHYSICAL-MEMORY
                           (MV-NTH
                            1
                            (LAS-TO-PAS
                             8
                             (LOGIOR
                              (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                              (LOGAND
                               4088
                               (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
                             :R X86))
                           X86)))
                        12))
                      :R X86))
                    X86)))
                 (-
                  (LOGAND
                   4503598553628672
                   (LOGIOR
                    (LOGAND
                     -4503598553628673
                     (LOGEXT
                      64
                      (READ-FROM-PHYSICAL-MEMORY
                       (MV-NTH
                        1
                        (LAS-TO-PAS
                         8
                         (LOGIOR
                          (LOGAND
                           4088
                           (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
                          (ASH
                           (LOGHEAD
                            40
                            (LOGTAIL
                             12
                             (READ-FROM-PHYSICAL-MEMORY
                              (MV-NTH
                               1
                               (LAS-TO-PAS
                                8
                                (LOGIOR
                                 (LOGAND
                                  -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                                 (LOGAND
                                  4088
                                  (LOGHEAD
                                   28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
                                :R X86))
                              X86)))
                           12))
                         :W X86))
                       X86)))
                    (LOGAND
                     4503598553628672
                     (LOGEXT
                      64
                      (READ-FROM-PHYSICAL-MEMORY
                       (MV-NTH
                        1
                        (LAS-TO-PAS
                         8
                         (LOGIOR
                          (LOGAND
                           4088
                           (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
                          (ASH
                           (LOGHEAD
                            40
                            (LOGTAIL
                             12
                             (READ-FROM-PHYSICAL-MEMORY
                              (MV-NTH
                               1
                               (LAS-TO-PAS
                                8
                                (LOGIOR
                                 (LOGAND
                                  -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                                 (LOGAND
                                  4088
                                  (LOGHEAD
                                   28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
                                :R X86))
                              X86)))
                           12))
                         :R X86))
                       X86)))))))))
              (!FLGI
               *AF*
               (SUB-AF-SPEC64
                (LOGAND
                 4503598553628672
                 (READ-FROM-PHYSICAL-MEMORY
                  (MV-NTH
                   1
                   (LAS-TO-PAS
                    8
                    (LOGIOR
                     (LOGAND 4088
                             (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
                     (ASH
                      (LOGHEAD
                       40
                       (LOGTAIL
                        12
                        (READ-FROM-PHYSICAL-MEMORY
                         (MV-NTH
                          1
                          (LAS-TO-PAS
                           8
                           (LOGIOR
                            (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                            (LOGAND
                             4088
                             (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
                           :R X86))
                         X86)))
                      12))
                    :R X86))
                  X86))
                (LOGAND
                 4503598553628672
                 (LOGIOR
                  (LOGAND
                   18442240475155922943
                   (READ-FROM-PHYSICAL-MEMORY
                    (MV-NTH
                     1
                     (LAS-TO-PAS
                      8
                      (LOGIOR
                       (LOGAND 4088
                               (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
                       (ASH
                        (LOGHEAD
                         40
                         (LOGTAIL
                          12
                          (READ-FROM-PHYSICAL-MEMORY
                           (MV-NTH
                            1
                            (LAS-TO-PAS
                             8
                             (LOGIOR
                              (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                              (LOGAND
                               4088
                               (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
                             :R X86))
                           X86)))
                        12))
                      :W X86))
                    X86))
                  (LOGAND
                   4503598553628672
                   (READ-FROM-PHYSICAL-MEMORY
                    (MV-NTH
                     1
                     (LAS-TO-PAS
                      8
                      (LOGIOR
                       (LOGAND 4088
                               (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
                       (ASH
                        (LOGHEAD
                         40
                         (LOGTAIL
                          12
                          (READ-FROM-PHYSICAL-MEMORY
                           (MV-NTH
                            1
                            (LAS-TO-PAS
                             8
                             (LOGIOR
                              (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                              (LOGAND
                               4088
                               (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
                             :R X86))
                           X86)))
                        12))
                      :R X86))
                    X86)))))
               (!FLGI
                *ZF* 1
                (!FLGI
                 *SF*
                 (SF-SPEC64
                  (LOGHEAD
                   64
                   (+
                    (LOGAND
                     4503598553628672
                     (LOGEXT
                      64
                      (READ-FROM-PHYSICAL-MEMORY
                       (MV-NTH
                        1
                        (LAS-TO-PAS
                         8
                         (LOGIOR
                          (LOGAND
                           4088
                           (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
                          (ASH
                           (LOGHEAD
                            40
                            (LOGTAIL
                             12
                             (READ-FROM-PHYSICAL-MEMORY
                              (MV-NTH
                               1
                               (LAS-TO-PAS
                                8
                                (LOGIOR
                                 (LOGAND
                                  -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                                 (LOGAND
                                  4088
                                  (LOGHEAD
                                   28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
                                :R X86))
                              X86)))
                           12))
                         :R X86))
                       X86)))
                    (-
                     (LOGAND
                      4503598553628672
                      (LOGIOR
                       (LOGAND
                        -4503598553628673
                        (LOGEXT
                         64
                         (READ-FROM-PHYSICAL-MEMORY
                          (MV-NTH
                           1
                           (LAS-TO-PAS
                            8
                            (LOGIOR
                             (LOGAND
                              4088
                              (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
                             (ASH
                              (LOGHEAD
                               40
                               (LOGTAIL
                                12
                                (READ-FROM-PHYSICAL-MEMORY
                                 (MV-NTH
                                  1
                                  (LAS-TO-PAS
                                   8
                                   (LOGIOR
                                    (LOGAND
                                     -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                                    (LOGAND
                                     4088
                                     (LOGHEAD
                                      28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
                                   :R X86))
                                 X86)))
                              12))
                            :W X86))
                          X86)))
                       (LOGAND
                        4503598553628672
                        (LOGEXT
                         64
                         (READ-FROM-PHYSICAL-MEMORY
                          (MV-NTH
                           1
                           (LAS-TO-PAS
                            8
                            (LOGIOR
                             (LOGAND
                              4088
                              (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
                             (ASH
                              (LOGHEAD
                               40
                               (LOGTAIL
                                12
                                (READ-FROM-PHYSICAL-MEMORY
                                 (MV-NTH
                                  1
                                  (LAS-TO-PAS
                                   8
                                   (LOGIOR
                                    (LOGAND
                                     -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                                    (LOGAND
                                     4088
                                     (LOGHEAD
                                      28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
                                   :R X86))
                                 X86)))
                              12))
                            :R X86))
                          X86)))))))))
                 (!FLGI
                  *OF*
                  (OF-SPEC64
                   (+
                    (LOGAND
                     4503598553628672
                     (LOGEXT
                      64
                      (READ-FROM-PHYSICAL-MEMORY
                       (MV-NTH
                        1
                        (LAS-TO-PAS
                         8
                         (LOGIOR
                          (LOGAND
                           4088
                           (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
                          (ASH
                           (LOGHEAD
                            40
                            (LOGTAIL
                             12
                             (READ-FROM-PHYSICAL-MEMORY
                              (MV-NTH
                               1
                               (LAS-TO-PAS
                                8
                                (LOGIOR
                                 (LOGAND
                                  -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                                 (LOGAND
                                  4088
                                  (LOGHEAD
                                   28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
                                :R X86))
                              X86)))
                           12))
                         :R X86))
                       X86)))
                    (-
                     (LOGAND
                      4503598553628672
                      (LOGIOR
                       (LOGAND
                        -4503598553628673
                        (LOGEXT
                         64
                         (READ-FROM-PHYSICAL-MEMORY
                          (MV-NTH
                           1
                           (LAS-TO-PAS
                            8
                            (LOGIOR
                             (LOGAND
                              4088
                              (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
                             (ASH
                              (LOGHEAD
                               40
                               (LOGTAIL
                                12
                                (READ-FROM-PHYSICAL-MEMORY
                                 (MV-NTH
                                  1
                                  (LAS-TO-PAS
                                   8
                                   (LOGIOR
                                    (LOGAND
                                     -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                                    (LOGAND
                                     4088
                                     (LOGHEAD
                                      28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
                                   :R X86))
                                 X86)))
                              12))
                            :W X86))
                          X86)))
                       (LOGAND
                        4503598553628672
                        (LOGEXT
                         64
                         (READ-FROM-PHYSICAL-MEMORY
                          (MV-NTH
                           1
                           (LAS-TO-PAS
                            8
                            (LOGIOR
                             (LOGAND
                              4088
                              (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
                             (ASH
                              (LOGHEAD
                               40
                               (LOGTAIL
                                12
                                (READ-FROM-PHYSICAL-MEMORY
                                 (MV-NTH
                                  1
                                  (LAS-TO-PAS
                                   8
                                   (LOGIOR
                                    (LOGAND
                                     -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                                    (LOGAND
                                     4088
                                     (LOGHEAD
                                      28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
                                   :R X86))
                                 X86)))
                              12))
                            :R X86))
                          X86))))))))
                  (MV-NTH
                   2
                   (LAS-TO-PAS
                    8 (XR :RGF *RSP* X86)
                    :R
                    (MV-NTH
                     2
                     (LAS-TO-PAS
                      40 (+ 206 (XR :RIP 0 X86))
                      :X
                      (MV-NTH
                       2
                       (LAS-TO-PAS
                        15 (+ 190 (XR :RIP 0 X86))
                        :X
                        (MV-NTH
                         2
                         (LAS-TO-PAS
                          8
                          (LOGIOR
                           (LOGAND
                            4088
                            (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
                           (ASH
                            (LOGHEAD
                             40
                             (LOGTAIL
                              12
                              (READ-FROM-PHYSICAL-MEMORY
                               (MV-NTH
                                1
                                (LAS-TO-PAS
                                 8
                                 (LOGIOR
                                  (LOGAND
                                   -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                                  (LOGAND
                                   4088
                                   (LOGHEAD
                                    28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
                                 :R X86))
                               X86)))
                            12))
                          :W
                          (MV-NTH
                           2
                           (LAS-TO-PAS
                            6 (+ 184 (XR :RIP 0 X86))
                            :X
                            (MV-NTH
                             2
                             (LAS-TO-PAS
                              8
                              (LOGIOR
                               (LOGAND
                                4088
                                (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
                               (ASH
                                (LOGHEAD
                                 40
                                 (LOGTAIL
                                  12
                                  (READ-FROM-PHYSICAL-MEMORY
                                   (MV-NTH
                                    1
                                    (LAS-TO-PAS
                                     8
                                     (LOGIOR
                                      (LOGAND
                                       -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                                      (LOGAND
                                       4088
                                       (LOGHEAD
                                        28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
                                     :R X86))
                                   X86)))
                                12))
                              :R
                              (MV-NTH
                               2
                               (LAS-TO-PAS
                                40 (+ 144 (XR :RIP 0 X86))
                                :X
                                (MV-NTH
                                 2
                                 (LAS-TO-PAS
                                  3 (+ 140 (XR :RIP 0 X86))
                                  :X
                                  (MV-NTH
                                   2
                                   (LAS-TO-PAS
                                    8
                                    (LOGIOR
                                     (LOGAND
                                      -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                                     (LOGAND
                                      4088
                                      (LOGHEAD
                                       28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
                                    :R
                                    (MV-NTH
                                     2
                                     (LAS-TO-PAS
                                      32 (+ 108 (XR :RIP 0 X86))
                                      :X
                                      (MV-NTH
                                       2
                                       (LAS-TO-PAS
                                        18 (+ 86 (XR :RIP 0 X86))
                                        :X
                                        (MV-NTH
                                         2
                                         (LAS-TO-PAS
                                          8
                                          (LOGIOR
                                           (LOGAND
                                            4088
                                            (LOGHEAD
                                             32
                                             (LOGTAIL
                                              27 (XR :RGF *RDI* X86))))
                                           (ASH
                                            (LOGHEAD
                                             40
                                             (LOGTAIL
                                              12
                                              (READ-FROM-PHYSICAL-MEMORY
                                               (MV-NTH
                                                1
                                                (LAS-TO-PAS
                                                 8
                                                 (LOGIOR
                                                  (LOGAND
                                                   -4096
                                                   (LOGEXT
                                                    64 (XR :CTR *CR3* X86)))
                                                  (LOGAND
                                                   4088
                                                   (LOGHEAD
                                                    28
                                                    (LOGTAIL
                                                     36
                                                     (XR :RGF *RDI* X86)))))
                                                 :R X86))
                                               X86)))
                                            12))
                                          :R
                                          (MV-NTH
                                           2
                                           (LAS-TO-PAS
                                            40 (+ 46 (XR :RIP 0 X86))
                                            :X
                                            (MV-NTH
                                             2
                                             (LAS-TO-PAS
                                              4 (+ 38 (XR :RIP 0 X86))
                                              :X
                                              (MV-NTH
                                               2
                                               (LAS-TO-PAS
                                                8
                                                (LOGIOR
                                                 (LOGAND
                                                  -4096
                                                  (LOGEXT
                                                   64 (XR :CTR *CR3* X86)))
                                                 (LOGAND
                                                  4088
                                                  (LOGHEAD
                                                   28
                                                   (LOGTAIL
                                                    36 (XR :RGF *RDI* X86)))))
                                                :R
                                                (MV-NTH
                                                 2
                                                 (LAS-TO-PAS
                                                  25 (+ 13 (XR :RIP 0 X86))
                                                  :X
                                                  (MV-NTH
                                                   2
                                                   (LAS-TO-PAS
                                                    8
                                                    (+
                                                     -24 (XR :RGF *RSP* X86))
                                                    :R
                                                    (MV-NTH
                                                     2
                                                     (LAS-TO-PAS
                                                      5 (+ 8 (XR :RIP 0 X86))
                                                      :X
                                                      (MV-NTH
                                                       2
                                                       (LAS-TO-PAS
                                                        8
                                                        (+
                                                         -24
                                                         (XR :RGF *RSP* X86))
                                                        :W
                                                        (MV-NTH
                                                         2
                                                         (LAS-TO-PAS
                                                          8 (XR :RIP 0 X86)
                                                          :X
                                                          (WRITE-TO-PHYSICAL-MEMORY
                                                           (MV-NTH
                                                            1
                                                            (LAS-TO-PAS
                                                             8
                                                             (LOGIOR
                                                              (LOGAND
                                                               4088
                                                               (LOGHEAD
                                                                32
                                                                (LOGTAIL
                                                                 27
                                                                 (XR
                                                                  :RGF *RSI*
                                                                  X86))))
                                                              (ASH
                                                               (LOGHEAD
                                                                40
                                                                (LOGTAIL
                                                                 12
                                                                 (READ-FROM-PHYSICAL-MEMORY
                                                                  (MV-NTH
                                                                   1
                                                                   (LAS-TO-PAS
                                                                    8
                                                                    (LOGIOR
                                                                     (LOGAND
                                                                      -4096
                                                                      (LOGEXT
                                                                       64
                                                                       (XR
                                                                        :CTR
                                                                        *CR3*
                                                                        X86)))
                                                                     (LOGAND
                                                                      4088
                                                                      (LOGHEAD
                                                                       28
                                                                       (LOGTAIL
                                                                        36
                                                                        (XR
                                                                         :RGF
                                                                         *RSI*
                                                                         X86)))))
                                                                    :R X86))
                                                                  X86)))
                                                               12))
                                                             :W X86))
                                                           (LOGIOR
                                                            (LOGAND
                                                             18442240475155922943
                                                             (READ-FROM-PHYSICAL-MEMORY
                                                              (MV-NTH
                                                               1
                                                               (LAS-TO-PAS
                                                                8
                                                                (LOGIOR
                                                                 (LOGAND
                                                                  4088
                                                                  (LOGHEAD
                                                                   32
                                                                   (LOGTAIL
                                                                    27
                                                                    (XR
                                                                     :RGF
                                                                     *RSI*
                                                                     X86))))
                                                                 (ASH
                                                                  (LOGHEAD
                                                                   40
                                                                   (LOGTAIL
                                                                    12
                                                                    (READ-FROM-PHYSICAL-MEMORY
                                                                     (MV-NTH
                                                                      1
                                                                      (LAS-TO-PAS
                                                                       8
                                                                       (LOGIOR
                                                                        (LOGAND
                                                                         -4096
                                                                         (LOGEXT
                                                                          64
                                                                          (XR
                                                                           :CTR
                                                                           *CR3*
                                                                           X86)))
                                                                        (LOGAND
                                                                         4088
                                                                         (LOGHEAD
                                                                          28
                                                                          (LOGTAIL
                                                                           36
                                                                           (XR
                                                                            :RGF
                                                                            *RSI*
                                                                            X86)))))
                                                                       :R
                                                                       X86))
                                                                     X86)))
                                                                  12))
                                                                :W X86))
                                                              X86))
                                                            (LOGAND
                                                             4503598553628672
                                                             (READ-FROM-PHYSICAL-MEMORY
                                                              (MV-NTH
                                                               1
                                                               (LAS-TO-PAS
                                                                8
                                                                (LOGIOR
                                                                 (LOGAND
                                                                  4088
                                                                  (LOGHEAD
                                                                   32
                                                                   (LOGTAIL
                                                                    27
                                                                    (XR
                                                                     :RGF
                                                                     *RDI*
                                                                     X86))))
                                                                 (ASH
                                                                  (LOGHEAD
                                                                   40
                                                                   (LOGTAIL
                                                                    12
                                                                    (READ-FROM-PHYSICAL-MEMORY
                                                                     (MV-NTH
                                                                      1
                                                                      (LAS-TO-PAS
                                                                       8
                                                                       (LOGIOR
                                                                        (LOGAND
                                                                         -4096
                                                                         (LOGEXT
                                                                          64
                                                                          (XR
                                                                           :CTR
                                                                           *CR3*
                                                                           X86)))
                                                                        (LOGAND
                                                                         4088
                                                                         (LOGHEAD
                                                                          28
                                                                          (LOGTAIL
                                                                           36
                                                                           (XR
                                                                            :RGF
                                                                            *RDI*
                                                                            X86)))))
                                                                       :R
                                                                       X86))
                                                                     X86)))
                                                                  12))
                                                                :R X86))
                                                              X86)))
                                                           (WRITE-TO-PHYSICAL-MEMORY
                                                            (MV-NTH
                                                             1
                                                             (LAS-TO-PAS
                                                              8
                                                              (+
                                                               -24
                                                               (XR :RGF
                                                                   *RSP* X86))
                                                              :W X86))
                                                            (XR
                                                             :CTR *CR3* X86)
                                                            X86)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(defthmd zeroCopy-state-and-zeroCopy-state-physical-memory
  (implies (rewire_dst_to_src-effects-preconditions x86)
           (equal
            (zeroCopy-state x86)
            (zeroCopy-state-physical-memory x86)))
  :hints (("Goal"
           :in-theory (e/d
                       (zeroCopy-state
                        zeroCopy-state-physical-memory
                        disjoint-p-all-xlation-governing-entries-paddrs-subset-p
                        rb wb)
                       ()))))

;; ----------------------------------------------------------------------

;; Theorems about the projection of viewl state's fields:

(defthmd preconditions-imply-ms-fault-view
  (implies (rewire_dst_to_src-effects-preconditions x86)
           (and (equal (xr :ms                          0 x86) nil)
                (equal (xr :fault                       0 x86) nil)
                (equal (xr :app-view       0 x86) nil)
                (equal (xr :marking-view 0 x86) t))))

(defthmd fault-projection
  (implies
   (rewire_dst_to_src-effects-preconditions x86)
   (equal
    (xr :fault 0 (zeroCopy-state x86))
    (xr :fault 0 x86)))
  :hints (("Goal"
           :do-not '(preprocess)
           :hands-off (x86-run)
           :in-theory (e/d* ()
                            (rewrite-rb-to-rb-alt
                             mv-nth-1-las-to-pas-subset-p-disjoint-from-other-p-addrs
                             mv-nth-1-las-to-pas-returns-nil-when-error
                             (:rewrite acl2::loghead-identity)
                             (:meta acl2::mv-nth-cons-meta)
                             force (force))))))

(defthmd ms-fault-application-level-and-marking-view-projection
  (implies (rewire_dst_to_src-effects-preconditions x86)
           (and
            (equal (xr :ms                          0 (zeroCopy-state x86)) nil)
            (equal (xr :fault                       0 (zeroCopy-state x86)) nil)
            (equal (xr :app-view       0 (zeroCopy-state x86)) nil)
            (equal (xr :marking-view 0 (zeroCopy-state x86)) t)))
  :hints (("Goal"
           :do-not '(preprocess)
           :use ((:instance fault-projection))
           :hands-off (x86-run)
           :in-theory
           (e/d* (preconditions-imply-ms-fault-view)
                 (rewire_dst_to_src-effects-preconditions)))))

;; ----------------------------------------------------------------------

;; Projection of the Program:

(defthmd program-pas-projection
  (implies
   (rewire_dst_to_src-effects-preconditions x86)
   (equal
    (mv-nth 1 (las-to-pas
               *rewire_dst_to_src-len* (xr :rip 0 x86) :x (zeroCopy-state x86)))
    (mv-nth 1 (las-to-pas *rewire_dst_to_src-len* (xr :rip 0 x86) :x x86))))
  :hints (("Goal" :in-theory (e/d (page-size) ()))))


(local
 (defthmd preconditions-imply-x86p
   (implies (rewire_dst_to_src-effects-preconditions x86)
            (x86p x86))))

(defthm program-at-alt-and-wb-to-paging-structures
  (implies
   (and
    (equal (page-size value) 1)
    (direct-map-p 8 lin-addr :w  (double-rewrite x86))
    (disjoint-p$
     (mv-nth 1 (las-to-pas (len bytes) prog-addr :x (double-rewrite x86)))
     (open-qword-paddr-list
      (gather-all-paging-structure-qword-addresses (double-rewrite x86))))
    (disjoint-p$
     (mv-nth 1 (las-to-pas 8 lin-addr :w  (double-rewrite x86)))
     (all-xlation-governing-entries-paddrs (len bytes) prog-addr (double-rewrite x86)))
    (disjoint-p$
     (mv-nth 1 (las-to-pas 8 lin-addr :w  (double-rewrite x86)))
     (mv-nth 1 (las-to-pas (len bytes) prog-addr :x (double-rewrite x86))))
    (physical-address-p lin-addr)
    (equal (loghead 3 lin-addr) 0)
    (canonical-address-p lin-addr)
    (unsigned-byte-p 64 value))
   (equal
    (program-at-alt prog-addr bytes (mv-nth 1 (wb 8 lin-addr w value x86)))
    (program-at-alt prog-addr bytes (double-rewrite x86))))
  :hints
  (("Goal"
    :do-not-induct t
    :in-theory (e/d* (disjointness-of-las-to-pas-from-wb-to-a-paging-entry
                      program-at-alt
                      program-at
                      disjoint-p$
                      subset-p
                      subset-p-reflexive
                      program-at-alt)
                     (rewrite-program-at-to-program-at-alt)))))

(defthmd program-at-alt-projection
  (implies
   (rewire_dst_to_src-effects-preconditions x86)
   (equal (program-at-alt (xr :rip 0 x86) *rewire_dst_to_src* (zeroCopy-state x86))
          (program-at-alt (xr :rip 0 x86) *rewire_dst_to_src* x86)))
  :hints (("Goal"
           :use ((:instance preconditions-imply-ms-fault-view)
                 (:instance preconditions-imply-x86p))
           :in-theory (e/d* (program-pas-projection
                             ms-fault-application-level-and-marking-view-projection
                             page-size
                             pdpt-base-addr
                             pml4-table-entry-addr
                             pml4-table-base-addr
                             page-dir-ptr-table-entry-addr-to-C-program-optimized-form)
                            ()))))

;; Proving that the program is unmodified in terms of program-at
;; instead of program-at-alt:

(local
 (defthmd unsigned-byte-p-64-of-modified-entry
   (unsigned-byte-p 64
                    (logior (logand 18442240475155922943 x)
                            (logand 4503598553628672 y)))
   :hints (("Goal"
            :use ((:instance bitops::unsigned-byte-p-logand-fix
                             (b 64)
                             (x  x)
                             (y 18442240475155922943))
                  (:instance bitops::unsigned-byte-p-logand-fix
                             (b 64)
                             (x  y)
                             (y 4503598553628672)))
            :in-theory (e/d* (unsigned-byte-p-of-logior
                              unsigned-byte-p)
                             ())))))

(defthmd gather-all-paging-structure-qword-addresses-and-wb-to-direct-mapped-entry-equal
  (implies
   (and
    (bind-free
     (find-an-xlate-equiv-x86
      'gather-all-paging-structure-qword-addresses-and-wb-to-direct-mapped-entry-equal
      x86-1 'x86-2 mfc state)
     (x86-2))
    ;; IMPORTANT: xlate-equiv-structures is weaker than
    ;; xlate-equiv-memory --- I use the former here so that this
    ;; rule can be applicable in cases where there are writes to
    ;; locations of memory disjoint from the paging structures.
    (xlate-equiv-structures (double-rewrite x86-1) (double-rewrite x86-2))
    (64-bit-modep x86-1) ; added
    (not (app-view (double-rewrite x86-1)))
    (member-p
     index
     (gather-all-paging-structure-qword-addresses (double-rewrite x86-1)))
    ;; (subset-p
    ;;  (addr-range 8 index)
    ;;  (open-qword-paddr-list
    ;;   (gather-all-paging-structure-qword-addresses (double-rewrite x86-1))))
    (xlate-equiv-entries (double-rewrite val) (rm-low-64 index x86-1))
    (direct-map-p 8 index :w (double-rewrite x86-1))
    (disjoint-p
     (addr-range 8 index)
     (all-xlation-governing-entries-paddrs 8 index (double-rewrite x86-1)))
    (unsigned-byte-p 64 val))
   (equal
    (gather-all-paging-structure-qword-addresses
     (mv-nth 1 (wb 8 index w val x86-1)))
    (gather-all-paging-structure-qword-addresses (double-rewrite x86-2))))
  :hints
  (("Goal"
    :in-theory (e/d* (wb
                      direct-map-p
                      subset-p
                      xlate-equiv-structures)
                     (gather-all-paging-structure-qword-addresses-wm-low-64-different-x86))
    :use ((:instance rewrite-wm-low-64-to-write-to-physical-memory
                     (index index)
                     (value val)
                     (x86 (mv-nth 2 (las-to-pas 8 index :w x86-1))))
          (:instance gather-all-paging-structure-qword-addresses-wm-low-64-different-x86
                     (x86-equiv (mv-nth 2 (las-to-pas 8 index :w x86-1)))
                     (x86 x86-2))))))

(defthm gather-all-paging-structure-qword-addresses-and-wb-to-direct-mapped-entry-subset-p
  (implies
   (and (direct-map-p 8 index :w (double-rewrite x86-1))
        (equal (page-size value) 1)
        (physical-address-p index)
        (equal (loghead 3 index) 0)
        (unsigned-byte-p 64 value)
        (64-bit-modep x86-1) ; added
        (not (app-view (double-rewrite x86-1)))
        ;; IMPORTANT: xlate-equiv-structures is weaker than
        ;; xlate-equiv-memory --- I use the former here so that this
        ;; rule can be applicable in cases where there are writes to
        ;; locations of memory disjoint from the paging structures.
        (xlate-equiv-structures (double-rewrite x86-1) (double-rewrite x86-2)))
   (subset-p
    (gather-all-paging-structure-qword-addresses
     (mv-nth 1 (wb 8 index w value x86-1)))
    (gather-all-paging-structure-qword-addresses x86-2)))
  :hints
  (("Goal"
    :in-theory (e/d* (wb
                      direct-map-p
                      subset-p
                      xlate-equiv-structures)
                     (gather-all-paging-structure-qword-addresses-and-write-to-physical-memory-subset-p))
    :use ((:instance gather-all-paging-structure-qword-addresses-and-write-to-physical-memory-subset-p
                     (p-addrs (addr-range 8 index))
                     (x86 (mv-nth 2 (las-to-pas 8 index :w x86-1))))
          (:instance gather-all-paging-structure-qword-addresses-and-write-to-physical-memory-subset-p
                     (p-addrs (addr-range 8 index))
                     (x86 x86-1))))))

(defthm xlate-equiv-structures-and-wb-disjoint-from-paging-structures
  (implies
   (and
    (bind-free
     (find-an-xlate-equiv-x86
      'xlate-equiv-structures-and-wb-disjoint-from-paging-structures
      x86-1 'x86-2 mfc state)
     (x86-2))
    (xlate-equiv-structures (double-rewrite x86-1)
                            (double-rewrite x86-2))
    (64-bit-modep x86-1) ; added
    (not (app-view x86-1))
    (disjoint-p
     (mv-nth 1 (las-to-pas n-w write-addr :w (double-rewrite x86-1)))
     (open-qword-paddr-list
      (gather-all-paging-structure-qword-addresses (double-rewrite x86-1)))))
   (xlate-equiv-structures (mv-nth 1 (wb n-w write-addr w write-val x86-1))
                           (double-rewrite x86-2)))
  :hints (("Goal" :in-theory (e/d* (wb) ()))))

(defthmd gather-all-paging-structure-qword-addresses-projection
  ;; TODO: I should be able to prove a stronger theorem, with equal in
  ;; the conclusion instead of subset-p (see
  ;; gather-all-paging-structure-qword-addresses-and-wb-to-direct-mapped-entry-equal).
  ;; ZeroCopy doesn't change the addresses of the paging structures,
  ;; just the contents of one entry.
  (implies
   (and (rewire_dst_to_src-effects-preconditions x86)
        (direct-map-p 8
                      (page-dir-ptr-table-entry-addr
                       (xr :rgf *rsi* x86)
                       (pdpt-base-addr (xr :rgf *rsi* x86) x86))
                      :r x86))
   (subset-p
    (gather-all-paging-structure-qword-addresses (zeroCopy-state x86))
    (gather-all-paging-structure-qword-addresses x86)))
  :hints (("Goal" :in-theory (e/d* (page-size
                                    direct-map-p
                                    page-dir-ptr-table-entry-addr-to-c-program-optimized-form
                                    pdpt-base-addr
                                    pml4-table-base-addr
                                    pml4-table-entry-addr
                                    pml4-table-entry-addr-to-c-program-optimized-form
                                    unsigned-byte-p-64-of-modified-entry)
                                   ()))))

(local
 (defthm subset-p-and-open-qword-paddr-list
   (implies (subset-p x y)
            (subset-p (open-qword-paddr-list x)
                      (open-qword-paddr-list y)))
   :hints (("Goal"
            :induct (subset-p (open-qword-paddr-list x)
                              (open-qword-paddr-list y))
            :in-theory (e/d* (subset-p open-qword-paddr-list) ())))))

(local
 (defthmd preconditions-imply-disjointness-of-program-from-paging-structures
   (implies (rewire_dst_to_src-effects-preconditions x86)
            (and
             (disjoint-p (mv-nth 1
                                 (las-to-pas *rewire_dst_to_src-len* (xr :rip 0 x86) :x x86))
                         (open-qword-paddr-list
                          (gather-all-paging-structure-qword-addresses x86)))
             (canonical-address-p (xr :rip 0 x86))
             (canonical-address-p (+ *rewire_dst_to_src-len* (xr :rip 0 x86)))))
   :hints (("Goal" :in-theory (e/d* (rewire_dst_to_src-effects-preconditions)
                                    ())))))

(defthmd program-at-projection-helper
  (implies
   (and (rewire_dst_to_src-effects-preconditions x86)
        (direct-map-p 8
                      (page-dir-ptr-table-entry-addr
                       (xr :rgf *rsi* x86)
                       (pdpt-base-addr (xr :rgf *rsi* x86) x86))
                      :r x86))
   (disjoint-p$
    (mv-nth 1 (las-to-pas *rewire_dst_to_src-len*
                          (xr :rip 0 x86) :x
                          (zeroCopy-state x86)))
    (open-qword-paddr-list
     (gather-all-paging-structure-qword-addresses (zeroCopy-state x86)))))
  :hints
  (("Goal"
    :use ((:instance program-pas-projection)
          (:instance gather-all-paging-structure-qword-addresses-projection)
          (:instance preconditions-imply-disjointness-of-program-from-paging-structures)
          (:instance disjoint-p-subset-p
                     (a (mv-nth 1 (las-to-pas *rewire_dst_to_src-len*
                                              (xr :rip 0 x86) :x x86)))
                     (x (mv-nth 1 (las-to-pas *rewire_dst_to_src-len*
                                              (xr :rip 0 x86) :x x86)))
                     (b (open-qword-paddr-list
                         (gather-all-paging-structure-qword-addresses
                          (zeroCopy-state x86))))
                     (y (open-qword-paddr-list
                         (gather-all-paging-structure-qword-addresses
                          x86)))))
    :in-theory (e/d* (disjoint-p$
                      subset-p-reflexive)
                     (direct-map-p
                      rewire_dst_to_src-effects-preconditions
                      zeroCopy-state)))))

(defthmd program-at-projection
  (implies
   (and (64-bit-modep x86) ; added
        (rewire_dst_to_src-effects-preconditions x86)
        (direct-map-p 8
                      (page-dir-ptr-table-entry-addr
                       (xr :rgf *rsi* x86)
                       (pdpt-base-addr (xr :rgf *rsi* x86) x86))
                      :r x86))
   (equal (program-at (xr :rip 0 x86) *rewire_dst_to_src* (zeroCopy-state x86))
          (program-at (xr :rip 0 x86) *rewire_dst_to_src* x86)))
  :hints (("Goal"
           :use
           ((:instance program-at-projection-helper)
            (:instance program-at-alt-projection)
            (:instance preconditions-imply-disjointness-of-program-from-paging-structures))
           :in-theory (e/d* (disjoint-p$
                             program-at-alt
                             ms-fault-application-level-and-marking-view-projection
                             preconditions-imply-ms-fault-view)
                            (rewrite-program-at-to-program-at-alt
                             zeroCopy-state
                             rewire_dst_to_src-effects-preconditions)))))

;; ----------------------------------------------------------------------

;; Theorems about the Projection of the Page Table Entries:

(defthm xlate-equiv-memory-and-pml4-table-base-addr
  (implies (xlate-equiv-memory x86-1 x86-2)
           (equal (pml4-table-base-addr x86-1)
                  (pml4-table-base-addr x86-2)))
  :hints (("Goal" :in-theory (e/d* (pml4-table-base-addr) ())))
  :rule-classes :congruence)

(defthmd pml4-table-base-addr-projection
  (implies
   (rewire_dst_to_src-effects-preconditions x86)
   (equal
    (pml4-table-base-addr (zeroCopy-state x86))
    (pml4-table-base-addr x86)))
  :hints (("Goal" :in-theory (e/d* (page-size direct-map-p) ()))))

;; Theorems about the Source and Destination PML4 Table Entries:

(defthmd source-pml4-table-entry-addr-projection
  ;; Not really necessary because we have
  ;; pml4-table-base-addr-projection.
  (implies
   (rewire_dst_to_src-effects-preconditions x86)
   (equal
    (pml4-table-entry-addr (xr :rgf *rdi* x86)
                           (pml4-table-base-addr (zeroCopy-state x86)))
    (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86))))
  :hints (("Goal" :in-theory (e/d* (pml4-table-base-addr-projection
                                    pml4-table-base-addr)
                                   (rewire_dst_to_src-effects-preconditions)))))

(defthmd source-pml4-table-entry-addr-pas-projection
  (implies
   (rewire_dst_to_src-effects-preconditions x86)
   (and
    (equal
     (mv-nth 0
             (las-to-pas
              8 (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86))
              :r (zeroCopy-state x86)))
     (mv-nth 0
             (las-to-pas
              8 (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86))
              :r x86)))
    (equal
     (mv-nth 1
             (las-to-pas
              8 (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86))
              :r (zeroCopy-state x86)))
     (mv-nth 1
             (las-to-pas
              8 (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86))
              :r x86)))))
  :hints (("Goal" :in-theory (e/d* (page-size direct-map-p)
                                   ()))))

(defthmd source-pml4-table-entry-addr-xlation-projection
  ;; Why did I need this?
  (implies
   (rewire_dst_to_src-effects-preconditions x86)
   (equal
    (all-xlation-governing-entries-paddrs
     8
     (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86))
     (zeroCopy-state x86))
    (all-xlation-governing-entries-paddrs
     8
     (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86))
     x86)))
  :hints (("Goal" :in-theory (e/d* (page-size direct-map-p) ()))))

(local
 (encapsulate
   ()

   (local (include-book "arithmetic-5/top" :dir :system))

   (defthm dumb-unsigned-byte-p-rule-for-page-dir-ptr-table-entry-addr
     (implies (integerp x)
              (unsigned-byte-p 52 (ash (loghead 40 x) 12)))
     :hints (("Goal" :in-theory (e/d* (unsigned-byte-p loghead) ()))))))

(defthmd source-pml4-table-entry-projection
  (implies
   (and (rewire_dst_to_src-effects-preconditions x86)
        (more-stack-containing-return-address-and-source-PML4E-no-interfere-p x86)
        (more-destination-PDPTE-and-source-PML4E-no-interfere-p x86)
        (more-destination-PML4TE-and-source-PML4TE-no-interfere-p x86)
        (more-source-PDPTE-and-source-PML4E-no-interfere-p x86))
   (equal
    (mv-nth 1
            (rb 8
                (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86))
                :r
                (zeroCopy-state x86)))
    (mv-nth 1
            (rb 8
                (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86))
                :r x86))))
  :hints (("Goal"
           :in-theory (e/d* (pml4-table-base-addr-projection
                             disjoint-p-all-xlation-governing-entries-paddrs-subset-p
                             source-pml4-table-entry-addr-pas-projection
                             pml4-table-base-addr
                             page-dir-ptr-table-entry-addr-to-C-program-optimized-form
                             disjoint-p-all-xlation-governing-entries-paddrs-subset-p)
                            (unsigned-byte-p-52-of-left-shifting-a-40-bit-vector-by-12
                             two-mv-nth-1-las-to-pas-subset-p-disjoint-from-las-to-pas

                             rewrite-rb-to-rb-alt
                             las-to-pas-values-and-!flgi
                             create-canonical-address-list
                             gather-all-paging-structure-qword-addresses-!flgi
                             subset-p
                             (:meta acl2::mv-nth-cons-meta)
                             r-w-x-is-irrelevant-for-mv-nth-2-las-to-pas-when-no-errors
                             acl2::loghead-identity
                             mv-nth-1-rb-and-xlate-equiv-memory-disjoint-from-paging-structures
                             mv-nth-2-las-to-pas-system-level-non-marking-view
                             member-p-canonical-address-listp
                             xr-marking-view-mv-nth-2-las-to-pas
                             right-shift-to-logtail
                             (:rewrite mv-nth-1-las-to-pas-subset-p-disjoint-from-other-p-addrs)
                             (:rewrite greater-logbitp-of-unsigned-byte-p . 2)
                             (:rewrite bitops::logand-with-bitmask)
                             (:rewrite xw-xw-intra-simple-field-shadow-writes)
                             (:rewrite x86-run-opener-not-ms-not-zp-n)
                             (:type-prescription acl2::bitmaskp$inline)
                             (:rewrite x86-run-opener-not-ms-not-fault-zp-n)
                             (:definition ms$inline)
                             (:definition fault$inline)
                             (:rewrite gl::nfix-natp))))))

(defthmd destination-pml4-table-entry-addr-projection
  ;; Not really necessary because we have
  ;; pml4-table-base-addr-projection.
  (implies
   (rewire_dst_to_src-effects-preconditions x86)
   (equal
    (pml4-table-entry-addr (xr :rgf *rsi* x86)
                           (pml4-table-base-addr (zeroCopy-state x86)))
    (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86))))
  :hints (("Goal" :in-theory (e/d* (pml4-table-base-addr-projection)
                                   (rewire_dst_to_src-effects-preconditions)))))

(defthmd destination-pml4-table-entry-projection
  (implies
   (and
    (rewire_dst_to_src-effects-preconditions x86)
    (more-stack-containing-return-address-and-destination-PML4E-no-interfere-p x86)
    (more-destination-PDPTE-and-destination-PML4TE-no-interfere-p x86))

   (equal
    (mv-nth 1
            (rb 8
                (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86))
                :r
                (zeroCopy-state x86)))
    (mv-nth 1
            (rb 8
                (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86))
                :r x86))))
  :hints (("Goal"
           :in-theory
           (e/d* (pml4-table-base-addr-projection
                  pml4-table-base-addr
                  disjoint-p-all-xlation-governing-entries-paddrs-subset-p
                  page-dir-ptr-table-entry-addr-to-C-program-optimized-form)
                 (two-mv-nth-1-las-to-pas-subset-p-disjoint-from-las-to-pas
                  rewrite-rb-to-rb-alt
                  las-to-pas-values-and-!flgi
                  create-canonical-address-list
                  gather-all-paging-structure-qword-addresses-!flgi
                  subset-p
                  (:meta acl2::mv-nth-cons-meta)
                  r-w-x-is-irrelevant-for-mv-nth-2-las-to-pas-when-no-errors
                  acl2::loghead-identity
                  mv-nth-1-rb-and-xlate-equiv-memory-disjoint-from-paging-structures
                  mv-nth-2-las-to-pas-system-level-non-marking-view
                  member-p-canonical-address-listp
                  xr-marking-view-mv-nth-2-las-to-pas
                  right-shift-to-logtail
                  (:rewrite mv-nth-1-las-to-pas-subset-p-disjoint-from-other-p-addrs)
                  (:rewrite greater-logbitp-of-unsigned-byte-p . 2)
                  (:rewrite bitops::logand-with-bitmask)
                  (:rewrite xw-xw-intra-simple-field-shadow-writes)
                  (:rewrite x86-run-opener-not-ms-not-zp-n)
                  (:type-prescription acl2::bitmaskp$inline)
                  (:rewrite x86-run-opener-not-ms-not-fault-zp-n)
                  (:definition ms$inline)
                  (:definition fault$inline)
                  (:rewrite gl::nfix-natp))))))

(in-theory (e/d () (pml4-table-base-addr pml4-table-entry-addr)))

;; Theorems about the Source and Destination PDPT Entries:

(defthm pdpt-base-addr-after-mv-nth-2-las-to-pas
  ;; Similar to mv-nth-1-rb-after-mv-nth-2-las-to-pas.
  (implies
   (and
    (disjoint-p
     (mv-nth
      1
      (las-to-pas 8 (pml4-table-entry-addr
                     lin-addr (pml4-table-base-addr (double-rewrite x86)))
                  :r (double-rewrite x86)))
     (all-xlation-governing-entries-paddrs
      n-2 lin-addr-2 (double-rewrite x86)))
    (disjoint-p
     (mv-nth
      1
      (las-to-pas 8
                  (pml4-table-entry-addr lin-addr (pml4-table-base-addr x86))
                  :r (double-rewrite x86)))
     (all-xlation-governing-entries-paddrs
      8
      (pml4-table-entry-addr lin-addr (pml4-table-base-addr (double-rewrite x86)))
      (double-rewrite x86)))
    (64-bit-modep x86) ; added
    (not (xr :app-view 0 x86)))
   (equal (pdpt-base-addr lin-addr (mv-nth 2 (las-to-pas n-2 lin-addr-2 r-w-x-2 x86)))
          (pdpt-base-addr lin-addr (double-rewrite x86))))
  :hints (("Goal" :in-theory (e/d* (pdpt-base-addr) (force (force))))))

(defthm pdpt-base-addr-after-mv-nth-1-wb
  ;; Similar to rb-wb-disjoint-in-sys-view
  (implies
   (and
    (disjoint-p
     (mv-nth 1 (las-to-pas n-w write-addr :w (double-rewrite x86)))
     (mv-nth
      1
      (las-to-pas 8
                  (pml4-table-entry-addr lin-addr (pml4-table-base-addr x86))
                  :r (double-rewrite x86))))
    (disjoint-p
     (mv-nth
      1
      (las-to-pas 8
                  (pml4-table-entry-addr lin-addr (pml4-table-base-addr x86))
                  :r (double-rewrite x86)))
     (all-xlation-governing-entries-paddrs
      n-w write-addr (double-rewrite x86)))
    (disjoint-p
     (mv-nth
      1
      (las-to-pas 8
                  (pml4-table-entry-addr lin-addr (pml4-table-base-addr x86))
                  :r (double-rewrite x86)))
     (all-xlation-governing-entries-paddrs
      8
      (pml4-table-entry-addr lin-addr (pml4-table-base-addr x86))
      (double-rewrite x86)))
    (disjoint-p
     (mv-nth 1 (las-to-pas n-w write-addr :w (double-rewrite x86)))
     (all-xlation-governing-entries-paddrs
      8
      (pml4-table-entry-addr lin-addr (pml4-table-base-addr x86))
      (double-rewrite x86)))
    (64-bit-modep x86) ; added
    (not (app-view x86)))
   (equal (pdpt-base-addr lin-addr (mv-nth 1 (wb n-w write-addr w value x86)))
          (pdpt-base-addr lin-addr (double-rewrite x86))))
  :hints (("Goal" :in-theory (e/d* (pdpt-base-addr)
                                   (force (force))))))

(defthmd source-pdpt-base-addr-projection
  (implies (and (rewire_dst_to_src-effects-preconditions x86)
                (more-stack-containing-return-address-and-source-PML4E-no-interfere-p x86)
                (more-destination-PDPTE-and-source-PML4E-no-interfere-p x86)
                (more-destination-PML4TE-and-source-PML4TE-no-interfere-p x86)
                (more-source-PDPTE-and-source-PML4E-no-interfere-p x86))
           (equal
            (pdpt-base-addr (xr :rgf *rdi* x86) (zeroCopy-state x86))
            (pdpt-base-addr (xr :rgf *rdi* x86) x86)))
  :hints (("Goal"
           :in-theory (e/d* (pdpt-base-addr
                             pml4-table-base-addr-projection
                             source-pml4-table-entry-projection)
                            (rewire_dst_to_src-effects-preconditions-defs
                             zeroCopy-state)))))

(defthmd destination-pdpt-base-addr-projection
  (implies
   (and (rewire_dst_to_src-effects-preconditions x86)
        (more-stack-containing-return-address-and-destination-PML4E-no-interfere-p x86)
        (more-destination-PDPTE-and-destination-PML4TE-no-interfere-p x86))
   (equal
    (pdpt-base-addr (xr :rgf *rsi* x86) (zeroCopy-state x86))
    (pdpt-base-addr (xr :rgf *rsi* x86) x86)))
  :hints (("Goal"
           :in-theory (e/d* (pdpt-base-addr
                             pml4-table-base-addr-projection
                             destination-pml4-table-entry-projection)
                            (zeroCopy-state
                             rewire_dst_to_src-effects-preconditions-defs)))))

;; We don't need lemmas about page-dir-ptr-table-entry-addr from the
;; final state because page-dir-ptr-table-entry-addr is not defined in
;; terms of x86.
(in-theory (e/d () (page-dir-ptr-table-entry-addr pdpt-base-addr)))

;; ----------------------------------------------------------------------

;; Theorems about the projection of source addresses and data:

(local
 (defthmd preconditions-imply-disjoint-source-pas-from-xlation
   (implies
    (rewire_dst_to_src-effects-preconditions x86)
    (disjoint-p
     (mv-nth
      1
      (las-to-pas
       8
       (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86))
       :r x86))
     (all-xlation-governing-entries-paddrs
      8
      (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86))
      x86)))))

(defthmd source-pas-projection
  (implies
   (and (rewire_dst_to_src-effects-preconditions x86)
        ;; The physical addresses corresponding to destination
        ;; PDPTE are disjoint from the translation-governing
        ;; addresses of the source linear addresses.  Note
        ;; that this means that the destination PDPTE can't
        ;; serve as the PML4TE or PDPTE of the source.
        (disjoint-p
         (mv-nth
          1
          (las-to-pas
           8
           (page-dir-ptr-table-entry-addr
            (xr :rgf *rsi* x86)
            (pdpt-base-addr (xr :rgf *rsi* x86) x86))
           :w  x86))
         (all-xlation-governing-entries-paddrs
          *2^30* (xr :rgf *rdi* x86) x86)))
   (equal
    (mv-nth 1 (las-to-pas *2^30* (xr :rgf *rdi* x86) :r (zeroCopy-state x86)))
    (mv-nth 1 (las-to-pas *2^30* (xr :rgf *rdi* x86) :r x86))))
  :hints (("Goal"
           :in-theory (e/d* (pml4-table-base-addr-projection
                             source-pml4-table-entry-projection
                             source-pdpt-base-addr-projection
                             pdpt-base-addr pml4-table-base-addr
                             page-dir-ptr-table-entry-addr-to-C-program-optimized-form
                             disjoint-p-all-xlation-governing-entries-paddrs-subset-p)
                            (two-mv-nth-1-las-to-pas-subset-p-disjoint-from-las-to-pas
                             rewrite-rb-to-rb-alt
                             create-canonical-address-list
                             gather-all-paging-structure-qword-addresses-!flgi
                             subset-p
                             (:meta acl2::mv-nth-cons-meta)
                             r-w-x-is-irrelevant-for-mv-nth-2-las-to-pas-when-no-errors
                             acl2::loghead-identity
                             mv-nth-1-rb-and-xlate-equiv-memory-disjoint-from-paging-structures
                             mv-nth-2-las-to-pas-system-level-non-marking-view
                             member-p-canonical-address-listp
                             xr-marking-view-mv-nth-2-las-to-pas
                             right-shift-to-logtail
                             (:rewrite mv-nth-1-las-to-pas-subset-p-disjoint-from-other-p-addrs)
                             (:rewrite greater-logbitp-of-unsigned-byte-p . 2)
                             (:rewrite bitops::logand-with-bitmask)
                             (:rewrite xw-xw-intra-simple-field-shadow-writes)
                             (:rewrite x86-run-opener-not-ms-not-zp-n)
                             (:type-prescription acl2::bitmaskp$inline)
                             (:rewrite x86-run-opener-not-ms-not-fault-zp-n)
                             (:definition ms$inline)
                             (:definition fault$inline)
                             (:rewrite gl::nfix-natp))))))

(defthmd source-data-projection
  (implies
   (and (rewire_dst_to_src-effects-preconditions x86)
        ;; The physical addresses corresponding to destination
        ;; PDPTE are disjoint from the translation-governing
        ;; addresses of the source linear addresses.  Note
        ;; that this means that the destination PDPTE can't
        ;; serve as the PML4TE or PDPTE of the source.
        (disjoint-p
         (mv-nth
          1
          (las-to-pas
           8
           (page-dir-ptr-table-entry-addr
            (xr :rgf *rsi* x86)
            (pdpt-base-addr (xr :rgf *rsi* x86) x86))
           :w  x86))
         (all-xlation-governing-entries-paddrs
          *2^30* (xr :rgf *rdi* x86) x86))

        ;; The physical addresses corresponding to destination
        ;; PDPTE are disjoint from the source physical
        ;; addresses.
        (disjoint-p
         (mv-nth
          1
          (las-to-pas
           8
           (page-dir-ptr-table-entry-addr
            (xr :rgf *rsi* x86)
            (pdpt-base-addr (xr :rgf *rsi* x86) x86))
           :w  x86))
         (mv-nth 1
                 (las-to-pas *2^30* (xr :rgf *rdi* x86)
                             :r  x86)))

        ;; The source physical addresses are disjoint from the
        ;; paging structures.
        (disjoint-p$
         (mv-nth 1
                 (las-to-pas *2^30* (xr :rgf *rdi* x86)
                             :r  x86))
         (open-qword-paddr-list
          (gather-all-paging-structure-qword-addresses x86)))

        ;; The stack is disjoint from the source physical
        ;; addresses.
        (disjoint-p
         (mv-nth
          1
          (las-to-pas
           8 (+ -24 (xr :rgf *rsp* x86))
           :w  x86))
         (mv-nth 1
                 (las-to-pas *2^30* (xr :rgf *rdi* x86)
                             :r  x86))))

   (equal
    (mv-nth 1 (rb *2^30* (xr :rgf *rdi* x86) :r (zeroCopy-state x86)))
    (mv-nth 1 (rb *2^30* (xr :rgf *rdi* x86) :r x86))))
  :hints (("Goal"
           :in-theory (e/d*
                       (page-dir-ptr-table-entry-addr-to-C-program-optimized-form
                        source-pdpt-base-addr-projection
                        pdpt-base-addr pml4-table-base-addr
                        disjoint-p-all-xlation-governing-entries-paddrs-subset-p
                        pml4-table-base-addr-projection
                        source-pml4-table-entry-projection
                        source-pas-projection
                        disjoint-p-all-xlation-governing-entries-paddrs-subset-p)

                       (two-mv-nth-1-las-to-pas-subset-p-disjoint-from-las-to-pas

                        rewrite-rb-to-rb-alt
                        create-canonical-address-list
                        gather-all-paging-structure-qword-addresses-!flgi
                        subset-p
                        (:meta acl2::mv-nth-cons-meta)
                        r-w-x-is-irrelevant-for-mv-nth-2-las-to-pas-when-no-errors
                        acl2::loghead-identity
                        mv-nth-1-rb-and-xlate-equiv-memory-disjoint-from-paging-structures
                        mv-nth-2-las-to-pas-system-level-non-marking-view
                        member-p-canonical-address-listp
                        xr-marking-view-mv-nth-2-las-to-pas
                        right-shift-to-logtail
                        (:rewrite mv-nth-1-las-to-pas-subset-p-disjoint-from-other-p-addrs)
                        (:rewrite greater-logbitp-of-unsigned-byte-p . 2)
                        (:rewrite bitops::logand-with-bitmask)
                        (:rewrite xw-xw-intra-simple-field-shadow-writes)
                        (:rewrite x86-run-opener-not-ms-not-zp-n)
                        (:type-prescription acl2::bitmaskp$inline)
                        (:rewrite x86-run-opener-not-ms-not-fault-zp-n)
                        (:definition ms$inline)
                        (:definition fault$inline)
                        (:rewrite gl::nfix-natp)
                        (:type-prescription bitops::logior-natp-type)
                        (:type-prescription bitops::logand-natp-type-1)
                        (:rewrite mv-nth-1-las-to-pas-returns-nil-when-error)
                        infer-disjointness-with-all-xlation-governing-entries-paddrs-from-gather-all-paging-structure-qword-addresses-1
                        infer-disjointness-with-all-xlation-governing-entries-paddrs-from-gather-all-paging-structure-qword-addresses-with-disjoint-p$
                        combine-mv-nth-2-las-to-pas-same-r-w-x
                        loghead-zero-smaller
                        pdpt-base-addr-after-mv-nth-2-las-to-pas
                        las-to-pas-values-1g-pages-and-wb-to-page-dir-ptr-table-entry-addr
                        rb-and-rm-low-64-for-direct-map
                        all-xlation-governing-entries-paddrs-1g-pages-and-wb-to-page-dir-ptr-table-entry-addr
                        xr-ctr-mv-nth-2-las-to-pas
                        direct-map-p-and-wb-disjoint-from-xlation-governing-addrs)))))

(defthmd source-data-from-initial-state-in-terms-of-read-from-physical-memory-and-las-to-pas
  (implies
   (and (64-bit-modep x86) ; added
        (rewire_dst_to_src-effects-preconditions x86)
        (disjoint-p$
         (mv-nth 1 (las-to-pas *2^30* (xr :rgf *rdi* x86) :r x86))
         (open-qword-paddr-list
          (gather-all-paging-structure-qword-addresses x86))))
   (equal
    (mv-nth 1 (rb *2^30* (xr :rgf *rdi* x86) :r x86))
    (read-from-physical-memory
     (mv-nth 1 (las-to-pas *2^30* (xr :rgf *rdi* x86) :r x86))
     x86)))
  :instructions
  (:pro (:dv 1 2)
        :x :top (:dv 1 2)
        (:dv 1 0)
        (:= nil)
        :top (:dv 1 2)
        :s (:dv 1)
        (:= nil)
        :top (:dv 1)
        :s :top (:dv 1)
        (:rewrite read-from-physical-memory-and-mv-nth-2-las-to-pas)
        :top
        :bash :bash))

(defthmd source-data-from-initial-state-in-terms-of-read-from-physical-memory-and-addr-range
  (implies
   (and (64-bit-modep x86) ; added
        (rewire_dst_to_src-effects-preconditions x86)
        (source-data-preconditions x86))
   (equal
    (mv-nth 1 (rb *2^30* (xr :rgf *rdi* x86) :r x86))
    (read-from-physical-memory
     (addr-range
      *2^30*
      (ash
       (loghead
        22
        (logtail
         30
         (rm-low-64
          (page-dir-ptr-table-entry-addr
           (xr :rgf *rdi* x86)
           (pdpt-base-addr (xr :rgf *rdi* x86) x86))
          x86)))
       30))
     x86)))
  :instructions
  (:pro
   (:dv 1)
   (:rewrite
    source-data-from-initial-state-in-terms-of-read-from-physical-memory-and-las-to-pas)
   :top
   (:change-goal nil t)
   (:= t)
   (:dv 1 1)
   (:rewrite
    las-to-pas-values-for-same-1g-page
    ((page-dir-ptr-table-entry
      (mv-nth
       1
       (rb
        8
        (page-dir-ptr-table-entry-addr (xr :rgf *rdi* x86)
                                       (pdpt-base-addr (xr :rgf *rdi* x86)
                                                       (double-rewrite x86)))
        :r (double-rewrite x86))))
     (page-dir-ptr-table-entry-addr
      (page-dir-ptr-table-entry-addr (xr :rgf *rdi* x86)
                                     (pdpt-base-addr (xr :rgf *rdi* x86)
                                                     (double-rewrite x86))))
     (pdpt-base-addr (pdpt-base-addr (xr :rgf *rdi* x86)
                                     (double-rewrite x86)))
     (pml4-table-entry-addr
      (pml4-table-entry-addr (xr :rgf *rdi* x86)
                             (pml4-table-base-addr (double-rewrite x86))))
     (pml4-table-base-addr (pml4-table-base-addr (double-rewrite x86))))
    t)
   :top (:= t)
   :bash :bash :bash :bash :bash :bash
   :bash
   (:in-theory (e/d (page-size) nil))
   :bash
   (:change-goal nil t)
   :bash :bash :bash :bash :bash :bash (:dv 1)
   (:rewrite
    mv-nth-0-ia32e-la-to-pa-member-of-mv-nth-1-las-to-pas-if-lin-addr-member-p
    ((n *2^30*)
     (addr-1 (xr :rgf *rdi* x86)))
    t)
   :bash :bash :bash :bash :bash))

;; ----------------------------------------------------------------------

;; Theorems about the projection of destination addresses and data:

;; I need
;; las-to-pas-values-1G-pages-and-wb-to-page-dir-ptr-table-entry-addr,
;; all-xlation-governing-entries-paddrs-1G-pages-and-wb-to-page-dir-ptr-table-entry-addr,
;; and rb-values-1G-pages-and-wb-to-page-dir-ptr-table-entry-addr.

(local
 (defthmd destination-pdpte-is-in-all-paging-structures
   (implies
    (and
     (x86-state-okp x86)
     (destination-addresses-ok-p x86)
     (destination-pml4te-ok-p x86)
     (direct-map-p
      8
      (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86))
      :r  x86))
    (subset-p
     (addr-range
      8 (page-dir-ptr-table-entry-addr
         (xr :rgf *rsi* x86)
         (pdpt-base-addr (xr :rgf *rsi* x86) x86)))
     (open-qword-paddr-list (gather-all-paging-structure-qword-addresses x86))))
   :hints
   (("Goal"
     :hands-off (disjoint-p)
     :in-theory (e/d* (direct-map-p pdpt-base-addr page-size)
                      (page-dir-ptr-table-entry-addr
                       page-dir-ptr-table-entry-addr-to-c-program-optimized-form))))))

(local
 (defthmd throwaway-destination-data-preconditions-lemma-helper
   (implies
    (and
     (x86-state-okp x86)
     (destination-addresses-ok-p x86)
     (destination-pml4te-ok-p x86)
     (direct-map-p
      8
      (pml4-table-entry-addr (xr :rgf *rsi* x86)
                             (pml4-table-base-addr x86))
      :r  x86)
     (disjoint-p$
      (addr-range
       *2^30*
       (ash (loghead 22
                     (logtail
                      30
                      (rm-low-64 (page-dir-ptr-table-entry-addr
                                  (xr :rgf *rdi* x86)
                                  (pdpt-base-addr (xr :rgf *rdi* x86) x86)) x86)))
            30))
      (open-qword-paddr-list (gather-all-paging-structure-qword-addresses x86))))
    (disjoint-p
     (addr-range
      *2^30*
      (ash (loghead 22
                    (logtail
                     30
                     (rm-low-64 (page-dir-ptr-table-entry-addr
                                 (xr :rgf *rdi* x86)
                                 (pdpt-base-addr (xr :rgf *rdi* x86) x86))
                                x86)))
           30))
     (addr-range
      8 (page-dir-ptr-table-entry-addr
         (xr :rgf *rsi* x86)
         (pdpt-base-addr (xr :rgf *rsi* x86) x86)))))
   :hints
   (("Goal"
     :hands-off (disjoint-p)
     :use ((:instance destination-pdpte-is-in-all-paging-structures)
           (:instance disjoint-p-subset-p
                      (x (addr-range
                          *2^30*
                          (ash (loghead 22
                                        (logtail
                                         30
                                         (rm-low-64 (page-dir-ptr-table-entry-addr
                                                     (xr :rgf *rdi* x86)
                                                     (pdpt-base-addr (xr :rgf *rdi* x86) x86)) x86)))
                               30)))
                      (y (open-qword-paddr-list (gather-all-paging-structure-qword-addresses x86)))
                      (a (addr-range
                          *2^30*
                          (ash (loghead 22
                                        (logtail
                                         30
                                         (rm-low-64 (page-dir-ptr-table-entry-addr
                                                     (xr :rgf *rdi* x86)
                                                     (pdpt-base-addr (xr :rgf *rdi* x86) x86)) x86)))
                               30)))
                      (b (addr-range
                          8 (page-dir-ptr-table-entry-addr
                             (xr :rgf *rsi* x86)
                             (pdpt-base-addr (xr :rgf *rsi* x86) x86))))))
     :in-theory (e/d* (disjoint-p$
                       subset-p subset-p-reflexive)
                      (disjoint-p-subset-p
                       page-dir-ptr-table-entry-addr
                       page-dir-ptr-table-entry-addr-to-c-program-optimized-form))))))

(local
 (defthmd throwaway-destination-data-preconditions-lemma
   (implies (and (rewire_dst_to_src-effects-preconditions x86)
                 (destination-data-preconditions x86))
            (throwaway-destination-data-preconditions x86))
   :hints (("Goal"
            :hands-off (disjoint-p)
            :use ((:instance throwaway-destination-data-preconditions-lemma-helper))
            :in-theory (e/d* (direct-map-p
                              disjoint-p$)
                             (rewrite-program-at-to-program-at-alt
                              (:rewrite mv-nth-0-las-to-pas-subset-p)
                              (:definition subset-p)
                              (:rewrite acl2::loghead-identity)
                              (:definition member-p)
                              (:rewrite page-dir-ptr-table-entry-addr-to-c-program-optimized-form)
                              (:rewrite subset-p-two-create-canonical-address-lists-general)
                              (:rewrite unsigned-byte-p-of-combine-bytes)
                              (:rewrite member-p-canonical-address-listp)
                              (:linear adding-7-to-page-dir-ptr-table-entry-addr)
                              (:rewrite greater-logbitp-of-unsigned-byte-p . 2)
                              (:linear *physical-address-size*p-page-dir-ptr-table-entry-addr)
                              (:linear size-of-combine-bytes)
                              (:linear unsigned-byte-p-of-combine-bytes)
                              (:rewrite cdr-create-canonical-address-list)
                              (:definition no-duplicates-p)
                              (:rewrite consp-mv-nth-1-las-to-pas)
                              (:rewrite member-p-of-not-a-consp)
                              (:definition create-canonical-address-list)
                              (:rewrite loghead-of-non-integerp)
                              (:rewrite default-+-2)
                              (:type-prescription acl2::|x < y  =>  0 < -x+y|)
                              (:rewrite acl2::equal-of-booleans-rewrite)
                              (:rewrite bitops::unsigned-byte-p-incr)
                              (:rewrite loghead-negative)
                              (:linear rip-is-i48p)
                              (:type-prescription subset-p)
                              (:rewrite default-+-1)
                              (:linear rgfi-is-i64p)
                              (:type-prescription member-p)
                              (:rewrite default-<-2)
                              (:type-prescription pdpt-base-addr)
                              (:rewrite default-<-1)
                              (:rewrite consp-of-create-canonical-address-list)
                              (:rewrite car-create-canonical-address-list)
                              (:meta acl2::cancel_plus-equal-correct)
                              (:meta acl2::cancel_times-equal-correct)
                              (:rewrite canonical-address-p-limits-thm-3)
                              (:rewrite subset-p-cdr-y)
                              (:rewrite member-p-cdr)
                              (:rewrite canonical-address-p-limits-thm-2)
                              (:meta acl2::cancel_plus-lessp-correct)
                              (:rewrite open-mv-nth-1-las-to-pas-for-same-1g-page-general-1)
                              (:rewrite canonical-address-p-limits-thm-0)
                              (:linear adding-7-to-pml4-table-entry-addr)
                              (:rewrite acl2::consp-when-member-equal-of-atom-listp)
                              (:rewrite member-p-of-subset-is-member-p-of-superset)
                              (:type-prescription adding-7-to-page-dir-ptr-table-entry-addr)
                              (:rewrite canonical-address-p-limits-thm-1)
                              (:rewrite member-p-and-mult-8-qword-paddr-listp)
                              (:rewrite default-cdr)
                              (:rewrite default-car)
                              (:linear *physical-address-size*p-pml4-table-entry-addr)
                              (:type-prescription booleanp)
                              (:rewrite subset-p-cdr-x)
                              (:linear ash-monotone-2)
                              (:rewrite rationalp-implies-acl2-numberp)
                              (:type-prescription consp-mv-nth-1-las-to-pas)
                              (:rewrite acl2::ash-0)
                              (:rewrite acl2::equal-constant-+)
                              (:definition combine-bytes)
                              (:type-prescription adding-7-to-pml4-table-entry-addr)
                              (:rewrite
                               mv-nth-0-ia32e-la-to-pa-member-of-mv-nth-1-las-to-pas-if-lin-addr-member-p)
                              (:rewrite acl2::zip-open)
                              (:type-prescription len)
                              (:rewrite rb-and-rm-low-64-for-direct-map)
                              (:rewrite car-mv-nth-1-las-to-pas)
                              (:definition open-qword-paddr-list)
                              (:rewrite rewrite-rb-to-rb-alt)
                              (:rewrite len-of-create-canonical-address-list)
                              (:definition addr-range)
                              (:definition byte-listp)
                              (:rewrite acl2::member-of-cons)
                              (:definition binary-append)
                              (:rewrite acl2::ifix-when-not-integerp)
                              (:definition len)
                              (:meta acl2::mv-nth-cons-meta)
                              (:linear acl2::expt->-1)
                              (:rewrite acl2::append-when-not-consp)
                              (:type-prescription bitops::ash-natp-type)
                              (:linear member-p-pos-value)
                              (:linear member-p-pos-1-value)
                              (:linear acl2::index-of-<-len)
                              (:rewrite
                               mv-nth-1-ia32e-la-to-pa-member-of-mv-nth-1-las-to-pas-if-lin-addr-member-p)
                              (:definition n08p$inline)
                              (:rewrite mv-nth-1-las-to-pas-when-error)
                              (:rewrite commutativity-of-+)
                              (:linear mv-nth-1-idiv-spec)
                              (:linear mv-nth-1-div-spec)
                              (:rewrite neg-addr-range=nil)
                              (:rewrite bitops::logbitp-nonzero-of-bit)
                              (:rewrite right-shift-to-logtail)
                              (:type-prescription combine-bytes)
                              (:type-prescription ifix)
                              (:rewrite car-addr-range)
                              (:type-prescription zip)
                              (:type-prescription gather-all-paging-structure-qword-addresses)
                              (:rewrite unsigned-byte-p-of-logtail)
                              ;; (:linear combine-bytes-size-for-rml64-app-view)
                              (:rewrite acl2::subsetp-member . 2)
                              (:rewrite acl2::subsetp-member . 1)
                              (:rewrite acl2::logtail-identity)
                              (:rewrite cdr-addr-range)
                              (:rewrite ia32e-la-to-pa-in-app-view)
                              (:rewrite canonical-address-p-rip)
                              (:type-prescription n64p-rm-low-64)
                              (:rewrite
                               mv-nth-1-rb-and-xlate-equiv-memory-disjoint-from-paging-structures)
                              (:rewrite mv-nth-1-ia32e-la-to-pa-when-error)
                              (:rewrite bitops::logbitp-when-bitmaskp)
                              (:type-prescription signed-byte-p)
                              (:type-prescription n52p-mv-nth-1-ia32e-la-to-pa)
                              (:rewrite acl2::logext-identity)
                              (:rewrite open-mv-nth-0-las-to-pas-for-same-1g-page-general-2)
                              (:rewrite acl2::expt-with-violated-guards)
                              (:rewrite no-duplicates-p-and-append)
                              (:type-prescription bitp)
                              (:type-prescription acl2::bitmaskp$inline)
                              (:rewrite loghead-30-of-1g-aligned-lin-addr-+-n-2)
                              (:rewrite rm-low-64-in-app-view)
                              (:type-prescription natp)
                              (:rewrite bitops::signed-byte-p-when-unsigned-byte-p-smaller)
                              (:rewrite bitops::signed-byte-p-when-signed-byte-p-smaller)
                              (:rewrite bitops::signed-byte-p-monotonicity)
                              (:type-prescription member-equal)
                              (:linear acl2::expt-is-increasing-for-base>1)
                              (:definition member-equal)
                              (:rewrite subset-p-cons-member-p-lemma)
                              (:rewrite not-member-p-when-disjoint-p)
                              (:rewrite bitops::normalize-logbitp-when-mods-equal)
                              (:rewrite bitops::logbitp-of-negative-const)
                              (:rewrite bitops::logbitp-of-mask)
                              (:rewrite bitops::logbitp-of-const)
                              (:rewrite greater-logbitp-of-unsigned-byte-p . 1)
                              (:meta bitops::open-logbitp-of-const-lite-meta)
                              (:rewrite
                               xlate-equiv-structures-and-logtail-30-rm-low-64-with-page-dir-ptr-table-entry-addr)
                              (:rewrite
                               all-mem-except-paging-structures-equal-aux-and-rm-low-64-from-rest-of-memory)
                              (:rewrite
                               all-mem-except-paging-structures-equal-and-rm-low-64-from-rest-of-memory)
                              (:linear bitops::expt-2-lower-bound-by-logbitp)))))))

(def-gl-export entry-attributes-unchanged-when-destination-PDPTE-modified
  :hyp (and (unsigned-byte-p 64 dest-pdpte)
            (unsigned-byte-p 64 src-pdpte))
  :concl (and
          (equal (page-present (logior (logand 18442240475155922943 dest-pdpte)
                                       (logand 4503598553628672 src-pdpte)))
                 (page-present dest-pdpte))
          (equal (page-read-write (logior (logand 18442240475155922943 dest-pdpte)
                                          (logand 4503598553628672 src-pdpte)))
                 (page-read-write dest-pdpte))
          (equal (page-user-supervisor (logior (logand 18442240475155922943 dest-pdpte)
                                               (logand 4503598553628672 src-pdpte)))
                 (page-user-supervisor dest-pdpte))
          (equal (page-execute-disable (logior (logand 18442240475155922943 dest-pdpte)
                                               (logand 4503598553628672 src-pdpte)))
                 (page-execute-disable dest-pdpte))
          (equal (page-size (logior (logand 18442240475155922943 dest-pdpte)
                                    (logand 4503598553628672 src-pdpte)))
                 (page-size dest-pdpte)))
  :g-bindings
  (gl::auto-bindings (:mix (:nat src-pdpte 64) (:nat dest-pdpte 64))))

(defthm pml4-table-base-addr-and-mv-nth-2-las-to-pas
  ;; I shouldn't need this lemma --- this should follow directly from
  ;; xlate-equiv-memory-and-pml4-table-base-addr and
  ;; xlate-equiv-memory-with-mv-nth-2-las-to-pas.
  (implies (64-bit-modep x86)
           (equal (pml4-table-base-addr (mv-nth 2 (las-to-pas l-addrs r-w-x cpl x86)))
                  (pml4-table-base-addr (double-rewrite x86)))))

(local
 (defthm translation-of-destination-pml4-table-entry-from-final-state-is-error-free
   (implies
    (and (rewire_dst_to_src-effects-preconditions x86)
         (disjoint-p
          (mv-nth 1 (las-to-pas
                     8 (+ -24 (xr :rgf *rsp* x86)) :w x86))
          (all-xlation-governing-entries-paddrs
           8
           (page-dir-ptr-table-entry-addr
            (xr :rgf *rsi* x86)
            (pdpt-base-addr (xr :rgf *rsi* x86) x86))
           x86))
         (disjoint-p
          (mv-nth
           1
           (las-to-pas
            8
            (page-dir-ptr-table-entry-addr
             (xr :rgf *rsi* x86)
             (pdpt-base-addr (xr :rgf *rsi* x86) x86))
            :w x86))
          (all-xlation-governing-entries-paddrs
           8
           (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86))
           x86)))
    (equal
     (mv-nth
      0 (las-to-pas
         8 (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86))
         :r
         (zeroCopy-state x86)))
     nil))
   :hints
   (("Goal"
     :in-theory
     (e/d*
      (pml4-table-base-addr-projection
       disjoint-p-all-xlation-governing-entries-paddrs-subset-p
       pml4-table-base-addr pdpt-base-addr
       page-dir-ptr-table-entry-addr-to-c-program-optimized-form
       disjoint-p-all-xlation-governing-entries-paddrs-subset-p)
      (two-mv-nth-1-las-to-pas-subset-p-disjoint-from-las-to-pas
       rewrite-rb-to-rb-alt
       gather-all-paging-structure-qword-addresses-!flgi
       subset-p (:meta acl2::mv-nth-cons-meta)
       r-w-x-is-irrelevant-for-mv-nth-2-las-to-pas-when-no-errors
       acl2::loghead-identity
       mv-nth-1-rb-and-xlate-equiv-memory-disjoint-from-paging-structures
       mv-nth-2-las-to-pas-system-level-non-marking-view
       member-p-canonical-address-listp
       xr-marking-view-mv-nth-2-las-to-pas
       right-shift-to-logtail
       (:rewrite mv-nth-1-las-to-pas-subset-p-disjoint-from-other-p-addrs)
       (:rewrite greater-logbitp-of-unsigned-byte-p . 2)
       (:rewrite bitops::logand-with-bitmask)
       (:rewrite xw-xw-intra-simple-field-shadow-writes)
       (:rewrite x86-run-opener-not-ms-not-zp-n)
       (:type-prescription acl2::bitmaskp$inline)
       (:rewrite x86-run-opener-not-ms-not-fault-zp-n)
       (:definition ms$inline)
       (:definition fault$inline)
       (:rewrite gl::nfix-natp)
       mv-nth-0-las-to-pas-subset-p))))))

(local
 (defthmd translation-of-destination-addresses-helper-1
   (implies
    (and (rewire_dst_to_src-effects-preconditions x86)
         (destination-data-preconditions x86)
         (direct-map-p 8
                       (page-dir-ptr-table-entry-addr
                        (xr :rgf *rsi* x86)
                        (pdpt-base-addr (xr :rgf *rsi* x86) x86))
                       :r x86)
         ;; From destination-PDPTE-and-program-no-interfere-p:
         (disjoint-p
          (mv-nth 1 (las-to-pas
                     8
                     (page-dir-ptr-table-entry-addr
                      (xr :rgf *rsi* x86)
                      (pdpt-base-addr (xr :rgf *rsi* x86) x86))
                     :w x86))
          (all-xlation-governing-entries-paddrs
           *rewire_dst_to_src-len* (xr :rip 0 x86) x86))
         ;; From destination-PDPTE-ok-p:
         (disjoint-p
          (mv-nth 1 (las-to-pas
                     8
                     (page-dir-ptr-table-entry-addr
                      (xr :rgf *rsi* x86)
                      (pdpt-base-addr (xr :rgf *rsi* x86) x86))
                     :r x86))
          (all-xlation-governing-entries-paddrs
           8
           (page-dir-ptr-table-entry-addr
            (xr :rgf *rsi* x86)
            (pdpt-base-addr (xr :rgf *rsi* x86) x86))
           x86))
         ;; From destination-PDPTE-and-stack-no-interfere-p:
         ;; (but commuted)
         (disjoint-p
          (mv-nth 1 (las-to-pas
                     8
                     (page-dir-ptr-table-entry-addr
                      (xr :rgf *rsi* x86)
                      (pdpt-base-addr (xr :rgf *rsi* x86) x86))
                     :r x86))
          (mv-nth 1 (las-to-pas
                     8 (+ -24 (xr :rgf *rsp* x86)) :w x86))))
    (equal
     (mv-nth 1 (las-to-pas *2^30* (xr :rgf *rsi* x86) :r (zeroCopy-state x86)))
     (addr-range
      *2^30*
      (ash (loghead 22
                    (logtail
                     30
                     (rm-low-64
                      (page-dir-ptr-table-entry-addr
                       (xr :rgf *rdi* x86)
                       (pdpt-base-addr (xr :rgf *rdi* x86) x86))
                      x86)))
           30))))
   :hints
   (("Goal"
     :in-theory
     (e/d*
      (direct-map-p
       page-present
       page-size
       pml4-table-base-addr-projection
       disjoint-p-all-xlation-governing-entries-paddrs-subset-p
       pml4-table-base-addr pdpt-base-addr
       page-dir-ptr-table-entry-addr-to-c-program-optimized-form
       disjoint-p-all-xlation-governing-entries-paddrs-subset-p)
      (two-mv-nth-1-las-to-pas-subset-p-disjoint-from-las-to-pas
       rewrite-rb-to-rb-alt
       gather-all-paging-structure-qword-addresses-!flgi
       subset-p
       (:meta acl2::mv-nth-cons-meta)
       r-w-x-is-irrelevant-for-mv-nth-2-las-to-pas-when-no-errors
       mv-nth-1-rb-and-xlate-equiv-memory-disjoint-from-paging-structures
       mv-nth-2-las-to-pas-system-level-non-marking-view
       member-p-canonical-address-listp
       xr-marking-view-mv-nth-2-las-to-pas
       (:rewrite mv-nth-1-las-to-pas-subset-p-disjoint-from-other-p-addrs)
       (:rewrite xw-xw-intra-simple-field-shadow-writes)
       (:rewrite x86-run-opener-not-ms-not-zp-n)
       (:rewrite x86-run-opener-not-ms-not-fault-zp-n)
       (:definition ms$inline)
       (:definition fault$inline)
       (:rewrite gl::nfix-natp)
       mv-nth-0-las-to-pas-subset-p
       (tau-system)))))))

(local
 (defthmd translation-of-destination-addresses-helper-2
   (implies
    (and (rewire_dst_to_src-effects-preconditions x86)
         (destination-data-preconditions x86)
         (direct-map-p 8
                       (page-dir-ptr-table-entry-addr
                        (xr :rgf *rsi* x86)
                        (pdpt-base-addr (xr :rgf *rsi* x86) x86))
                       :r x86)
         ;; From destination-PDPTE-and-program-no-interfere-p:
         (disjoint-p
          (mv-nth 1 (las-to-pas
                     8
                     (page-dir-ptr-table-entry-addr
                      (xr :rgf *rsi* x86)
                      (pdpt-base-addr (xr :rgf *rsi* x86) x86))
                     :w x86))
          (all-xlation-governing-entries-paddrs
           *rewire_dst_to_src-len* (xr :rip 0 x86) x86))
         ;; From destination-PDPTE-ok-p:
         (disjoint-p
          (mv-nth 1 (las-to-pas
                     8
                     (page-dir-ptr-table-entry-addr
                      (xr :rgf *rsi* x86)
                      (pdpt-base-addr (xr :rgf *rsi* x86) x86))
                     :r x86))
          (all-xlation-governing-entries-paddrs
           8
           (page-dir-ptr-table-entry-addr
            (xr :rgf *rsi* x86)
            (pdpt-base-addr (xr :rgf *rsi* x86) x86))
           x86))
         ;; From destination-PDPTE-and-stack-no-interfere-p:
         ;; (but commuted)
         (disjoint-p
          (mv-nth 1 (las-to-pas
                     8
                     (page-dir-ptr-table-entry-addr
                      (xr :rgf *rsi* x86)
                      (pdpt-base-addr (xr :rgf *rsi* x86) x86))
                     :r x86))
          (mv-nth 1 (las-to-pas
                     8 (+ -24 (xr :rgf *rsp* x86)) :w x86))))
    (equal
     (mv-nth 0 (las-to-pas *2^30* (xr :rgf *rsi* x86) :r (zeroCopy-state x86)))
     nil))
   :hints
   (("Goal"
     :in-theory
     (e/d*
      (direct-map-p
       page-present
       page-size
       pml4-table-base-addr-projection
       disjoint-p-all-xlation-governing-entries-paddrs-subset-p
       pml4-table-base-addr pdpt-base-addr
       page-dir-ptr-table-entry-addr-to-c-program-optimized-form
       disjoint-p-all-xlation-governing-entries-paddrs-subset-p)
      (two-mv-nth-1-las-to-pas-subset-p-disjoint-from-las-to-pas
       rewrite-rb-to-rb-alt
       gather-all-paging-structure-qword-addresses-!flgi
       subset-p
       (:meta acl2::mv-nth-cons-meta)
       r-w-x-is-irrelevant-for-mv-nth-2-las-to-pas-when-no-errors
       mv-nth-1-rb-and-xlate-equiv-memory-disjoint-from-paging-structures
       mv-nth-2-las-to-pas-system-level-non-marking-view
       member-p-canonical-address-listp
       xr-marking-view-mv-nth-2-las-to-pas
       (:rewrite mv-nth-1-las-to-pas-subset-p-disjoint-from-other-p-addrs)
       (:rewrite xw-xw-intra-simple-field-shadow-writes)
       (:rewrite x86-run-opener-not-ms-not-zp-n)
       (:rewrite x86-run-opener-not-ms-not-fault-zp-n)
       (:definition ms$inline)
       (:definition fault$inline)
       (:rewrite gl::nfix-natp)
       mv-nth-0-las-to-pas-subset-p
       (tau-system)))))))

(defthm translation-of-destination-addresses
  (implies
   (and (rewire_dst_to_src-effects-preconditions x86)
        (destination-data-preconditions x86)
        (direct-map-p 8
                      (page-dir-ptr-table-entry-addr
                       (xr :rgf *rsi* x86)
                       (pdpt-base-addr (xr :rgf *rsi* x86) x86))
                      :r x86)
        ;; From destination-PDPTE-and-program-no-interfere-p:
        (disjoint-p
         (mv-nth 1 (las-to-pas
                    8
                    (page-dir-ptr-table-entry-addr
                     (xr :rgf *rsi* x86)
                     (pdpt-base-addr (xr :rgf *rsi* x86) x86))
                    :w x86))
         (all-xlation-governing-entries-paddrs
          *rewire_dst_to_src-len* (xr :rip 0 x86) x86))
        ;; From destination-PDPTE-ok-p:
        (disjoint-p
         (mv-nth 1 (las-to-pas
                    8
                    (page-dir-ptr-table-entry-addr
                     (xr :rgf *rsi* x86)
                     (pdpt-base-addr (xr :rgf *rsi* x86) x86))
                    :r x86))
         (all-xlation-governing-entries-paddrs
          8
          (page-dir-ptr-table-entry-addr
           (xr :rgf *rsi* x86)
           (pdpt-base-addr (xr :rgf *rsi* x86) x86))
          x86))
        ;; From destination-PDPTE-and-stack-no-interfere-p:
        ;; (but commuted)
        (disjoint-p
         (mv-nth 1 (las-to-pas
                    8
                    (page-dir-ptr-table-entry-addr
                     (xr :rgf *rsi* x86)
                     (pdpt-base-addr (xr :rgf *rsi* x86) x86))
                    :r x86))
         (mv-nth 1 (las-to-pas
                    8 (+ -24 (xr :rgf *rsp* x86)) :w x86))))
   (and
    (equal (mv-nth 0 (las-to-pas *2^30* (xr :rgf *rsi* x86) :r (zeroCopy-state x86)))
           nil)
    (equal (mv-nth 1 (las-to-pas *2^30* (xr :rgf *rsi* x86) :r (zeroCopy-state x86)))
           (addr-range
            *2^30*
            (ash (loghead 22
                          (logtail
                           30
                           (rm-low-64
                            (page-dir-ptr-table-entry-addr
                             (xr :rgf *rdi* x86)
                             (pdpt-base-addr (xr :rgf *rdi* x86) x86))
                            x86)))
                 30)))))
  :hints
  (("Goal"
    :use ((:instance translation-of-destination-addresses-helper-1)
          (:instance translation-of-destination-addresses-helper-2))
    :in-theory
    (e/d*
     ()
     (rewire_dst_to_src-effects-preconditions
      two-mv-nth-1-las-to-pas-subset-p-disjoint-from-las-to-pas
      rewrite-rb-to-rb-alt
      gather-all-paging-structure-qword-addresses-!flgi
      subset-p
      (:meta acl2::mv-nth-cons-meta)
      r-w-x-is-irrelevant-for-mv-nth-2-las-to-pas-when-no-errors
      mv-nth-1-rb-and-xlate-equiv-memory-disjoint-from-paging-structures
      mv-nth-2-las-to-pas-system-level-non-marking-view
      member-p-canonical-address-listp
      xr-marking-view-mv-nth-2-las-to-pas
      (:rewrite mv-nth-1-las-to-pas-subset-p-disjoint-from-other-p-addrs)
      (:rewrite xw-xw-intra-simple-field-shadow-writes)
      (:rewrite x86-run-opener-not-ms-not-zp-n)
      (:rewrite x86-run-opener-not-ms-not-fault-zp-n)
      (:definition ms$inline)
      (:definition fault$inline)
      (:rewrite gl::nfix-natp)
      mv-nth-0-las-to-pas-subset-p
      (tau-system))))))

(local
 (defthmd destination-data-from-final-state-in-terms-of-read-from-physical-memory-and-addr-range-helper-1
   (implies
    (and (rewire_dst_to_src-effects-preconditions x86)
         (destination-data-preconditions x86)
         (direct-map-p 8
                       (page-dir-ptr-table-entry-addr
                        (xr :rgf *rsi* x86)
                        (pdpt-base-addr (xr :rgf *rsi* x86) x86))
                       :r x86)
         ;; From destination-PDPTE-and-program-no-interfere-p:
         (disjoint-p
          (mv-nth 1 (las-to-pas
                     8
                     (page-dir-ptr-table-entry-addr
                      (xr :rgf *rsi* x86)
                      (pdpt-base-addr (xr :rgf *rsi* x86) x86))
                     :w x86))
          (all-xlation-governing-entries-paddrs
           *rewire_dst_to_src-len* (xr :rip 0 x86) x86))
         ;; From destination-PDPTE-ok-p:
         (disjoint-p
          (mv-nth 1 (las-to-pas
                     8
                     (page-dir-ptr-table-entry-addr
                      (xr :rgf *rsi* x86)
                      (pdpt-base-addr (xr :rgf *rsi* x86) x86))
                     :r x86))
          (all-xlation-governing-entries-paddrs
           8
           (page-dir-ptr-table-entry-addr
            (xr :rgf *rsi* x86)
            (pdpt-base-addr (xr :rgf *rsi* x86) x86))
           x86))
         ;; From destination-PDPTE-and-stack-no-interfere-p:
         ;; (but commuted)
         (disjoint-p
          (mv-nth 1 (las-to-pas
                     8
                     (page-dir-ptr-table-entry-addr
                      (xr :rgf *rsi* x86)
                      (pdpt-base-addr (xr :rgf *rsi* x86) x86))
                     :r x86))
          (mv-nth 1 (las-to-pas
                     8 (+ -24 (xr :rgf *rsp* x86)) :w x86)))

         ;; !!

         (disjoint-p
          (addr-range
           *2^30*
           (ash (loghead 22
                         (logtail
                          30
                          (rm-low-64
                           (page-dir-ptr-table-entry-addr
                            (xr :rgf *rdi* x86)
                            (pdpt-base-addr (xr :rgf *rdi* x86) x86))
                           x86)))
                30))
          (all-xlation-governing-entries-paddrs
           8 (xr :rgf *rsp* x86) x86))
         (disjoint-p
          (addr-range
           *2^30*
           (ash (loghead 22
                         (logtail
                          30
                          (rm-low-64
                           (page-dir-ptr-table-entry-addr
                            (xr :rgf *rdi* x86)
                            (pdpt-base-addr (xr :rgf *rdi* x86) x86))
                           x86)))
                30))
          (all-xlation-governing-entries-paddrs
           *rewire_dst_to_src-len* (xr :rip 0 x86) x86))

         (disjoint-p
          (addr-range
           *2^30*
           (ash (loghead 22
                         (logtail
                          30
                          (rm-low-64
                           (page-dir-ptr-table-entry-addr
                            (xr :rgf *rdi* x86)
                            (pdpt-base-addr (xr :rgf *rdi* x86) x86))
                           x86)))
                30))
          (mv-nth 1 (las-to-pas
                     8
                     (page-dir-ptr-table-entry-addr
                      (xr :rgf *rsi* x86)
                      (pdpt-base-addr (xr :rgf *rsi* x86) x86))
                     :r x86)))

         (disjoint-p
          (addr-range
           *2^30*
           (ash (loghead 22
                         (logtail
                          30
                          (rm-low-64
                           (page-dir-ptr-table-entry-addr
                            (xr :rgf *rdi* x86)
                            (pdpt-base-addr (xr :rgf *rdi* x86) x86))
                           x86)))
                30))
          (all-xlation-governing-entries-paddrs
           8
           (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86))
           x86))
         (disjoint-p
          (addr-range
           *2^30*
           (ash (loghead 22
                         (logtail
                          30
                          (rm-low-64
                           (page-dir-ptr-table-entry-addr
                            (xr :rgf *rdi* x86)
                            (pdpt-base-addr (xr :rgf *rdi* x86) x86))
                           x86)))
                30))
          (all-xlation-governing-entries-paddrs
           8
           (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86))
           x86)))

    (equal
     (read-from-physical-memory
      (addr-range
       *2^30*
       (ash (loghead 22
                     (logtail
                      30
                      (rm-low-64
                       (page-dir-ptr-table-entry-addr
                        (xr :rgf *rdi* x86)
                        (pdpt-base-addr (xr :rgf *rdi* x86) x86))
                       x86)))
            30))
      (mv-nth 2
              (las-to-pas *2^30* (xr :rgf *rsi* x86)
                          :r
                          (zeroCopy-state x86))))
     (read-from-physical-memory
      (addr-range
       *2^30*
       (ash (loghead 22
                     (logtail
                      30
                      (rm-low-64
                       (page-dir-ptr-table-entry-addr
                        (xr :rgf *rdi* x86)
                        (pdpt-base-addr (xr :rgf *rdi* x86) x86))
                       x86)))
            30))
      x86)))
   :hints
   (("Goal"
     :in-theory
     (e/d*
      (direct-map-p
       page-present
       page-size
       pml4-table-base-addr-projection
       disjoint-p-all-xlation-governing-entries-paddrs-subset-p
       pml4-table-base-addr pdpt-base-addr
       page-dir-ptr-table-entry-addr-to-c-program-optimized-form
       disjoint-p-all-xlation-governing-entries-paddrs-subset-p)
      (two-mv-nth-1-las-to-pas-subset-p-disjoint-from-las-to-pas
       rewrite-rb-to-rb-alt
       gather-all-paging-structure-qword-addresses-!flgi
       subset-p
       (:meta acl2::mv-nth-cons-meta)
       r-w-x-is-irrelevant-for-mv-nth-2-las-to-pas-when-no-errors
       mv-nth-1-rb-and-xlate-equiv-memory-disjoint-from-paging-structures
       mv-nth-2-las-to-pas-system-level-non-marking-view
       member-p-canonical-address-listp
       xr-marking-view-mv-nth-2-las-to-pas
       (:rewrite mv-nth-1-las-to-pas-subset-p-disjoint-from-other-p-addrs)
       (:rewrite xw-xw-intra-simple-field-shadow-writes)
       (:rewrite x86-run-opener-not-ms-not-zp-n)
       (:rewrite x86-run-opener-not-ms-not-fault-zp-n)
       (:definition ms$inline)
       (:definition fault$inline)
       (:rewrite gl::nfix-natp)
       mv-nth-0-las-to-pas-subset-p
       size-of-read-from-physical-memory
       cdr-mv-nth-1-las-to-pas-no-error
       mv-nth-0-ia32e-la-to-pa-member-of-mv-nth-1-las-to-pas-if-lin-addr-member-p
       (tau-system)))))))

(local
 (defthmd destination-data-from-final-state-in-terms-of-read-from-physical-memory-and-addr-range-helper-2
   (implies
    (and (rewire_dst_to_src-effects-preconditions x86)
         (destination-data-preconditions x86)
         (direct-map-p 8
                       (page-dir-ptr-table-entry-addr
                        (xr :rgf *rsi* x86)
                        (pdpt-base-addr (xr :rgf *rsi* x86) x86))
                       :r x86)
         ;; From destination-PDPTE-and-program-no-interfere-p:
         (disjoint-p
          (mv-nth 1 (las-to-pas
                     8
                     (page-dir-ptr-table-entry-addr
                      (xr :rgf *rsi* x86)
                      (pdpt-base-addr (xr :rgf *rsi* x86) x86))
                     :w x86))
          (all-xlation-governing-entries-paddrs
           *rewire_dst_to_src-len* (xr :rip 0 x86) x86))
         ;; From destination-PDPTE-ok-p:
         (disjoint-p
          (mv-nth 1 (las-to-pas
                     8
                     (page-dir-ptr-table-entry-addr
                      (xr :rgf *rsi* x86)
                      (pdpt-base-addr (xr :rgf *rsi* x86) x86))
                     :r x86))
          (all-xlation-governing-entries-paddrs
           8
           (page-dir-ptr-table-entry-addr
            (xr :rgf *rsi* x86)
            (pdpt-base-addr (xr :rgf *rsi* x86) x86))
           x86))
         ;; From destination-PDPTE-and-stack-no-interfere-p:
         ;; (but commuted)
         (disjoint-p
          (mv-nth 1 (las-to-pas
                     8
                     (page-dir-ptr-table-entry-addr
                      (xr :rgf *rsi* x86)
                      (pdpt-base-addr (xr :rgf *rsi* x86) x86))
                     :r x86))
          (mv-nth 1 (las-to-pas
                     8 (+ -24 (xr :rgf *rsp* x86)) :w x86)))

         ;; !!

         (disjoint-p
          (addr-range
           *2^30*
           (ash (loghead 22
                         (logtail
                          30
                          (rm-low-64
                           (page-dir-ptr-table-entry-addr
                            (xr :rgf *rdi* x86)
                            (pdpt-base-addr (xr :rgf *rdi* x86) x86))
                           x86)))
                30))
          (all-xlation-governing-entries-paddrs
           8 (xr :rgf *rsp* x86) x86))
         (disjoint-p
          (addr-range
           *2^30*
           (ash (loghead 22
                         (logtail
                          30
                          (rm-low-64
                           (page-dir-ptr-table-entry-addr
                            (xr :rgf *rdi* x86)
                            (pdpt-base-addr (xr :rgf *rdi* x86) x86))
                           x86)))
                30))
          (all-xlation-governing-entries-paddrs
           *rewire_dst_to_src-len* (xr :rip 0 x86) x86))

         (disjoint-p
          (addr-range
           *2^30*
           (ash (loghead 22
                         (logtail
                          30
                          (rm-low-64
                           (page-dir-ptr-table-entry-addr
                            (xr :rgf *rdi* x86)
                            (pdpt-base-addr (xr :rgf *rdi* x86) x86))
                           x86)))
                30))
          (mv-nth 1 (las-to-pas
                     8
                     (page-dir-ptr-table-entry-addr
                      (xr :rgf *rsi* x86)
                      (pdpt-base-addr (xr :rgf *rsi* x86) x86))
                     :r x86)))

         (disjoint-p
          (addr-range
           *2^30*
           (ash (loghead 22
                         (logtail
                          30
                          (rm-low-64
                           (page-dir-ptr-table-entry-addr
                            (xr :rgf *rdi* x86)
                            (pdpt-base-addr (xr :rgf *rdi* x86) x86))
                           x86)))
                30))
          (all-xlation-governing-entries-paddrs
           8
           (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86))
           x86))
         (disjoint-p
          (addr-range
           *2^30*
           (ash (loghead 22
                         (logtail
                          30
                          (rm-low-64
                           (page-dir-ptr-table-entry-addr
                            (xr :rgf *rdi* x86)
                            (pdpt-base-addr (xr :rgf *rdi* x86) x86))
                           x86)))
                30))
          (all-xlation-governing-entries-paddrs
           8
           (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86))
           x86)))

    (equal
     (read-from-physical-memory
      (addr-range
       *2^30*
       (ash (loghead 22
                     (logtail
                      30
                      (rm-low-64
                       (page-dir-ptr-table-entry-addr
                        (xr :rgf *rdi* x86)
                        (pdpt-base-addr (xr :rgf *rdi* x86) x86))
                       x86)))
            30))
      (mv-nth 2 (las-to-pas
                 *2^30* (xr :rgf *rsi* x86) :r
                 (zeroCopy-state x86))))
     (read-from-physical-memory
      (addr-range
       *2^30*
       (ash (loghead 22
                     (logtail
                      30
                      (rm-low-64
                       (page-dir-ptr-table-entry-addr
                        (xr :rgf *rdi* x86)
                        (pdpt-base-addr (xr :rgf *rdi* x86) x86))
                       x86)))
            30))
      x86)))
   :hints
   (("Goal"
     :hands-off (x86-run)
     :use ((:instance destination-data-from-final-state-in-terms-of-read-from-physical-memory-and-addr-range-helper-1))
     :in-theory (union-theories
                 '()
                 (theory 'minimal-theory))))))

(defthmd destination-data-from-final-state-in-terms-of-read-from-physical-memory-and-addr-range
  (implies
   (and (rewire_dst_to_src-effects-preconditions x86)
        (throwaway-destination-data-preconditions x86)
        (destination-data-preconditions x86)
        (source-data-preconditions x86)
        (more-destination-data-preconditions x86))
   (equal
    (mv-nth 1 (rb *2^30* (xr :rgf *rsi* x86) :r (x86-run (rewire_dst_to_src-clk) x86)))
    (read-from-physical-memory
     (addr-range
      *2^30*
      (ash (loghead 22
                    (logtail
                     30
                     (rm-low-64
                      (page-dir-ptr-table-entry-addr
                       (xr :rgf *rdi* x86)
                       (pdpt-base-addr (xr :rgf *rdi* x86) x86))
                      x86)))
           30))
     x86)))
  :hints
  (("Goal"
    :use ((:instance destination-pml4-table-entry-projection)
          (:instance destination-pdpt-base-addr-projection)
          (:instance destination-data-from-final-state-in-terms-of-read-from-physical-memory-and-addr-range-helper-2)
          (:instance rewire_dst_to_src-effects))
    :hands-off (x86-run)
    :in-theory
    (e/d*
     (rb
      preconditions-imply-ms-fault-view
      ms-fault-application-level-and-marking-view-projection

      page-size
      pml4-table-base-addr-projection
      source-pml4-table-entry-projection
      source-pdpt-base-addr-projection
      source-pas-projection
      disjoint-p-all-xlation-governing-entries-paddrs-subset-p)
     (rewire_dst_to_src-effects-preconditions
      zeroCopy-state
      rewire_dst_to_src-disable
      read-from-physical-memory
      pdpt-base-addr-after-mv-nth-2-las-to-pas
      xw-xw-intra-simple-field-shadow-writes
      rewrite-rb-to-rb-alt
      page-dir-ptr-table-entry-addr-to-c-program-optimized-form
      unsigned-byte-p-52-of-left-shifting-a-40-bit-vector-by-12
      (:meta acl2::mv-nth-cons-meta)
      (:rewrite mv-nth-0-las-to-pas-subset-p)
      (:definition subset-p)
      (:rewrite mv-nth-1-las-to-pas-subset-p-disjoint-from-other-p-addrs)
      (:rewrite member-p-canonical-address-listp)

      (:definition create-canonical-address-list)
      (:type-prescription member-p)
      (:rewrite two-mv-nth-1-las-to-pas-subset-p-disjoint-from-las-to-pas)
      (:rewrite open-mv-nth-1-las-to-pas-for-same-1g-page-general-1)
      (:rewrite r-w-x-is-irrelevant-for-mv-nth-2-las-to-pas-when-no-errors)
      (:rewrite mv-nth-2-las-to-pas-system-level-non-marking-view)
      (:rewrite canonical-address-p-rip)
      (:rewrite xr-marking-view-mv-nth-2-las-to-pas)
      (:rewrite
       mv-nth-1-rb-and-xlate-equiv-memory-disjoint-from-paging-structures)

      (:rewrite disjoint-p-two-addr-ranges-thm-3)
      (:rewrite disjoint-p-two-addr-ranges-thm-2)
      (:rewrite greater-logbitp-of-unsigned-byte-p . 2)
      (:rewrite subset-p-two-addr-ranges)
      (:rewrite xr-marking-view-mv-nth-1-wb)
      (:rewrite rm-low-64-in-app-view)
      (:rewrite member-p-addr-range)
      (:type-prescription acl2::|x < y  =>  0 < y-x|)
      (:rewrite
       all-mem-except-paging-structures-equal-aux-and-rm-low-64-from-rest-of-memory)
      (:rewrite
       all-mem-except-paging-structures-equal-and-rm-low-64-from-rest-of-memory)
      (:type-prescription member-p-physical-address-p-physical-address-listp)
      (:linear n64p-rm-low-64)
      (:rewrite multiples-of-8-and-disjointness-of-physical-addresses-1)
      (:rewrite
       infer-disjointness-with-all-xlation-governing-entries-paddrs-from-gather-all-paging-structure-qword-addresses-with-disjoint-p$)
      (:rewrite car-addr-range)
      (:type-prescription member-p-physical-address-p)
      (:type-prescription n01p-page-size)
      (:rewrite acl2::consp-of-append)
      (:rewrite disjoint-p-two-addr-ranges-thm-0)
      (:rewrite not-disjoint-p-two-addr-ranges-thm)
      (:rewrite right-shift-to-logtail)
      (:rewrite disjoint-p-two-addr-ranges-thm-1)

      (:rewrite cdr-addr-range)
      (:type-prescription n01p-page-user-supervisor)
      (:type-prescription n01p-page-read-write)
      (:type-prescription n01p-page-present)
      (:type-prescription n01p-page-execute-disable)

      (:rewrite member-p-addr-range-from-member-p-addr-range)
      (:rewrite car-of-append)
      (:rewrite
       xlate-equiv-structures-and-logtail-30-rm-low-64-with-page-dir-ptr-table-entry-addr)
      (:type-prescription xlate-equiv-memory)
      (:rewrite open-mv-nth-0-las-to-pas-for-same-1g-page-general-2)
      (:rewrite loghead-30-of-1g-aligned-lin-addr-+-n-2)
      (:type-prescription rm-low-64-logand-logior-helper-1)
      (:rewrite
       canonical-address-p-pml4-table-entry-addr-to-c-program-optimized-form)
      (:rewrite xlate-equiv-structures-and-logtail-12-rm-low-64-with-pml4-table-entry-addr)
      (:rewrite acl2::right-cancellation-for-+)
      (:rewrite pml4-table-entry-addr-is-a-multiple-of-8)
      (:rewrite ctri-is-n64p))))))

;; ----------------------------------------------------------------------

;; Top-level theorems:

;; 1. No errors encountered during program run; also, final state is
;; still in the system-level marking view.

(defthmd no-errors-during-program-execution
  ;; Derived from ms-fault-application-level-and-marking-view-projection.
  (implies
   (rewire_dst_to_src-effects-preconditions x86)
   (and (equal (xr :ms  0 (x86-run (rewire_dst_to_src-clk) x86)) nil)
        (equal (xr :fault 0 (x86-run (rewire_dst_to_src-clk) x86)) nil)
        (equal (xr :app-view 0 (x86-run (rewire_dst_to_src-clk) x86)) nil)
        (equal (xr :marking-view 0 (x86-run (rewire_dst_to_src-clk) x86))
               t)))
  :hints (("Goal"
           :use ((:instance ms-fault-application-level-and-marking-view-projection)
                 (:instance rewire_dst_to_src-effects))
           :in-theory (theory 'minimal-theory))))

;; 2. Destination data in final state == source data in initial state,
;; i.e., copy was done successfully.

(defthmd destination-data-in-final-state-==-source-data-in-initial-state
  (implies (and
            (64-bit-modep x86)
            (rewire_dst_to_src-effects-preconditions x86)
            (source-data-preconditions x86)
            (destination-data-preconditions x86)
            (more-destination-data-preconditions x86))
           (equal
            ;; Destination, after the copy:
            (mv-nth 1 (rb *2^30* (xr :rgf *rsi* x86) :r
                          (x86-run (rewire_dst_to_src-clk) x86)))
            ;; Source, before the copy:
            (mv-nth 1 (rb *2^30* (xr :rgf *rdi* x86) :r
                          x86))))
  :hints (("Goal"
           :do-not '(preprocess)
           :do-not-induct t
           :hands-off (x86-run)
           :use ((:instance destination-data-from-final-state-in-terms-of-read-from-physical-memory-and-addr-range)
                 (:instance source-data-from-initial-state-in-terms-of-read-from-physical-memory-and-addr-range)
                 (:instance throwaway-destination-data-preconditions-lemma)
                 (:instance rewire_dst_to_src-effects))
           :in-theory (union-theories
                       '()
                       (theory 'minimal-theory)))))

;; 3. Source data in the final state === source data in the initial
;; state, i.e., the source data is unmodified.

(defthmd source-data-in-final-state-==-source-data-in-initial-state
  (implies (and (rewire_dst_to_src-effects-preconditions x86)
                (source-data-preconditions x86))

           (equal
            ;; Source, after the copy:
            (mv-nth 1 (rb *2^30* (xr :rgf *rdi* x86) :r
                          (x86-run (rewire_dst_to_src-clk) x86)))
            ;; Source, before the copy:
            (mv-nth 1 (rb *2^30* (xr :rgf *rdi* x86) :r
                          x86))))
  :hints (("Goal"
           :use ((:instance source-data-projection)
                 (:instance rewire_dst_to_src-effects))
           :in-theory (union-theories
                       '(source-data-preconditions)
                       (theory 'minimal-theory)))))


;; 4. Final value in rax == 1, which signals that the 1G-aligned
;; physical address of the destination at the end of execution of the
;; program is equal to the 1G-aligned physical address of the source.

(defthmd rax-==-1-rewire_dst_to_src-effects
  (implies
   (rewire_dst_to_src-effects-preconditions x86)
   (equal (xr :rgf *rax* (x86-run (rewire_dst_to_src-clk) x86)) 1))
  :hints (("Goal"
           :use ((:instance rewire_dst_to_src-effects))
           :in-theory (union-theories
                       '(xr-xw-intra-array-field
                         member-equal
                         zeroCopy-state)
                       (theory 'minimal-theory)))))

;; 5. Program is unmodified in the final state.

(defthmd program-is-unmodified
  (implies
   (and (64-bit-modep x86)
        (rewire_dst_to_src-effects-preconditions x86)
        (direct-map-p 8
                      (page-dir-ptr-table-entry-addr
                       (xr :rgf *rsi* x86)
                       (pdpt-base-addr (xr :rgf *rsi* x86) x86))
                      :r x86))
   (equal (program-at (xr :rip 0 x86) *rewire_dst_to_src*
                      (x86-run (rewire_dst_to_src-clk) x86))
          (program-at (xr :rip 0 x86) *rewire_dst_to_src* x86)))
  :hints (("Goal"
           :use
           ((:instance program-at-projection)
            (:instance rewire_dst_to_src-effects))
           :in-theory (e/d* ()
                            (rewrite-program-at-to-program-at-alt
                             zeroCopy-state
                             rewire_dst_to_src-effects-preconditions)))))

;; ----------------------------------------------------------------------
