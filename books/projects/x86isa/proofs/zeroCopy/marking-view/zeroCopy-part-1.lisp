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

(include-book "zeroCopy-init")

;; ======================================================================

;; Effects Theorem:

(local
 (in-theory
  ;; For the effects theorems:
  (e/d* (instruction-decoding-and-spec-rules
         x86-operation-mode
         rflag-RoWs-enables
         cr3bits->pdb
         segment-selectorbits->rpl

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
         one-byte-opcode-execute
         two-byte-opcode-decode-and-execute
         x86-operand-from-modr/m-and-sib-bytes
         check-instruction-length
         x86-effective-addr-when-64-bit-modep
         x86-effective-addr-32/64
         x86-effective-addr-from-sib
         x86-operand-to-reg/mem
         rr08 rr32 rr64 wr08 wr32 wr64
         riml08 riml32 riml64
         write-user-rflags

         select-segment-register

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

;; (acl2::why x86-run-opener-not-ms-not-zp-n)
;; (acl2::why x86-fetch-decode-execute-opener-in-marking-view)
;; (acl2::why get-prefixes-alt-opener-lemma-no-prefix-byte)
;; (acl2::why get-prefixes-alt-opener-lemma-no-legacy-prefix-but-rex-prefix)

(local
 (in-theory (e/d (ia32e-pml4ebits->pdpt
                  ia32e-pdpte-1gb-pagebits->page
                  ia32e-page-tablesbits->ps
                  cr3bits->pdb
                  cr0bits->wp
                  cr4bits->smep
                  cr4bits->smap
                  ia32_eferbits->nxe
                  segment-selectorbits->rpl
                  rflagsbits->ac)
                 ((:rewrite no-errors-when-translating-program-bytes-in-marking-view)
                  (:rewrite rewrite-program-at-to-program-at-alt)
                  (:meta acl2::mv-nth-cons-meta)
                  (:rewrite mv-nth-1-las-to-pas-returns-nil-when-error)
                  (:rewrite rb-no-reads-when-zp-n)
                  (:rewrite greater-logbitp-of-unsigned-byte-p . 2)
                  (:rewrite rflagsbits->vm-of-write-with-mask)
                  (:rewrite rflagsbits->vip-of-write-with-mask)
                  (:rewrite rflagsbits->vif-of-write-with-mask)
                  (:rewrite rflagsbits->tf-of-write-with-mask)
                  (:rewrite rflagsbits->rf-of-write-with-mask)
                  (:rewrite rflagsbits->res5-of-write-with-mask)
                  (:rewrite rflagsbits->res4-of-write-with-mask)
                  (:rewrite rflagsbits->res3-of-write-with-mask)
                  (:rewrite rflagsbits->res2-of-write-with-mask)
                  (:rewrite rflagsbits->res1-of-write-with-mask)
                  (:rewrite rflagsbits->nt-of-write-with-mask)
                  (:rewrite rflagsbits->iopl-of-write-with-mask)
                  (:rewrite rflagsbits->intf-of-write-with-mask)
                  (:rewrite rflagsbits->id-of-write-with-mask)
                  (:rewrite rflagsbits->df-of-write-with-mask)
                  (:rewrite acl2::bfix-when-not-bitp)
                  (:type-prescription acl2::bit->bool$inline)
                  (:rewrite acl2::bfix-when-not-bit->bool)
                  (:rewrite acl2::bfix-when-bit->bool)
                  (:rewrite rflagsbits->ac-of-write-with-mask)
                  (:rewrite acl2::bfix-when-not-1)
                  (:rewrite unsigned-byte-p-when-mxcsrbits-p)
                  (:rewrite unsigned-byte-p-when-cr0bits-p)
                  (:rewrite
                   infer-disjointness-with-all-xlation-governing-entries-paddrs-from-gather-all-paging-structure-qword-addresses-with-disjoint-p$)
                  (:definition subset-p)
                  (:type-prescription program-at)
                  (:rewrite fty::unsigned-byte-p-1-when-bitp)
                  (:rewrite unsigned-byte-p-when-evex-prefixes-p)
                  (:rewrite unsigned-byte-p-when-32bits-p)
                  (:rewrite unsigned-byte-p-when-40bits-p)
                  (:rewrite unsigned-byte-p-when-ia32e-pml4ebits-p)
                  (:rewrite unsigned-byte-p-when-ia32e-pdpte-pg-dirbits-p)
                  (:rewrite unsigned-byte-p-when-ia32e-pdpte-1gb-pagebits-p)
                  (:rewrite unsigned-byte-p-when-ia32e-pde-pg-tablebits-p)
                  (:rewrite unsigned-byte-p-when-ia32e-pde-2mb-pagebits-p)
                  (:rewrite unsigned-byte-p-when-ia32e-page-tablesbits-p)
                  (:rewrite unsigned-byte-p-when-data-segment-descriptorbits-p)
                  (:rewrite unsigned-byte-p-when-code-segment-descriptorbits-p)
                  (:linear size-of-rb)
                  (:type-prescription subset-p)
                  (:type-prescription mxcsrbits-p)
                  (:rewrite mxcsrbits-p-when-unsigned-byte-p)
                  (:type-prescription cr0bits-p$inline)
                  (:rewrite cr0bits-p-when-unsigned-byte-p)
                  (:type-prescription natp-create-undef)
                  (:type-prescription bitp)
                  (:rewrite fty::bitp-when-unsigned-byte-p-1)
                  (:rewrite rme-size-non-canonical-when-64-bit-modep-and-not-fs/gs)
                  (:type-prescription member-p)
                  (:rewrite cdr-mv-nth-1-las-to-pas-no-error)
                  (:rewrite unsigned-byte-p-when-3bits-p)
                  (:rewrite unsigned-byte-p-when-xcr0bits-p)
                  (:rewrite unsigned-byte-p-when-cr3bits-p)
                  (:rewrite unsigned-byte-p-when-64bits-p)
                  (:type-prescription 40bits-p)
                  (:rewrite 40bits-p-when-unsigned-byte-p)
                  (:rewrite
                   infer-disjointness-with-all-xlation-governing-entries-paddrs-from-gather-all-paging-structure-qword-addresses-1)
                  (:type-prescription ia32e-pml4ebits-p)
                  (:type-prescription ia32e-pdpte-pg-dirbits-p)
                  (:type-prescription ia32e-pdpte-1gb-pagebits-p)
                  (:type-prescription ia32e-pde-pg-tablebits-p)
                  (:type-prescription ia32e-pde-2mb-pagebits-p)
                  (:type-prescription data-segment-descriptorbits-p)
                  (:type-prescription code-segment-descriptorbits-p)
                  (:rewrite ia32e-pml4ebits-p-when-unsigned-byte-p)
                  (:rewrite ia32e-pdpte-pg-dirbits-p-when-unsigned-byte-p)
                  (:rewrite ia32e-pdpte-1gb-pagebits-p-when-unsigned-byte-p)
                  (:rewrite ia32e-pde-pg-tablebits-p-when-unsigned-byte-p)
                  (:rewrite ia32e-pde-2mb-pagebits-p-when-unsigned-byte-p)
                  (:rewrite data-segment-descriptorbits-p-when-unsigned-byte-p)
                  (:rewrite code-segment-descriptorbits-p-when-unsigned-byte-p)
                  (:rewrite rflagsbits->of-of-write-with-mask)
                  (:rewrite rflagsbits->zf-of-write-with-mask)
                  (:rewrite rflagsbits->sf-of-write-with-mask)
                  (:rewrite rflagsbits->af-of-write-with-mask)
                  (:rewrite rflagsbits->pf-of-write-with-mask)
                  (:rewrite rflagsbits->cf-of-write-with-mask)
                  (:rewrite mv-nth-1-las-to-pas-subset-p)
                  (:linear n01p-zf-spec)
                  (:type-prescription evex-prefixes-p$inline)
                  (:type-prescription 32bits-p)
                  (:rewrite evex-prefixes-p-when-unsigned-byte-p)
                  (:rewrite 32bits-p-when-unsigned-byte-p)
                  (:linear n01p-sf-spec64)
                  (:linear n01p-pf-spec64)
                  (:type-prescription acl2::logext-type)
                  (:type-prescription xcr0bits-p$inline)
                  (:type-prescription 64bits-p)
                  (:rewrite xcr0bits-p-when-unsigned-byte-p)
                  (:rewrite 64bits-p-when-unsigned-byte-p)
                  (:rewrite cr3bits->pdb-of-write-with-mask)
                  (:type-prescription 3bits-p)
                  (:rewrite 3bits-p-when-unsigned-byte-p)
                  (:linear size-of-rb-in-app-view)
                  (:rewrite bitops::signed-byte-p-incr)
                  (:rewrite unsigned-byte-p-when-vex3-byte2-p)
                  (:rewrite unsigned-byte-p-when-vex3-byte1-p)
                  (:rewrite unsigned-byte-p-when-vex2-byte1-p)
                  (:rewrite unsigned-byte-p-when-sib-p)
                  (:rewrite unsigned-byte-p-when-modr/m-p)
                  (:rewrite unsigned-byte-p-when-evex-byte3-p)
                  (:rewrite unsigned-byte-p-when-evex-byte2-p)
                  (:rewrite unsigned-byte-p-when-evex-byte1-p)
                  (:rewrite unsigned-byte-p-when-8bits-p)
                  (:type-prescription acl2::expt-type-prescription-positive)
                  (:type-prescription acl2::expt-type-prescription-nonzero)
                  (:type-prescription acl2::expt-type-prescription-integerp)
                  (:linear n01p-sf-spec32)
                  (:linear n01p-pf-spec32)
                  (:rewrite ia32e-page-tablesbits->ps-of-write-with-mask)
                  (:rewrite rme-size-when-64-bit-modep-fs/gs)
                  (:rewrite rme-size-unaligned-when-64-bit-modep-and-not-fs/gs)
                  (:rewrite unsigned-byte-p-when-2bits-p)
                  (:rewrite unsigned-byte-p-when-system-segment-descriptor-attributesbits-p)
                  (:rewrite
                   unsigned-byte-p-when-interrupt/trap-gate-descriptor-attributesbits-p)
                  (:rewrite unsigned-byte-p-when-fp-statusbits-p)
                  (:rewrite unsigned-byte-p-when-data-segment-descriptor-attributesbits-p)
                  (:rewrite unsigned-byte-p-when-code-segment-descriptor-attributesbits-p)
                  (:rewrite unsigned-byte-p-when-call-gate-descriptor-attributesbits-p)
                  (:rewrite rime-size-non-canonical-when-64-bit-modep-and-not-fs/gs)
                  (:linear n01p-sub-af-spec64)
                  (:linear n01p-of-spec64)
                  (:type-prescription vex3-byte2-p$inline)
                  (:type-prescription vex3-byte1-p$inline)
                  (:type-prescription vex2-byte1-p$inline)
                  (:type-prescription sib-p$inline)
                  (:type-prescription modr/m-p$inline)
                  (:type-prescription evex-byte3-p$inline)
                  (:type-prescription evex-byte2-p$inline)
                  (:type-prescription evex-byte1-p$inline)
                  (:type-prescription 8bits-p)
                  (:rewrite vex3-byte2-p-when-unsigned-byte-p)
                  (:rewrite vex3-byte1-p-when-unsigned-byte-p)
                  (:rewrite vex2-byte1-p-when-unsigned-byte-p)
                  (:rewrite sib-p-when-unsigned-byte-p)
                  (:rewrite modr/m-p-when-unsigned-byte-p)
                  (:rewrite evex-byte3-p-when-unsigned-byte-p)
                  (:rewrite evex-byte2-p-when-unsigned-byte-p)
                  (:rewrite evex-byte1-p-when-unsigned-byte-p)
                  (:rewrite 8bits-p-when-unsigned-byte-p)
                  (:type-prescription 2bits-p)
                  (:rewrite 2bits-p-when-unsigned-byte-p)
                  (:rewrite unsigned-byte-p-when-segment-selectorbits-p)
                  (:type-prescription system-segment-descriptor-attributesbits-p)
                  (:type-prescription interrupt/trap-gate-descriptor-attributesbits-p)
                  (:type-prescription fp-statusbits-p)
                  (:type-prescription data-segment-descriptor-attributesbits-p)
                  (:type-prescription code-segment-descriptor-attributesbits-p)
                  (:type-prescription call-gate-descriptor-attributesbits-p)
                  (:rewrite rme08-when-64-bit-modep-and-fs/gs)
                  (:rewrite system-segment-descriptor-attributesbits-p-when-unsigned-byte-p)
                  (:rewrite
                   interrupt/trap-gate-descriptor-attributesbits-p-when-unsigned-byte-p)
                  (:rewrite fp-statusbits-p-when-unsigned-byte-p)
                  (:rewrite data-segment-descriptor-attributesbits-p-when-unsigned-byte-p)
                  (:rewrite code-segment-descriptor-attributesbits-p-when-unsigned-byte-p)
                  (:rewrite call-gate-descriptor-attributesbits-p-when-unsigned-byte-p)
                  (:type-prescription binary-logand)
                  (:rewrite wme-size-when-64-bit-modep-fs/gs)
                  (:rewrite wme-size-non-canonical-when-64-bit-modep-and-not-fs/gs)
                  (:rewrite wme-size-64-bit-unaligned-when-64-bit-modep-and-not-fs/gs)
                  (:rewrite segment-selectorbits->rpl-of-write-with-mask)
                  (:rewrite rime-size-when-64-bit-modep-fs/gs)
                  (:rewrite rime-size-unaligned-when-64-bit-modep-and-not-fs/gs)))))

(defthmd rewire_dst_to_src-effects-1-to-45-instructions
  (implies
   (and
    (x86-state-okp x86)
    ;; (program-ok-p x86)
    ;; rewrite-program-at-to-program-at-alt is expensive, so I'm
    ;; replacing program-ok-p with program-alt-ok-p. They're equal
    ;; anyway (see program-alt-ok-p-and-program-ok-p).
    (program-alt-ok-p x86)
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
    (direct-map-p
     8
     (page-dir-ptr-table-entry-addr
      (xr :rgf *rsi* x86)
      (pdpt-base-addr (xr :rgf *rsi* x86) x86))
     :w x86)

    ;; !!! FIXME? Some of the following are in terms of disjoint-p
    ;; !!! instead of disjoint-p$.
    (hide (return-address-ok-p x86))
    (hide (stack-containing-return-address-ok-p x86))
    (hide (stack-containing-return-address-and-program-no-interfere-p x86))
    (hide (stack-containing-return-address-and-source-PML4E-no-interfere-p x86))
    (hide (stack-containing-return-address-and-source-PDPTE-no-interfere-p x86))
    (hide (stack-containing-return-address-and-destination-PML4E-no-interfere-p x86))
    (hide (stack-containing-return-address-and-destination-PDPTE-no-interfere-p x86))
    (hide (stack-containing-return-address-and-rest-of-the-stack-no-interfere-p x86)))

   (equal
    (x86-run (rewire_dst_to_src-clk-1-to-45) x86)
    (XW
     :RGF *RAX*
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
                (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
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
                (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                        (LOGAND 4088
                                (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
                :R X86))))
            12))
          :R X86)))))
     (XW
      :RGF *RCX*
      (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
              (LOGAND 4088
                      (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
      (XW
       :RGF *RDX*
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
            :R X86)))))
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
          :RIP nil (+ 193 (XR :RIP nil X86))
          (XW
           :UNDEF nil (+ 39 (NFIX (XR :UNDEF nil X86)))
           (XW
            :RFLAGS nil
            (RFLAGSBITS
             0 (RFLAGSBITS->RES1 (XR :RFLAGS nil X86))
             (PF-SPEC64
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
                  :R X86)))))
             (RFLAGSBITS->RES2 (XR :RFLAGS nil X86))
             (LOGHEAD 1
                      (CREATE-UNDEF (+ 38 (NFIX (XR :UNDEF nil X86)))))
             (RFLAGSBITS->RES3 (XR :RFLAGS nil X86))
             (ZF-SPEC
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
                  :R X86)))))
             (SF-SPEC64
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
                  :R X86)))))
             (RFLAGSBITS->TF (XR :RFLAGS nil X86))
             (RFLAGSBITS->INTF (XR :RFLAGS nil X86))
             (RFLAGSBITS->DF (XR :RFLAGS nil X86))
             0 (RFLAGSBITS->IOPL (XR :RFLAGS nil X86))
             (RFLAGSBITS->NT (XR :RFLAGS nil X86))
             (RFLAGSBITS->RES4 (XR :RFLAGS nil X86))
             (RFLAGSBITS->RF (XR :RFLAGS nil X86))
             (RFLAGSBITS->VM (XR :RFLAGS nil X86))
             (BOOL->BIT (LOGBITP 18 (XR :RFLAGS nil X86)))
             (RFLAGSBITS->VIF (XR :RFLAGS nil X86))
             (RFLAGSBITS->VIP (XR :RFLAGS nil X86))
             (RFLAGSBITS->ID (XR :RFLAGS nil X86))
             (RFLAGSBITS->RES5 (XR :RFLAGS nil X86)))
            (MV-NTH
             2
             (LAS-TO-PAS
              3 (+ 190 (XR :RIP nil X86))
              :X
              (MV-NTH
               1
               (WB
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
                :W
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
                    :R X86))))
                (MV-NTH
                 2
                 (LAS-TO-PAS
                  6 (+ 184 (XR :RIP nil X86))
                  :X
                  (MV-NTH
                   2
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
                    :R
                    (MV-NTH
                     2
                     (LAS-TO-PAS
                      40 (+ 144 (XR :RIP nil X86))
                      :X
                      (MV-NTH
                       2
                       (LAS-TO-PAS
                        3 (+ 140 (XR :RIP nil X86))
                        :X
                        (MV-NTH
                         2
                         (LAS-TO-PAS
                          8
                          (LOGIOR
                           (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                           (LOGAND
                            4088
                            (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
                          :R
                          (MV-NTH
                           2
                           (LAS-TO-PAS
                            32 (+ 108 (XR :RIP nil X86))
                            :X
                            (MV-NTH
                             2
                             (LAS-TO-PAS
                              18 (+ 86 (XR :RIP nil X86))
                              :X
                              (MV-NTH
                               2
                               (LAS-TO-PAS
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
                                :R
                                (MV-NTH
                                 2
                                 (LAS-TO-PAS
                                  40 (+ 46 (XR :RIP nil X86))
                                  :X
                                  (MV-NTH
                                   2
                                   (LAS-TO-PAS
                                    4 (+ 38 (XR :RIP nil X86))
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
                                         28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
                                      :R
                                      (MV-NTH
                                       2
                                       (LAS-TO-PAS
                                        25 (+ 13 (XR :RIP nil X86))
                                        :X
                                        (MV-NTH
                                         2
                                         (LAS-TO-PAS
                                          8 (+ -24 (XR :RGF *RSP* X86))
                                          :R
                                          (MV-NTH
                                           2
                                           (LAS-TO-PAS
                                            5 (+ 8 (XR :RIP nil X86))
                                            :X
                                            (MV-NTH
                                             1
                                             (WB
                                              8 (+ -24 (XR :RGF *RSP* X86))
                                              :W (XR :CTR *CR3* X86)
                                              (MV-NTH
                                               2
                                               (LAS-TO-PAS
                                                8 (XR :RIP nil X86)
                                                :X
                                                X86))))))))))))))))))))))))))))))))))))))))))))))

  :hints (("Goal"
           :do-not-induct t
           :do-not '(preprocess)
           :in-theory
           (e/d* (len
                  page-size
                  loghead-negative
                  disjoint-p-all-xlation-governing-entries-paddrs-subset-p
                  rme-size wme-size
                  rime-size wime-size)
                 (create-canonical-address-list
                  disjointness-of-las-to-pas-from-wb-to-a-paging-entry
                  (:rewrite get-prefixes-opener-lemma-group-4-prefix-in-marking-view)
                  (:rewrite get-prefixes-opener-lemma-group-3-prefix-in-marking-view)
                  (:rewrite get-prefixes-opener-lemma-group-2-prefix-in-marking-view)
                  (:rewrite get-prefixes-opener-lemma-group-1-prefix-in-marking-view)
                  (:rewrite mv-nth-1-rb-and-xlate-equiv-memory-disjoint-from-paging-structures)
                  (:rewrite mv-nth-2-rb-in-system-level-non-marking-view)
                  (:rewrite rb-returns-x86-app-view)
                  (:linear rm-low-64-logand-logior-helper-1)
                  (:definition n64p$inline)
                  (:type-prescription xlate-equiv-memory)
                  (:rewrite program-at-alt-wb-disjoint-in-sys-view)
                  (:type-prescription natp-page-dir-ptr-table-entry-addr)
                  mv-nth-1-las-to-pas-subset-p-disjoint-from-other-p-addrs
                  mv-nth-2-las-to-pas-system-level-non-marking-view
                  (:rewrite r-w-x-is-irrelevant-for-mv-nth-2-las-to-pas-when-no-errors)
                  (:rewrite acl2::cdr-of-append-when-consp)
                  (:rewrite acl2::car-of-append)
                  (:rewrite acl2::consp-of-append)
                  (:rewrite acl2::append-atom-under-list-equiv)
                  (:type-prescription binary-append)
                  (:rewrite xr-fault-wb-in-sys-view)
                  (:type-prescription n01p-page-size)
                  (:type-prescription member-p-physical-address-p-physical-address-listp)
                  (:rewrite acl2::right-cancellation-for-+)
                  (:type-prescription member-p-physical-address-p)
                  (:rewrite acl2::append-singleton-under-set-equiv))))))

;; ----------------------------------------------------------------------
