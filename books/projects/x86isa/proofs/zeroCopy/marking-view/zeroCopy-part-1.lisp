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
(include-book "zeroCopy-init")

(include-book "centaur/bitops/ihs-extensions" :dir :system)
(include-book "centaur/bitops/signed-byte-p" :dir :system)
(include-book "arithmetic/top-with-meta" :dir :system)

;; ======================================================================

;; Effects Theorems:

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
         check-instruction-length
         x86-effective-addr-when-64-bit-modep
         x86-effective-addr-32/64
         x86-effective-addr-from-sib
         x86-operand-to-reg/mem
         x86-operand-to-reg/mem$
         rr08 rr32 rr64 wr08 wr32 wr64
         riml08 riml32 riml64
         !flgi-undefined
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
;; (acl2::why get-prefixes-alt-and-wb-in-system-level-marking-view-disjoint-from-paging-structures)
;; (acl2::why la-to-pas-values-and-mv-nth-1-wb-disjoint-from-xlation-gov-addrs)
;; (acl2::why mv-nth-1-rb-after-mv-nth-2-rb-alt)
;; (acl2::why all-xlation-governing-entries-paddrs-and-mv-nth-1-wb-disjoint)
;; (acl2::why la-to-pas-values-and-mv-nth-1-wb-disjoint-from-xlation-gov-addrs)
;; (acl2::why mv-nth-1-rb-after-mv-nth-2-get-prefixes-alt-no-prefix-byte)
;; (acl2::why mv-nth-2-get-prefixes-alt-no-prefix-byte)
;; (acl2::why mv-nth-2-rb-in-system-level-marking-view)
;; (acl2::why combine-mv-nth-2-las-to-pas-same-r-w-x)
;; (acl2::why mv-nth-1-rb-after-mv-nth-2-las-to-pas)
;; (acl2::why mv-nth-1-rb-after-mv-nth-2-rb)
;; (acl2::why get-prefixes-alt-and-wb-to-paging-structures)
;; (acl2::why rb-wb-disjoint-in-sys-view)
;; (acl2::why x86-fetch-decode-execute-opener-in-marking-view)
;; (acl2::why mv-nth-2-get-prefixes-alt-no-prefix-byte)
;; (acl2::why rb-alt-and-wb-to-paging-structures-disjoint)
;; (acl2::why two-mv-nth-1-las-to-pas-subset-p-disjoint-from-las-to-pas)
;; (acl2::why rb-alt-wb-disjoint-in-sys-view)
;; (acl2::why rb-alt-wb-equal-in-sys-view)
;; (acl2::why mv-nth-1-rb-and-xlate-equiv-memory-disjoint-from-paging-structures)
;; (acl2::why mv-nth-1-rb-after-mv-nth-2-las-to-pas)
;; (acl2::why la-to-pas-values-and-mv-nth-1-wb-disjoint-from-xlation-gov-addrs)
;; (acl2::why all-xlation-governing-entries-paddrs-subset-of-paging-structures)
;; (acl2::why infer-disjointness-with-all-xlation-governing-entries-paddrs-from-gather-all-paging-structure-qword-addresses-with-both-disjoint-p-and-disjoint-p$-and-subset-p)
;; (acl2::why disjointness-of-las-to-pas-from-wb-to-a-paging-entry)

(local (in-theory (e/d* (disjointness-of-las-to-pas-from-wb-to-a-paging-entry) ())))

(defthmd rewire_dst_to_src-effects-1-to-45-instructions
  ;; !!! Speed this monster up.
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
          :RIP 0 (+ 193 (XR :RIP 0 X86))
          (XW
           :UNDEF 0 (+ 39 (NFIX (XR :UNDEF 0 X86)))
           (!FLGI
            *CF* 0
            (!FLGI
             *PF*
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
                         (LOGAND 4088
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
                         (LOGAND 4088
                                 (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
                        :R X86))))
                    12))
                  :R X86)))))
             (!FLGI
              *AF*
              (LOGHEAD 1
                       (CREATE-UNDEF (+ 38 (NFIX (XR :UNDEF 0 X86)))))
              (!FLGI
               *ZF*
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
               (!FLGI
                *SF*
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
                (!FLGI
                 *OF* 0
                 (MV-NTH
                  2
                  (LAS-TO-PAS
                   3 (+ 190 (XR :RIP 0 X86))
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
                            (LOGAND
                             4088
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
                       6 (+ 184 (XR :RIP 0 X86))
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
                                (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                                (LOGAND
                                 4088
                                 (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
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
                                             -4096
                                             (LOGEXT 64 (XR :CTR *CR3* X86)))
                                            (LOGAND
                                             4088
                                             (LOGHEAD
                                              28
                                              (LOGTAIL 36 (XR :RGF *RDI* X86)))))
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
                                             (LOGEXT 64 (XR :CTR *CR3* X86)))
                                            (LOGAND
                                             4088
                                             (LOGHEAD
                                              28
                                              (LOGTAIL 36 (XR :RGF *RDI* X86)))))
                                           :R
                                           (MV-NTH
                                            2
                                            (LAS-TO-PAS
                                             25 (+ 13 (XR :RIP 0 X86))
                                             :X
                                             (MV-NTH
                                              2
                                              (LAS-TO-PAS
                                               8 (+ -24 (XR :RGF *RSP* X86))
                                               :R
                                               (MV-NTH
                                                2
                                                (LAS-TO-PAS
                                                 5 (+ 8 (XR :RIP 0 X86))
                                                 :X
                                                 (MV-NTH
                                                  1
                                                  (WB
                                                   8 (+ -24 (XR :RGF *RSP* X86))
                                                   :W (XR :CTR *CR3* X86)
                                                   (MV-NTH
                                                    2
                                                    (LAS-TO-PAS
                                                     8 (XR :RIP 0 X86)
                                                     :X
                                                     X86)))))))))))))))))))))))))))))))))))))))))))))))))))

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
                  (:rewrite program-at-values-and-!flgi)
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

;; ======================================================================

;; (defthmd foo
;;   (IMPLIES
;;    (AND

;;     (X86P X86)
;;     (NOT (XR :MS 0 X86))
;;     (NOT (XR :FAULT 0 X86))
;;     (NOT (ALIGNMENT-CHECKING-ENABLED-P X86))
;;     (NOT (XR :APP-VIEW 0 X86))
;;     (XR :PAGE-STRUCTURE-MARKING-VIEW 0 X86)
;;     (EQUAL (LOGHEAD 2 (XR :SEG-VISIBLE 1 X86))
;;            0)
;;     (EQUAL (LOGTAIL 40 (XR :CTR *CR3* X86))
;;            0)
;;     (CANONICAL-ADDRESS-P (+ 272 (XR :RIP 0 X86)))
;;     (PROGRAM-AT-ALT (XR :RIP 0 X86)
;;                     '(15 32 216 72 137 68 36 232 72 139 84 36 232
;;                          72 137 248 72 193 232 36 37 248 15 0 0
;;                          72 129 226 0 240 255 255 72 9 208 72 139
;;                          0 168 1 15 132 210 0 0 0 72 193 232 12
;;                          73 184 255 255 255 255 255 0 0 0 72 137
;;                          249 76 33 192 72 193 233 27 129 225 248
;;                          15 0 0 72 193 224 12 72 9 200 72 139 0
;;                          72 137 193 129 225 129 0 0 0 72 129 249
;;                          129 0 0 0 15 133 148 0 0 0 72 137 241
;;                          73 185 0 0 0 192 255 255 15 0 72 193 233
;;                          36 73 33 193 129 225 248 15 0 0 72 9 209
;;                          72 139 1 168 1 116 112 72 193 232 12 72
;;                          137 242 76 33 192 72 193 234 27 129 226
;;                          248 15 0 0 72 193 224 12 72 9 208 72 186
;;                          255 255 255 63 0 0 240 255 72 35 16 76
;;                          9 202 72 137 16 72 137 208 37 129 0 0 0
;;                          72 61 129 0 0 0 117 50 72 184 0 0 0 192
;;                          255 255 15 0 129 230 255 255 255 63 129
;;                          231 255 255 255 63 72 33 194 76 9 207
;;                          49 192 72 9 242 72 57 215 15 148 192 195
;;                          102 46 15 31 132 0 0 0 0 0 72 199 192
;;                          255 255 255 255 195 15 31 132 0 0 0 0 0)
;;                     X86)
;;     (DISJOINT-P$
;;      (MV-NTH 1
;;              (LAS-TO-PAS 272 (XR :RIP 0 X86) :X X86))
;;      (OPEN-QWORD-PADDR-LIST (GATHER-ALL-PAGING-STRUCTURE-QWORD-ADDRESSES X86)))
;;     (CANONICAL-ADDRESS-P (+ -24 (XR :RGF *RSP* X86)))
;;     (CANONICAL-ADDRESS-P (+ 8 (XR :RGF *RSP* X86)))
;;     (NOT (MV-NTH 0
;;                  (LAS-TO-PAS 8 (+ -24 (XR :RGF *RSP* X86))
;;                              :W X86)))
;;     (NOT (MV-NTH 0
;;                  (LAS-TO-PAS 8 (+ -24 (XR :RGF *RSP* X86))
;;                              :R X86)))
;;     (NO-DUPLICATES-P (MV-NTH 1
;;                              (LAS-TO-PAS 8 (+ -24 (XR :RGF *RSP* X86))
;;                                          :W X86)))
;;     (DISJOINT-P$
;;      (MV-NTH 1
;;              (LAS-TO-PAS 8 (+ -24 (XR :RGF *RSP* X86))
;;                          :W X86))
;;      (OPEN-QWORD-PADDR-LIST (GATHER-ALL-PAGING-STRUCTURE-QWORD-ADDRESSES X86)))
;;     (DISJOINT-P$ (MV-NTH 1
;;                          (LAS-TO-PAS 8 (+ -24 (XR :RGF *RSP* X86))
;;                                      :W X86))
;;                  (MV-NTH 1
;;                          (LAS-TO-PAS 272 (XR :RIP 0 X86)
;;                                      :X X86)))
;;     (DISJOINT-P$ (MV-NTH 1
;;                          (LAS-TO-PAS 8 (+ -24 (XR :RGF *RSP* X86))
;;                                      :W X86))
;;                  (ALL-XLATION-GOVERNING-ENTRIES-PADDRS 272 (XR :RIP 0 X86)
;;                                                        X86))
;;     (CANONICAL-ADDRESS-P (XR :RGF *RDI* X86))
;;     (CANONICAL-ADDRESS-P (+ 1073741823 (XR :RGF *RDI* X86)))
;;     (EQUAL (LOGHEAD 30 (XR :RGF *RDI* X86))
;;            0)
;;     (NOT (MV-NTH 0
;;                  (LAS-TO-PAS 1073741824 (XR :RGF *RDI* X86)
;;                              :R X86)))
;;     (NOT
;;      (MV-NTH
;;       0
;;       (LAS-TO-PAS
;;        8
;;        (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                (LOGAND 4088
;;                        (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
;;        :R X86)))
;;     (EQUAL
;;      (LOGHEAD
;;       1
;;       (MV-NTH
;;        1
;;        (RB 8
;;            (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                    (LOGAND 4088
;;                            (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
;;            :R X86)))
;;      1)
;;     (DISJOINT-P$
;;      (MV-NTH
;;       1
;;       (LAS-TO-PAS
;;        8
;;        (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                (LOGAND 4088
;;                        (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
;;        :R X86))
;;      (ALL-XLATION-GOVERNING-ENTRIES-PADDRS
;;       8
;;       (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;               (LOGAND 4088
;;                       (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
;;       X86))
;;     (NOT
;;      (MV-NTH
;;       0
;;       (LAS-TO-PAS
;;        8
;;        (LOGIOR
;;         (LOGAND 4088
;;                 (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
;;         (ASH
;;          (LOGHEAD
;;           40
;;           (LOGTAIL
;;            12
;;            (MV-NTH
;;             1
;;             (RB 8
;;                 (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                         (LOGAND 4088
;;                                 (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
;;                 :R X86))))
;;          12))
;;        :R X86)))
;;     (EQUAL
;;      (LOGHEAD
;;       1
;;       (MV-NTH
;;        1
;;        (RB
;;         8
;;         (LOGIOR
;;          (LOGAND 4088
;;                  (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
;;          (ASH
;;           (LOGHEAD
;;            40
;;            (LOGTAIL
;;             12
;;             (MV-NTH
;;              1
;;              (RB
;;               8
;;               (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                       (LOGAND 4088
;;                               (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
;;               :R X86))))
;;           12))
;;         :R X86)))
;;      1)
;;     (LOGBITP
;;      7
;;      (MV-NTH
;;       1
;;       (RB
;;        8
;;        (LOGIOR
;;         (LOGAND 4088
;;                 (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
;;         (ASH
;;          (LOGHEAD
;;           40
;;           (LOGTAIL
;;            12
;;            (MV-NTH
;;             1
;;             (RB 8
;;                 (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                         (LOGAND 4088
;;                                 (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
;;                 :R X86))))
;;          12))
;;        :R X86)))
;;     (DISJOINT-P$
;;      (MV-NTH
;;       1
;;       (LAS-TO-PAS
;;        8
;;        (LOGIOR
;;         (LOGAND 4088
;;                 (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
;;         (ASH
;;          (LOGHEAD
;;           40
;;           (LOGTAIL
;;            12
;;            (MV-NTH
;;             1
;;             (RB 8
;;                 (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                         (LOGAND 4088
;;                                 (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
;;                 :R X86))))
;;          12))
;;        :R X86))
;;      (ALL-XLATION-GOVERNING-ENTRIES-PADDRS
;;       8
;;       (LOGIOR
;;        (LOGAND 4088
;;                (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
;;        (ASH
;;         (LOGHEAD
;;          40
;;          (LOGTAIL
;;           12
;;           (MV-NTH
;;            1
;;            (RB 8
;;                (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                        (LOGAND 4088
;;                                (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
;;                :R X86))))
;;         12))
;;       X86))
;;     (DISJOINT-P$
;;      (MV-NTH 1
;;              (LAS-TO-PAS 8 (+ -24 (XR :RGF *RSP* X86))
;;                          :W X86))
;;      (MV-NTH
;;       1
;;       (LAS-TO-PAS
;;        8
;;        (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                (LOGAND 4088
;;                        (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
;;        :R X86)))
;;     (DISJOINT-P$
;;      (MV-NTH
;;       1
;;       (LAS-TO-PAS
;;        8
;;        (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                (LOGAND 4088
;;                        (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
;;        :R X86))
;;      (ALL-XLATION-GOVERNING-ENTRIES-PADDRS 8 (+ -24 (XR :RGF *RSP* X86))
;;                                            X86))
;;     (DISJOINT-P$
;;      (MV-NTH 1
;;              (LAS-TO-PAS 8 (+ -24 (XR :RGF *RSP* X86))
;;                          :W X86))
;;      (ALL-XLATION-GOVERNING-ENTRIES-PADDRS
;;       8
;;       (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;               (LOGAND 4088
;;                       (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
;;       X86))
;;     (DISJOINT-P$
;;      (MV-NTH
;;       1
;;       (LAS-TO-PAS
;;        8
;;        (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                (LOGAND 4088
;;                        (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
;;        :R X86))
;;      (ALL-XLATION-GOVERNING-ENTRIES-PADDRS 272 (XR :RIP 0 X86)
;;                                            X86))
;;     (DISJOINT-P$
;;      (MV-NTH 1
;;              (LAS-TO-PAS 8 (+ -24 (XR :RGF *RSP* X86))
;;                          :W X86))
;;      (MV-NTH
;;       1
;;       (LAS-TO-PAS
;;        8
;;        (LOGIOR
;;         (LOGAND 4088
;;                 (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
;;         (ASH
;;          (LOGHEAD
;;           40
;;           (LOGTAIL
;;            12
;;            (MV-NTH
;;             1
;;             (RB 8
;;                 (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                         (LOGAND 4088
;;                                 (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
;;                 :R X86))))
;;          12))
;;        :R X86)))
;;     (DISJOINT-P$
;;      (MV-NTH
;;       1
;;       (LAS-TO-PAS
;;        8
;;        (LOGIOR
;;         (LOGAND 4088
;;                 (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
;;         (ASH
;;          (LOGHEAD
;;           40
;;           (LOGTAIL
;;            12
;;            (MV-NTH
;;             1
;;             (RB 8
;;                 (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                         (LOGAND 4088
;;                                 (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
;;                 :R X86))))
;;          12))
;;        :R X86))
;;      (ALL-XLATION-GOVERNING-ENTRIES-PADDRS 8 (+ -24 (XR :RGF *RSP* X86))
;;                                            X86))
;;     (DISJOINT-P$
;;      (MV-NTH
;;       1
;;       (LAS-TO-PAS
;;        8
;;        (LOGIOR
;;         (LOGAND 4088
;;                 (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
;;         (ASH
;;          (LOGHEAD
;;           40
;;           (LOGTAIL
;;            12
;;            (MV-NTH
;;             1
;;             (RB 8
;;                 (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                         (LOGAND 4088
;;                                 (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
;;                 :R X86))))
;;          12))
;;        :R X86))
;;      (ALL-XLATION-GOVERNING-ENTRIES-PADDRS 272 (XR :RIP 0 X86)
;;                                            X86))
;;     (DISJOINT-P$
;;      (MV-NTH
;;       1
;;       (LAS-TO-PAS
;;        8
;;        (LOGIOR
;;         (LOGAND 4088
;;                 (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
;;         (ASH
;;          (LOGHEAD
;;           40
;;           (LOGTAIL
;;            12
;;            (MV-NTH
;;             1
;;             (RB 8
;;                 (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                         (LOGAND 4088
;;                                 (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
;;                 :R X86))))
;;          12))
;;        :R X86))
;;      (ALL-XLATION-GOVERNING-ENTRIES-PADDRS
;;       8
;;       (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;               (LOGAND 4088
;;                       (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
;;       X86))
;;     (CANONICAL-ADDRESS-P (XR :RGF *RSI* X86))
;;     (CANONICAL-ADDRESS-P (+ 1073741823 (XR :RGF *RSI* X86)))
;;     (EQUAL (LOGHEAD 30 (XR :RGF *RSI* X86))
;;            0)
;;     (NOT (MV-NTH 0
;;                  (LAS-TO-PAS 1073741824 (XR :RGF *RSI* X86)
;;                              :R X86)))
;;     (NOT
;;      (MV-NTH
;;       0
;;       (LAS-TO-PAS
;;        8
;;        (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                (LOGAND 4088
;;                        (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
;;        :R X86)))
;;     (EQUAL
;;      (LOGHEAD
;;       1
;;       (MV-NTH
;;        1
;;        (RB 8
;;            (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                    (LOGAND 4088
;;                            (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
;;            :R X86)))
;;      1)
;;     (NOT
;;      (LOGBITP
;;       7
;;       (MV-NTH
;;        1
;;        (RB 8
;;            (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                    (LOGAND 4088
;;                            (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
;;            :R X86))))
;;     (DISJOINT-P$
;;      (MV-NTH
;;       1
;;       (LAS-TO-PAS
;;        8
;;        (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                (LOGAND 4088
;;                        (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
;;        :R X86))
;;      (ALL-XLATION-GOVERNING-ENTRIES-PADDRS
;;       8
;;       (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;               (LOGAND 4088
;;                       (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
;;       X86))
;;     (CANONICAL-ADDRESS-P
;;      (LOGIOR
;;       (LOGAND 4088
;;               (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
;;       (ASH
;;        (LOGHEAD
;;         40
;;         (LOGTAIL
;;          12
;;          (MV-NTH
;;           1
;;           (RB 8
;;               (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                       (LOGAND 4088
;;                               (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
;;               :R X86))))
;;        12)))
;;     (CANONICAL-ADDRESS-P
;;      (LOGIOR
;;       (LOGAND 4088
;;               (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
;;       (ASH
;;        (LOGHEAD
;;         40
;;         (LOGTAIL
;;          12
;;          (MV-NTH
;;           1
;;           (RB 8
;;               (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                       (LOGAND 4088
;;                               (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
;;               :R X86))))
;;        12)))
;;     (NOT
;;      (MV-NTH
;;       0
;;       (LAS-TO-PAS
;;        8
;;        (LOGIOR
;;         (LOGAND 4088
;;                 (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
;;         (ASH
;;          (LOGHEAD
;;           40
;;           (LOGTAIL
;;            12
;;            (MV-NTH
;;             1
;;             (RB 8
;;                 (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                         (LOGAND 4088
;;                                 (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
;;                 :R X86))))
;;          12))
;;        :R X86)))
;;     (NOT
;;      (MV-NTH
;;       0
;;       (LAS-TO-PAS
;;        8
;;        (LOGIOR
;;         (LOGAND 4088
;;                 (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
;;         (ASH
;;          (LOGHEAD
;;           40
;;           (LOGTAIL
;;            12
;;            (MV-NTH
;;             1
;;             (RB 8
;;                 (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                         (LOGAND 4088
;;                                 (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
;;                 :R X86))))
;;          12))
;;        :W X86)))
;;     (EQUAL
;;      (LOGHEAD
;;       1
;;       (MV-NTH
;;        1
;;        (RB
;;         8
;;         (LOGIOR
;;          (LOGAND 4088
;;                  (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
;;          (ASH
;;           (LOGHEAD
;;            40
;;            (LOGTAIL
;;             12
;;             (MV-NTH
;;              1
;;              (RB
;;               8
;;               (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                       (LOGAND 4088
;;                               (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
;;               :R X86))))
;;           12))
;;         :R X86)))
;;      1)
;;     (LOGBITP
;;      7
;;      (MV-NTH
;;       1
;;       (RB
;;        8
;;        (LOGIOR
;;         (LOGAND 4088
;;                 (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
;;         (ASH
;;          (LOGHEAD
;;           40
;;           (LOGTAIL
;;            12
;;            (MV-NTH
;;             1
;;             (RB 8
;;                 (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                         (LOGAND 4088
;;                                 (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
;;                 :R X86))))
;;          12))
;;        :R X86)))
;;     (DISJOINT-P$
;;      (MV-NTH
;;       1
;;       (LAS-TO-PAS
;;        8
;;        (LOGIOR
;;         (LOGAND 4088
;;                 (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
;;         (ASH
;;          (LOGHEAD
;;           40
;;           (LOGTAIL
;;            12
;;            (MV-NTH
;;             1
;;             (RB 8
;;                 (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                         (LOGAND 4088
;;                                 (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
;;                 :R X86))))
;;          12))
;;        :W X86))
;;      (ALL-XLATION-GOVERNING-ENTRIES-PADDRS
;;       8
;;       (LOGIOR
;;        (LOGAND 4088
;;                (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
;;        (ASH
;;         (LOGHEAD
;;          40
;;          (LOGTAIL
;;           12
;;           (MV-NTH
;;            1
;;            (RB 8
;;                (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                        (LOGAND 4088
;;                                (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
;;                :R X86))))
;;         12))
;;       X86))
;;     (DISJOINT-P$
;;      (MV-NTH 1
;;              (LAS-TO-PAS 8 (+ -24 (XR :RGF *RSP* X86))
;;                          :W X86))
;;      (MV-NTH
;;       1
;;       (LAS-TO-PAS
;;        8
;;        (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                (LOGAND 4088
;;                        (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
;;        :R X86)))
;;     (DISJOINT-P$
;;      (MV-NTH
;;       1
;;       (LAS-TO-PAS
;;        8
;;        (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                (LOGAND 4088
;;                        (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
;;        :R X86))
;;      (ALL-XLATION-GOVERNING-ENTRIES-PADDRS 8 (+ -24 (XR :RGF *RSP* X86))
;;                                            X86))
;;     (DISJOINT-P$
;;      (MV-NTH 1
;;              (LAS-TO-PAS 8 (+ -24 (XR :RGF *RSP* X86))
;;                          :W X86))
;;      (ALL-XLATION-GOVERNING-ENTRIES-PADDRS
;;       8
;;       (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;               (LOGAND 4088
;;                       (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
;;       X86))
;;     (DISJOINT-P$
;;      (MV-NTH
;;       1
;;       (LAS-TO-PAS
;;        8
;;        (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                (LOGAND 4088
;;                        (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
;;        :R X86))
;;      (ALL-XLATION-GOVERNING-ENTRIES-PADDRS 272 (XR :RIP 0 X86)
;;                                            X86))
;;     (DISJOINT-P$
;;      (MV-NTH
;;       1
;;       (LAS-TO-PAS
;;        8
;;        (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                (LOGAND 4088
;;                        (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
;;        :R X86))
;;      (ALL-XLATION-GOVERNING-ENTRIES-PADDRS
;;       8
;;       (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;               (LOGAND 4088
;;                       (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
;;       X86))
;;     (DISJOINT-P$
;;      (MV-NTH
;;       1
;;       (LAS-TO-PAS
;;        8
;;        (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                (LOGAND 4088
;;                        (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
;;        :R X86))
;;      (ALL-XLATION-GOVERNING-ENTRIES-PADDRS
;;       8
;;       (LOGIOR
;;        (LOGAND 4088
;;                (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
;;        (ASH
;;         (LOGHEAD
;;          40
;;          (LOGTAIL
;;           12
;;           (MV-NTH
;;            1
;;            (RB 8
;;                (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                        (LOGAND 4088
;;                                (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
;;                :R X86))))
;;         12))
;;       X86))
;;     (DISJOINT-P$
;;      (MV-NTH
;;       1
;;       (LAS-TO-PAS
;;        8
;;        (LOGIOR
;;         (LOGAND 4088
;;                 (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
;;         (ASH
;;          (LOGHEAD
;;           40
;;           (LOGTAIL
;;            12
;;            (MV-NTH
;;             1
;;             (RB 8
;;                 (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                         (LOGAND 4088
;;                                 (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
;;                 :R X86))))
;;          12))
;;        :W X86))
;;      (ALL-XLATION-GOVERNING-ENTRIES-PADDRS
;;       8
;;       (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;               (LOGAND 4088
;;                       (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
;;       X86))
;;     (DISJOINT-P$
;;      (MV-NTH
;;       1
;;       (LAS-TO-PAS
;;        8
;;        (LOGIOR
;;         (LOGAND 4088
;;                 (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
;;         (ASH
;;          (LOGHEAD
;;           40
;;           (LOGTAIL
;;            12
;;            (MV-NTH
;;             1
;;             (RB 8
;;                 (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                         (LOGAND 4088
;;                                 (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
;;                 :R X86))))
;;          12))
;;        :W X86))
;;      (ALL-XLATION-GOVERNING-ENTRIES-PADDRS
;;       8
;;       (LOGIOR
;;        (LOGAND 4088
;;                (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
;;        (ASH
;;         (LOGHEAD
;;          40
;;          (LOGTAIL
;;           12
;;           (MV-NTH
;;            1
;;            (RB 8
;;                (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                        (LOGAND 4088
;;                                (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
;;                :R X86))))
;;         12))
;;       X86))
;;     (DISJOINT-P$
;;      (MV-NTH
;;       1
;;       (LAS-TO-PAS
;;        8
;;        (LOGIOR
;;         (LOGAND 4088
;;                 (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
;;         (ASH
;;          (LOGHEAD
;;           40
;;           (LOGTAIL
;;            12
;;            (MV-NTH
;;             1
;;             (RB 8
;;                 (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                         (LOGAND 4088
;;                                 (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
;;                 :R X86))))
;;          12))
;;        :W X86))
;;      (ALL-XLATION-GOVERNING-ENTRIES-PADDRS
;;       8
;;       (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;               (LOGAND 4088
;;                       (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
;;       X86))
;;     (DISJOINT-P$
;;      (MV-NTH 1
;;              (LAS-TO-PAS 8 (+ -24 (XR :RGF *RSP* X86))
;;                          :W X86))
;;      (MV-NTH
;;       1
;;       (LAS-TO-PAS
;;        8
;;        (LOGIOR
;;         (LOGAND 4088
;;                 (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
;;         (ASH
;;          (LOGHEAD
;;           40
;;           (LOGTAIL
;;            12
;;            (MV-NTH
;;             1
;;             (RB 8
;;                 (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                         (LOGAND 4088
;;                                 (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
;;                 :R X86))))
;;          12))
;;        :W X86)))
;;     (DISJOINT-P$
;;      (MV-NTH
;;       1
;;       (LAS-TO-PAS
;;        8
;;        (LOGIOR
;;         (LOGAND 4088
;;                 (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
;;         (ASH
;;          (LOGHEAD
;;           40
;;           (LOGTAIL
;;            12
;;            (MV-NTH
;;             1
;;             (RB 8
;;                 (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                         (LOGAND 4088
;;                                 (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
;;                 :R X86))))
;;          12))
;;        :W X86))
;;      (ALL-XLATION-GOVERNING-ENTRIES-PADDRS 8 (+ -24 (XR :RGF *RSP* X86))
;;                                            X86))
;;     (DISJOINT-P$
;;      (MV-NTH 1
;;              (LAS-TO-PAS 8 (+ -24 (XR :RGF *RSP* X86))
;;                          :W X86))
;;      (ALL-XLATION-GOVERNING-ENTRIES-PADDRS
;;       8
;;       (LOGIOR
;;        (LOGAND 4088
;;                (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
;;        (ASH
;;         (LOGHEAD
;;          40
;;          (LOGTAIL
;;           12
;;           (MV-NTH
;;            1
;;            (RB 8
;;                (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                        (LOGAND 4088
;;                                (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
;;                :R X86))))
;;         12))
;;       X86))
;;     (DISJOINT-P$
;;      (MV-NTH
;;       1
;;       (LAS-TO-PAS
;;        8
;;        (LOGIOR
;;         (LOGAND 4088
;;                 (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
;;         (ASH
;;          (LOGHEAD
;;           40
;;           (LOGTAIL
;;            12
;;            (MV-NTH
;;             1
;;             (RB 8
;;                 (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                         (LOGAND 4088
;;                                 (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
;;                 :R X86))))
;;          12))
;;        :W X86))
;;      (MV-NTH 1
;;              (LAS-TO-PAS 272 (XR :RIP 0 X86)
;;                          :X X86)))
;;     (DISJOINT-P$
;;      (MV-NTH
;;       1
;;       (LAS-TO-PAS
;;        8
;;        (LOGIOR
;;         (LOGAND 4088
;;                 (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
;;         (ASH
;;          (LOGHEAD
;;           40
;;           (LOGTAIL
;;            12
;;            (MV-NTH
;;             1
;;             (RB 8
;;                 (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                         (LOGAND 4088
;;                                 (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
;;                 :R X86))))
;;          12))
;;        :W X86))
;;      (ALL-XLATION-GOVERNING-ENTRIES-PADDRS 272 (XR :RIP 0 X86)
;;                                            X86))
;;     (DISJOINT-P$
;;      (MV-NTH 1
;;              (LAS-TO-PAS 272 (XR :RIP 0 X86) :X X86))
;;      (ALL-XLATION-GOVERNING-ENTRIES-PADDRS
;;       8
;;       (LOGIOR
;;        (LOGAND 4088
;;                (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
;;        (ASH
;;         (LOGHEAD
;;          40
;;          (LOGTAIL
;;           12
;;           (MV-NTH
;;            1
;;            (RB 8
;;                (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                        (LOGAND 4088
;;                                (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
;;                :R X86))))
;;         12))
;;       X86))
;;     (DIRECT-MAP-P
;;      8
;;      (LOGIOR
;;       (LOGAND 4088
;;               (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
;;       (ASH
;;        (LOGHEAD
;;         40
;;         (LOGTAIL
;;          12
;;          (MV-NTH
;;           1
;;           (RB 8
;;               (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                       (LOGAND 4088
;;                               (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
;;               :R X86))))
;;        12))
;;      :W X86)
;;     (HIDE (RETURN-ADDRESS-OK-P X86))
;;     (HIDE (STACK-CONTAINING-RETURN-ADDRESS-OK-P X86))
;;     (HIDE (STACK-CONTAINING-RETURN-ADDRESS-AND-PROGRAM-NO-INTERFERE-P X86))
;;     (HIDE
;;      (STACK-CONTAINING-RETURN-ADDRESS-AND-SOURCE-PML4E-NO-INTERFERE-P X86))
;;     (HIDE
;;      (STACK-CONTAINING-RETURN-ADDRESS-AND-SOURCE-PDPTE-NO-INTERFERE-P X86))
;;     (HIDE (STACK-CONTAINING-RETURN-ADDRESS-AND-DESTINATION-PML4E-NO-INTERFERE-P
;;            X86))
;;     (HIDE (STACK-CONTAINING-RETURN-ADDRESS-AND-DESTINATION-PDPTE-NO-INTERFERE-P
;;            X86))
;;     (HIDE (STACK-CONTAINING-RETURN-ADDRESS-AND-REST-OF-THE-STACK-NO-INTERFERE-P
;;            X86)))
;;    (ZP
;;     (GET-ONE-BYTE-PREFIX-ARRAY-CODE
;;      (MV-NTH
;;       '1
;;       (RB-ALT
;;        '1
;;        (BINARY-+ '190 (XR ':RIP '0 X86))
;;        ':X
;;        (!FLGI
;;         '0
;;         '0
;;         (!FLGI
;;          '2
;;          (PF-SPEC64$INLINE
;;           (BINARY-LOGIOR
;;            (BINARY-LOGAND
;;             '18442240475155922943
;;             (MV-NTH
;;              '1
;;              (RB
;;               '8
;;               (BINARY-LOGIOR
;;                (BINARY-LOGAND
;;                 '4088
;;                 (ACL2::LOGHEAD$INLINE '32
;;                                       (ACL2::LOGTAIL$INLINE '27
;;                                                             (XR ':RGF '6 X86))))
;;                (ASH
;;                 (ACL2::LOGHEAD$INLINE
;;                  '40
;;                  (ACL2::LOGTAIL$INLINE
;;                   '12
;;                   (MV-NTH
;;                    '1
;;                    (RB
;;                     '8
;;                     (BINARY-LOGIOR
;;                      (BINARY-LOGAND '-4096
;;                                     (LOGEXT '64 (XR ':CTR '3 X86)))
;;                      (BINARY-LOGAND
;;                       '4088
;;                       (ACL2::LOGHEAD$INLINE
;;                        '28
;;                        (ACL2::LOGTAIL$INLINE '36
;;                                              (XR ':RGF '6 X86)))))
;;                     ':R
;;                     X86))))
;;                 '12))
;;               ':R
;;               X86)))
;;            (BINARY-LOGAND
;;             '4503598553628672
;;             (MV-NTH
;;              '1
;;              (RB
;;               '8
;;               (BINARY-LOGIOR
;;                (BINARY-LOGAND
;;                 '4088
;;                 (ACL2::LOGHEAD$INLINE '32
;;                                       (ACL2::LOGTAIL$INLINE '27
;;                                                             (XR ':RGF '7 X86))))
;;                (ASH
;;                 (ACL2::LOGHEAD$INLINE
;;                  '40
;;                  (ACL2::LOGTAIL$INLINE
;;                   '12
;;                   (MV-NTH
;;                    '1
;;                    (RB
;;                     '8
;;                     (BINARY-LOGIOR
;;                      (BINARY-LOGAND '-4096
;;                                     (LOGEXT '64 (XR ':CTR '3 X86)))
;;                      (BINARY-LOGAND
;;                       '4088
;;                       (ACL2::LOGHEAD$INLINE
;;                        '28
;;                        (ACL2::LOGTAIL$INLINE '36
;;                                              (XR ':RGF '7 X86)))))
;;                     ':R
;;                     X86))))
;;                 '12))
;;               ':R
;;               X86)))))
;;          (!FLGI
;;           '4
;;           (ACL2::LOGHEAD$INLINE
;;            '1
;;            (CREATE-UNDEF (BINARY-+ '38
;;                                    (NFIX (XR ':UNDEF '0 X86)))))
;;           (!FLGI
;;            '6
;;            (ZF-SPEC$INLINE
;;             (BINARY-LOGIOR
;;              (BINARY-LOGAND
;;               '18442240475155922943
;;               (MV-NTH
;;                '1
;;                (RB
;;                 '8
;;                 (BINARY-LOGIOR
;;                  (BINARY-LOGAND '4088
;;                                 (ACL2::LOGHEAD$INLINE
;;                                  '32
;;                                  (ACL2::LOGTAIL$INLINE '27
;;                                                        (XR ':RGF '6 X86))))
;;                  (ASH
;;                   (ACL2::LOGHEAD$INLINE
;;                    '40
;;                    (ACL2::LOGTAIL$INLINE
;;                     '12
;;                     (MV-NTH
;;                      '1
;;                      (RB
;;                       '8
;;                       (BINARY-LOGIOR
;;                        (BINARY-LOGAND '-4096
;;                                       (LOGEXT '64 (XR ':CTR '3 X86)))
;;                        (BINARY-LOGAND
;;                         '4088
;;                         (ACL2::LOGHEAD$INLINE
;;                          '28
;;                          (ACL2::LOGTAIL$INLINE '36
;;                                                (XR ':RGF '6 X86)))))
;;                       ':R
;;                       X86))))
;;                   '12))
;;                 ':R
;;                 X86)))
;;              (BINARY-LOGAND
;;               '4503598553628672
;;               (MV-NTH
;;                '1
;;                (RB
;;                 '8
;;                 (BINARY-LOGIOR
;;                  (BINARY-LOGAND '4088
;;                                 (ACL2::LOGHEAD$INLINE
;;                                  '32
;;                                  (ACL2::LOGTAIL$INLINE '27
;;                                                        (XR ':RGF '7 X86))))
;;                  (ASH
;;                   (ACL2::LOGHEAD$INLINE
;;                    '40
;;                    (ACL2::LOGTAIL$INLINE
;;                     '12
;;                     (MV-NTH
;;                      '1
;;                      (RB
;;                       '8
;;                       (BINARY-LOGIOR
;;                        (BINARY-LOGAND '-4096
;;                                       (LOGEXT '64 (XR ':CTR '3 X86)))
;;                        (BINARY-LOGAND
;;                         '4088
;;                         (ACL2::LOGHEAD$INLINE
;;                          '28
;;                          (ACL2::LOGTAIL$INLINE '36
;;                                                (XR ':RGF '7 X86)))))
;;                       ':R
;;                       X86))))
;;                   '12))
;;                 ':R
;;                 X86)))))
;;            (!FLGI
;;             '7
;;             (SF-SPEC64$INLINE
;;              (BINARY-LOGIOR
;;               (BINARY-LOGAND
;;                '18442240475155922943
;;                (MV-NTH
;;                 '1
;;                 (RB
;;                  '8
;;                  (BINARY-LOGIOR
;;                   (BINARY-LOGAND '4088
;;                                  (ACL2::LOGHEAD$INLINE
;;                                   '32
;;                                   (ACL2::LOGTAIL$INLINE '27
;;                                                         (XR ':RGF '6 X86))))
;;                   (ASH
;;                    (ACL2::LOGHEAD$INLINE
;;                     '40
;;                     (ACL2::LOGTAIL$INLINE
;;                      '12
;;                      (MV-NTH
;;                       '1
;;                       (RB
;;                        '8
;;                        (BINARY-LOGIOR
;;                         (BINARY-LOGAND '-4096
;;                                        (LOGEXT '64 (XR ':CTR '3 X86)))
;;                         (BINARY-LOGAND
;;                          '4088
;;                          (ACL2::LOGHEAD$INLINE
;;                           '28
;;                           (ACL2::LOGTAIL$INLINE '36
;;                                                 (XR ':RGF '6 X86)))))
;;                        ':R
;;                        X86))))
;;                    '12))
;;                  ':R
;;                  X86)))
;;               (BINARY-LOGAND
;;                '4503598553628672
;;                (MV-NTH
;;                 '1
;;                 (RB
;;                  '8
;;                  (BINARY-LOGIOR
;;                   (BINARY-LOGAND '4088
;;                                  (ACL2::LOGHEAD$INLINE
;;                                   '32
;;                                   (ACL2::LOGTAIL$INLINE '27
;;                                                         (XR ':RGF '7 X86))))
;;                   (ASH
;;                    (ACL2::LOGHEAD$INLINE
;;                     '40
;;                     (ACL2::LOGTAIL$INLINE
;;                      '12
;;                      (MV-NTH
;;                       '1
;;                       (RB
;;                        '8
;;                        (BINARY-LOGIOR
;;                         (BINARY-LOGAND '-4096
;;                                        (LOGEXT '64 (XR ':CTR '3 X86)))
;;                         (BINARY-LOGAND
;;                          '4088
;;                          (ACL2::LOGHEAD$INLINE
;;                           '28
;;                           (ACL2::LOGTAIL$INLINE '36
;;                                                 (XR ':RGF '7 X86)))))
;;                        ':R
;;                        X86))))
;;                    '12))
;;                  ':R
;;                  X86)))))
;;             (!FLGI
;;              '11
;;              '0
;;              (MV-NTH
;;               '1
;;               (WB
;;                '8
;;                (BINARY-LOGIOR
;;                 (BINARY-LOGAND '4088
;;                                (ACL2::LOGHEAD$INLINE
;;                                 '32
;;                                 (ACL2::LOGTAIL$INLINE '27
;;                                                       (XR ':RGF '6 X86))))
;;                 (ASH
;;                  (ACL2::LOGHEAD$INLINE
;;                   '40
;;                   (ACL2::LOGTAIL$INLINE
;;                    '12
;;                    (MV-NTH
;;                     '1
;;                     (RB
;;                      '8
;;                      (BINARY-LOGIOR
;;                       (BINARY-LOGAND '-4096
;;                                      (LOGEXT '64 (XR ':CTR '3 X86)))
;;                       (BINARY-LOGAND
;;                        '4088
;;                        (ACL2::LOGHEAD$INLINE
;;                         '28
;;                         (ACL2::LOGTAIL$INLINE '36
;;                                               (XR ':RGF '6 X86)))))
;;                      ':R
;;                      X86))))
;;                  '12))
;;                ':W
;;                (BINARY-LOGIOR
;;                 (BINARY-LOGAND
;;                  '18442240475155922943
;;                  (MV-NTH
;;                   '1
;;                   (RB
;;                    '8
;;                    (BINARY-LOGIOR
;;                     (BINARY-LOGAND
;;                      '4088
;;                      (ACL2::LOGHEAD$INLINE
;;                       '32
;;                       (ACL2::LOGTAIL$INLINE '27
;;                                             (XR ':RGF '6 X86))))
;;                     (ASH
;;                      (ACL2::LOGHEAD$INLINE
;;                       '40
;;                       (ACL2::LOGTAIL$INLINE
;;                        '12
;;                        (MV-NTH
;;                         '1
;;                         (RB
;;                          '8
;;                          (BINARY-LOGIOR
;;                           (BINARY-LOGAND '-4096
;;                                          (LOGEXT '64 (XR ':CTR '3 X86)))
;;                           (BINARY-LOGAND
;;                            '4088
;;                            (ACL2::LOGHEAD$INLINE
;;                             '28
;;                             (ACL2::LOGTAIL$INLINE '36
;;                                                   (XR ':RGF '6 X86)))))
;;                          ':R
;;                          X86))))
;;                      '12))
;;                    ':R
;;                    X86)))
;;                 (BINARY-LOGAND
;;                  '4503598553628672
;;                  (MV-NTH
;;                   '1
;;                   (RB
;;                    '8
;;                    (BINARY-LOGIOR
;;                     (BINARY-LOGAND
;;                      '4088
;;                      (ACL2::LOGHEAD$INLINE
;;                       '32
;;                       (ACL2::LOGTAIL$INLINE '27
;;                                             (XR ':RGF '7 X86))))
;;                     (ASH
;;                      (ACL2::LOGHEAD$INLINE
;;                       '40
;;                       (ACL2::LOGTAIL$INLINE
;;                        '12
;;                        (MV-NTH
;;                         '1
;;                         (RB
;;                          '8
;;                          (BINARY-LOGIOR
;;                           (BINARY-LOGAND '-4096
;;                                          (LOGEXT '64 (XR ':CTR '3 X86)))
;;                           (BINARY-LOGAND
;;                            '4088
;;                            (ACL2::LOGHEAD$INLINE
;;                             '28
;;                             (ACL2::LOGTAIL$INLINE '36
;;                                                   (XR ':RGF '7 X86)))))
;;                          ':R
;;                          X86))))
;;                      '12))
;;                    ':R
;;                    X86))))
;;                (MV-NTH
;;                 '2
;;                 (LAS-TO-PAS
;;                  '6
;;                  (BINARY-+ '184 (XR ':RIP '0 X86))
;;                  ':X
;;                  (MV-NTH
;;                   '2
;;                   (LAS-TO-PAS
;;                    '8
;;                    (BINARY-LOGIOR
;;                     (BINARY-LOGAND
;;                      '4088
;;                      (ACL2::LOGHEAD$INLINE
;;                       '32
;;                       (ACL2::LOGTAIL$INLINE '27
;;                                             (XR ':RGF '6 X86))))
;;                     (ASH
;;                      (ACL2::LOGHEAD$INLINE
;;                       '40
;;                       (ACL2::LOGTAIL$INLINE
;;                        '12
;;                        (MV-NTH
;;                         '1
;;                         (RB
;;                          '8
;;                          (BINARY-LOGIOR
;;                           (BINARY-LOGAND '-4096
;;                                          (LOGEXT '64 (XR ':CTR '3 X86)))
;;                           (BINARY-LOGAND
;;                            '4088
;;                            (ACL2::LOGHEAD$INLINE
;;                             '28
;;                             (ACL2::LOGTAIL$INLINE '36
;;                                                   (XR ':RGF '6 X86)))))
;;                          ':R
;;                          X86))))
;;                      '12))
;;                    ':R
;;                    (MV-NTH
;;                     '2
;;                     (LAS-TO-PAS
;;                      '40
;;                      (BINARY-+ '144 (XR ':RIP '0 X86))
;;                      ':X
;;                      (MV-NTH
;;                       '2
;;                       (LAS-TO-PAS
;;                        '3
;;                        (BINARY-+ '140 (XR ':RIP '0 X86))
;;                        ':X
;;                        (MV-NTH
;;                         '2
;;                         (LAS-TO-PAS
;;                          '8
;;                          (BINARY-LOGIOR
;;                           (BINARY-LOGAND '-4096
;;                                          (LOGEXT '64 (XR ':CTR '3 X86)))
;;                           (BINARY-LOGAND
;;                            '4088
;;                            (ACL2::LOGHEAD$INLINE
;;                             '28
;;                             (ACL2::LOGTAIL$INLINE '36
;;                                                   (XR ':RGF '6 X86)))))
;;                          ':R
;;                          (MV-NTH
;;                           '2
;;                           (LAS-TO-PAS
;;                            '32
;;                            (BINARY-+ '108 (XR ':RIP '0 X86))
;;                            ':X
;;                            (MV-NTH
;;                             '2
;;                             (LAS-TO-PAS
;;                              '18
;;                              (BINARY-+ '86 (XR ':RIP '0 X86))
;;                              ':X
;;                              (MV-NTH
;;                               '2
;;                               (LAS-TO-PAS
;;                                '8
;;                                (BINARY-LOGIOR
;;                                 (BINARY-LOGAND
;;                                  '4088
;;                                  (ACL2::LOGHEAD$INLINE
;;                                   '32
;;                                   (ACL2::LOGTAIL$INLINE '27
;;                                                         (XR ':RGF '7 X86))))
;;                                 (ASH
;;                                  (ACL2::LOGHEAD$INLINE
;;                                   '40
;;                                   (ACL2::LOGTAIL$INLINE
;;                                    '12
;;                                    (MV-NTH
;;                                     '1
;;                                     (RB
;;                                      '8
;;                                      (BINARY-LOGIOR
;;                                       (BINARY-LOGAND
;;                                        '-4096
;;                                        (LOGEXT '64 (XR ':CTR '3 X86)))
;;                                       (BINARY-LOGAND
;;                                        '4088
;;                                        (ACL2::LOGHEAD$INLINE
;;                                         '28
;;                                         (ACL2::LOGTAIL$INLINE
;;                                          '36
;;                                          (XR ':RGF '7 X86)))))
;;                                      ':R
;;                                      X86))))
;;                                  '12))
;;                                ':R
;;                                (MV-NTH
;;                                 '2
;;                                 (LAS-TO-PAS
;;                                  '40
;;                                  (BINARY-+ '46 (XR ':RIP '0 X86))
;;                                  ':X
;;                                  (MV-NTH
;;                                   '2
;;                                   (LAS-TO-PAS
;;                                    '4
;;                                    (BINARY-+ '38 (XR ':RIP '0 X86))
;;                                    ':X
;;                                    (MV-NTH
;;                                     '2
;;                                     (LAS-TO-PAS
;;                                      '8
;;                                      (BINARY-LOGIOR
;;                                       (BINARY-LOGAND
;;                                        '-4096
;;                                        (LOGEXT '64 (XR ':CTR '3 X86)))
;;                                       (BINARY-LOGAND
;;                                        '4088
;;                                        (ACL2::LOGHEAD$INLINE
;;                                         '28
;;                                         (ACL2::LOGTAIL$INLINE
;;                                          '36
;;                                          (XR ':RGF '7 X86)))))
;;                                      ':R
;;                                      (MV-NTH
;;                                       '2
;;                                       (LAS-TO-PAS
;;                                        '25
;;                                        (BINARY-+ '13 (XR ':RIP '0 X86))
;;                                        ':X
;;                                        (MV-NTH
;;                                         '2
;;                                         (LAS-TO-PAS
;;                                          '8
;;                                          (BINARY-+ '-24 (XR ':RGF '4 X86))
;;                                          ':R
;;                                          (MV-NTH
;;                                           '2
;;                                           (LAS-TO-PAS
;;                                            '5
;;                                            (BINARY-+ '8 (XR ':RIP '0 X86))
;;                                            ':X
;;                                            (MV-NTH
;;                                             '1
;;                                             (WB
;;                                              '8
;;                                              (BINARY-+ '-24 (XR ':RGF '4 X86))
;;                                              ':W
;;                                              (XR ':CTR '3 X86)
;;                                              (MV-NTH
;;                                               '2
;;                                               (LAS-TO-PAS
;;                                                '8
;;                                                (XR ':RIP '0 X86)
;;                                                ':X
;;                                                X86)))))))))))))))))))))))))))))))))))))))))))))
;;   :hints (("Goal"
;;            :do-not-induct t
;;            :do-not '(preprocess)
;;            :in-theory
;;            (e/d* (len
;;                   page-size
;;                   loghead-negative
;;                   disjoint-p-all-xlation-governing-entries-paddrs-subset-p)
;;                  (create-canonical-address-list
;;                   (:rewrite program-at-values-and-!flgi)
;;                   (:rewrite get-prefixes-opener-lemma-group-4-prefix-in-marking-view)
;;                   (:rewrite get-prefixes-opener-lemma-group-3-prefix-in-marking-view)
;;                   (:rewrite get-prefixes-opener-lemma-group-2-prefix-in-marking-view)
;;                   (:rewrite get-prefixes-opener-lemma-group-1-prefix-in-marking-view)
;;                   (:rewrite mv-nth-1-rb-and-xlate-equiv-memory-disjoint-from-paging-structures)
;;                   (:rewrite mv-nth-2-rb-in-system-level-non-marking-view)
;;                   (:rewrite rb-returns-x86-app-view)
;;                   (:linear rm-low-64-logand-logior-helper-1)
;;                   (:definition n64p$inline)
;;                   (:type-prescription xlate-equiv-memory)
;;                   (:rewrite program-at-alt-wb-disjoint-in-sys-view)
;;                   (:type-prescription natp-page-dir-ptr-table-entry-addr)
;;                   mv-nth-1-las-to-pas-subset-p-disjoint-from-other-p-addrs
;;                   mv-nth-2-las-to-pas-system-level-non-marking-view
;;                   (:rewrite r-w-x-is-irrelevant-for-mv-nth-2-las-to-pas-when-no-errors)
;;                   (:rewrite acl2::cdr-of-append-when-consp)
;;                   (:rewrite acl2::car-of-append)
;;                   (:rewrite acl2::consp-of-append)
;;                   (:rewrite acl2::append-atom-under-list-equiv)
;;                   (:type-prescription binary-append)
;;                   (:rewrite xr-fault-wb-in-sys-view)
;;                   (:type-prescription n01p-page-size)
;;                   (:type-prescription member-p-physical-address-p-physical-address-listp)
;;                   (:rewrite acl2::right-cancellation-for-+)
;;                   (:type-prescription member-p-physical-address-p)
;;                   (:rewrite acl2::append-singleton-under-set-equiv))))))

;; (thm
;;  (IMPLIES
;;   (AND

;;    (X86P X86)
;;    (NOT (XR :MS 0 X86))
;;    (NOT (XR :FAULT 0 X86))
;;    (NOT (ALIGNMENT-CHECKING-ENABLED-P X86))
;;    (NOT (XR :APP-VIEW 0 X86))
;;    (XR :PAGE-STRUCTURE-MARKING-VIEW 0 X86)
;;    (EQUAL (LOGHEAD 2 (XR :SEG-VISIBLE 1 X86))
;;           0)
;;    (EQUAL (LOGTAIL 40 (XR :CTR *CR3* X86))
;;           0)
;;    (CANONICAL-ADDRESS-P (+ 272 (XR :RIP 0 X86)))
;;    (PROGRAM-AT-ALT (XR :RIP 0 X86)
;;                    '(15 32 216 72 137 68 36 232 72 139 84 36 232
;;                         72 137 248 72 193 232 36 37 248 15 0 0
;;                         72 129 226 0 240 255 255 72 9 208 72 139
;;                         0 168 1 15 132 210 0 0 0 72 193 232 12
;;                         73 184 255 255 255 255 255 0 0 0 72 137
;;                         249 76 33 192 72 193 233 27 129 225 248
;;                         15 0 0 72 193 224 12 72 9 200 72 139 0
;;                         72 137 193 129 225 129 0 0 0 72 129 249
;;                         129 0 0 0 15 133 148 0 0 0 72 137 241
;;                         73 185 0 0 0 192 255 255 15 0 72 193 233
;;                         36 73 33 193 129 225 248 15 0 0 72 9 209
;;                         72 139 1 168 1 116 112 72 193 232 12 72
;;                         137 242 76 33 192 72 193 234 27 129 226
;;                         248 15 0 0 72 193 224 12 72 9 208 72 186
;;                         255 255 255 63 0 0 240 255 72 35 16 76
;;                         9 202 72 137 16 72 137 208 37 129 0 0 0
;;                         72 61 129 0 0 0 117 50 72 184 0 0 0 192
;;                         255 255 15 0 129 230 255 255 255 63 129
;;                         231 255 255 255 63 72 33 194 76 9 207
;;                         49 192 72 9 242 72 57 215 15 148 192 195
;;                         102 46 15 31 132 0 0 0 0 0 72 199 192
;;                         255 255 255 255 195 15 31 132 0 0 0 0 0)
;;                    X86)
;;    (DISJOINT-P$
;;     (MV-NTH 1
;;             (LAS-TO-PAS 272 (XR :RIP 0 X86) :X X86))
;;     (OPEN-QWORD-PADDR-LIST (GATHER-ALL-PAGING-STRUCTURE-QWORD-ADDRESSES X86)))
;;    (CANONICAL-ADDRESS-P (+ -24 (XR :RGF *RSP* X86)))
;;    (CANONICAL-ADDRESS-P (+ 8 (XR :RGF *RSP* X86)))
;;    (NOT (MV-NTH 0
;;                 (LAS-TO-PAS 8 (+ -24 (XR :RGF *RSP* X86))
;;                             :W X86)))
;;    (NOT (MV-NTH 0
;;                 (LAS-TO-PAS 8 (+ -24 (XR :RGF *RSP* X86))
;;                             :R X86)))
;;    (NO-DUPLICATES-P (MV-NTH 1
;;                             (LAS-TO-PAS 8 (+ -24 (XR :RGF *RSP* X86))
;;                                         :W X86)))
;;    (DISJOINT-P$
;;     (MV-NTH 1
;;             (LAS-TO-PAS 8 (+ -24 (XR :RGF *RSP* X86))
;;                         :W X86))
;;     (OPEN-QWORD-PADDR-LIST (GATHER-ALL-PAGING-STRUCTURE-QWORD-ADDRESSES X86)))
;;    (DISJOINT-P$ (MV-NTH 1
;;                         (LAS-TO-PAS 8 (+ -24 (XR :RGF *RSP* X86))
;;                                     :W X86))
;;                 (MV-NTH 1
;;                         (LAS-TO-PAS 272 (XR :RIP 0 X86)
;;                                     :X X86)))
;;    (DISJOINT-P$ (MV-NTH 1
;;                         (LAS-TO-PAS 8 (+ -24 (XR :RGF *RSP* X86))
;;                                     :W X86))
;;                 (ALL-XLATION-GOVERNING-ENTRIES-PADDRS 272 (XR :RIP 0 X86)
;;                                                       X86))
;;    (CANONICAL-ADDRESS-P (XR :RGF *RDI* X86))
;;    (CANONICAL-ADDRESS-P (+ 1073741823 (XR :RGF *RDI* X86)))
;;    (EQUAL (LOGHEAD 30 (XR :RGF *RDI* X86))
;;           0)
;;    (NOT (MV-NTH 0
;;                 (LAS-TO-PAS 1073741824 (XR :RGF *RDI* X86)
;;                             :R X86)))
;;    (NOT
;;     (MV-NTH
;;      0
;;      (LAS-TO-PAS
;;       8
;;       (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;               (LOGAND 4088
;;                       (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
;;       :R X86)))
;;    (EQUAL
;;     (LOGHEAD
;;      1
;;      (MV-NTH
;;       1
;;       (RB 8
;;           (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                   (LOGAND 4088
;;                           (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
;;           :R X86)))
;;     1)
;;    (DISJOINT-P$
;;     (MV-NTH
;;      1
;;      (LAS-TO-PAS
;;       8
;;       (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;               (LOGAND 4088
;;                       (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
;;       :R X86))
;;     (ALL-XLATION-GOVERNING-ENTRIES-PADDRS
;;      8
;;      (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;              (LOGAND 4088
;;                      (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
;;      X86))
;;    (NOT
;;     (MV-NTH
;;      0
;;      (LAS-TO-PAS
;;       8
;;       (LOGIOR
;;        (LOGAND 4088
;;                (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
;;        (ASH
;;         (LOGHEAD
;;          40
;;          (LOGTAIL
;;           12
;;           (MV-NTH
;;            1
;;            (RB 8
;;                (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                        (LOGAND 4088
;;                                (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
;;                :R X86))))
;;         12))
;;       :R X86)))
;;    (EQUAL
;;     (LOGHEAD
;;      1
;;      (MV-NTH
;;       1
;;       (RB
;;        8
;;        (LOGIOR
;;         (LOGAND 4088
;;                 (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
;;         (ASH
;;          (LOGHEAD
;;           40
;;           (LOGTAIL
;;            12
;;            (MV-NTH
;;             1
;;             (RB
;;              8
;;              (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                      (LOGAND 4088
;;                              (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
;;              :R X86))))
;;          12))
;;        :R X86)))
;;     1)
;;    (LOGBITP
;;     7
;;     (MV-NTH
;;      1
;;      (RB
;;       8
;;       (LOGIOR
;;        (LOGAND 4088
;;                (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
;;        (ASH
;;         (LOGHEAD
;;          40
;;          (LOGTAIL
;;           12
;;           (MV-NTH
;;            1
;;            (RB 8
;;                (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                        (LOGAND 4088
;;                                (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
;;                :R X86))))
;;         12))
;;       :R X86)))
;;    (DISJOINT-P$
;;     (MV-NTH
;;      1
;;      (LAS-TO-PAS
;;       8
;;       (LOGIOR
;;        (LOGAND 4088
;;                (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
;;        (ASH
;;         (LOGHEAD
;;          40
;;          (LOGTAIL
;;           12
;;           (MV-NTH
;;            1
;;            (RB 8
;;                (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                        (LOGAND 4088
;;                                (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
;;                :R X86))))
;;         12))
;;       :R X86))
;;     (ALL-XLATION-GOVERNING-ENTRIES-PADDRS
;;      8
;;      (LOGIOR
;;       (LOGAND 4088
;;               (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
;;       (ASH
;;        (LOGHEAD
;;         40
;;         (LOGTAIL
;;          12
;;          (MV-NTH
;;           1
;;           (RB 8
;;               (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                       (LOGAND 4088
;;                               (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
;;               :R X86))))
;;        12))
;;      X86))
;;    (DISJOINT-P$
;;     (MV-NTH 1
;;             (LAS-TO-PAS 8 (+ -24 (XR :RGF *RSP* X86))
;;                         :W X86))
;;     (MV-NTH
;;      1
;;      (LAS-TO-PAS
;;       8
;;       (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;               (LOGAND 4088
;;                       (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
;;       :R X86)))
;;    (DISJOINT-P$
;;     (MV-NTH
;;      1
;;      (LAS-TO-PAS
;;       8
;;       (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;               (LOGAND 4088
;;                       (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
;;       :R X86))
;;     (ALL-XLATION-GOVERNING-ENTRIES-PADDRS 8 (+ -24 (XR :RGF *RSP* X86))
;;                                           X86))
;;    (DISJOINT-P$
;;     (MV-NTH 1
;;             (LAS-TO-PAS 8 (+ -24 (XR :RGF *RSP* X86))
;;                         :W X86))
;;     (ALL-XLATION-GOVERNING-ENTRIES-PADDRS
;;      8
;;      (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;              (LOGAND 4088
;;                      (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
;;      X86))
;;    (DISJOINT-P$
;;     (MV-NTH
;;      1
;;      (LAS-TO-PAS
;;       8
;;       (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;               (LOGAND 4088
;;                       (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
;;       :R X86))
;;     (ALL-XLATION-GOVERNING-ENTRIES-PADDRS 272 (XR :RIP 0 X86)
;;                                           X86))
;;    (DISJOINT-P$
;;     (MV-NTH 1
;;             (LAS-TO-PAS 8 (+ -24 (XR :RGF *RSP* X86))
;;                         :W X86))
;;     (MV-NTH
;;      1
;;      (LAS-TO-PAS
;;       8
;;       (LOGIOR
;;        (LOGAND 4088
;;                (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
;;        (ASH
;;         (LOGHEAD
;;          40
;;          (LOGTAIL
;;           12
;;           (MV-NTH
;;            1
;;            (RB 8
;;                (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                        (LOGAND 4088
;;                                (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
;;                :R X86))))
;;         12))
;;       :R X86)))
;;    (DISJOINT-P$
;;     (MV-NTH
;;      1
;;      (LAS-TO-PAS
;;       8
;;       (LOGIOR
;;        (LOGAND 4088
;;                (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
;;        (ASH
;;         (LOGHEAD
;;          40
;;          (LOGTAIL
;;           12
;;           (MV-NTH
;;            1
;;            (RB 8
;;                (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                        (LOGAND 4088
;;                                (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
;;                :R X86))))
;;         12))
;;       :R X86))
;;     (ALL-XLATION-GOVERNING-ENTRIES-PADDRS 8 (+ -24 (XR :RGF *RSP* X86))
;;                                           X86))
;;    (DISJOINT-P$
;;     (MV-NTH
;;      1
;;      (LAS-TO-PAS
;;       8
;;       (LOGIOR
;;        (LOGAND 4088
;;                (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
;;        (ASH
;;         (LOGHEAD
;;          40
;;          (LOGTAIL
;;           12
;;           (MV-NTH
;;            1
;;            (RB 8
;;                (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                        (LOGAND 4088
;;                                (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
;;                :R X86))))
;;         12))
;;       :R X86))
;;     (ALL-XLATION-GOVERNING-ENTRIES-PADDRS 272 (XR :RIP 0 X86)
;;                                           X86))
;;    (DISJOINT-P$
;;     (MV-NTH
;;      1
;;      (LAS-TO-PAS
;;       8
;;       (LOGIOR
;;        (LOGAND 4088
;;                (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
;;        (ASH
;;         (LOGHEAD
;;          40
;;          (LOGTAIL
;;           12
;;           (MV-NTH
;;            1
;;            (RB 8
;;                (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                        (LOGAND 4088
;;                                (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
;;                :R X86))))
;;         12))
;;       :R X86))
;;     (ALL-XLATION-GOVERNING-ENTRIES-PADDRS
;;      8
;;      (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;              (LOGAND 4088
;;                      (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
;;      X86))
;;    (CANONICAL-ADDRESS-P (XR :RGF *RSI* X86))
;;    (CANONICAL-ADDRESS-P (+ 1073741823 (XR :RGF *RSI* X86)))
;;    (EQUAL (LOGHEAD 30 (XR :RGF *RSI* X86))
;;           0)
;;    (NOT (MV-NTH 0
;;                 (LAS-TO-PAS 1073741824 (XR :RGF *RSI* X86)
;;                             :R X86)))
;;    (NOT
;;     (MV-NTH
;;      0
;;      (LAS-TO-PAS
;;       8
;;       (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;               (LOGAND 4088
;;                       (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
;;       :R X86)))
;;    (EQUAL
;;     (LOGHEAD
;;      1
;;      (MV-NTH
;;       1
;;       (RB 8
;;           (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                   (LOGAND 4088
;;                           (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
;;           :R X86)))
;;     1)
;;    (NOT
;;     (LOGBITP
;;      7
;;      (MV-NTH
;;       1
;;       (RB 8
;;           (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                   (LOGAND 4088
;;                           (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
;;           :R X86))))
;;    (DISJOINT-P$
;;     (MV-NTH
;;      1
;;      (LAS-TO-PAS
;;       8
;;       (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;               (LOGAND 4088
;;                       (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
;;       :R X86))
;;     (ALL-XLATION-GOVERNING-ENTRIES-PADDRS
;;      8
;;      (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;              (LOGAND 4088
;;                      (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
;;      X86))
;;    (CANONICAL-ADDRESS-P
;;     (LOGIOR
;;      (LOGAND 4088
;;              (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
;;      (ASH
;;       (LOGHEAD
;;        40
;;        (LOGTAIL
;;         12
;;         (MV-NTH
;;          1
;;          (RB 8
;;              (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                      (LOGAND 4088
;;                              (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
;;              :R X86))))
;;       12)))
;;    (CANONICAL-ADDRESS-P
;;     (LOGIOR
;;      (LOGAND 4088
;;              (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
;;      (ASH
;;       (LOGHEAD
;;        40
;;        (LOGTAIL
;;         12
;;         (MV-NTH
;;          1
;;          (RB 8
;;              (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                      (LOGAND 4088
;;                              (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
;;              :R X86))))
;;       12)))
;;    (NOT
;;     (MV-NTH
;;      0
;;      (LAS-TO-PAS
;;       8
;;       (LOGIOR
;;        (LOGAND 4088
;;                (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
;;        (ASH
;;         (LOGHEAD
;;          40
;;          (LOGTAIL
;;           12
;;           (MV-NTH
;;            1
;;            (RB 8
;;                (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                        (LOGAND 4088
;;                                (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
;;                :R X86))))
;;         12))
;;       :R X86)))
;;    (NOT
;;     (MV-NTH
;;      0
;;      (LAS-TO-PAS
;;       8
;;       (LOGIOR
;;        (LOGAND 4088
;;                (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
;;        (ASH
;;         (LOGHEAD
;;          40
;;          (LOGTAIL
;;           12
;;           (MV-NTH
;;            1
;;            (RB 8
;;                (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                        (LOGAND 4088
;;                                (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
;;                :R X86))))
;;         12))
;;       :W X86)))
;;    (EQUAL
;;     (LOGHEAD
;;      1
;;      (MV-NTH
;;       1
;;       (RB
;;        8
;;        (LOGIOR
;;         (LOGAND 4088
;;                 (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
;;         (ASH
;;          (LOGHEAD
;;           40
;;           (LOGTAIL
;;            12
;;            (MV-NTH
;;             1
;;             (RB
;;              8
;;              (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                      (LOGAND 4088
;;                              (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
;;              :R X86))))
;;          12))
;;        :R X86)))
;;     1)
;;    (LOGBITP
;;     7
;;     (MV-NTH
;;      1
;;      (RB
;;       8
;;       (LOGIOR
;;        (LOGAND 4088
;;                (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
;;        (ASH
;;         (LOGHEAD
;;          40
;;          (LOGTAIL
;;           12
;;           (MV-NTH
;;            1
;;            (RB 8
;;                (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                        (LOGAND 4088
;;                                (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
;;                :R X86))))
;;         12))
;;       :R X86)))
;;    (DISJOINT-P$
;;     (MV-NTH
;;      1
;;      (LAS-TO-PAS
;;       8
;;       (LOGIOR
;;        (LOGAND 4088
;;                (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
;;        (ASH
;;         (LOGHEAD
;;          40
;;          (LOGTAIL
;;           12
;;           (MV-NTH
;;            1
;;            (RB 8
;;                (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                        (LOGAND 4088
;;                                (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
;;                :R X86))))
;;         12))
;;       :W X86))
;;     (ALL-XLATION-GOVERNING-ENTRIES-PADDRS
;;      8
;;      (LOGIOR
;;       (LOGAND 4088
;;               (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
;;       (ASH
;;        (LOGHEAD
;;         40
;;         (LOGTAIL
;;          12
;;          (MV-NTH
;;           1
;;           (RB 8
;;               (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                       (LOGAND 4088
;;                               (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
;;               :R X86))))
;;        12))
;;      X86))
;;    (DISJOINT-P$
;;     (MV-NTH 1
;;             (LAS-TO-PAS 8 (+ -24 (XR :RGF *RSP* X86))
;;                         :W X86))
;;     (MV-NTH
;;      1
;;      (LAS-TO-PAS
;;       8
;;       (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;               (LOGAND 4088
;;                       (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
;;       :R X86)))
;;    (DISJOINT-P$
;;     (MV-NTH
;;      1
;;      (LAS-TO-PAS
;;       8
;;       (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;               (LOGAND 4088
;;                       (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
;;       :R X86))
;;     (ALL-XLATION-GOVERNING-ENTRIES-PADDRS 8 (+ -24 (XR :RGF *RSP* X86))
;;                                           X86))
;;    (DISJOINT-P$
;;     (MV-NTH 1
;;             (LAS-TO-PAS 8 (+ -24 (XR :RGF *RSP* X86))
;;                         :W X86))
;;     (ALL-XLATION-GOVERNING-ENTRIES-PADDRS
;;      8
;;      (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;              (LOGAND 4088
;;                      (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
;;      X86))
;;    (DISJOINT-P$
;;     (MV-NTH
;;      1
;;      (LAS-TO-PAS
;;       8
;;       (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;               (LOGAND 4088
;;                       (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
;;       :R X86))
;;     (ALL-XLATION-GOVERNING-ENTRIES-PADDRS 272 (XR :RIP 0 X86)
;;                                           X86))
;;    (DISJOINT-P$
;;     (MV-NTH
;;      1
;;      (LAS-TO-PAS
;;       8
;;       (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;               (LOGAND 4088
;;                       (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
;;       :R X86))
;;     (ALL-XLATION-GOVERNING-ENTRIES-PADDRS
;;      8
;;      (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;              (LOGAND 4088
;;                      (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
;;      X86))
;;    (DISJOINT-P$
;;     (MV-NTH
;;      1
;;      (LAS-TO-PAS
;;       8
;;       (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;               (LOGAND 4088
;;                       (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
;;       :R X86))
;;     (ALL-XLATION-GOVERNING-ENTRIES-PADDRS
;;      8
;;      (LOGIOR
;;       (LOGAND 4088
;;               (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
;;       (ASH
;;        (LOGHEAD
;;         40
;;         (LOGTAIL
;;          12
;;          (MV-NTH
;;           1
;;           (RB 8
;;               (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                       (LOGAND 4088
;;                               (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
;;               :R X86))))
;;        12))
;;      X86))
;;    (DISJOINT-P$
;;     (MV-NTH
;;      1
;;      (LAS-TO-PAS
;;       8
;;       (LOGIOR
;;        (LOGAND 4088
;;                (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
;;        (ASH
;;         (LOGHEAD
;;          40
;;          (LOGTAIL
;;           12
;;           (MV-NTH
;;            1
;;            (RB 8
;;                (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                        (LOGAND 4088
;;                                (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
;;                :R X86))))
;;         12))
;;       :W X86))
;;     (ALL-XLATION-GOVERNING-ENTRIES-PADDRS
;;      8
;;      (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;              (LOGAND 4088
;;                      (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
;;      X86))
;;    (DISJOINT-P$
;;     (MV-NTH
;;      1
;;      (LAS-TO-PAS
;;       8
;;       (LOGIOR
;;        (LOGAND 4088
;;                (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
;;        (ASH
;;         (LOGHEAD
;;          40
;;          (LOGTAIL
;;           12
;;           (MV-NTH
;;            1
;;            (RB 8
;;                (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                        (LOGAND 4088
;;                                (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
;;                :R X86))))
;;         12))
;;       :W X86))
;;     (ALL-XLATION-GOVERNING-ENTRIES-PADDRS
;;      8
;;      (LOGIOR
;;       (LOGAND 4088
;;               (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
;;       (ASH
;;        (LOGHEAD
;;         40
;;         (LOGTAIL
;;          12
;;          (MV-NTH
;;           1
;;           (RB 8
;;               (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                       (LOGAND 4088
;;                               (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
;;               :R X86))))
;;        12))
;;      X86))
;;    (DISJOINT-P$
;;     (MV-NTH
;;      1
;;      (LAS-TO-PAS
;;       8
;;       (LOGIOR
;;        (LOGAND 4088
;;                (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
;;        (ASH
;;         (LOGHEAD
;;          40
;;          (LOGTAIL
;;           12
;;           (MV-NTH
;;            1
;;            (RB 8
;;                (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                        (LOGAND 4088
;;                                (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
;;                :R X86))))
;;         12))
;;       :W X86))
;;     (ALL-XLATION-GOVERNING-ENTRIES-PADDRS
;;      8
;;      (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;              (LOGAND 4088
;;                      (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
;;      X86))
;;    (DISJOINT-P$
;;     (MV-NTH 1
;;             (LAS-TO-PAS 8 (+ -24 (XR :RGF *RSP* X86))
;;                         :W X86))
;;     (MV-NTH
;;      1
;;      (LAS-TO-PAS
;;       8
;;       (LOGIOR
;;        (LOGAND 4088
;;                (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
;;        (ASH
;;         (LOGHEAD
;;          40
;;          (LOGTAIL
;;           12
;;           (MV-NTH
;;            1
;;            (RB 8
;;                (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                        (LOGAND 4088
;;                                (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
;;                :R X86))))
;;         12))
;;       :W X86)))
;;    (DISJOINT-P$
;;     (MV-NTH
;;      1
;;      (LAS-TO-PAS
;;       8
;;       (LOGIOR
;;        (LOGAND 4088
;;                (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
;;        (ASH
;;         (LOGHEAD
;;          40
;;          (LOGTAIL
;;           12
;;           (MV-NTH
;;            1
;;            (RB 8
;;                (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                        (LOGAND 4088
;;                                (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
;;                :R X86))))
;;         12))
;;       :W X86))
;;     (ALL-XLATION-GOVERNING-ENTRIES-PADDRS 8 (+ -24 (XR :RGF *RSP* X86))
;;                                           X86))
;;    (DISJOINT-P$
;;     (MV-NTH 1
;;             (LAS-TO-PAS 8 (+ -24 (XR :RGF *RSP* X86))
;;                         :W X86))
;;     (ALL-XLATION-GOVERNING-ENTRIES-PADDRS
;;      8
;;      (LOGIOR
;;       (LOGAND 4088
;;               (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
;;       (ASH
;;        (LOGHEAD
;;         40
;;         (LOGTAIL
;;          12
;;          (MV-NTH
;;           1
;;           (RB 8
;;               (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                       (LOGAND 4088
;;                               (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
;;               :R X86))))
;;        12))
;;      X86))
;;    (DISJOINT-P$
;;     (MV-NTH
;;      1
;;      (LAS-TO-PAS
;;       8
;;       (LOGIOR
;;        (LOGAND 4088
;;                (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
;;        (ASH
;;         (LOGHEAD
;;          40
;;          (LOGTAIL
;;           12
;;           (MV-NTH
;;            1
;;            (RB 8
;;                (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                        (LOGAND 4088
;;                                (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
;;                :R X86))))
;;         12))
;;       :W X86))
;;     (MV-NTH 1
;;             (LAS-TO-PAS 272 (XR :RIP 0 X86)
;;                         :X X86)))
;;    (DISJOINT-P$
;;     (MV-NTH
;;      1
;;      (LAS-TO-PAS
;;       8
;;       (LOGIOR
;;        (LOGAND 4088
;;                (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
;;        (ASH
;;         (LOGHEAD
;;          40
;;          (LOGTAIL
;;           12
;;           (MV-NTH
;;            1
;;            (RB 8
;;                (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                        (LOGAND 4088
;;                                (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
;;                :R X86))))
;;         12))
;;       :W X86))
;;     (ALL-XLATION-GOVERNING-ENTRIES-PADDRS 272 (XR :RIP 0 X86)
;;                                           X86))
;;    (DISJOINT-P$
;;     (MV-NTH 1
;;             (LAS-TO-PAS 272 (XR :RIP 0 X86) :X X86))
;;     (ALL-XLATION-GOVERNING-ENTRIES-PADDRS
;;      8
;;      (LOGIOR
;;       (LOGAND 4088
;;               (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
;;       (ASH
;;        (LOGHEAD
;;         40
;;         (LOGTAIL
;;          12
;;          (MV-NTH
;;           1
;;           (RB 8
;;               (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                       (LOGAND 4088
;;                               (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
;;               :R X86))))
;;        12))
;;      X86))
;;    (DIRECT-MAP-P
;;     8
;;     (LOGIOR
;;      (LOGAND 4088
;;              (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
;;      (ASH
;;       (LOGHEAD
;;        40
;;        (LOGTAIL
;;         12
;;         (MV-NTH
;;          1
;;          (RB 8
;;              (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                      (LOGAND 4088
;;                              (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
;;              :R X86))))
;;       12))
;;     :W X86)
;;    (HIDE (RETURN-ADDRESS-OK-P X86))
;;    (HIDE (STACK-CONTAINING-RETURN-ADDRESS-OK-P X86))
;;    (HIDE (STACK-CONTAINING-RETURN-ADDRESS-AND-PROGRAM-NO-INTERFERE-P X86))
;;    (HIDE
;;     (STACK-CONTAINING-RETURN-ADDRESS-AND-SOURCE-PML4E-NO-INTERFERE-P X86))
;;    (HIDE
;;     (STACK-CONTAINING-RETURN-ADDRESS-AND-SOURCE-PDPTE-NO-INTERFERE-P X86))
;;    (HIDE (STACK-CONTAINING-RETURN-ADDRESS-AND-DESTINATION-PML4E-NO-INTERFERE-P
;;           X86))
;;    (HIDE (STACK-CONTAINING-RETURN-ADDRESS-AND-DESTINATION-PDPTE-NO-INTERFERE-P
;;           X86))
;;    (HIDE (STACK-CONTAINING-RETURN-ADDRESS-AND-REST-OF-THE-STACK-NO-INTERFERE-P
;;           X86)))
;;   (EQUAL
;;    (X86-FETCH-DECODE-EXECUTE
;;     (XW
;;      :RGF *RAX*
;;      (LOGIOR
;;       (LOGAND 4088
;;               (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
;;       (ASH
;;        (LOGHEAD
;;         40
;;         (LOGTAIL
;;          12
;;          (MV-NTH
;;           1
;;           (RB 8
;;               (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                       (LOGAND 4088
;;                               (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
;;               :R X86))))
;;        12))
;;      (XW
;;       :RGF *RCX*
;;       (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;               (LOGAND 4088
;;                       (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
;;       (XW
;;        :RGF *RDX*
;;        (LOGIOR
;;         (LOGAND
;;          -4503598553628673
;;          (LOGEXT
;;           64
;;           (MV-NTH
;;            1
;;            (RB
;;             8
;;             (LOGIOR
;;              (LOGAND 4088
;;                      (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
;;              (ASH
;;               (LOGHEAD
;;                40
;;                (LOGTAIL
;;                 12
;;                 (MV-NTH
;;                  1
;;                  (RB
;;                   8
;;                   (LOGIOR
;;                    (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                    (LOGAND 4088
;;                            (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
;;                   :R X86))))
;;               12))
;;             :R X86))))
;;         (LOGAND
;;          4503598553628672
;;          (LOGEXT
;;           64
;;           (MV-NTH
;;            1
;;            (RB
;;             8
;;             (LOGIOR
;;              (LOGAND 4088
;;                      (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
;;              (ASH
;;               (LOGHEAD
;;                40
;;                (LOGTAIL
;;                 12
;;                 (MV-NTH
;;                  1
;;                  (RB
;;                   8
;;                   (LOGIOR
;;                    (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                    (LOGAND 4088
;;                            (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
;;                   :R X86))))
;;               12))
;;             :R X86)))))
;;        (XW
;;         :RGF *R8* 1099511627775
;;         (XW
;;          :RGF *R9*
;;          (LOGAND
;;           4503598553628672
;;           (LOGEXT
;;            64
;;            (MV-NTH
;;             1
;;             (RB
;;              8
;;              (LOGIOR
;;               (LOGAND 4088
;;                       (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
;;               (ASH
;;                (LOGHEAD
;;                 40
;;                 (LOGTAIL
;;                  12
;;                  (MV-NTH
;;                   1
;;                   (RB
;;                    8
;;                    (LOGIOR
;;                     (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                     (LOGAND 4088
;;                             (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
;;                    :R X86))))
;;                12))
;;              :R X86))))
;;          (XW
;;           :RIP 0 (+ 190 (XR :RIP 0 X86))
;;           (XW
;;            :UNDEF 0 (+ 39 (NFIX (XR :UNDEF 0 X86)))
;;            (!FLGI
;;             *CF* 0
;;             (!FLGI
;;              *PF*
;;              (PF-SPEC64
;;               (LOGIOR
;;                (LOGAND
;;                 18442240475155922943
;;                 (MV-NTH
;;                  1
;;                  (RB
;;                   8
;;                   (LOGIOR
;;                    (LOGAND 4088
;;                            (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
;;                    (ASH
;;                     (LOGHEAD
;;                      40
;;                      (LOGTAIL
;;                       12
;;                       (MV-NTH
;;                        1
;;                        (RB
;;                         8
;;                         (LOGIOR
;;                          (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                          (LOGAND
;;                           4088
;;                           (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
;;                         :R X86))))
;;                     12))
;;                   :R X86)))
;;                (LOGAND
;;                 4503598553628672
;;                 (MV-NTH
;;                  1
;;                  (RB
;;                   8
;;                   (LOGIOR
;;                    (LOGAND 4088
;;                            (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
;;                    (ASH
;;                     (LOGHEAD
;;                      40
;;                      (LOGTAIL
;;                       12
;;                       (MV-NTH
;;                        1
;;                        (RB
;;                         8
;;                         (LOGIOR
;;                          (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                          (LOGAND
;;                           4088
;;                           (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
;;                         :R X86))))
;;                     12))
;;                   :R X86)))))
;;              (!FLGI
;;               *AF*
;;               (LOGHEAD 1
;;                        (CREATE-UNDEF (+ 38 (NFIX (XR :UNDEF 0 X86)))))
;;               (!FLGI
;;                *ZF*
;;                (ZF-SPEC
;;                 (LOGIOR
;;                  (LOGAND
;;                   18442240475155922943
;;                   (MV-NTH
;;                    1
;;                    (RB
;;                     8
;;                     (LOGIOR
;;                      (LOGAND 4088
;;                              (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
;;                      (ASH
;;                       (LOGHEAD
;;                        40
;;                        (LOGTAIL
;;                         12
;;                         (MV-NTH
;;                          1
;;                          (RB
;;                           8
;;                           (LOGIOR
;;                            (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                            (LOGAND
;;                             4088
;;                             (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
;;                           :R X86))))
;;                       12))
;;                     :R X86)))
;;                  (LOGAND
;;                   4503598553628672
;;                   (MV-NTH
;;                    1
;;                    (RB
;;                     8
;;                     (LOGIOR
;;                      (LOGAND 4088
;;                              (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
;;                      (ASH
;;                       (LOGHEAD
;;                        40
;;                        (LOGTAIL
;;                         12
;;                         (MV-NTH
;;                          1
;;                          (RB
;;                           8
;;                           (LOGIOR
;;                            (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                            (LOGAND
;;                             4088
;;                             (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
;;                           :R X86))))
;;                       12))
;;                     :R X86)))))
;;                (!FLGI
;;                 *SF*
;;                 (SF-SPEC64
;;                  (LOGIOR
;;                   (LOGAND
;;                    18442240475155922943
;;                    (MV-NTH
;;                     1
;;                     (RB
;;                      8
;;                      (LOGIOR
;;                       (LOGAND 4088
;;                               (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
;;                       (ASH
;;                        (LOGHEAD
;;                         40
;;                         (LOGTAIL
;;                          12
;;                          (MV-NTH
;;                           1
;;                           (RB
;;                            8
;;                            (LOGIOR
;;                             (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                             (LOGAND
;;                              4088
;;                              (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
;;                            :R X86))))
;;                        12))
;;                      :R X86)))
;;                   (LOGAND
;;                    4503598553628672
;;                    (MV-NTH
;;                     1
;;                     (RB
;;                      8
;;                      (LOGIOR
;;                       (LOGAND 4088
;;                               (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
;;                       (ASH
;;                        (LOGHEAD
;;                         40
;;                         (LOGTAIL
;;                          12
;;                          (MV-NTH
;;                           1
;;                           (RB
;;                            8
;;                            (LOGIOR
;;                             (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                             (LOGAND
;;                              4088
;;                              (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
;;                            :R X86))))
;;                        12))
;;                      :R X86)))))
;;                 (!FLGI
;;                  *OF* 0
;;                  (MV-NTH
;;                   1
;;                   (WB
;;                    8
;;                    (LOGIOR
;;                     (LOGAND 4088
;;                             (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
;;                     (ASH
;;                      (LOGHEAD
;;                       40
;;                       (LOGTAIL
;;                        12
;;                        (MV-NTH
;;                         1
;;                         (RB
;;                          8
;;                          (LOGIOR
;;                           (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                           (LOGAND
;;                            4088
;;                            (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
;;                          :R X86))))
;;                      12))
;;                    :W
;;                    (LOGIOR
;;                     (LOGAND
;;                      18442240475155922943
;;                      (MV-NTH
;;                       1
;;                       (RB
;;                        8
;;                        (LOGIOR
;;                         (LOGAND 4088
;;                                 (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
;;                         (ASH
;;                          (LOGHEAD
;;                           40
;;                           (LOGTAIL
;;                            12
;;                            (MV-NTH
;;                             1
;;                             (RB
;;                              8
;;                              (LOGIOR
;;                               (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                               (LOGAND
;;                                4088
;;                                (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
;;                              :R X86))))
;;                          12))
;;                        :R X86)))
;;                     (LOGAND
;;                      4503598553628672
;;                      (MV-NTH
;;                       1
;;                       (RB
;;                        8
;;                        (LOGIOR
;;                         (LOGAND 4088
;;                                 (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
;;                         (ASH
;;                          (LOGHEAD
;;                           40
;;                           (LOGTAIL
;;                            12
;;                            (MV-NTH
;;                             1
;;                             (RB
;;                              8
;;                              (LOGIOR
;;                               (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                               (LOGAND
;;                                4088
;;                                (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
;;                              :R X86))))
;;                          12))
;;                        :R X86))))
;;                    (MV-NTH
;;                     2
;;                     (LAS-TO-PAS
;;                      6 (+ 184 (XR :RIP 0 X86))
;;                      :X
;;                      (MV-NTH
;;                       2
;;                       (LAS-TO-PAS
;;                        8
;;                        (LOGIOR
;;                         (LOGAND 4088
;;                                 (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
;;                         (ASH
;;                          (LOGHEAD
;;                           40
;;                           (LOGTAIL
;;                            12
;;                            (MV-NTH
;;                             1
;;                             (RB
;;                              8
;;                              (LOGIOR
;;                               (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                               (LOGAND
;;                                4088
;;                                (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
;;                              :R X86))))
;;                          12))
;;                        :R
;;                        (MV-NTH
;;                         2
;;                         (LAS-TO-PAS
;;                          40 (+ 144 (XR :RIP 0 X86))
;;                          :X
;;                          (MV-NTH
;;                           2
;;                           (LAS-TO-PAS
;;                            3 (+ 140 (XR :RIP 0 X86))
;;                            :X
;;                            (MV-NTH
;;                             2
;;                             (LAS-TO-PAS
;;                              8
;;                              (LOGIOR
;;                               (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                               (LOGAND
;;                                4088
;;                                (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
;;                              :R
;;                              (MV-NTH
;;                               2
;;                               (LAS-TO-PAS
;;                                32 (+ 108 (XR :RIP 0 X86))
;;                                :X
;;                                (MV-NTH
;;                                 2
;;                                 (LAS-TO-PAS
;;                                  18 (+ 86 (XR :RIP 0 X86))
;;                                  :X
;;                                  (MV-NTH
;;                                   2
;;                                   (LAS-TO-PAS
;;                                    8
;;                                    (LOGIOR
;;                                     (LOGAND
;;                                      4088
;;                                      (LOGHEAD
;;                                       32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
;;                                     (ASH
;;                                      (LOGHEAD
;;                                       40
;;                                       (LOGTAIL
;;                                        12
;;                                        (MV-NTH
;;                                         1
;;                                         (RB
;;                                          8
;;                                          (LOGIOR
;;                                           (LOGAND
;;                                            -4096
;;                                            (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                                           (LOGAND
;;                                            4088
;;                                            (LOGHEAD
;;                                             28
;;                                             (LOGTAIL
;;                                              36 (XR :RGF *RDI* X86)))))
;;                                          :R X86))))
;;                                      12))
;;                                    :R
;;                                    (MV-NTH
;;                                     2
;;                                     (LAS-TO-PAS
;;                                      40 (+ 46 (XR :RIP 0 X86))
;;                                      :X
;;                                      (MV-NTH
;;                                       2
;;                                       (LAS-TO-PAS
;;                                        4 (+ 38 (XR :RIP 0 X86))
;;                                        :X
;;                                        (MV-NTH
;;                                         2
;;                                         (LAS-TO-PAS
;;                                          8
;;                                          (LOGIOR
;;                                           (LOGAND
;;                                            -4096
;;                                            (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                                           (LOGAND
;;                                            4088
;;                                            (LOGHEAD
;;                                             28
;;                                             (LOGTAIL
;;                                              36 (XR :RGF *RDI* X86)))))
;;                                          :R
;;                                          (MV-NTH
;;                                           2
;;                                           (LAS-TO-PAS
;;                                            25 (+ 13 (XR :RIP 0 X86))
;;                                            :X
;;                                            (MV-NTH
;;                                             2
;;                                             (LAS-TO-PAS
;;                                              8 (+ -24 (XR :RGF *RSP* X86))
;;                                              :R
;;                                              (MV-NTH
;;                                               2
;;                                               (LAS-TO-PAS
;;                                                5 (+ 8 (XR :RIP 0 X86))
;;                                                :X
;;                                                (MV-NTH
;;                                                 1
;;                                                 (WB
;;                                                  8 (+ -24 (XR :RGF *RSP* X86))
;;                                                  :W (XR :CTR *CR3* X86)
;;                                                  (MV-NTH
;;                                                   2
;;                                                   (LAS-TO-PAS
;;                                                    8 (XR :RIP 0 X86)
;;                                                    :X
;;                                                    X86))))))))))))))))))))))))))))))))))))))))))))))))
;;    (XW
;;     :RGF *RAX*
;;     (LOGIOR
;;      (LOGAND
;;       -4503598553628673
;;       (LOGEXT
;;        64
;;        (MV-NTH
;;         1
;;         (RB
;;          8
;;          (LOGIOR
;;           (LOGAND 4088
;;                   (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
;;           (ASH
;;            (LOGHEAD
;;             40
;;             (LOGTAIL
;;              12
;;              (MV-NTH
;;               1
;;               (RB
;;                8
;;                (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                        (LOGAND 4088
;;                                (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
;;                :R X86))))
;;            12))
;;          :R X86))))
;;      (LOGAND
;;       4503598553628672
;;       (LOGEXT
;;        64
;;        (MV-NTH
;;         1
;;         (RB
;;          8
;;          (LOGIOR
;;           (LOGAND 4088
;;                   (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
;;           (ASH
;;            (LOGHEAD
;;             40
;;             (LOGTAIL
;;              12
;;              (MV-NTH
;;               1
;;               (RB
;;                8
;;                (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                        (LOGAND 4088
;;                                (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
;;                :R X86))))
;;            12))
;;          :R X86)))))
;;     (XW
;;      :RGF *RCX*
;;      (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;              (LOGAND 4088
;;                      (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
;;      (XW
;;       :RGF *RDX*
;;       (LOGIOR
;;        (LOGAND
;;         -4503598553628673
;;         (LOGEXT
;;          64
;;          (MV-NTH
;;           1
;;           (RB
;;            8
;;            (LOGIOR
;;             (LOGAND 4088
;;                     (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
;;             (ASH
;;              (LOGHEAD
;;               40
;;               (LOGTAIL
;;                12
;;                (MV-NTH
;;                 1
;;                 (RB
;;                  8
;;                  (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                          (LOGAND 4088
;;                                  (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
;;                  :R X86))))
;;              12))
;;            :R X86))))
;;        (LOGAND
;;         4503598553628672
;;         (LOGEXT
;;          64
;;          (MV-NTH
;;           1
;;           (RB
;;            8
;;            (LOGIOR
;;             (LOGAND 4088
;;                     (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
;;             (ASH
;;              (LOGHEAD
;;               40
;;               (LOGTAIL
;;                12
;;                (MV-NTH
;;                 1
;;                 (RB
;;                  8
;;                  (LOGIOR (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                          (LOGAND 4088
;;                                  (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
;;                  :R X86))))
;;              12))
;;            :R X86)))))
;;       (XW
;;        :RGF *R8* 1099511627775
;;        (XW
;;         :RGF *R9*
;;         (LOGAND
;;          4503598553628672
;;          (LOGEXT
;;           64
;;           (MV-NTH
;;            1
;;            (RB
;;             8
;;             (LOGIOR
;;              (LOGAND 4088
;;                      (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
;;              (ASH
;;               (LOGHEAD
;;                40
;;                (LOGTAIL
;;                 12
;;                 (MV-NTH
;;                  1
;;                  (RB
;;                   8
;;                   (LOGIOR
;;                    (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                    (LOGAND 4088
;;                            (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
;;                   :R X86))))
;;               12))
;;             :R X86))))
;;         (XW
;;          :RIP 0 (+ 193 (XR :RIP 0 X86))
;;          (XW
;;           :UNDEF 0 (+ 39 (NFIX (XR :UNDEF 0 X86)))
;;           (!FLGI
;;            *CF* 0
;;            (!FLGI
;;             *PF*
;;             (PF-SPEC64
;;              (LOGIOR
;;               (LOGAND
;;                18442240475155922943
;;                (MV-NTH
;;                 1
;;                 (RB
;;                  8
;;                  (LOGIOR
;;                   (LOGAND 4088
;;                           (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
;;                   (ASH
;;                    (LOGHEAD
;;                     40
;;                     (LOGTAIL
;;                      12
;;                      (MV-NTH
;;                       1
;;                       (RB
;;                        8
;;                        (LOGIOR
;;                         (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                         (LOGAND 4088
;;                                 (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
;;                        :R X86))))
;;                    12))
;;                  :R X86)))
;;               (LOGAND
;;                4503598553628672
;;                (MV-NTH
;;                 1
;;                 (RB
;;                  8
;;                  (LOGIOR
;;                   (LOGAND 4088
;;                           (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
;;                   (ASH
;;                    (LOGHEAD
;;                     40
;;                     (LOGTAIL
;;                      12
;;                      (MV-NTH
;;                       1
;;                       (RB
;;                        8
;;                        (LOGIOR
;;                         (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                         (LOGAND 4088
;;                                 (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
;;                        :R X86))))
;;                    12))
;;                  :R X86)))))
;;             (!FLGI
;;              *AF*
;;              (LOGHEAD 1
;;                       (CREATE-UNDEF (+ 38 (NFIX (XR :UNDEF 0 X86)))))
;;              (!FLGI
;;               *ZF*
;;               (ZF-SPEC
;;                (LOGIOR
;;                 (LOGAND
;;                  18442240475155922943
;;                  (MV-NTH
;;                   1
;;                   (RB
;;                    8
;;                    (LOGIOR
;;                     (LOGAND 4088
;;                             (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
;;                     (ASH
;;                      (LOGHEAD
;;                       40
;;                       (LOGTAIL
;;                        12
;;                        (MV-NTH
;;                         1
;;                         (RB
;;                          8
;;                          (LOGIOR
;;                           (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                           (LOGAND
;;                            4088
;;                            (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
;;                          :R X86))))
;;                      12))
;;                    :R X86)))
;;                 (LOGAND
;;                  4503598553628672
;;                  (MV-NTH
;;                   1
;;                   (RB
;;                    8
;;                    (LOGIOR
;;                     (LOGAND 4088
;;                             (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
;;                     (ASH
;;                      (LOGHEAD
;;                       40
;;                       (LOGTAIL
;;                        12
;;                        (MV-NTH
;;                         1
;;                         (RB
;;                          8
;;                          (LOGIOR
;;                           (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                           (LOGAND
;;                            4088
;;                            (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
;;                          :R X86))))
;;                      12))
;;                    :R X86)))))
;;               (!FLGI
;;                *SF*
;;                (SF-SPEC64
;;                 (LOGIOR
;;                  (LOGAND
;;                   18442240475155922943
;;                   (MV-NTH
;;                    1
;;                    (RB
;;                     8
;;                     (LOGIOR
;;                      (LOGAND 4088
;;                              (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
;;                      (ASH
;;                       (LOGHEAD
;;                        40
;;                        (LOGTAIL
;;                         12
;;                         (MV-NTH
;;                          1
;;                          (RB
;;                           8
;;                           (LOGIOR
;;                            (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                            (LOGAND
;;                             4088
;;                             (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
;;                           :R X86))))
;;                       12))
;;                     :R X86)))
;;                  (LOGAND
;;                   4503598553628672
;;                   (MV-NTH
;;                    1
;;                    (RB
;;                     8
;;                     (LOGIOR
;;                      (LOGAND 4088
;;                              (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
;;                      (ASH
;;                       (LOGHEAD
;;                        40
;;                        (LOGTAIL
;;                         12
;;                         (MV-NTH
;;                          1
;;                          (RB
;;                           8
;;                           (LOGIOR
;;                            (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                            (LOGAND
;;                             4088
;;                             (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
;;                           :R X86))))
;;                       12))
;;                     :R X86)))))
;;                (!FLGI
;;                 *OF* 0
;;                 (MV-NTH
;;                  2
;;                  (LAS-TO-PAS
;;                   3 (+ 190 (XR :RIP 0 X86))
;;                   :X
;;                   (MV-NTH
;;                    1
;;                    (WB
;;                     8
;;                     (LOGIOR
;;                      (LOGAND 4088
;;                              (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
;;                      (ASH
;;                       (LOGHEAD
;;                        40
;;                        (LOGTAIL
;;                         12
;;                         (MV-NTH
;;                          1
;;                          (RB
;;                           8
;;                           (LOGIOR
;;                            (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                            (LOGAND
;;                             4088
;;                             (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
;;                           :R X86))))
;;                       12))
;;                     :W
;;                     (LOGIOR
;;                      (LOGAND
;;                       18442240475155922943
;;                       (MV-NTH
;;                        1
;;                        (RB
;;                         8
;;                         (LOGIOR
;;                          (LOGAND 4088
;;                                  (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
;;                          (ASH
;;                           (LOGHEAD
;;                            40
;;                            (LOGTAIL
;;                             12
;;                             (MV-NTH
;;                              1
;;                              (RB
;;                               8
;;                               (LOGIOR
;;                                (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                                (LOGAND
;;                                 4088
;;                                 (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
;;                               :R X86))))
;;                           12))
;;                         :R X86)))
;;                      (LOGAND
;;                       4503598553628672
;;                       (MV-NTH
;;                        1
;;                        (RB
;;                         8
;;                         (LOGIOR
;;                          (LOGAND 4088
;;                                  (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
;;                          (ASH
;;                           (LOGHEAD
;;                            40
;;                            (LOGTAIL
;;                             12
;;                             (MV-NTH
;;                              1
;;                              (RB
;;                               8
;;                               (LOGIOR
;;                                (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                                (LOGAND
;;                                 4088
;;                                 (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86)))))
;;                               :R X86))))
;;                           12))
;;                         :R X86))))
;;                     (MV-NTH
;;                      2
;;                      (LAS-TO-PAS
;;                       6 (+ 184 (XR :RIP 0 X86))
;;                       :X
;;                       (MV-NTH
;;                        2
;;                        (LAS-TO-PAS
;;                         8
;;                         (LOGIOR
;;                          (LOGAND 4088
;;                                  (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
;;                          (ASH
;;                           (LOGHEAD
;;                            40
;;                            (LOGTAIL
;;                             12
;;                             (MV-NTH
;;                              1
;;                              (RB
;;                               8
;;                               (LOGIOR
;;                                (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                                (LOGAND
;;                                 4088
;;                                 (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
;;                               :R X86))))
;;                           12))
;;                         :R
;;                         (MV-NTH
;;                          2
;;                          (LAS-TO-PAS
;;                           40 (+ 144 (XR :RIP 0 X86))
;;                           :X
;;                           (MV-NTH
;;                            2
;;                            (LAS-TO-PAS
;;                             3 (+ 140 (XR :RIP 0 X86))
;;                             :X
;;                             (MV-NTH
;;                              2
;;                              (LAS-TO-PAS
;;                               8
;;                               (LOGIOR
;;                                (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                                (LOGAND
;;                                 4088
;;                                 (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86)))))
;;                               :R
;;                               (MV-NTH
;;                                2
;;                                (LAS-TO-PAS
;;                                 32 (+ 108 (XR :RIP 0 X86))
;;                                 :X
;;                                 (MV-NTH
;;                                  2
;;                                  (LAS-TO-PAS
;;                                   18 (+ 86 (XR :RIP 0 X86))
;;                                   :X
;;                                   (MV-NTH
;;                                    2
;;                                    (LAS-TO-PAS
;;                                     8
;;                                     (LOGIOR
;;                                      (LOGAND
;;                                       4088
;;                                       (LOGHEAD
;;                                        32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
;;                                      (ASH
;;                                       (LOGHEAD
;;                                        40
;;                                        (LOGTAIL
;;                                         12
;;                                         (MV-NTH
;;                                          1
;;                                          (RB
;;                                           8
;;                                           (LOGIOR
;;                                            (LOGAND
;;                                             -4096
;;                                             (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                                            (LOGAND
;;                                             4088
;;                                             (LOGHEAD
;;                                              28
;;                                              (LOGTAIL 36 (XR :RGF *RDI* X86)))))
;;                                           :R X86))))
;;                                       12))
;;                                     :R
;;                                     (MV-NTH
;;                                      2
;;                                      (LAS-TO-PAS
;;                                       40 (+ 46 (XR :RIP 0 X86))
;;                                       :X
;;                                       (MV-NTH
;;                                        2
;;                                        (LAS-TO-PAS
;;                                         4 (+ 38 (XR :RIP 0 X86))
;;                                         :X
;;                                         (MV-NTH
;;                                          2
;;                                          (LAS-TO-PAS
;;                                           8
;;                                           (LOGIOR
;;                                            (LOGAND
;;                                             -4096
;;                                             (LOGEXT 64 (XR :CTR *CR3* X86)))
;;                                            (LOGAND
;;                                             4088
;;                                             (LOGHEAD
;;                                              28
;;                                              (LOGTAIL 36 (XR :RGF *RDI* X86)))))
;;                                           :R
;;                                           (MV-NTH
;;                                            2
;;                                            (LAS-TO-PAS
;;                                             25 (+ 13 (XR :RIP 0 X86))
;;                                             :X
;;                                             (MV-NTH
;;                                              2
;;                                              (LAS-TO-PAS
;;                                               8 (+ -24 (XR :RGF *RSP* X86))
;;                                               :R
;;                                               (MV-NTH
;;                                                2
;;                                                (LAS-TO-PAS
;;                                                 5 (+ 8 (XR :RIP 0 X86))
;;                                                 :X
;;                                                 (MV-NTH
;;                                                  1
;;                                                  (WB
;;                                                   8 (+ -24 (XR :RGF *RSP* X86))
;;                                                   :W (XR :CTR *CR3* X86)
;;                                                   (MV-NTH
;;                                                    2
;;                                                    (LAS-TO-PAS
;;                                                     8 (XR :RIP 0 X86)
;;                                                     :X
;;                                                     X86)))))))))))))))))))))))))))))))))))))))))))))))))))
;;  :hints (("Goal"
;;           :do-not-induct t
;; ;          :use ((:instance foo))
;;           :in-theory (e/d* (len
;;                             page-size
;;                             loghead-negative
;;                             disjoint-p-all-xlation-governing-entries-paddrs-subset-p)
;;                            (create-canonical-address-list
;;                             (:rewrite program-at-values-and-!flgi)
;;                             (:rewrite get-prefixes-opener-lemma-group-4-prefix-in-marking-view)
;;                             (:rewrite get-prefixes-opener-lemma-group-3-prefix-in-marking-view)
;;                             (:rewrite get-prefixes-opener-lemma-group-2-prefix-in-marking-view)
;;                             (:rewrite get-prefixes-opener-lemma-group-1-prefix-in-marking-view)
;;                             (:rewrite mv-nth-1-rb-and-xlate-equiv-memory-disjoint-from-paging-structures)
;;                             (:rewrite mv-nth-2-rb-in-system-level-non-marking-view)
;;                             (:rewrite rb-returns-x86-app-view)
;;                             (:linear rm-low-64-logand-logior-helper-1)
;;                             (:definition n64p$inline)
;;                             (:type-prescription xlate-equiv-memory)
;;                             (:rewrite program-at-alt-wb-disjoint-in-sys-view)
;;                             (:type-prescription natp-page-dir-ptr-table-entry-addr)
;;                             mv-nth-1-las-to-pas-subset-p-disjoint-from-other-p-addrs
;;                             mv-nth-2-las-to-pas-system-level-non-marking-view
;;                             (:rewrite r-w-x-is-irrelevant-for-mv-nth-2-las-to-pas-when-no-errors)
;;                             (:rewrite acl2::cdr-of-append-when-consp)
;;                             (:rewrite acl2::car-of-append)
;;                             (:rewrite acl2::consp-of-append)
;;                             (:rewrite acl2::append-atom-under-list-equiv)
;;                             (:type-prescription binary-append)
;;                             (:rewrite xr-fault-wb-in-sys-view)
;;                             (:type-prescription n01p-page-size)
;;                             (:type-prescription member-p-physical-address-p-physical-address-listp)
;;                             (:rewrite acl2::right-cancellation-for-+)
;;                             (:type-prescription member-p-physical-address-p)
;;                             (:rewrite acl2::append-singleton-under-set-equiv))))))
