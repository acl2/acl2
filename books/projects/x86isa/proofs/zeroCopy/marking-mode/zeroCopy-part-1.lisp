;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")

(include-book "system-level-mode/marking-mode-top" :dir :proof-utils)
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
         x86-effective-addr
         x86-effective-addr-from-sib
         x86-operand-to-reg/mem
         rr08 rr32 rr64 wr08 wr32 wr64
         rim08 rim32 rim64
         !flgi-undefined
         write-user-rflags

         pos
         mv-nth-0-las-to-pas-subset-p
         member-p
         subset-p

         rb-alt-wb-equal-in-system-level-mode)

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
;; (acl2::why x86-fetch-decode-execute-opener-in-marking-mode)
;; (acl2::why get-prefixes-alt-opener-lemma-no-prefix-byte)
;; (acl2::why get-prefixes-alt-and-wb-in-system-level-marking-mode-disjoint-from-paging-structures)
;; (acl2::why la-to-pas-values-and-mv-nth-1-wb-disjoint-from-xlation-gov-addrs)
;; (acl2::why rb-alt-wb-disjoint-in-system-level-mode)
;; (acl2::why rb-alt-wb-equal-in-system-level-mode)
;; (acl2::why mv-nth-1-rb-after-mv-nth-2-rb-alt)
;; (acl2::why all-translation-governing-addresses-and-mv-nth-1-wb-disjoint)
;; (acl2::why la-to-pas-values-and-mv-nth-1-wb-disjoint-from-xlation-gov-addrs)
;; (acl2::why mv-nth-1-rb-after-mv-nth-2-get-prefixes-alt-no-prefix-byte)
;; (acl2::why mv-nth-2-get-prefixes-alt-no-prefix-byte)
;; (acl2::why mv-nth-2-rb-in-system-level-marking-mode)
;; (acl2::why combine-mv-nth-2-las-to-pas-same-r-w-x)
;; (acl2::why mv-nth-1-rb-after-mv-nth-2-las-to-pas)
;; (acl2::why mv-nth-1-rb-after-mv-nth-2-rb)
;; (acl2::why get-prefixes-alt-and-wb-to-paging-structures)
;; (acl2::why rb-wb-disjoint-in-system-level-mode)
;; (acl2::why x86-fetch-decode-execute-opener-in-marking-mode)
;; (acl2::why mv-nth-2-get-prefixes-alt-no-prefix-byte)
;; (acl2::why rb-alt-and-wb-to-paging-structures-disjoint)

(defthmd rewire_dst_to_src-effects-1-to-45-instructions
  ;; !!! FIXME: Speed this monster up.
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
     :w (cpl x86) x86)

    ;; !!! FIXME: Some of the following are in terms of disjoint-p
    ;; !!! instead of disjoint-p$.
    (hide (return-address-ok-p x86))
    (hide (stack-containing-return-address-ok-p x86))
    (hide (stack-containing-return-address-and-program-no-interfere-p x86))
    (hide (stack-containing-return-address-and-source-PML4E-no-interfere-p x86))
    (hide (stack-containing-return-address-and-source-PDPTE-no-interfere-p x86))
    (hide (stack-containing-return-address-and-destination-PML4E-no-interfere-p x86))
    (hide (stack-containing-return-address-and-destination-PDPTE-no-interfere-p x86))
    (hide (stack-containing-return-address-and-rest-of-the-stack-no-interfere-p x86)))

   (equal (x86-run (rewire_dst_to_src-clk-1-to-45) x86)
          (XW
           :RGF *RAX*
           (LOGIOR
            (LOGAND
             -4503598553628673
             (LOGEXT
              64
              (COMBINE-BYTES
               (MV-NTH
                1
                (RB
                 (CREATE-CANONICAL-ADDRESS-LIST
                  8
                  (LOGIOR
                   (LOGAND 4088
                           (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
                   (ASH
                    (LOGHEAD
                     40
                     (LOGTAIL
                      12
                      (COMBINE-BYTES
                       (MV-NTH
                        1
                        (RB
                         (CREATE-CANONICAL-ADDRESS-LIST
                          8
                          (LOGIOR
                           (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                           (LOGAND 4088
                                   (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86))))))
                         :R X86)))))
                    12)))
                 :R X86)))))
            (LOGAND
             4503598553628672
             (LOGEXT
              64
              (COMBINE-BYTES
               (MV-NTH
                1
                (RB
                 (CREATE-CANONICAL-ADDRESS-LIST
                  8
                  (LOGIOR
                   (LOGAND 4088
                           (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
                   (ASH
                    (LOGHEAD
                     40
                     (LOGTAIL
                      12
                      (COMBINE-BYTES
                       (MV-NTH
                        1
                        (RB
                         (CREATE-CANONICAL-ADDRESS-LIST
                          8
                          (LOGIOR
                           (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                           (LOGAND 4088
                                   (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86))))))
                         :R X86)))))
                    12)))
                 :R X86))))))
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
                (COMBINE-BYTES
                 (MV-NTH
                  1
                  (RB
                   (CREATE-CANONICAL-ADDRESS-LIST
                    8
                    (LOGIOR
                     (LOGAND 4088
                             (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
                     (ASH
                      (LOGHEAD
                       40
                       (LOGTAIL
                        12
                        (COMBINE-BYTES
                         (MV-NTH
                          1
                          (RB
                           (CREATE-CANONICAL-ADDRESS-LIST
                            8
                            (LOGIOR
                             (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                             (LOGAND 4088
                                     (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86))))))
                           :R X86)))))
                      12)))
                   :R X86)))))
              (LOGAND
               4503598553628672
               (LOGEXT
                64
                (COMBINE-BYTES
                 (MV-NTH
                  1
                  (RB
                   (CREATE-CANONICAL-ADDRESS-LIST
                    8
                    (LOGIOR
                     (LOGAND 4088
                             (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
                     (ASH
                      (LOGHEAD
                       40
                       (LOGTAIL
                        12
                        (COMBINE-BYTES
                         (MV-NTH
                          1
                          (RB
                           (CREATE-CANONICAL-ADDRESS-LIST
                            8
                            (LOGIOR
                             (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                             (LOGAND 4088
                                     (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86))))))
                           :R X86)))))
                      12)))
                   :R X86))))))
             (XW
              :RGF *R8* 1099511627775
              (XW
               :RGF *R9*
               (LOGAND
                4503598553628672
                (LOGEXT
                 64
                 (COMBINE-BYTES
                  (MV-NTH
                   1
                   (RB
                    (CREATE-CANONICAL-ADDRESS-LIST
                     8
                     (LOGIOR
                      (LOGAND 4088
                              (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
                      (ASH
                       (LOGHEAD
                        40
                        (LOGTAIL
                         12
                         (COMBINE-BYTES
                          (MV-NTH
                           1
                           (RB
                            (CREATE-CANONICAL-ADDRESS-LIST
                             8
                             (LOGIOR
                              (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                              (LOGAND
                               4088
                               (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86))))))
                            :R X86)))))
                       12)))
                    :R X86)))))
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
                      (COMBINE-BYTES
                       (MV-NTH
                        1
                        (RB
                         (CREATE-CANONICAL-ADDRESS-LIST
                          8
                          (LOGIOR
                           (LOGAND 4088
                                   (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
                           (ASH
                            (LOGHEAD
                             40
                             (LOGTAIL
                              12
                              (COMBINE-BYTES
                               (MV-NTH
                                1
                                (RB
                                 (CREATE-CANONICAL-ADDRESS-LIST
                                  8
                                  (LOGIOR
                                   (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                                   (LOGAND
                                    4088
                                    (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RSI* X86))))))
                                 :R X86)))))
                            12)))
                         :R X86))))
                     (LOGAND
                      4503598553628672
                      (COMBINE-BYTES
                       (MV-NTH
                        1
                        (RB
                         (CREATE-CANONICAL-ADDRESS-LIST
                          8
                          (LOGIOR
                           (LOGAND 4088
                                   (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
                           (ASH
                            (LOGHEAD
                             40
                             (LOGTAIL
                              12
                              (COMBINE-BYTES
                               (MV-NTH
                                1
                                (RB
                                 (CREATE-CANONICAL-ADDRESS-LIST
                                  8
                                  (LOGIOR
                                   (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                                   (LOGAND
                                    4088
                                    (LOGHEAD 28 (LOGTAIL 36 (XR :RGF *RDI* X86))))))
                                 :R X86)))))
                            12)))
                         :R X86))))))
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
                        (COMBINE-BYTES
                         (MV-NTH
                          1
                          (RB
                           (CREATE-CANONICAL-ADDRESS-LIST
                            8
                            (LOGIOR
                             (LOGAND 4088
                                     (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
                             (ASH
                              (LOGHEAD
                               40
                               (LOGTAIL
                                12
                                (COMBINE-BYTES
                                 (MV-NTH
                                  1
                                  (RB
                                   (CREATE-CANONICAL-ADDRESS-LIST
                                    8
                                    (LOGIOR
                                     (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                                     (LOGAND
                                      4088
                                      (LOGHEAD
                                       28 (LOGTAIL 36 (XR :RGF *RSI* X86))))))
                                   :R X86)))))
                              12)))
                           :R X86))))
                       (LOGAND
                        4503598553628672
                        (COMBINE-BYTES
                         (MV-NTH
                          1
                          (RB
                           (CREATE-CANONICAL-ADDRESS-LIST
                            8
                            (LOGIOR
                             (LOGAND 4088
                                     (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
                             (ASH
                              (LOGHEAD
                               40
                               (LOGTAIL
                                12
                                (COMBINE-BYTES
                                 (MV-NTH
                                  1
                                  (RB
                                   (CREATE-CANONICAL-ADDRESS-LIST
                                    8
                                    (LOGIOR
                                     (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                                     (LOGAND
                                      4088
                                      (LOGHEAD
                                       28 (LOGTAIL 36 (XR :RGF *RDI* X86))))))
                                   :R X86)))))
                              12)))
                           :R X86))))))
                     (!FLGI
                      *SF*
                      (SF-SPEC64
                       (LOGIOR
                        (LOGAND
                         18442240475155922943
                         (COMBINE-BYTES
                          (MV-NTH
                           1
                           (RB
                            (CREATE-CANONICAL-ADDRESS-LIST
                             8
                             (LOGIOR
                              (LOGAND 4088
                                      (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
                              (ASH
                               (LOGHEAD
                                40
                                (LOGTAIL
                                 12
                                 (COMBINE-BYTES
                                  (MV-NTH
                                   1
                                   (RB
                                    (CREATE-CANONICAL-ADDRESS-LIST
                                     8
                                     (LOGIOR
                                      (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                                      (LOGAND
                                       4088
                                       (LOGHEAD
                                        28 (LOGTAIL 36 (XR :RGF *RSI* X86))))))
                                    :R X86)))))
                               12)))
                            :R X86))))
                        (LOGAND
                         4503598553628672
                         (COMBINE-BYTES
                          (MV-NTH
                           1
                           (RB
                            (CREATE-CANONICAL-ADDRESS-LIST
                             8
                             (LOGIOR
                              (LOGAND 4088
                                      (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RDI* X86))))
                              (ASH
                               (LOGHEAD
                                40
                                (LOGTAIL
                                 12
                                 (COMBINE-BYTES
                                  (MV-NTH
                                   1
                                   (RB
                                    (CREATE-CANONICAL-ADDRESS-LIST
                                     8
                                     (LOGIOR
                                      (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                                      (LOGAND
                                       4088
                                       (LOGHEAD
                                        28 (LOGTAIL 36 (XR :RGF *RDI* X86))))))
                                    :R X86)))))
                               12)))
                            :R X86))))))
                      (!FLGI
                       *OF* 0
                       (MV-NTH
                        2
                        (LAS-TO-PAS
                         (CREATE-CANONICAL-ADDRESS-LIST 3 (+ 190 (XR :RIP 0 X86)))
                         :X 0
                         (MV-NTH
                          1
                          (WB
                           (CREATE-ADDR-BYTES-ALIST
                            (CREATE-CANONICAL-ADDRESS-LIST
                             8
                             (LOGIOR
                              (LOGAND 4088
                                      (LOGHEAD 32 (LOGTAIL 27 (XR :RGF *RSI* X86))))
                              (ASH
                               (LOGHEAD
                                40
                                (LOGTAIL
                                 12
                                 (COMBINE-BYTES
                                  (MV-NTH
                                   1
                                   (RB
                                    (CREATE-CANONICAL-ADDRESS-LIST
                                     8
                                     (LOGIOR
                                      (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                                      (LOGAND
                                       4088
                                       (LOGHEAD
                                        28 (LOGTAIL 36 (XR :RGF *RSI* X86))))))
                                    :R X86)))))
                               12)))
                            (BYTE-IFY
                             8
                             (LOGIOR
                              (LOGAND
                               18442240475155922943
                               (COMBINE-BYTES
                                (MV-NTH
                                 1
                                 (RB
                                  (CREATE-CANONICAL-ADDRESS-LIST
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
                                       (COMBINE-BYTES
                                        (MV-NTH
                                         1
                                         (RB
                                          (CREATE-CANONICAL-ADDRESS-LIST
                                           8
                                           (LOGIOR
                                            (LOGAND
                                             -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                                            (LOGAND
                                             4088
                                             (LOGHEAD
                                              28 (LOGTAIL 36 (XR :RGF *RSI* X86))))))
                                          :R X86)))))
                                     12)))
                                  :R X86))))
                              (LOGAND
                               4503598553628672
                               (COMBINE-BYTES
                                (MV-NTH
                                 1
                                 (RB
                                  (CREATE-CANONICAL-ADDRESS-LIST
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
                                       (COMBINE-BYTES
                                        (MV-NTH
                                         1
                                         (RB
                                          (CREATE-CANONICAL-ADDRESS-LIST
                                           8
                                           (LOGIOR
                                            (LOGAND
                                             -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                                            (LOGAND
                                             4088
                                             (LOGHEAD
                                              28 (LOGTAIL 36 (XR :RGF *RDI* X86))))))
                                          :R X86)))))
                                     12)))
                                  :R X86)))))))
                           (MV-NTH
                            2
                            (LAS-TO-PAS
                             (CREATE-CANONICAL-ADDRESS-LIST
                              6 (+ 184 (XR :RIP 0 X86)))
                             :X 0
                             (MV-NTH
                              2
                              (LAS-TO-PAS
                               (CREATE-CANONICAL-ADDRESS-LIST
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
                                    (COMBINE-BYTES
                                     (MV-NTH
                                      1
                                      (RB
                                       (CREATE-CANONICAL-ADDRESS-LIST
                                        8
                                        (LOGIOR
                                         (LOGAND
                                          -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                                         (LOGAND
                                          4088
                                          (LOGHEAD
                                           28 (LOGTAIL 36 (XR :RGF *RSI* X86))))))
                                       :R X86)))))
                                  12)))
                               :R 0
                               (MV-NTH
                                2
                                (LAS-TO-PAS
                                 (CREATE-CANONICAL-ADDRESS-LIST
                                  40 (+ 144 (XR :RIP 0 X86)))
                                 :X 0
                                 (MV-NTH
                                  2
                                  (LAS-TO-PAS
                                   (CREATE-CANONICAL-ADDRESS-LIST
                                    3 (+ 140 (XR :RIP 0 X86)))
                                   :X 0
                                   (MV-NTH
                                    2
                                    (LAS-TO-PAS
                                     (CREATE-CANONICAL-ADDRESS-LIST
                                      8
                                      (LOGIOR
                                       (LOGAND -4096 (LOGEXT 64 (XR :CTR *CR3* X86)))
                                       (LOGAND
                                        4088
                                        (LOGHEAD
                                         28 (LOGTAIL 36 (XR :RGF *RSI* X86))))))
                                     :R 0
                                     (MV-NTH
                                      2
                                      (LAS-TO-PAS
                                       (CREATE-CANONICAL-ADDRESS-LIST
                                        32 (+ 108 (XR :RIP 0 X86)))
                                       :X 0
                                       (MV-NTH
                                        2
                                        (LAS-TO-PAS
                                         (CREATE-CANONICAL-ADDRESS-LIST
                                          18 (+ 86 (XR :RIP 0 X86)))
                                         :X 0
                                         (MV-NTH
                                          2
                                          (LAS-TO-PAS
                                           (CREATE-CANONICAL-ADDRESS-LIST
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
                                                (COMBINE-BYTES
                                                 (MV-NTH
                                                  1
                                                  (RB
                                                   (CREATE-CANONICAL-ADDRESS-LIST
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
                                                        36 (XR :RGF *RDI* X86))))))
                                                   :R X86)))))
                                              12)))
                                           :R 0
                                           (MV-NTH
                                            2
                                            (LAS-TO-PAS
                                             (CREATE-CANONICAL-ADDRESS-LIST
                                              40 (+ 46 (XR :RIP 0 X86)))
                                             :X 0
                                             (MV-NTH
                                              2
                                              (LAS-TO-PAS
                                               (CREATE-CANONICAL-ADDRESS-LIST
                                                4 (+ 38 (XR :RIP 0 X86)))
                                               :X 0
                                               (MV-NTH
                                                2
                                                (LAS-TO-PAS
                                                 (CREATE-CANONICAL-ADDRESS-LIST
                                                  8
                                                  (LOGIOR
                                                   (LOGAND
                                                    -4096
                                                    (LOGEXT 64 (XR :CTR *CR3* X86)))
                                                   (LOGAND
                                                    4088
                                                    (LOGHEAD
                                                     28
                                                     (LOGTAIL
                                                      36 (XR :RGF *RDI* X86))))))
                                                 :R 0
                                                 (MV-NTH
                                                  2
                                                  (LAS-TO-PAS
                                                   (CREATE-CANONICAL-ADDRESS-LIST
                                                    25 (+ 13 (XR :RIP 0 X86)))
                                                   :X 0
                                                   (MV-NTH
                                                    2
                                                    (LAS-TO-PAS
                                                     (CREATE-CANONICAL-ADDRESS-LIST
                                                      8 (+ -24 (XR :RGF *RSP* X86)))
                                                     :R 0
                                                     (MV-NTH
                                                      2
                                                      (LAS-TO-PAS
                                                       (CREATE-CANONICAL-ADDRESS-LIST
                                                        5 (+ 8 (XR :RIP 0 X86)))
                                                       :X 0
                                                       (MV-NTH
                                                        1
                                                        (WB
                                                         (CREATE-ADDR-BYTES-ALIST
                                                          (CREATE-CANONICAL-ADDRESS-LIST
                                                           8
                                                           (+
                                                            -24 (XR :RGF *RSP* X86)))
                                                          (BYTE-IFY
                                                           8 (XR :CTR *CR3* X86)))
                                                         (MV-NTH
                                                          2
                                                          (LAS-TO-PAS
                                                           (CREATE-CANONICAL-ADDRESS-LIST
                                                            8 (XR :RIP 0 X86))
                                                           :X 0
                                                           X86)))))))))))))))))))))))))))))))))))))))))))))))))))

  :hints (("Goal"
           :do-not-induct t
           :do-not '(preprocess)
           :in-theory (e/d* (len
                             page-size
                             consp-of-create-canonical-address-list
                             car-create-canonical-address-list
                             cdr-create-canonical-address-list
                             loghead-negative
                             disjoint-p-all-translation-governing-addresses-subset-p)
                            (create-canonical-address-list
                             (:rewrite program-at-values-and-!flgi)
                             (:rewrite get-prefixes-opener-lemma-group-4-prefix-in-marking-mode)
                             (:rewrite rb-in-terms-of-rb-subset-p-in-system-level-mode)
                             (:rewrite get-prefixes-opener-lemma-group-3-prefix-in-marking-mode)
                             (:rewrite get-prefixes-opener-lemma-group-2-prefix-in-marking-mode)
                             (:rewrite get-prefixes-opener-lemma-group-1-prefix-in-marking-mode)
                             (:rewrite mv-nth-1-rb-and-xlate-equiv-memory-disjoint-from-paging-structures)
                             (:rewrite mv-nth-2-rb-in-system-level-non-marking-mode)
                             (:rewrite rb-returns-x86-programmer-level-mode)
                             (:linear rm-low-64-logand-logior-helper-1)
                             (:definition n64p$inline)
                             (:type-prescription xlate-equiv-memory)
                             (:rewrite program-at-alt-wb-disjoint-in-system-level-mode)
                             (:type-prescription natp-page-dir-ptr-table-entry-addr)
                             mv-nth-1-las-to-pas-subset-p-disjoint-from-other-p-addrs
                             mv-nth-2-las-to-pas-system-level-non-marking-mode
                             (:rewrite r/x-is-irrelevant-for-mv-nth-2-las-to-pas-when-no-errors)
                             (:rewrite acl2::cdr-of-append-when-consp)
                             (:rewrite acl2::car-of-append)
                             (:rewrite acl2::consp-of-append)
                             (:rewrite acl2::append-atom-under-list-equiv)
                             (:rewrite int-lists-in-seq-p-and-append)
                             (:type-prescription binary-append)
                             (:rewrite xr-fault-wb-in-system-level-mode)
                             (:type-prescription n01p-page-size)
                             (:type-prescription member-p-physical-address-p-physical-address-listp)
                             (:rewrite acl2::right-cancellation-for-+)
                             (:type-prescription member-p-physical-address-p)
                             (:rewrite acl2::append-singleton-under-set-equiv))))))

;; ======================================================================
