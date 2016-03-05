;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")

(include-book "../utilities/system-level-mode/paging-defs")

(include-book "centaur/bitops/ihs-extensions" :dir :system)
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))

;; ======================================================================

;; Introducing the system-level program:

(defconst *rewire_dst_to_src*

  '(#xF #x20 #xD8 #x48 #x89 #x44 #x24 #xE8
        #x48 #x8B #x54 #x24 #xE8 #x48 #x89 #xF8
        #x48 #xC1 #xE8 #x24 #x25 #xF8 #xF #x0
        #x0 #x48 #x81 #xE2 #x0 #xF0 #xFF #xFF
        #x48 #x9 #xD0 #x48 #x8B #x0 #xA8 #x1
        #xF #x84 #xD2 #x0 #x0 #x0 #x48 #xC1 #xE8
        #xC #x49 #xB8 #xFF #xFF #xFF #xFF #xFF
        #x0 #x0 #x0 #x48 #x89 #xF9 #x4C #x21
        #xC0 #x48 #xC1 #xE9 #x1B #x81 #xE1 #xF8
        #xF #x0 #x0 #x48 #xC1 #xE0 #xC #x48 #x9
        #xC8 #x48 #x8B #x0 #x48 #x89 #xC1 #x81
        #xE1 #x81 #x0 #x0 #x0 #x48 #x81 #xF9
        #x81 #x0 #x0 #x0 #xF #x85 #x94 #x0 #x0
        #x0 #x48 #x89 #xF1 #x49 #xB9 #x0 #x0 #x0
        #xC0 #xFF #xFF #xF #x0 #x48 #xC1 #xE9
        #x24 #x49 #x21 #xC1 #x81 #xE1 #xF8 #xF
        #x0 #x0 #x48 #x9 #xD1 #x48 #x8B #x1 #xA8
        #x1 #x74 #x70 #x48 #xC1 #xE8 #xC #x48
        #x89 #xF2 #x4C #x21 #xC0 #x48 #xC1 #xEA
        #x1B #x81 #xE2 #xF8 #xF #x0 #x0 #x48
        #xC1 #xE0 #xC #x48 #x9 #xD0 #x48 #xBA
        #xFF #xFF #xFF #x3F #x0 #x0 #xF0 #xFF
        #x48 #x23 #x10 #x4C #x9 #xCA #x48 #x89
        #x10 #x48 #x89 #xD0 #x25 #x81 #x0 #x0
        #x0 #x48 #x3D #x81 #x0 #x0 #x0 #x75 #x32
        #x48 #xB8 #x0 #x0 #x0 #xC0 #xFF #xFF
        #xF #x0 #x81 #xE6 #xFF #xFF #xFF #x3F
        #x81 #xE7 #xFF #xFF #xFF #x3F #x48 #x21
        #xC2 #x4C #x9 #xCF #x31 #xC0 #x48 #x9
        #xF2 #x48 #x39 #xD7 #xF #x94 #xC0 #xC3
        #x66 #x2E #xF #x1F #x84 #x0 #x0 #x0 #x0
        #x0 #x48 #xC7 #xC0 #xFF #xFF #xFF #xFF
        #xC3 #xF #x1F #x84 #x0 #x0 #x0 #x0 #x0))

;; ======================================================================

;; Control printing:

(acl2::add-untranslate-pattern-function
 (program-at (create-canonical-address-list 272 (xr :rip 0 x86))
             '(15 32 216 72 137 68 36 232 72 139 84 36 232
                  72 137 248 72 193 232 36 37 248 15 0 0
                  72 129 226 0 240 255 255 72 9 208 72 139
                  0 168 1 15 132 210 0 0 0 72 193 232 12
                  73 184 255 255 255 255 255 0 0 0 72 137
                  249 76 33 192 72 193 233 27 129 225 248
                  15 0 0 72 193 224 12 72 9 200 72 139 0
                  72 137 193 129 225 129 0 0 0 72 129 249
                  129 0 0 0 15 133 148 0 0 0 72 137 241
                  73 185 0 0 0 192 255 255 15 0 72 193 233
                  36 73 33 193 129 225 248 15 0 0 72 9 209
                  72 139 1 168 1 116 112 72 193 232 12 72
                  137 242 76 33 192 72 193 234 27 129 226
                  248 15 0 0 72 193 224 12 72 9 208 72 186
                  255 255 255 63 0 0 240 255 72 35 16 76
                  9 202 72 137 16 72 137 208 37 129 0 0 0
                  72 61 129 0 0 0 117 50 72 184 0 0 0 192
                  255 255 15 0 129 230 255 255 255 63 129
                  231 255 255 255 63 72 33 194 76 9 207
                  49 192 72 9 242 72 57 215 15 148 192 195
                  102 46 15 31 132 0 0 0 0 0 72 199 192
                  255 255 255 255 195 15 31 132 0 0 0 0 0)
             x86)
 (program-at (create-canonical-address-list (len *rewire_dst_to_src*) (xr :rip 0 x86))
             *rewire_dst_to_src*
             x86))

(acl2::add-untranslate-pattern-function
 '(15 32 216 72 137 68 36 232 72 139 84 36 232
      72 137 248 72 193 232 36 37 248 15 0 0
      72 129 226 0 240 255 255 72 9 208 72 139
      0 168 1 15 132 210 0 0 0 72 193 232 12
      73 184 255 255 255 255 255 0 0 0 72 137
      249 76 33 192 72 193 233 27 129 225 248
      15 0 0 72 193 224 12 72 9 200 72 139 0
      72 137 193 129 225 129 0 0 0 72 129 249
      129 0 0 0 15 133 148 0 0 0 72 137 241
      73 185 0 0 0 192 255 255 15 0 72 193 233
      36 73 33 193 129 225 248 15 0 0 72 9 209
      72 139 1 168 1 116 112 72 193 232 12 72
      137 242 76 33 192 72 193 234 27 129 226
      248 15 0 0 72 193 224 12 72 9 208 72 186
      255 255 255 63 0 0 240 255 72 35 16 76
      9 202 72 137 16 72 137 208 37 129 0 0 0
      72 61 129 0 0 0 117 50 72 184 0 0 0 192
      255 255 15 0 129 230 255 255 255 63 129
      231 255 255 255 63 72 33 194 76 9 207
      49 192 72 9 242 72 57 215 15 148 192 195
      102 46 15 31 132 0 0 0 0 0 72 199 192
      255 255 255 255 195 15 31 132 0 0 0 0 0)
 *rewire_dst_to_src*)

;; ======================================================================

;; (acl2::why x86-run-opener-not-ms-not-zp-n)
;; (acl2::why x86-fetch-decode-execute-opener)
;; (acl2::why get-prefixes-opener-lemma-no-prefix-byte)
;; (acl2::why rb-in-terms-of-nth-and-pos-in-system-level-non-marking-mode)
;; (acl2::why combine-bytes-rb-in-terms-of-rb-subset-p-in-system-level-non-marking-mode)
;; (acl2::why program-at-wb-disjoint-in-system-level-non-marking-mode)
;; (acl2::why member-p-canonical-address-listp)

;; Prove away all the skip-proofs below.

(skip-proofs
 (defthm ia32e-la-to-pa-values-and-!flgi
   (implies t
            (and (equal (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x cpl (!flgi index value x86)))
                        (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x cpl x86)))
                 (equal (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x cpl (!flgi index value x86)))
                        (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x cpl x86)))))))

(skip-proofs
 (defthm ia32e-la-to-pa-values-and-!flgi-undefined
   (implies t
            (and (equal (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x cpl (!flgi-undefined index x86)))
                        (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x cpl x86)))
                 (equal (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x cpl (!flgi-undefined index x86)))
                        (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x cpl x86)))))))

(skip-proofs
 (defthm las-to-pas-values-and-!flgi
   (implies t
            (and (equal (mv-nth 0 (las-to-pas l-addrs r-w-x cpl (!flgi index value x86)))
                        (mv-nth 0 (las-to-pas l-addrs r-w-x cpl x86)))
                 (equal (mv-nth 1 (las-to-pas l-addrs r-w-x cpl (!flgi index value x86)))
                        (mv-nth 1 (las-to-pas l-addrs r-w-x cpl x86)))))))

(skip-proofs
 (defthm las-to-pas-values-and-!flgi-undefined
   (implies t
            (and (equal (mv-nth 0 (las-to-pas l-addrs r-w-x cpl (!flgi-undefined index x86)))
                        (mv-nth 0 (las-to-pas l-addrs r-w-x cpl x86)))
                 (equal (mv-nth 1 (las-to-pas l-addrs r-w-x cpl (!flgi-undefined index x86)))
                        (mv-nth 1 (las-to-pas l-addrs r-w-x cpl x86)))))))

(skip-proofs
 (defthm rb-values-and-!flgi
   (implies t
            (and (equal (mv-nth 0 (rb lin-addr r-w-x (!flgi index value x86)))
                        (mv-nth 0 (rb lin-addr r-w-x x86)))
                 (equal (mv-nth 1 (rb lin-addr r-w-x (!flgi index value x86)))
                        (mv-nth 1 (rb lin-addr r-w-x x86)))))))

(skip-proofs
 (defthm rb-values-and-!flgi-undefined
   (implies t
            (and (equal (mv-nth 0 (rb lin-addr r-w-x (!flgi-undefined index x86)))
                        (mv-nth 0 (rb lin-addr r-w-x x86)))
                 (equal (mv-nth 1 (rb lin-addr r-w-x (!flgi-undefined index x86)))
                        (mv-nth 1 (rb lin-addr r-w-x x86)))))))

(defthm rewire_dst_to_src-effects
  (implies (and
            (x86p x86)
            (not (programmer-level-mode x86))
            (not (page-structure-marking-mode x86))
            (not (alignment-checking-enabled-p x86))

            (canonical-address-p (+ (len *rewire_dst_to_src*) (xr :rip 0 x86)))
            (canonical-address-p (xr :rip 0 x86))
            (canonical-address-p (+ -24 (xr :rgf *rsp* x86)))
            (canonical-address-p (xr :rgf *rsp* x86))
            (equal (xr :ms 0 x86) nil)
            (equal (xr :fault 0 x86) nil)
            (equal (cpl x86) 0)
            (program-at (create-canonical-address-list (len *rewire_dst_to_src*) (xr :rip 0 x86))
                        *rewire_dst_to_src* x86)

            ;; No errors encountered while translating the linear
            ;; addresses where the program is located.
            (not
             (mv-nth 0
                     (las-to-pas
                      (create-canonical-address-list (len *rewire_dst_to_src*) (xr :rip 0 x86))
                      :x (loghead 2 (xr :seg-visible 1 x86)) x86)))
            ;; No errors encountered while translating the linear
            ;; addresses corresponding to the program stack.
            (not
             (mv-nth
              0
              (las-to-pas (create-canonical-address-list 8 (+ -24 (xr :rgf *rsp* x86)))
                          :w 0 x86))))
           (equal (x86-run 2 x86)
                  (XW
                   :RGF
                   *RAX* (LOGEXT 64 (XR :CTR *CR3* X86))
                   (XW
                    :RIP 0 (+ 8 (XR :RIP 0 X86))
                    (MV-NTH
                     1
                     (WB
                      (CREATE-ADDR-BYTES-ALIST
                       (CREATE-CANONICAL-ADDRESS-LIST 8 (+ -24 (XR :RGF *RSP* X86)))
                       (BYTE-IFY 8 (XR :CTR *CR3* X86)))
                      (!FLGI-UNDEFINED
                       11
                       (!FLGI-UNDEFINED
                        7
                        (!FLGI-UNDEFINED
                         6
                         (!FLGI-UNDEFINED 4
                                          (!FLGI-UNDEFINED 2 (!FLGI-UNDEFINED 0 X86))))))))))))
  :hints (("Goal" :in-theory (e/d* (instruction-decoding-and-spec-rules
                                    top-level-opcode-execute
                                    two-byte-opcode-decode-and-execute
                                    x86-operand-from-modr/m-and-sib-bytes
                                    x86-effective-addr
                                    x86-effective-addr-from-sib
                                    x86-operand-to-reg/mem
                                    rr64 wr64
                                    rim08

                                    pos member-p subset-p)

                                   (unsigned-byte-p
                                    force (force))))))


;; ======================================================================
