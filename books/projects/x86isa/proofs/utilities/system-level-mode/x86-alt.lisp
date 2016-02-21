;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")

(include-book "physical-memory-utils" :ttags :all)
(include-book "paging-lib/paging-top" :ttags :all)
(include-book "normalize-memory-accesses" :ttags :all)

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))

;; ======================================================================

(local (in-theory (e/d (entry-found-p-and-lin-addr
                        entry-found-p-and-good-paging-structures-x86p)
                       (unsigned-byte-p
                        signed-byte-p))))

;; ======================================================================

;; Right now, it looks like I have to define alternative versions of
;; get-prefixes, x86-fetch-decode-execute, and x86-run, similar to the
;; alternative versions of paging traversal functions I defined in
;; paging-lib/x86-ia32e-paging-alt.lisp.

;; !!! BTW, an alternative version of x86-fetch-decode-execute means
;; !!! also having alternative versions of all the instruction
;; !!! semantic functions. SIGH.

;; Once I have these alternative versions, I should be able to define
;; get-prefixes-alt-and-mv-nth-2-xlate-equiv-x86s,
;; x86-fetch-decode-execute-alt-and-xlate-equiv-x86s, and
;; x86-run-alt-and-xlate-equiv-x86s as congruence rules.

;; (defthm get-prefixes-alt-and-mv-nth-2-xlate-equiv-x86s
;;   (implies (xlate-equiv-x86s x86-1 x86-2)
;;            (xlate-equiv-x86s
;;             (mv-nth 2 (get-prefixes-alt start-rip prefixes cnt x86-1))
;;             (mv-nth 2 (get-prefixes-alt start-rip prefixes cnt x86-2))))
;;   :rule-classes :congruence)

;; (defthm x86-fetch-decode-execute-alt-and-xlate-equiv-x86s
;;   (implies (xlate-equiv-x86s x86-1 x86-2)
;;            (xlate-equiv-x86s (x86-fetch-decode-execute-alt x86-1)
;;                              (x86-fetch-decode-execute-alt x86-2)))
;;   :rule-classes :congruence)

;; (defthm x86-run-alt-and-xlate-equiv-x86s
;;   (implies (xlate-equiv-x86s x86-1 x86-2)
;;            (xlate-equiv-x86s (x86-run-alt n x86-1)
;;                              (x86-run-alt n x86-2)))
;;   :rule-classes :congruence)

;; We also prove an opener lemma (a driver rule) for
;; x86-fetch-decode-execute.

;; (defthm x86-fetch-decode-execute-alt-opener-in-system-level-mode
;;   (implies
;;    (and (other-hyps-tbd)
;;         (not (xr :programmer-level-mode 0 x86)))
;;    (xlate-equiv-x86s
;;     (x86-fetch-decode-execute-alt x86)
;;     (top-level-opcode-execute
;;      start-rip temp-rip3 prefixes rex-byte opcode/escape-byte modr/m sib x86))))

;; Then, while unraveling the interpreter during a code proof, a new
;;  rule x86-run-alt-opener-not-ms-not-zp-n (similar to
;;  x86-run-opener-not-ms-not-zp-n) will rewrite (x86-run-alt n x86)
;;  to (x86-run-alt (1- n) (x86-fetch-decode-execute-alt x86)).

;; x86-run-alt-and-xlate-equiv-x86s says that it's okay to rewrite the
;; second argument of x86-run (i.e., (x86-fetch-decode-execute-alt
;; x86)) with something that's xlate-equiv-x86s to it. So, the rewrite
;; rule x86-fetch-decode-execute-opener-alt-in-system-level-mode will
;; be applicable, passing control over to top-level-opcode-execute and
;; eventually, the instruction semantic functions.

;; (i-am-here)

;; (defthm mv-nth-0-x86-operand-from-modr/m-and-sib-bytes-and-xlate-equiv-x86s
;;   (implies (xlate-equiv-x86s x86-1 x86-2)
;;            (equal (mv-nth
;;                    0
;;                    (x86-operand-from-modr/m-and-sib-bytes
;;                     reg-type operand-size inst-ac? p2 p4? temp-rip
;;                     rex-byte r/m mod sib num-imm-bytes x86-1))
;;                   (mv-nth
;;                    0
;;                    (x86-operand-from-modr/m-and-sib-bytes
;;                     reg-type operand-size inst-ac? p2 p4? temp-rip
;;                     rex-byte r/m mod sib num-imm-bytes x86-2))))
;;   :hints (("Goal" :in-theory (e/d* (x86-operand-from-modr/m-and-sib-bytes
;;                                     x86-effective-addr
;;                                     x86-effective-addr-from-sib
;;                                     alignment-checking-enabled-p
;;                                     rim08)
;;                                    (unsigned-byte-p
;;                                     signed-byte-p)))))


;; (defthm x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G-and-xlate-equiv-x86s
;;   (implies (xlate-equiv-x86s x86-1 x86-2)
;;            (xlate-equiv-x86s
;;             (x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G
;;              operation start-rip temp-rip prefixes rex-byte opcode modr/m sib x86-1)
;;             (x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G
;;              operation start-rip temp-rip prefixes rex-byte opcode modr/m sib x86-2)))
;;   :hints (("Goal" :in-theory (e/d* (x86-add/adc/sub/sbb/or/and/xor/cmp/test-E-G)
;;                                    ()))))


;; (defthm mv-nth-2-rm08-and-xlate-equiv-x86s
;;   (implies (and (paging-entries-found-p lin-addr (double-rewrite x86))
;;                 (not
;;                  (mv-nth
;;                   0
;;                   (ia32e-entries-found-la-to-pa
;;                    lin-addr r-w-x (loghead 2 (xr :seg-visible 1 x86)) x86))))
;;            (xlate-equiv-x86s
;;             (mv-nth 2 (rm08 lin-addr r-w-x x86))
;;             (double-rewrite x86)))
;;   :hints (("Goal" :in-theory (e/d* (rm08) ()))))

;; (defthm xlate-equiv-x86s-with-mv-nth-2-ia32e-entries-found-la-to-pa-new
;;   (implies
;;    (and (bind-free
;;          (find-an-xlate-equiv-x86
;;           'xlate-equiv-x86s-with-mv-nth-2-ia32e-entries-found-la-to-pa-new
;;           x86-1 'x86-2
;;           mfc state)
;;          (x86-2))
;;         ;; (not (mv-nth 0
;;         ;;              (ia32e-entries-found-la-to-pa lin-addr r-w-x cpl x86-1)))
;;         (xlate-equiv-x86s (double-rewrite x86-1) x86-2))
;;    (xlate-equiv-x86s
;;     (mv-nth 2 (ia32e-entries-found-la-to-pa lin-addr r-w-x cpl x86-1))
;;     (mv-nth 2 (ia32e-entries-found-la-to-pa lin-addr r-w-x cpl x86-2))))
;;   :hints (("Goal"
;;            :use ((:instance xlate-equiv-structures-open-for-ctr-and-msr))
;;            :in-theory (e/d* (ia32e-entries-found-la-to-pa
;;                              not-good-paging-structures-x86p-and-ia32e-la-to-pa-PML4T)
;;                             ()))))

;; (defthm mv-nth-2-rm08-and-xlate-equiv-x86s-new
;;   (implies (and (paging-entries-found-p lin-addr (double-rewrite x86-1))
;;                 (xlate-equiv-x86s x86-1 x86-2)
;;                 )
;;            (xlate-equiv-x86s
;;             (mv-nth 2 (rm08 lin-addr r-w-x x86-1))
;;             (mv-nth 2 (rm08 lin-addr r-w-x x86-2))))
;;   :hints (("Goal"
;;            :use ((:instance all-seg-visibles-equal-open (j 1)))
;;            :in-theory (e/d* (rm08)
;;                             (all-seg-visibles-equal-open)))))


;; (defthm xlate-equiv-x86s-with-mv-nth-2-ia32e-entries-found-la-to-pa-new
;;   (implies
;;    (xlate-equiv-x86s x86-1 x86-2)
;;    (xlate-equiv-x86s
;;     (mv-nth 2 (ia32e-entries-found-la-to-pa lin-addr r-w-x cpl x86-1))
;;     (mv-nth 2 (ia32e-entries-found-la-to-pa lin-addr r-w-x cpl x86-2))))
;;   :hints (("Goal"
;;            :use ((:instance xlate-equiv-structures-open-for-ctr-and-msr))
;;            :in-theory (e/d* (ia32e-entries-found-la-to-pa
;;                              not-good-paging-structures-x86p-and-ia32e-la-to-pa-PML4T)
;;                             ()))))

;; ======================================================================

(defthm mv-nth-2-page-table-entry-no-page-fault-p-with-xlate-equiv-x86s-1
  (implies
   (and (xlate-equiv-x86s x86-1 x86-2)
        (x86p x86-1)
        (x86p x86-2))
   (xlate-equiv-x86s
    (mv-nth 2 (page-table-entry-no-page-fault-p lin-addr e u-s-acc wp smep nxe r-w-x cpl x86-1))
    (mv-nth 2 (page-table-entry-no-page-fault-p lin-addr e u-s-acc wp smep nxe r-w-x cpl x86-2))))
  :hints (("Goal" :in-theory (e/d* (xlate-equiv-entries-and-page-present
                                    xlate-equiv-entries-and-page-read-write
                                    xlate-equiv-entries-and-page-user-supervisor
                                    xlate-equiv-entries-and-page-size
                                    page-table-entry-no-page-fault-p
                                    page-fault-exception
                                    xlate-equiv-x86s)
                                   (xlate-equiv-x86s-and-xr-simple-fields)))))

(defthm mv-nth-2-page-table-entry-no-page-fault-p-with-xlate-equiv-x86s-2
  (implies
   (and (xlate-equiv-entries e-1 e-2)
        (unsigned-byte-p 64 e-1)
        (unsigned-byte-p 64 e-2))
   (xlate-equiv-x86s
    (mv-nth 2 (page-table-entry-no-page-fault-p lin-addr e-1 u-s-acc wp smep nxe r-w-x cpl x86))
    (mv-nth 2 (page-table-entry-no-page-fault-p lin-addr e-2 u-s-acc wp smep nxe r-w-x cpl x86))))
  :hints (("Goal"
           :use ((:instance xlate-equiv-entries-and-logtail
                            (e-1 e-1) (e-2 e-2) (n 12))
                 (:instance xlate-equiv-entries-and-logtail
                            (e-1 e-1) (e-2 e-2) (n 52))
                 (:instance xlate-equiv-entries-and-page-execute-disable))
           :in-theory (e/d* (xlate-equiv-entries-and-page-present
                             xlate-equiv-entries-and-page-read-write
                             xlate-equiv-entries-and-page-user-supervisor
                             xlate-equiv-entries-and-page-size
                             page-table-entry-no-page-fault-p
                             page-fault-exception
                             xlate-equiv-x86s)
                            (xlate-equiv-x86s-and-xr-simple-fields)))))

(defthm xlate-equiv-x86s-with-mv-nth-2-ia32e-la-to-pa-PT-new
  (implies (xlate-equiv-x86s x86-1 x86-2)
           (xlate-equiv-x86s
            (mv-nth 2 (ia32e-la-to-pa-PT lin-addr u-s-acc wp smep nxe r-w-x cpl x86-1))
            (mv-nth 2 (ia32e-la-to-pa-PT lin-addr u-s-acc wp smep nxe r-w-x cpl x86-2))))
  :hints (("Goal" :do-not '(preprocess)
           :use ((:instance entry-found-p-and-good-paging-structures-x86p (x86 x86-1))
                 (:instance entry-found-p-and-good-paging-structures-x86p (x86 x86-2))
                 (:instance mv-nth-2-page-table-entry-no-page-fault-p-with-xlate-equiv-x86s-1
                            (lin-addr (logext 48 lin-addr))
                            (e (mv-nth 2 (read-page-table-entry (logext 48 lin-addr) x86-1))))
                 (:instance mv-nth-2-page-table-entry-no-page-fault-p-with-xlate-equiv-x86s-1
                            (lin-addr (logext 48 lin-addr))
                            (e (mv-nth 2 (read-page-table-entry (logext 48 lin-addr) x86-2))))
                 (:instance mv-nth-2-page-table-entry-no-page-fault-p-with-xlate-equiv-x86s-2
                            (lin-addr (logext 48 lin-addr))
                            (e-1 (mv-nth 2 (read-page-table-entry (logext 48 lin-addr) x86-1)))
                            (e-2 (mv-nth 2 (read-page-table-entry (logext 48 lin-addr) x86-2)))
                            (x86 x86-1))
                 (:instance mv-nth-2-page-table-entry-no-page-fault-p-with-xlate-equiv-x86s-2
                            (lin-addr (logext 48 lin-addr))
                            (e-1 (mv-nth 2 (read-page-table-entry (logext 48 lin-addr) x86-1)))
                            (e-2 (mv-nth 2 (read-page-table-entry (logext 48 lin-addr) x86-2)))
                            (x86 x86-2))
                 (:instance gather-all-paging-structure-qword-addresses-with-xlate-equiv-structures
                            (x86 x86-1)
                            (x86-equiv x86-2)))
           :in-theory (e/d* (ia32e-la-to-pa-PT
                             ia32e-la-to-pa-page-table-alt
                             read-page-table-entry)
                            (mv-nth-2-page-table-entry-no-page-fault-p-with-xlate-equiv-x86s-1
                             mv-nth-2-page-table-entry-no-page-fault-p-with-xlate-equiv-x86s-2
                             xlate-equiv-x86s-and-xr-simple-fields
                             bitops::logand-with-negated-bitmask
                             accessed-bit
                             dirty-bit
                             not
                             entry-found-p-and-good-paging-structures-x86p
                             no-duplicates-list-p))))
  :rule-classes :congruence)

;; ======================================================================

(defthm mv-nth-2-paging-entry-no-page-fault-p-with-xlate-equiv-x86s-1
  (implies (and (xlate-equiv-x86s x86-1 x86-2)
                (x86p x86-1)
                (x86p x86-2))
           (xlate-equiv-x86s
            (mv-nth 2 (paging-entry-no-page-fault-p lin-addr e wp smep nxe r-w-x cpl x86-1))
            (mv-nth 2 (paging-entry-no-page-fault-p lin-addr e wp smep nxe r-w-x cpl x86-2))))
  :hints (("Goal" :in-theory (e/d* (xlate-equiv-entries-and-page-present
                                    xlate-equiv-entries-and-page-read-write
                                    xlate-equiv-entries-and-page-user-supervisor
                                    xlate-equiv-entries-and-page-size
                                    paging-entry-no-page-fault-p
                                    page-fault-exception
                                    xlate-equiv-x86s)
                                   (xlate-equiv-x86s-and-xr-simple-fields)))))

(defthm mv-nth-2-paging-entry-no-page-fault-p-with-xlate-equiv-x86s-2
  (implies
   (and (xlate-equiv-entries e-1 e-2)
        (unsigned-byte-p 64 e-1)
        (unsigned-byte-p 64 e-2))
   (xlate-equiv-x86s
    (mv-nth 2 (paging-entry-no-page-fault-p lin-addr e-1 wp smep nxe r-w-x cpl x86))
    (mv-nth 2 (paging-entry-no-page-fault-p lin-addr e-2 wp smep nxe r-w-x cpl x86))))
  :hints (("Goal"
           :use ((:instance xlate-equiv-entries-and-logtail
                            (e-1 e-1) (e-2 e-2) (n 13))
                 (:instance xlate-equiv-entries-and-logtail
                            (e-1 e-1) (e-2 e-2) (n 52))
                 (:instance xlate-equiv-entries-and-page-execute-disable)
                 (:instance xlate-equiv-entries-and-page-size))
           :in-theory (e/d* (xlate-equiv-entries-and-page-present
                             xlate-equiv-entries-and-page-read-write
                             xlate-equiv-entries-and-page-user-supervisor
                             paging-entry-no-page-fault-p
                             page-fault-exception
                             xlate-equiv-x86s)
                            (xlate-equiv-x86s-and-xr-simple-fields)))))

(i-am-here)

(defthm xlate-equiv-x86s-with-mv-nth-2-ia32e-la-to-pa-PD-new
  (implies (xlate-equiv-x86s x86-1 x86-2)
           (xlate-equiv-x86s
            (mv-nth 2 (ia32e-la-to-pa-PD lin-addr wp smep nxe r-w-x cpl x86-2))
            (mv-nth 2 (ia32e-la-to-pa-PD lin-addr wp smep nxe r-w-x cpl x86-1))))
  :hints (("Goal" :do-not '(preprocess)
           :use ((:instance entry-found-p-and-good-paging-structures-x86p (x86 x86-1))
                 (:instance entry-found-p-and-good-paging-structures-x86p (x86 x86-2))
                 (:instance mv-nth-2-paging-entry-no-page-fault-p-with-xlate-equiv-x86s-1
                            (lin-addr lin-addr)
                            (e (mv-nth 2 (read-page-directory-entry lin-addr x86-1))))
                 (:instance mv-nth-2-paging-entry-no-page-fault-p-with-xlate-equiv-x86s-1
                            (lin-addr lin-addr)
                            (e (mv-nth 2 (read-page-directory-entry lin-addr x86-2))))
                 (:instance mv-nth-2-paging-entry-no-page-fault-p-with-xlate-equiv-x86s-2
                            (lin-addr lin-addr)
                            (e-1 (mv-nth 2 (read-page-directory-entry lin-addr x86-1)))
                            (e-2 (mv-nth 2 (read-page-directory-entry lin-addr x86-2)))
                            (x86 x86-1))
                 (:instance mv-nth-2-paging-entry-no-page-fault-p-with-xlate-equiv-x86s-2
                            (lin-addr lin-addr)
                            (e-1 (mv-nth 2 (read-page-directory-entry lin-addr x86-1)))
                            (e-2 (mv-nth 2 (read-page-directory-entry lin-addr x86-2)))
                            (x86 x86-2))
                 (:instance gather-all-paging-structure-qword-addresses-with-xlate-equiv-structures
                            (x86 x86-1)
                            (x86-equiv x86-2)))
           :in-theory (e/d* (ia32e-la-to-pa-PD
                             ia32e-la-to-pa-page-directory-alt
                             read-page-directory-entry)
                            (mv-nth-2-paging-entry-no-page-fault-p-with-xlate-equiv-x86s-1
                             mv-nth-2-paging-entry-no-page-fault-p-with-xlate-equiv-x86s-2
                             xlate-equiv-x86s-and-xr-simple-fields
                             bitops::logand-with-negated-bitmask
                             accessed-bit
                             dirty-bit
                             not
                             entry-found-p-and-good-paging-structures-x86p
                             no-duplicates-list-p)))))

;; ======================================================================

(i-am-here)

(include-book "x86-ia32e-paging-alt")
(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))

(local (include-book "gl-lemmas" :dir :system))

(local (in-theory (e/d* () (signed-byte-p unsigned-byte-p))))

(defthm not-superior-entry-points-to-an-inferior-one-p-implies-error-in-paging-entry-no-page-fault-p-of-inferior-entry
  (implies (and
            ;; Together, the two hyps below say that the superior
            ;; entry is supposed to point to to an inferior one but
            ;; the page present bit in the superior entry is clear.
            (not (superior-entry-points-to-an-inferior-one-p superior-entry-addr x86))
            (equal (page-size (rm-low-64 superior-entry-addr x86)) 0)
            (x86p x86))
           (mv-nth
            0
            (paging-entry-no-page-fault-p
             lin-addr
             (rm-low-64 superior-entry-addr x86)
             wp smep nxe r-w-x cpl x86)))
  :hints (("Goal" :in-theory (e/d* (superior-entry-points-to-an-inferior-one-p
                                    paging-entry-no-page-fault-p)
                                   ()))))

(defthm ia32e-la-to-pa-pml4-table-when-no-page-dir-ptr-table-entry-addr-found-p
  (implies (and
            (equal pml4-table-base-addr (mv-nth 1 (pml4-table-base-addr x86)))
            (pml4-table-entry-addr-found-p lin-addr (double-rewrite x86))
            ;; TO-DO: Shouldn't the page size always be 0 for a
            ;; pml4-entry?  Check the definition of
            ;; ia32e-la-to-pa-pml4-table.
            (equal
             (page-size
              (rm-low-64 (pml4-table-entry-addr lin-addr pml4-table-base-addr) x86))
             0)
            (not (page-dir-ptr-table-entry-addr-found-p lin-addr (double-rewrite x86))))
           (equal (mv-nth
                   0
                   (ia32e-la-to-pa-pml4-table
                    lin-addr pml4-table-base-addr wp smep nxe r-w-x cpl x86))
                  'page-fault))
  :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa-pml4-table
                                    ia32e-la-to-pa-page-dir-ptr-table)
                                   (bitops::logand-with-negated-bitmask)))))


;; (defthm ia32e-la-to-pa-page-table-when-not-page-table-entry-addr-found-p
;;   (implies (and (not (page-table-entry-addr-found-p lin-addr x86))
;;                 ;; If page-directory-entry-addr-found-p doesn't hold,
;;                 ;; then we shouldn't have been in the walker for page
;;                 ;; table in the first place.
;;                 (page-directory-entry-addr-found-p lin-addr x86)
;;                 (canonical-address-p lin-addr)
;;                 (not (programmer-level-mode x86))
;;                 (equal base-addr (mv-nth 1 (page-table-base-addr lin-addr x86))))
;;            (equal
;;             (ia32e-la-to-pa-page-table
;;              lin-addr base-addr u-s-acc wp smep nxe r-w-x cpl x86)
;;             xxx))
;;   :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa-page-table
;;                                     page-table-entry-addr-found-p
;;                                     page-table-entry-addr
;;                                     page-execute-disable
;;                                     page-present
;;                                     page-size
;;                                     page-read-write
;;                                     page-user-supervisor)
;;                                    (bitops::logand-with-negated-bitmask)))))

;; (defthm ia32e-la-to-pa-page-table-alt-when-not-page-table-entry-addr-found-p
;;   (implies (and (not (page-table-entry-addr-found-p lin-addr x86))
;;                 (canonical-address-p lin-addr)
;;                 (not (programmer-level-mode x86))
;;                 )
;;            (equal
;;             (ia32e-la-to-pa-page-table-alt
;;              lin-addr u-s-acc wp smep nxe r-w-x cpl x86)
;;             xxxx))
;;   :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa-page-table-alt) ()))))

;; (defthm ia32e-la-to-pa-when-not-paging-entries-found-p
;;   (implies (and (not (paging-entries-found-p lin-addr (double-rewrite x86)))
;;                 (canonical-address-p lin-addr)
;;                 (not (programmer-level-mode x86)))
;;            (equal (ia32e-la-to-pa lin-addr r-w-x cpl x86)
;;                   xxxx))
;;   :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa
;;                                     ia32e-la-to-pa-pml4-table
;;                                     pml4-table-base-addr
;;                                     paging-entries-found-p
;;                                     paging-entry-no-page-fault-p)
;;                                    ()))))
