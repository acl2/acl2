;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")
(include-book "paging-lib/paging-top")

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))

;; ======================================================================

(defsection system-level-memory-utils
  :parents (proof-utilities)

  :short "Helper lemmas for reasoning about memory in the system-level
  mode"
  )

(local (xdoc::set-default-parents system-level-memory-utils))

(local (in-theory (e/d* (entry-found-p-and-good-paging-structures-x86p
                         entry-found-p-and-lin-addr)
                        ())))

;; ======================================================================

(i-am-here)

(defthm ia32e-entries-found-la-to-pa-and-xw-mem-disjoint
  ;; [Shilpi]: Maybe I need something like this first?
  (implies (and (paging-entries-found-p addr-1 x86)
                (paging-entries-found-p addr-2 x86)
                (disjoint-p
                 ;; The physical addresses corresponding to addr-1 and
                 ;; the physical address addr-2 are disjoint.
                 (addr-range 8 (mv-nth 1 (ia32e-entries-found-la-to-pa addr-1 r-x cpl x86)))
                 (addr-range 8 addr-2))
                (pairwise-disjoint-p-aux
                 ;; Physical address addr-2 does not contain paging
                 ;; structure content.  This means that the
                 ;; translation-governing entries for addr-1 cannot be
                 ;; affected by the write to addr-2.
                 (addr-range 8 addr-2)
                 (gather-all-paging-structure-qword-addresses x86)))
           (equal (mv-nth 1 (ia32e-entries-found-la-to-pa addr-1 r-w-x cpl (xw :mem addr-2 val x86)))
                  (mv-nth 1 (ia32e-entries-found-la-to-pa addr-1 r-w-x cpl x86)))))

(defthm mv-nth-2-ia32e-entries-found-la-to-pa-and-xw-mem-disjoint
  ;; [Shilpi]: Maybe I need something like this first?
  (implies (and (paging-entries-found-p addr-1 x86)
                (paging-entries-found-p addr-2 x86)
                (disjoint-p
                 ;; The physical addresses corresponding to addr-1 and
                 ;; the physical address addr-2 are disjoint.
                 (addr-range 8 (mv-nth 1 (ia32e-entries-found-la-to-pa addr-1 r-x cpl x86)))
                 (addr-range 8 addr-2))
                (pairwise-disjoint-p-aux
                 ;; Physical address addr-2 does not contain paging
                 ;; structure content.  This means that the
                 ;; translation-governing entries for addr-1 cannot be
                 ;; affected by the write to addr-2.
                 (addr-range 8 addr-2)
                 (gather-all-paging-structure-qword-addresses x86)))
           (equal (xw :mem addr-2 val (mv-nth 2 (ia32e-entries-found-la-to-pa addr-1 r-w-x cpl x86)))
                  (mv-nth 2 (ia32e-entries-found-la-to-pa addr-1 r-w-x cpl (xw :mem addr-2 val x86))))))

(defthm rm08-wm08-disjoint-in-system-level-mode
  (implies (and (not (programmer-level-mode x86))
                (paging-entries-found-p addr-1 x86)
                (paging-entries-found-p addr-2 x86)
                (equal cpl
                       (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
                (disjoint-p
                 ;; The physical addresses corresponding to addr-1 and
                 ;; addr-2 are disjoint.
                 (addr-range 8 (mv-nth 1 (ia32e-entries-found-la-to-pa addr-1 r-x cpl x86)))
                 (addr-range 8 (mv-nth 1 (ia32e-entries-found-la-to-pa addr-2  :w cpl x86))))
                (pairwise-disjoint-p-aux
                 ;; The write isn't being done to the page tables ---
                 ;; this means that the translation-governing entries
                 ;; for addr-1 cannot be affected by the write.
                 (addr-range 8 (mv-nth 1 (ia32e-entries-found-la-to-pa addr-2  :w cpl x86)))
                 (gather-all-paging-structure-qword-addresses x86)))
           (equal (mv-nth 1 (rm08 addr-1 r-x (mv-nth 1 (wm08 addr-2 val x86))))
                  (mv-nth 1 (rm08 addr-1 r-x x86))))
  :hints (("Goal"
           :in-theory (e/d* (rm08-and-rm08-mapped
                             wm08-and-wm08-mapped
                             ia32e-la-to-pa-and-ia32e-entries-found-la-to-pa
                             wm08-mapped
                             rm08-mapped
                             rm08
                             wm08
                             ;; rm08
                             ;; wm08
                             )
                            (signed-byte-p))))
  :otf-flg t)


;; The events below are similar to those in
;; programmer-level-memory-utils.lisp.

;; Theorems about rb and wb:

;; (defthm rm08-wm08-different-physical-addresses-no-overlapping-walks

;;   ;; Remember that translation-governing-addresses does not include
;;   ;; the linear address or the physical address.  It just has the
;;   ;; addresses of the paging entries that govern the translation of
;;   ;; that linear address.

;;   (implies
;;    (and

;;     ;; If I eliminate the (not (programmer-level-mode x86))
;;     ;; hypothesis, then i'd have to include the (not (equal
;;     ;; addr1 addr2)) hypothesis.

;;     (not (programmer-level-mode x86))
;;     (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))

;;     ;; Page walks for addr1 and addr2 have disjoint
;;     ;; translation-governing-addresses.

;;     ;; This is the hypothesis I'd like to remove from this theorem.
;;     ;; The other hypotheses rule out rm08 and wm08 operating on
;;     ;; addresses where the paging data structures are stored.

;;     (pairwise-disjoint-p
;;      (append (translation-governing-addresses addr2 x86)
;;              (translation-governing-addresses addr1 x86)))

;;     ;; Physical address corresponding to addr2 is disjoint from all
;;     ;; the translation-governing-addresses of addr1.
;;     (pairwise-disjoint-p-aux
;;      (addr-range 1 (mv-nth 1 (ia32e-la-to-pa addr2 :w cpl x86)))
;;      (translation-governing-addresses addr1 x86))

;;     ;; Physical address corresponding to addr1 is disjoint from all
;;     ;; the translation-governing-addresses of addr1.
;;     (pairwise-disjoint-p-aux
;;      (addr-range 1 (mv-nth 1 (ia32e-la-to-pa addr1 r-x cpl x86)))
;;      (translation-governing-addresses addr1 x86))

;;     ;; Physical address corresponding to addr1 is disjoint from all
;;     ;; the translation-governing-addresses of addr2.
;;     (pairwise-disjoint-p-aux
;;      (addr-range 1 (mv-nth 1 (ia32e-la-to-pa addr1 r-x cpl x86)))
;;      (translation-governing-addresses addr2 x86))

;;     ;; Physical addresses corresponding to addr1 and addr2 are
;;     ;; unequal.
;;     (disjoint-p (addr-range 1 (mv-nth 1 (ia32e-la-to-pa addr2 :w cpl x86)))
;;                 (addr-range 1 (mv-nth 1 (ia32e-la-to-pa addr1 r-x cpl x86))))

;;     (ia32e-la-to-pa-validp addr1 r-x cpl x86)
;;     (ia32e-la-to-pa-validp addr2 :w cpl x86)
;;     (canonical-address-p addr2)
;;     (x86p x86))

;;    (equal (mv-nth 1 (rm08 addr1 r-x (mv-nth 1 (wm08 addr2 val x86))))
;;           (mv-nth 1 (rm08 addr1 r-x x86))))
;;   :hints (("Goal" :in-theory (e/d (rm08 wm08)
;;                                   (ia32e-la-to-pa-validp
;;                                    translation-governing-addresses
;;                                    pml4-table-entry-validp-to-page-dir-ptr-entry-validp
;;                                    addr-range-1
;;                                    mv-nth-1-no-error-ia32e-la-to-pa
;;                                    mv-nth-2-no-error-ia32e-la-to-pa)))))

;; ======================================================================

;; Relating top-level memory accessors and updaters with rb in system-level
;; mode:

;; (defthm rb-and-rm16-in-system-level-mode
;;   (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
;;                 (ia32e-la-to-pa-validp lin-addr r-w-x cpl x86)
;;                 (ia32e-la-to-pa-validp (1+ lin-addr) r-w-x cpl x86)

;;                 ;; See the lemmas:
;;                 ;; mv-nth-0-no-error-ia32e-la-to-pa and
;;                 ;; validity-preserved-same-x86-state-disjoint-addresses-top-level-thm
;;                 ;; to know why we need the following hypothesis.

;;                 ;; Of course, this is a stupid hypothesis for this theorem
;;                 ;; because the translation-governing-addresses of lin-addr and
;;                 ;; (1+ lin-addr) might definitely overlap. I need more work in
;;                 ;; paging-utils.lisp to prove more general version(s) of
;;                 ;; validity-preserved-same-x86-state-disjoint-addresses-top-level-thm.

;;                 ;; Instead, I'd like to have the following hyps. here:
;;                 ;; (pairwise-disjoint-p
;;                 ;;  (translation-governing-addresses lin-addr x86))
;;                 ;; (pairwise-disjoint-p
;;                 ;;  (translation-governing-addresses (+ 1 lin-addr) x86))
;;                 ;; Of course, these two are true only if lin-addr and
;;                 ;; 1+lin-addr fall within the same page. I might need
;;                 ;; other hyps in an OR to capture other cases.
;;                 (pairwise-disjoint-p
;;                  (append (translation-governing-addresses lin-addr x86)
;;                          (translation-governing-addresses (+ 1 lin-addr) x86)))


;;                 ;; See the lemma
;;                 ;; disjoint-memi-read-mv-nth-2-no-error-ia32e-la-to-pa
;;                 ;; to know why we need the following hypothesis.
;;                 (pairwise-disjoint-p-aux
;;                  (list (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x cpl x86)))
;;                  (translation-governing-addresses (+ 1 lin-addr) x86))

;;                 (not (programmer-level-mode x86))
;;                 (canonical-address-p lin-addr)
;;                 (canonical-address-p (1+ lin-addr))
;;                 (x86p x86))
;;            (equal (rm16 lin-addr r-w-x x86)
;;                   (b* (((mv flg bytes x86)
;;                         (rb (create-canonical-address-list 2 lin-addr) r-w-x x86))
;;                        (result (combine-bytes bytes)))
;;                       (mv flg result x86))))
;;   :hints (("Goal" :in-theory (e/d* (rm08 rb rm16 rvm16)
;;                                    (mv-nth-1-no-error-ia32e-la-to-pa
;;                                     mv-nth-2-no-error-ia32e-la-to-pa
;;                                     pairwise-disjoint-p
;;                                     translation-governing-addresses
;;                                     ia32e-la-to-pa-validp)))))
