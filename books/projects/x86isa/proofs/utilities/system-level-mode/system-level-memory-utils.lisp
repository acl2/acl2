;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")
(include-book "paging-top")
;; [Shilpi]: Why do I need the following book?
;; (include-book "../programmer-level-mode/programmer-level-memory-utils")

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))

;; ======================================================================

(defsection system-level-memory-utils
  :parents (proof-utilities)

  :short "Helper lemmas for reasoning about memory in the system-level
  mode"
  )

(local (xdoc::set-default-parents system-level-memory-utils))

;; ======================================================================

;; The events below are similar to those in
;; programmer-level-memory-utils.lisp.

;; Theorems about rb and wb:

(defthm rm08-wm08-different-physical-addresses-no-overlapping-walks

  ;; Remember that translation-governing-addresses does not include
  ;; the linear address or the physical address.  It just has the
  ;; addresses of the paging entries that govern the translation of
  ;; that linear address.

  (implies
   (and

    ;; If I eliminate the (not (programmer-level-mode x86))
    ;; hypothesis, then i'd have to include the (not (equal
    ;; addr1 addr2)) hypothesis.

    (not (programmer-level-mode x86))
    (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))

    ;; Page walks for addr1 and addr2 have disjoint
    ;; translation-governing-addresses.

    ;; This is the hypothesis I'd like to remove from this theorem.
    ;; The other hypotheses rule out rm08 and wm08 operating on
    ;; addresses where the paging data structures are stored.

    (pairwise-disjoint-p
     (append (translation-governing-addresses addr2 x86)
             (translation-governing-addresses addr1 x86)))

    ;; Physical address corresponding to addr2 is disjoint from all
    ;; the translation-governing-addresses of addr1.
    (pairwise-disjoint-p-aux
     (addr-range 1 (mv-nth 1 (ia32e-la-to-pa addr2 :w cpl x86)))
     (translation-governing-addresses addr1 x86))

    ;; Physical address corresponding to addr1 is disjoint from all
    ;; the translation-governing-addresses of addr1.
    (pairwise-disjoint-p-aux
     (addr-range 1 (mv-nth 1 (ia32e-la-to-pa addr1 r-x cpl x86)))
     (translation-governing-addresses addr1 x86))

    ;; Physical address corresponding to addr1 is disjoint from all
    ;; the translation-governing-addresses of addr2.
    (pairwise-disjoint-p-aux
     (addr-range 1 (mv-nth 1 (ia32e-la-to-pa addr1 r-x cpl x86)))
     (translation-governing-addresses addr2 x86))

    ;; Physical addresses corresponding to addr1 and addr2 are
    ;; unequal.
    (disjoint-p (addr-range 1 (mv-nth 1 (ia32e-la-to-pa addr2 :w cpl x86)))
                (addr-range 1 (mv-nth 1 (ia32e-la-to-pa addr1 r-x cpl x86))))

    (ia32e-la-to-pa-validp addr1 r-x cpl x86)
    (ia32e-la-to-pa-validp addr2 :w cpl x86)
    (canonical-address-p addr2)
    (x86p x86))

   (equal (mv-nth 1 (rm08 addr1 r-x (mv-nth 1 (wm08 addr2 val x86))))
          (mv-nth 1 (rm08 addr1 r-x x86))))
  :hints (("Goal" :in-theory (e/d (rm08 wm08)
                                  (ia32e-la-to-pa-validp
                                   translation-governing-addresses
                                   pml4-table-entry-validp-to-page-dir-ptr-entry-validp
                                   addr-range-1
                                   mv-nth-1-no-error-ia32e-la-to-pa
                                   mv-nth-2-no-error-ia32e-la-to-pa)))))

;; ======================================================================

;; Relating top-level memory accessors and updaters with rb in system-level
;; mode:

(defthm rb-and-rm16-in-system-level-mode
  (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
                (ia32e-la-to-pa-validp lin-addr r-w-x cpl x86)
                (ia32e-la-to-pa-validp (1+ lin-addr) r-w-x cpl x86)

                ;; See the lemmas:
                ;; mv-nth-0-no-error-ia32e-la-to-pa and
                ;; validity-preserved-same-x86-state-disjoint-addresses-top-level-thm
                ;; to know why we need the following hypothesis.

                ;; Of course, this is a stupid hypothesis for this theorem
                ;; because the translation-governing-addresses of lin-addr and
                ;; (1+ lin-addr) might definitely overlap. I need more work in
                ;; paging-utils.lisp to prove more general version(s) of
                ;; validity-preserved-same-x86-state-disjoint-addresses-top-level-thm.

                ;; Instead, I'd like to have the following hyps. here:
                ;; (pairwise-disjoint-p
                ;;  (translation-governing-addresses lin-addr x86))
                ;; (pairwise-disjoint-p
                ;;  (translation-governing-addresses (+ 1 lin-addr) x86))
                ;; Of course, these two are true only if lin-addr and
                ;; 1+lin-addr fall within the same page. I might need
                ;; other hyps in an OR to capture other cases.
                (pairwise-disjoint-p
                 (append (translation-governing-addresses lin-addr x86)
                         (translation-governing-addresses (+ 1 lin-addr) x86)))


                ;; See the lemma
                ;; disjoint-memi-read-mv-nth-2-no-error-ia32e-la-to-pa
                ;; to know why we need the following hypothesis.
                (pairwise-disjoint-p-aux
                 (list (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x cpl x86)))
                 (translation-governing-addresses (+ 1 lin-addr) x86))

                (not (programmer-level-mode x86))
                (canonical-address-p lin-addr)
                (canonical-address-p (1+ lin-addr))
                (x86p x86))
           (equal (rm16 lin-addr r-w-x x86)
                  (b* (((mv flg bytes x86)
                        (rb (create-canonical-address-list 2 lin-addr) r-w-x x86))
                       (result (combine-bytes bytes)))
                      (mv flg result x86))))
  :hints (("Goal" :in-theory (e/d* (rm08 rb rm16 rvm16)
                                   (mv-nth-1-no-error-ia32e-la-to-pa
                                    mv-nth-2-no-error-ia32e-la-to-pa
                                    pairwise-disjoint-p
                                    translation-governing-addresses
                                    ia32e-la-to-pa-validp)))))
