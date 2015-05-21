;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")
(include-book "paging-utils" :dir :proof-utils)
(include-book "programmer-level-memory-utils" :dir :proof-utils)

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


;; TO-DO@Shilpi: Relating a linear memory read/write to a physical
;; memory read/write...
;; (equal (rm08 lin-addr r-x x86)
;;        (memi phy-addr x86))


;; ======================================================================
