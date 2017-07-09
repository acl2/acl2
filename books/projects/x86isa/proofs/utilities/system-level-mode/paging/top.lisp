;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")
(include-book "common-paging-lemmas" :ttags :all)
(include-book "la-to-pa-lemmas" :ttags :all)

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))

(local (in-theory (e/d* () (unsigned-byte-p signed-byte-p))))

(defsection reasoning-about-page-tables
  :parents (system-level-marking-mode-proof-utilities)
  )

(local (xdoc::set-default-parents reasoning-about-page-tables))

;; ======================================================================

;; Some congruence rules about xlation-governing-entries-paddrs:

(defthm xlation-governing-entries-paddrs-for-page-table-and-xlate-equiv-memory-cong
  (implies (xlate-equiv-memory x86-1 x86-2)
           (equal (xlation-governing-entries-paddrs-for-page-table lin-addr base-addr x86-1)
                  (xlation-governing-entries-paddrs-for-page-table lin-addr base-addr x86-2)))
  :hints (("Goal" :in-theory (e/d* (xlation-governing-entries-paddrs-for-page-table) ())))
  :rule-classes :congruence)

(defthm xlation-governing-entries-paddrs-for-page-directory-and-xlate-equiv-memory-cong
  (implies (xlate-equiv-memory x86-1 x86-2)
           (equal (xlation-governing-entries-paddrs-for-page-directory lin-addr base-addr x86-1)
                  (xlation-governing-entries-paddrs-for-page-directory lin-addr base-addr x86-2)))
  :hints (("Goal" :in-theory (e/d* (xlation-governing-entries-paddrs-for-page-directory)
                                   (xlate-equiv-memory-and-xlate-equiv-entries-rm-low-64-with-page-directory-entry-addr-cong))
           :use ((:instance xlate-equiv-memory-and-xlate-equiv-entries-rm-low-64-with-page-directory-entry-addr-cong)
                 (:instance xlate-equiv-entries-and-page-size
                            (e-1 (rm-low-64 (page-directory-entry-addr lin-addr base-addr) x86-1))
                            (e-2 (rm-low-64 (page-directory-entry-addr lin-addr base-addr) x86-2))))))
  :rule-classes :congruence)

(defthm xlation-governing-entries-paddrs-for-page-dir-ptr-table-and-xlate-equiv-memory-cong
  (implies (xlate-equiv-memory x86-1 x86-2)
           (equal (xlation-governing-entries-paddrs-for-page-dir-ptr-table lin-addr base-addr x86-1)
                  (xlation-governing-entries-paddrs-for-page-dir-ptr-table lin-addr base-addr x86-2)))
  :hints (("Goal" :in-theory (e/d* (xlation-governing-entries-paddrs-for-page-dir-ptr-table)
                                   (xlate-equiv-memory-and-xlate-equiv-entries-rm-low-64-with-page-dir-ptr-table-entry-addr-cong))
           :use ((:instance xlate-equiv-memory-and-xlate-equiv-entries-rm-low-64-with-page-dir-ptr-table-entry-addr-cong)
                 (:instance xlate-equiv-entries-and-page-size
                            (e-1 (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr) x86-1))
                            (e-2 (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr) x86-2))))))
  :rule-classes :congruence)

(defthm xlation-governing-entries-paddrs-for-pml4-table-and-xlate-equiv-memory-cong
  (implies (xlate-equiv-memory x86-1 x86-2)
           (equal (xlation-governing-entries-paddrs-for-pml4-table lin-addr base-addr x86-1)
                  (xlation-governing-entries-paddrs-for-pml4-table lin-addr base-addr x86-2)))
  :hints (("Goal" :in-theory (e/d* (xlation-governing-entries-paddrs-for-pml4-table)
                                   (xlate-equiv-memory-and-xlate-equiv-entries-rm-low-64-with-pml4-table-entry-addr-cong))
           :use ((:instance xlate-equiv-memory-and-xlate-equiv-entries-rm-low-64-with-pml4-table-entry-addr-cong)
                 (:instance xlate-equiv-entries-and-page-size
                            (e-1 (rm-low-64 (pml4-table-entry-addr lin-addr base-addr) x86-1))
                            (e-2 (rm-low-64 (pml4-table-entry-addr lin-addr base-addr) x86-2))))))
  :rule-classes :congruence)

(defthm xlation-governing-entries-paddrs-and-xlate-equiv-memory-cong
  (implies (xlate-equiv-memory x86-1 x86-2)
           (equal (xlation-governing-entries-paddrs lin-addr x86-1)
                  (xlation-governing-entries-paddrs lin-addr x86-2)))
  :hints (("Goal"
           :in-theory (e/d* (xlation-governing-entries-paddrs) ())
           :use ((:instance xlate-equiv-memory-and-cr3-cong))))
  :rule-classes :congruence)

(defthm all-xlation-governing-entries-paddrs-and-xlate-equiv-memory-cong
  (implies (xlate-equiv-memory x86-1 x86-2)
           (equal (all-xlation-governing-entries-paddrs lin-addr x86-1)
                  (all-xlation-governing-entries-paddrs lin-addr x86-2)))
  :rule-classes :congruence)

;; ======================================================================

;; Memory reads from the state returned after a page walk:

(defthm xr-mem-disjoint-ia32e-la-to-pa-page-table
  (implies (and (disjoint-p (list index)
                            (xlation-governing-entries-paddrs-for-page-table
                             lin-addr base-addr (double-rewrite x86)))
                (canonical-address-p lin-addr)
                (physical-address-p base-addr)
                (equal (loghead 12 base-addr) 0))
           (equal (xr :mem index (mv-nth 2 (ia32e-la-to-pa-page-table
                                            lin-addr
                                            base-addr u/s-acc r/w-acc x/d-acc
                                            wp smep smap ac nxe r-w-x cpl x86)))
                  (xr :mem index x86)))
  :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa-page-table
                                    xlation-governing-entries-paddrs-for-page-table)
                                   (negative-logand-to-positive-logand-with-integerp-x
                                    bitops::logand-with-negated-bitmask)))))

(defthm xr-mem-disjoint-ia32e-la-to-pa-page-directory
  (implies (and (disjoint-p (list index)
                            (xlation-governing-entries-paddrs-for-page-directory
                             lin-addr base-addr (double-rewrite x86)))
                (canonical-address-p lin-addr)
                (physical-address-p base-addr)
                (equal (loghead 12 base-addr) 0))
           (equal (xr :mem index (mv-nth 2 (ia32e-la-to-pa-page-directory
                                            lin-addr
                                            base-addr u/s-acc r/w-acc x/d-acc
                                            wp smep smap ac nxe r-w-x cpl x86)))
                  (xr :mem index x86)))
  :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa-page-directory
                                    xlation-governing-entries-paddrs-for-page-directory)
                                   (negative-logand-to-positive-logand-with-integerp-x
                                    bitops::logand-with-negated-bitmask)))))

(defthm xr-mem-disjoint-ia32e-la-to-pa-page-dir-ptr-table
  (implies (and (disjoint-p (list index)
                            (xlation-governing-entries-paddrs-for-page-dir-ptr-table
                             lin-addr base-addr (double-rewrite x86)))
                (canonical-address-p lin-addr)
                (physical-address-p base-addr)
                (equal (loghead 12 base-addr) 0))
           (equal (xr :mem index (mv-nth 2 (ia32e-la-to-pa-page-dir-ptr-table
                                            lin-addr
                                            base-addr u/s-acc r/w-acc x/d-acc
                                            wp smep smap ac nxe r-w-x cpl x86)))
                  (xr :mem index x86)))
  :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa-page-dir-ptr-table
                                    xlation-governing-entries-paddrs-for-page-dir-ptr-table)
                                   (negative-logand-to-positive-logand-with-integerp-x
                                    bitops::logand-with-negated-bitmask)))))

(defthm xr-mem-disjoint-ia32e-la-to-pa-pml4-table
  (implies (and (disjoint-p (list index)
                            (xlation-governing-entries-paddrs-for-pml4-table
                             lin-addr base-addr (double-rewrite x86)))
                (canonical-address-p lin-addr)
                (physical-address-p base-addr)
                (equal (loghead 12 base-addr) 0))
           (equal (xr :mem index (mv-nth 2 (ia32e-la-to-pa-pml4-table
                                            lin-addr base-addr
                                            wp smep smap ac nxe r-w-x cpl x86)))
                  (xr :mem index x86)))
  :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa-pml4-table
                                    xlation-governing-entries-paddrs-for-pml4-table)
                                   (negative-logand-to-positive-logand-with-integerp-x
                                    bitops::logand-with-negated-bitmask)))))

(defthm xr-mem-disjoint-ia32e-la-to-pa
  (implies (and (disjoint-p (list index)
                            (xlation-governing-entries-paddrs lin-addr (double-rewrite x86)))
                (canonical-address-p lin-addr))
           (equal (xr :mem index (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x x86)))
                  (xr :mem index x86)))
  :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa
                                    xlation-governing-entries-paddrs)
                                   (negative-logand-to-positive-logand-with-integerp-x
                                    bitops::logand-with-negated-bitmask
                                    force (force))))))

(i-am-here)

(defthm xr-mem-disjoint-las-to-pas
  (implies
   (and
    (disjoint-p (list index)
                (all-xlation-governing-entries-paddrs l-addrs (double-rewrite x86)))
    (canonical-address-listp l-addrs))
   (equal (xr :mem index (mv-nth 2 (las-to-pas l-addrs r-w-x cpl x86)))
          (xr :mem index x86)))
  :hints (("Goal"
           :induct (las-to-pas l-addrs r-w-x cpl x86)
           :in-theory (e/d* (las-to-pas
                             all-xlation-governing-entries-paddrs
                             disjoint-p
                             member-p)
                            (negative-logand-to-positive-logand-with-integerp-x
                             bitops::logand-with-negated-bitmask
                             force (force))))))

(defthm read-from-physical-memory-and-mv-nth-2-ia32e-la-to-pa
  (implies (and (canonical-address-p lin-addr)
                (disjoint-p p-addrs (xlation-governing-entries-paddrs lin-addr (double-rewrite x86))))
           (equal (read-from-physical-memory p-addrs (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x cpl x86)))
                  (read-from-physical-memory p-addrs x86)))
  :hints (("Goal" :in-theory (e/d* (disjoint-p) (force (force))))))

(defthm read-from-physical-memory-and-mv-nth-2-las-to-pas
  (implies (and (disjoint-p p-addrs (all-xlation-governing-entries-paddrs l-addrs (double-rewrite x86)))
                (canonical-address-listp l-addrs))
           (equal (read-from-physical-memory p-addrs (mv-nth 2 (las-to-pas l-addrs r-w-x cpl x86)))
                  (read-from-physical-memory p-addrs x86)))
  :hints (("Goal" :in-theory (e/d* (disjoint-p) (force (force))))))

(defthm rm-low-64-disjoint-ia32e-la-to-pa
  (implies (and (disjoint-p (addr-range 8 index)
                            (xlation-governing-entries-paddrs lin-addr (double-rewrite x86)))
                (canonical-address-p lin-addr))
           (equal (rm-low-64 index (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x cpl x86)))
                  (rm-low-64 index x86)))
  :hints (("Goal" :in-theory (e/d* (rm-low-64 rm-low-32 disjoint-p)
                                   (xlation-governing-entries-paddrs
                                    negative-logand-to-positive-logand-with-integerp-x
                                    bitops::logand-with-negated-bitmask
                                    force (force))))))

(defthm rm-low-64-disjoint-las-to-pas
  (implies (and (disjoint-p (addr-range 8 index)
                            (all-xlation-governing-entries-paddrs l-addrs (double-rewrite x86)))
                (canonical-address-listp l-addrs)
                (x86p x86))
           (equal (rm-low-64 index (mv-nth 2 (las-to-pas l-addrs r-w-x cpl x86)))
                  (rm-low-64 index x86)))
  :hints (("Goal" :induct (las-to-pas l-addrs r-w-x cpl x86)
           :in-theory (e/d* (las-to-pas
                             disjoint-p)
                            (xlation-governing-entries-paddrs
                             negative-logand-to-positive-logand-with-integerp-x
                             bitops::logand-with-negated-bitmask
                             force (force))))))

;; ======================================================================

;; Proof that the xlation-governing-entries-paddrs for every canonical
;; address are a subset of the addresses described by
;; gather-all-paging-structure-qword-addresses:

(defthm xlation-governing-entries-paddrs-for-page-table-subset-of-paging-structures
  (implies
   (and (equal base-addr (page-table-base-addr lin-addr x86))
        ;; The following hyps are not needed when an
        ;; over-approximation of paging addresses is collected
        ;; instead.
        ;; (equal
        ;;  (page-present
        ;;   (rm-low-64 (pml4-table-entry-addr lin-addr (pml4-table-base-addr x86)) x86))
        ;;  1)
        (equal
         (page-size
          (rm-low-64 (pml4-table-entry-addr lin-addr (pml4-table-base-addr x86)) x86))
         0)
        ;; (equal
        ;;  (page-present
        ;;   (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr (page-dir-ptr-table-base-addr lin-addr x86)) x86))
        ;;  1)
        (equal
         (page-size
          (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr (page-dir-ptr-table-base-addr lin-addr x86)) x86))
         0)
        ;; (equal
        ;;  (page-present
        ;;   (rm-low-64 (page-directory-entry-addr lin-addr (page-directory-base-addr lin-addr x86)) x86))
        ;;  1)
        (equal
         (page-size
          (rm-low-64 (page-directory-entry-addr lin-addr (page-directory-base-addr lin-addr x86)) x86))
         0)
        (canonical-address-p lin-addr))
   (subset-p
    (xlation-governing-entries-paddrs-for-page-table
     lin-addr base-addr x86)
    (open-qword-paddr-list (gather-all-paging-structure-qword-addresses x86))))
  :hints (("Goal"
           :in-theory (e/d* (xlation-governing-entries-paddrs-for-page-table)
                            ()))))

(defthm xlation-governing-entries-paddrs-for-page-directory-subset-of-paging-structures
  (implies
   (and (equal base-addr (page-directory-base-addr lin-addr x86))
        ;; The following hyps are not needed when an
        ;; over-approximation of paging addresses is collected
        ;; instead.
        ;; (equal
        ;;  (page-present
        ;;   (rm-low-64 (pml4-table-entry-addr lin-addr (pml4-table-base-addr x86)) x86))
        ;;  1)
        (equal
         (page-size
          (rm-low-64 (pml4-table-entry-addr lin-addr (pml4-table-base-addr x86)) x86))
         0)
        ;; (equal
        ;;  (page-present
        ;;   (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr (page-dir-ptr-table-base-addr lin-addr x86)) x86))
        ;;  1)
        (equal
         (page-size
          (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr (page-dir-ptr-table-base-addr lin-addr x86)) x86))
         0)
        ;; (equal
        ;;  (page-present
        ;;   (rm-low-64 (page-directory-entry-addr lin-addr (page-directory-base-addr lin-addr x86)) x86))
        ;;  1)
        (canonical-address-p lin-addr))
   (subset-p
    (xlation-governing-entries-paddrs-for-page-directory
     lin-addr base-addr x86)
    (open-qword-paddr-list (gather-all-paging-structure-qword-addresses x86))))
  :hints (("Goal" :in-theory (e/d* (subset-p
                                    xlation-governing-entries-paddrs-for-page-directory)
                                   (xlation-governing-entries-paddrs-for-page-table)))))

(defthm xlation-governing-entries-paddrs-for-page-dir-ptr-table-subset-of-paging-structures
  (implies (and (equal base-addr (page-dir-ptr-table-base-addr lin-addr x86))
                ;; The following hyps are not needed when an
                ;; over-approximation of paging addresses is collected
                ;; instead.
                ;; (equal
                ;;  (page-present
                ;;   (rm-low-64 (pml4-table-entry-addr lin-addr (pml4-table-base-addr x86)) x86))
                ;;  1)
                (equal
                 (page-size
                  (rm-low-64 (pml4-table-entry-addr lin-addr (pml4-table-base-addr x86)) x86))
                 0)
                ;; (equal
                ;;  (page-present
                ;;   (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr (page-dir-ptr-table-base-addr lin-addr x86)) x86))
                ;;  1)
                (canonical-address-p lin-addr))
           (subset-p
            (xlation-governing-entries-paddrs-for-page-dir-ptr-table
             lin-addr base-addr x86)
            (open-qword-paddr-list (gather-all-paging-structure-qword-addresses x86))))
  :hints (("Goal"
           :cases ((equal
                    (page-size
                     (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr (page-dir-ptr-table-base-addr lin-addr x86)) x86))
                    1))
           :in-theory (e/d* (subset-p
                             xlation-governing-entries-paddrs-for-page-dir-ptr-table)
                            ()))))

(defthm xlation-governing-entries-paddrs-for-pml4-table-subset-of-paging-structures
  (implies (and (equal base-addr (pml4-table-base-addr x86))
                (canonical-address-p lin-addr))
           (subset-p
            (xlation-governing-entries-paddrs-for-pml4-table
             lin-addr base-addr x86)
            (open-qword-paddr-list (gather-all-paging-structure-qword-addresses x86))))
  :hints (("Goal" :in-theory (e/d* (subset-p
                                    xlation-governing-entries-paddrs-for-pml4-table)
                                   ()))))

(defthm xlation-governing-entries-paddrs-subset-of-paging-structures
  (implies (canonical-address-p lin-addr)
           (subset-p
            (xlation-governing-entries-paddrs lin-addr x86)
            (open-qword-paddr-list
             (gather-all-paging-structure-qword-addresses x86))))
  :hints (("Goal"
           :in-theory (e/d* (xlation-governing-entries-paddrs
                             subset-p)
                            (canonical-address-p)))))

(defthm all-xlation-governing-entries-paddrs-subset-of-paging-structures
  (implies (canonical-address-listp l-addrs)
           (subset-p
            (all-xlation-governing-entries-paddrs l-addrs x86)
            (open-qword-paddr-list
             (gather-all-paging-structure-qword-addresses x86))))
  :hints (("Goal" :in-theory (e/d* (all-xlation-governing-entries-paddrs
                                    subset-p)
                                   (canonical-address-p)))))

;; ======================================================================

;; Proof of xlation-governing-entries-paddrs-and-mv-nth-1-wb-disjoint-p
;; and all-xlation-governing-entries-paddrs-and-mv-nth-1-wb-disjoint.

(defthm xlation-governing-entries-paddrs-for-page-table-and-write-to-physical-memory
  (equal (xlation-governing-entries-paddrs-for-page-table
          lin-addr page-table-base-addr
          (write-to-physical-memory p-addrs bytes x86))
         (xlation-governing-entries-paddrs-for-page-table
          lin-addr page-table-base-addr (double-rewrite x86)))
  :hints (("Goal" :in-theory (e/d* (xlation-governing-entries-paddrs-for-page-table)
                                   ()))))

(defthm xlation-governing-entries-paddrs-for-page-table-and-mv-nth-1-wb
  (equal (xlation-governing-entries-paddrs-for-page-table
          lin-addr page-table-base-addr
          (mv-nth 1 (wb addr-lst w x86)))
         (xlation-governing-entries-paddrs-for-page-table
          lin-addr page-table-base-addr (double-rewrite x86)))
  :hints (("Goal" :in-theory (e/d* (wb
                                    xlation-governing-entries-paddrs-for-page-table)
                                   ()))))

(defthm xlation-governing-entries-paddrs-for-page-directory-and-write-to-physical-memory-disjoint-p
  (implies (disjoint-p p-addrs
                       (xlation-governing-entries-paddrs-for-page-directory
                        lin-addr page-directory-base-addr (double-rewrite x86)))
           (equal (xlation-governing-entries-paddrs-for-page-directory
                   lin-addr page-directory-base-addr
                   (write-to-physical-memory p-addrs bytes x86))
                  (xlation-governing-entries-paddrs-for-page-directory
                   lin-addr page-directory-base-addr (double-rewrite x86))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (disjoint-p
                             disjoint-p-commutative
                             xlation-governing-entries-paddrs-for-page-directory)
                            ()))))

(defthm xlation-governing-entries-paddrs-for-page-directory-and-mv-nth-1-wb-disjoint-p
  (implies (and
            (disjoint-p
             (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w (cpl x86) (double-rewrite x86)))
             (xlation-governing-entries-paddrs-for-page-directory
              lin-addr page-directory-base-addr (double-rewrite x86)))
            (not (programmer-level-mode x86)))
           (equal (xlation-governing-entries-paddrs-for-page-directory
                   lin-addr page-directory-base-addr
                   (mv-nth 1 (wb addr-lst w x86)))
                  (xlation-governing-entries-paddrs-for-page-directory
                   lin-addr page-directory-base-addr (double-rewrite x86))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance xlate-equiv-entries-and-page-size
                            (e-1 (rm-low-64 (page-directory-entry-addr lin-addr page-directory-base-addr)
                                            x86))
                            (e-2 (rm-low-64 (page-directory-entry-addr lin-addr page-directory-base-addr)
                                            (mv-nth 2 (las-to-pas (strip-cars addr-lst) :w (cpl x86) x86))))))
           :in-theory (e/d* (disjoint-p
                             disjoint-p-commutative
                             wb
                             xlation-governing-entries-paddrs-for-page-directory)
                            ()))))

(defthm xlation-governing-entries-paddrs-for-page-dir-ptr-table-and-write-to-physical-memory-disjoint-p
  (implies (disjoint-p p-addrs
                       (xlation-governing-entries-paddrs-for-page-dir-ptr-table
                        lin-addr page-dir-ptr-table-base-addr (double-rewrite x86)))
           (equal (xlation-governing-entries-paddrs-for-page-dir-ptr-table
                   lin-addr page-dir-ptr-table-base-addr
                   (write-to-physical-memory p-addrs bytes x86))
                  (xlation-governing-entries-paddrs-for-page-dir-ptr-table
                   lin-addr page-dir-ptr-table-base-addr (double-rewrite x86))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (disjoint-p
                             disjoint-p-commutative
                             xlation-governing-entries-paddrs-for-page-dir-ptr-table)
                            ()))))

(defthm xlation-governing-entries-paddrs-for-page-dir-ptr-table-and-mv-nth-1-wb-disjoint-p
  (implies (and (disjoint-p
                 (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w (cpl x86)
                                       (double-rewrite x86)))
                 (xlation-governing-entries-paddrs-for-page-dir-ptr-table
                  lin-addr page-dir-ptr-table-base-addr (double-rewrite x86)))
                (not (programmer-level-mode x86)))
           (equal (xlation-governing-entries-paddrs-for-page-dir-ptr-table
                   lin-addr page-dir-ptr-table-base-addr
                   (mv-nth 1 (wb addr-lst w x86)))
                  (xlation-governing-entries-paddrs-for-page-dir-ptr-table
                   lin-addr page-dir-ptr-table-base-addr (double-rewrite x86))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance xlate-equiv-entries-and-page-size
                            (e-1 (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr page-dir-ptr-table-base-addr)
                                            x86))
                            (e-2 (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr page-dir-ptr-table-base-addr)
                                            (mv-nth 2 (las-to-pas (strip-cars addr-lst) :w (cpl x86) x86))))))
           :in-theory (e/d* (disjoint-p
                             disjoint-p-commutative
                             wb
                             xlation-governing-entries-paddrs-for-page-dir-ptr-table)
                            ()))))

(defthm xlation-governing-entries-paddrs-for-pml4-table-and-write-to-physical-memory-disjoint-p
  (implies (disjoint-p p-addrs
                       (xlation-governing-entries-paddrs-for-pml4-table
                        lin-addr pml4-table-base-addr (double-rewrite x86)))
           (equal (xlation-governing-entries-paddrs-for-pml4-table
                   lin-addr pml4-table-base-addr
                   (write-to-physical-memory p-addrs bytes x86))
                  (xlation-governing-entries-paddrs-for-pml4-table
                   lin-addr pml4-table-base-addr (double-rewrite x86))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (disjoint-p
                             disjoint-p-commutative
                             xlation-governing-entries-paddrs-for-pml4-table)
                            ()))))

(defthm xlation-governing-entries-paddrs-for-pml4-table-and-mv-nth-1-wb-disjoint-p
  (implies (and (disjoint-p
                 (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w (cpl x86)
                                       (double-rewrite x86)))
                 (xlation-governing-entries-paddrs-for-pml4-table
                  lin-addr pml4-table-base-addr (double-rewrite x86)))
                (not (programmer-level-mode x86)))
           (equal (xlation-governing-entries-paddrs-for-pml4-table
                   lin-addr pml4-table-base-addr
                   (mv-nth 1 (wb addr-lst w x86)))
                  (xlation-governing-entries-paddrs-for-pml4-table
                   lin-addr pml4-table-base-addr (double-rewrite x86))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance xlate-equiv-structures-and-xlate-equiv-entries
                            (index (pml4-table-entry-addr lin-addr pml4-table-base-addr))
                            (x86-1 x86)
                            (x86-2 (mv-nth 2 (las-to-pas (strip-cars addr-lst) :w (cpl x86) x86))))
                 (:instance xlate-equiv-entries-and-page-size
                            (e-1 (rm-low-64 (pml4-table-entry-addr lin-addr pml4-table-base-addr) x86))
                            (e-2 (rm-low-64 (pml4-table-entry-addr lin-addr pml4-table-base-addr)
                                            (mv-nth 2 (las-to-pas (strip-cars addr-lst) :w (cpl x86) x86))))))
           :in-theory (e/d* (disjoint-p
                             disjoint-p-commutative
                             wb
                             xlation-governing-entries-paddrs-for-pml4-table)
                            (force (force))))))

(defthm xlation-governing-entries-paddrs-and-write-to-physical-memory-disjoint-p
  (implies (disjoint-p p-addrs
                       (xlation-governing-entries-paddrs lin-addr (double-rewrite x86)))
           (equal (xlation-governing-entries-paddrs
                   lin-addr (write-to-physical-memory p-addrs bytes x86))
                  (xlation-governing-entries-paddrs lin-addr (double-rewrite x86))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (disjoint-p xlation-governing-entries-paddrs) ()))))

(defthm xlation-governing-entries-paddrs-and-mv-nth-1-wb-disjoint-p
  (implies (and
            (disjoint-p (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w (cpl x86)
                                              (double-rewrite x86)))
                        (xlation-governing-entries-paddrs lin-addr (double-rewrite x86)))
            (not (programmer-level-mode x86)))
           (equal (xlation-governing-entries-paddrs lin-addr (mv-nth 1 (wb addr-lst w x86)))
                  (xlation-governing-entries-paddrs lin-addr (double-rewrite x86))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (disjoint-p
                             disjoint-p-commutative
                             xlation-governing-entries-paddrs)
                            (wb)))))

(defthm all-xlation-governing-entries-paddrs-and-write-to-physical-memory-disjoint-p
  (implies (and
            (disjoint-p p-addrs
                        (all-xlation-governing-entries-paddrs l-addrs (double-rewrite x86)))
            (physical-address-listp p-addrs))
           (equal (all-xlation-governing-entries-paddrs
                   l-addrs (write-to-physical-memory p-addrs bytes x86))
                  (all-xlation-governing-entries-paddrs l-addrs (double-rewrite x86))))
  :hints (("Goal"
           :in-theory (e/d* (disjoint-p
                             disjoint-p-commutative
                             all-xlation-governing-entries-paddrs)
                            ()))))

(defthm all-xlation-governing-entries-paddrs-and-mv-nth-1-wb-disjoint
  (implies (and
            (disjoint-p (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w (cpl x86) (double-rewrite x86)))
                        (all-xlation-governing-entries-paddrs l-addrs (double-rewrite x86)))
            (not (programmer-level-mode x86)))
           (equal (all-xlation-governing-entries-paddrs l-addrs (mv-nth 1 (wb addr-lst w x86)))
                  (all-xlation-governing-entries-paddrs l-addrs (double-rewrite x86))))
  :hints (("Goal"
           :in-theory (e/d* (all-xlation-governing-entries-paddrs)
                            (xlation-governing-entries-paddrs
                             disjointness-of-all-xlation-governing-entries-paddrs-from-all-xlation-governing-entries-paddrs-subset-p
                             wb))
           :induct (all-xlation-governing-entries-paddrs l-addrs x86))))

;; ======================================================================

;; Lemmas relating ia32e-la-to-pa and las-to-pas:

(defthm mv-nth-0-ia32e-la-to-pa-member-of-mv-nth-1-las-to-pas-if-lin-addr-member-p
  (implies (and (bind-free (find-l-addrs-from-las-to-pas 'l-addrs mfc state)
                           (l-addrs))
                (member-p lin-addr l-addrs)
                (not (mv-nth 0 (las-to-pas l-addrs r-w-x cpl x86))))
           (equal (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x cpl x86)) nil))
  :hints (("Goal" :in-theory (e/d* (member-p) ()))))

(defthm mv-nth-1-ia32e-la-to-pa-member-of-mv-nth-1-las-to-pas-if-lin-addr-member-p
  (implies (and (member-p lin-addr l-addrs)
                (not (mv-nth 0 (las-to-pas l-addrs r-w-x cpl x86))))
           (member-p (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x cpl x86))
                     (mv-nth 1 (las-to-pas     l-addrs r-w-x cpl x86))))
  :hints (("Goal" :in-theory (e/d* (member-p) ()))))

(defthmd open-mv-nth-0-las-to-pas
  (implies (and (canonical-address-p lin-addr)
                (not (zp n)))
           (equal (mv-nth 0 (las-to-pas (create-canonical-address-list n lin-addr) r-w-x cpl x86))
                  (if (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x cpl x86))
                      (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x cpl x86))
                    (mv-nth 0 (las-to-pas (create-canonical-address-list (+ -1 n) (+ 1 lin-addr))
                                          r-w-x cpl x86))))))

(defthmd open-mv-nth-1-las-to-pas
  (implies (and (canonical-address-p lin-addr)
                (not (zp n))
                (not (mv-nth 0 (las-to-pas (create-canonical-address-list n lin-addr) r-w-x cpl x86))))
           (equal (mv-nth 1 (las-to-pas (create-canonical-address-list n lin-addr) r-w-x cpl x86))
                  (cons (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x cpl x86))
                        (mv-nth 1 (las-to-pas (create-canonical-address-list (+ -1 n) (+ 1 lin-addr))
                                              r-w-x cpl x86))))))

;; ======================================================================

;; Commuting physical memory writes with page table traversals:

(encapsulate
  ()

  ;; This is an odd book --- it characterizes the effects of a page walk
  ;; in terms of EQUAL instead of XLATE-EQUIV-MEMORY, which is an
  ;; aberration for this library.  However, this characterization is
  ;; useful in proving theorems like
  ;; xw-mem-and-ia32e-la-to-pa-page-table-commute.  We include this book
  ;; locally so that EQUAL doesn't pollute our canonical forms that rely
  ;; on XLATE-EQUIV-MEMORY.
  (local (include-book "page-walk-side-effects"))

  (defthm xw-mem-and-ia32e-la-to-pa-page-table-commute
    (implies (and
              (disjoint-p
               (list index)
               (xlation-governing-entries-paddrs-for-page-table lin-addr base-addr (double-rewrite x86)))
              (canonical-address-p lin-addr)
              (physical-address-p base-addr)
              (equal (loghead 12 base-addr) 0)
              (x86p x86) (integerp index) (unsigned-byte-p 8 value))
             (equal (xw :mem index value (mv-nth 2 (ia32e-la-to-pa-page-table
                                                    lin-addr
                                                    base-addr u/s-acc r/w-acc x/d-acc
                                                    wp smep smap ac nxe r-w-x cpl x86)))
                    (mv-nth 2 (ia32e-la-to-pa-page-table
                               lin-addr
                               base-addr u/s-acc r/w-acc x/d-acc
                               wp smep smap ac nxe r-w-x cpl
                               (xw :mem index value x86)))))
    :hints (("Goal" :in-theory (e/d* ()
                                     (bitops::logand-with-negated-bitmask)))))


  (defthm xw-mem-and-ia32e-la-to-pa-page-directory-commute
    (implies (and
              (disjoint-p
               (list index)
               (xlation-governing-entries-paddrs-for-page-directory lin-addr base-addr (double-rewrite x86)))
              (canonical-address-p lin-addr)
              (physical-address-p base-addr)
              (equal (loghead 12 base-addr) 0)
              (x86p x86) (integerp index) (unsigned-byte-p 8 value))
             (equal (xw :mem index value
                        (mv-nth 2 (ia32e-la-to-pa-page-directory
                                   lin-addr
                                   base-addr u/s-acc r/w-acc x/d-acc
                                   wp smep smap ac nxe r-w-x cpl x86)))
                    (mv-nth 2 (ia32e-la-to-pa-page-directory
                               lin-addr
                               base-addr u/s-acc r/w-acc x/d-acc
                               wp smep smap ac nxe r-w-x cpl
                               (xw :mem index value x86)))))
    :hints (("Goal"
             :in-theory (e/d* ()
                              (bitops::logand-with-negated-bitmask
                               |(xw :mem addr1 (wm-low-64 addr2 val x86)) --- disjoint addr|)))))

  (defthm xw-mem-and-ia32e-la-to-pa-page-dir-ptr-table-commute
    (implies (and
              (disjoint-p
               (list index)
               (xlation-governing-entries-paddrs-for-page-dir-ptr-table lin-addr base-addr (double-rewrite x86)))
              (canonical-address-p lin-addr)
              (physical-address-p base-addr)
              (equal (loghead 12 base-addr) 0)
              (x86p x86) (integerp index) (unsigned-byte-p 8 value))
             (equal (xw :mem index value (mv-nth 2 (ia32e-la-to-pa-page-dir-ptr-table
                                                    lin-addr
                                                    base-addr u/s-acc r/w-acc x/d-acc
                                                    wp smep smap ac nxe r-w-x cpl x86)))
                    (mv-nth 2 (ia32e-la-to-pa-page-dir-ptr-table
                               lin-addr
                               base-addr u/s-acc r/w-acc x/d-acc
                               wp smep smap ac nxe r-w-x cpl
                               (xw :mem index value x86)))))
    :hints (("Goal" :in-theory (e/d* ()
                                     (|(xw :mem addr1 (wm-low-64 addr2 val x86)) --- disjoint addr|
                                      bitops::logand-with-negated-bitmask)))))

  (defthm xw-mem-and-ia32e-la-to-pa-pml4-table-commute
    (implies (and
              (disjoint-p
               (list index)
               (xlation-governing-entries-paddrs-for-pml4-table lin-addr base-addr (double-rewrite x86)))
              (canonical-address-p lin-addr)
              (physical-address-p base-addr)
              (equal (loghead 12 base-addr) 0)
              (x86p x86) (integerp index) (unsigned-byte-p 8 value))
             (equal (xw :mem index value (mv-nth 2 (ia32e-la-to-pa-pml4-table
                                                    lin-addr base-addr
                                                    wp smep smap ac nxe r-w-x cpl x86)))
                    (mv-nth 2 (ia32e-la-to-pa-pml4-table
                               lin-addr base-addr
                               wp smep smap ac nxe r-w-x cpl
                               (xw :mem index value x86)))))
    :hints (("Goal" :in-theory (e/d* ()
                                     (|(xw :mem addr1 (wm-low-64 addr2 val x86)) --- disjoint addr|
                                      bitops::logand-with-negated-bitmask)))))

  (defthm xw-mem-and-ia32e-la-to-pa-commute
    (implies (and (disjoint-p
                   (list index)
                   (xlation-governing-entries-paddrs lin-addr (double-rewrite x86)))
                  (canonical-address-p lin-addr)
                  (x86p x86) (integerp index) (unsigned-byte-p 8 value))
             (equal (xw :mem index value
                        (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x cpl x86)))
                    (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x cpl
                                              (xw :mem index value x86))))))

  (defthm xw-mem-and-las-to-pas-commute
    (implies
     (and (disjoint-p (list index)
                      (all-xlation-governing-entries-paddrs
                       l-addrs (double-rewrite x86)))
          (not (mv-nth 0 (las-to-pas l-addrs r-w-x cpl (double-rewrite x86))))
          (canonical-address-listp l-addrs)
          (x86p x86) (integerp index) (unsigned-byte-p 8 value))
     (equal (xw :mem index value (mv-nth 2 (las-to-pas l-addrs r-w-x cpl x86)))
            (mv-nth 2 (las-to-pas l-addrs r-w-x cpl (xw :mem index value x86)))))
    :hints
    (("Goal"
      :expand ((las-to-pas l-addrs r-w-x cpl (xw :mem index value x86)))
      :in-theory (e/d* (disjoint-p
                        las-to-pas
                        member-p
                        all-xlation-governing-entries-paddrs)
                       ()))))

  ) ;; End of encapsulate

(defthm write-to-physical-memory-and-mv-nth-2-ia32e-la-to-pa-commute
  (implies (and (disjoint-p
                 p-addrs
                 (xlation-governing-entries-paddrs lin-addr (double-rewrite x86)))
                (canonical-address-p lin-addr)
                (physical-address-listp p-addrs)
                (byte-listp bytes)
                (equal (len bytes) (len p-addrs))
                (x86p x86))
           (equal (write-to-physical-memory
                   p-addrs bytes (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x cpl x86)))
                  (mv-nth 2 (ia32e-la-to-pa
                             lin-addr r-w-x cpl
                             (write-to-physical-memory p-addrs bytes x86)))))
  :hints (("Goal"
           :induct (write-to-physical-memory p-addrs bytes x86)
           :in-theory (e/d* (disjoint-p) ()))))

(defthm write-to-physical-memory-and-mv-nth-2-las-to-pas-commute
  (implies
   (and (disjoint-p p-addrs
                    (all-xlation-governing-entries-paddrs
                     l-addrs (double-rewrite x86)))
        (canonical-address-listp l-addrs)
        (physical-address-listp p-addrs)
        (byte-listp bytes)
        (equal (len bytes) (len p-addrs))
        (x86p x86))
   (equal
    (write-to-physical-memory p-addrs bytes (mv-nth 2 (las-to-pas l-addrs r-w-x cpl x86)))
    (mv-nth 2 (las-to-pas l-addrs r-w-x cpl (write-to-physical-memory p-addrs bytes x86)))))
  :hints
  (("Goal" :induct (cons (las-to-pas l-addrs r-w-x cpl x86)
                         (write-to-physical-memory p-addrs bytes x86))
    :in-theory (e/d* (disjoint-p las-to-pas all-xlation-governing-entries-paddrs) ()))))

;; ======================================================================

;; Misc. lemmas about las-to-pas that need some congruence-based
;; reasoning to be proved:

(defthm cdr-mv-nth-1-las-to-pas
  (implies (not (mv-nth 0 (ia32e-la-to-pa (car l-addrs) r-w-x cpl x86)))
           (equal (cdr (mv-nth 1 (las-to-pas l-addrs r-w-x cpl x86)))
                  (mv-nth 1 (las-to-pas (cdr l-addrs) r-w-x cpl x86)))))

(defthm las-to-pas-values-and-xw-mem-not-member
  (implies (and
            (not
             (member-p
              index
              (all-xlation-governing-entries-paddrs l-addrs (double-rewrite x86))))
            (canonical-address-listp l-addrs)
            (x86p x86)
            (integerp index)
            (unsigned-byte-p 8 byte))
           (and (equal (mv-nth 0 (las-to-pas l-addrs r-w-x cpl
                                             (xw :mem index byte x86)))
                       (mv-nth 0 (las-to-pas l-addrs r-w-x cpl x86)))
                (equal (mv-nth 1 (las-to-pas l-addrs r-w-x cpl
                                             (xw :mem index byte x86)))
                       (mv-nth 1 (las-to-pas l-addrs r-w-x cpl x86)))))
  :hints (("Goal"
           :in-theory (e/d* (open-mv-nth-0-las-to-pas
                             open-mv-nth-1-las-to-pas
                             disjoint-p
                             member-p)
                            (xlation-governing-entries-paddrs)))))

(defthm mv-nth-1-las-to-pas-subset-p
  (implies (and (subset-p l-addrs-subset l-addrs)
                (not (mv-nth 0 (las-to-pas l-addrs r-w-x cpl x86))))
           (subset-p (mv-nth 1 (las-to-pas l-addrs-subset r-w-x cpl x86))
                     (mv-nth 1 (las-to-pas l-addrs r-w-x cpl x86))))
  :hints (("Goal" :in-theory (e/d* (subset-p) ()))))

;; ======================================================================

;; Lemmas to aid in inferring disjointness of las-to-pas and
;; translation-governing addresses:

(defun get-subterms-if-match (n match-fn terms)
  (declare (xargs :guard (and (natp n)
                              (symbolp match-fn)
                              (pseudo-term-listp terms))))
  ;; E.g.:
  ;; (get-subterms-if-match
  ;;  1
  ;;  'create-canonical-address-list
  ;;  '((all-xlation-governing-entries-paddrs
  ;;     (create-canonical-address-list cnt start-rip)
  ;;     p-addrs)
  ;;    (all-xlation-governing-entries-paddrs
  ;;     (cons 'start-rip nil)
  ;;     p-addrs)))
  (if (atom terms)
      nil
    (let ((term (nth n (acl2::list-fix (car terms)))))
      (if (and (consp term)
               (eq (car term) match-fn))
          (cons term (get-subterms-if-match n match-fn (cdr terms)))
        (get-subterms-if-match n match-fn (cdr terms))))))

(defun find-l-addrs-like-create-canonical-address-list-from-fn
  (fn l-addrs-var mfc state)
  (declare (xargs :stobjs (state) :mode :program)
           (ignorable state))
  (b* ((calls (acl2::find-calls-lst fn (acl2::mfc-clause mfc)))
       ((when (not calls)) nil)
       (l-addrs (get-subterms-if-match 1 'create-canonical-address-list calls))
       (alst-lst
        (make-bind-free-alist-lists l-addrs-var l-addrs)))
    alst-lst))

(defthmd mv-nth-0-las-to-pas-subset-p
  ;; This is a pretty expensive rule --- a more general version of
  ;;  mv-nth-0-las-to-pas-subset-p-with-l-addrs-from-bind-free.
  (implies (and (bind-free
                 (find-l-addrs-from-fn 'las-to-pas 'l-addrs mfc state)
                 (l-addrs))
                (syntaxp (not (eq l-addrs-subset l-addrs)))
                (subset-p l-addrs-subset l-addrs)
                (not (mv-nth 0 (las-to-pas l-addrs r-w-x cpl (double-rewrite x86)))))
           (equal (mv-nth 0 (las-to-pas l-addrs-subset r-w-x cpl x86))
                  nil))
  :hints (("Goal" :in-theory (e/d* (subset-p) ()))))

(defun find-l-addrs-from-program-at-or-program-at-alt-term (thm l-addrs-var mfc state)
  (declare (xargs :stobjs (state) :mode :program)
           (ignorable thm state))
  (b* ((call (acl2::find-call-lst 'program-at (acl2::mfc-clause mfc)))
       (call (if (not call)
                 (acl2::find-call-lst 'program-at-alt (acl2::mfc-clause mfc))
               call))
       ((when (not call))
        ;; (cw "~%~p0: Program-At and Program-At-Alt term not encountered.~%" thm)
        nil)
       (addresses (cadr call)))
    `((,l-addrs-var . ,addresses))))

(defthm mv-nth-0-las-to-pas-subset-p-with-l-addrs-from-bind-free
  ;; This rule is tailored to rewrite (mv-nth 0 (las-to-pas
  ;; l-addrs-subset r-w-x cpl x86)) to nil, given that l-addrs-subset
  ;; is a subset of l-addrs, which are the program addresses. Thus, it
  ;; helps in proving that the translation of an instruction doesn't
  ;; yield an error, given that the entire program's translation
  ;; doesn't yield an error.
  (implies (and (bind-free
                 (find-l-addrs-from-program-at-or-program-at-alt-term
                  'mv-nth-0-las-to-pas-subset-p-with-l-addrs-from-bind-free
                  'l-addrs mfc state)
                 (l-addrs))
                (syntaxp (not (eq l-addrs-subset l-addrs)))
                (not (mv-nth 0 (las-to-pas l-addrs r-w-x cpl (double-rewrite x86))))
                (subset-p l-addrs-subset l-addrs))
           (equal (mv-nth 0 (las-to-pas l-addrs-subset r-w-x cpl x86))
                  nil))
  :hints (("Goal" :in-theory (e/d* (subset-p) ()))))

(defthm mv-nth-1-las-to-pas-subset-p-disjoint-from-other-p-addrs
  ;; This rule is tailored to rewrite
  ;; (disjoint-p (mv-nth 1 (las-to-pas l-addrs-subset r-w-x cpl x86))
  ;;             other-p-addrs)
  ;; to t, given that l-addrs-subset is a subset of l-addrs, which are
  ;; taken from a program-at/program-at-alt term.

  ;; Disjointness of l-addrs with other addresses should be expressed
  ;; in terms of disjoint-p$.
  (implies
   (and
    ;; (bind-free
    ;;  (find-l-addrs-from-fn 'las-to-pas 'l-addrs mfc state)
    ;;  (l-addrs))
    (bind-free
     (find-l-addrs-from-program-at-or-program-at-alt-term
      'mv-nth-0-las-to-pas-subset-p-with-l-addrs-from-bind-free
      'l-addrs mfc state)
     (l-addrs))
    (syntaxp (not (eq l-addrs-subset l-addrs)))
    ;; Note: This is in terms of disjoint-p$.
    (disjoint-p$ (mv-nth 1 (las-to-pas l-addrs r-w-x cpl (double-rewrite x86)))
                 other-p-addrs)
    (subset-p l-addrs-subset l-addrs)
    (not (mv-nth 0 (las-to-pas l-addrs r-w-x cpl (double-rewrite x86)))))
   (disjoint-p (mv-nth 1 (las-to-pas l-addrs-subset r-w-x cpl x86))
               other-p-addrs))
  :hints
  (("Goal"
    :in-theory (e/d* (disjoint-p disjoint-p$ subset-p member-p las-to-pas)
                     (mv-nth-1-ia32e-la-to-pa-member-of-mv-nth-1-las-to-pas-if-lin-addr-member-p)))
   ("Subgoal *1/6"
    :in-theory (e/d* (disjoint-p subset-p member-p las-to-pas)
                     (mv-nth-1-ia32e-la-to-pa-member-of-mv-nth-1-las-to-pas-if-lin-addr-member-p))
    :use ((:instance mv-nth-1-ia32e-la-to-pa-member-of-mv-nth-1-las-to-pas-if-lin-addr-member-p
                     (lin-addr (car l-addrs-subset))
                     (l-addrs l-addrs))))))

(defthm disjoint-p-las-to-pas-subset-p-and-all-xlation-governing-entries-paddrs-subsets
  ;; Very similar to
  ;; mv-nth-1-las-to-pas-subset-p-disjoint-from-other-p-addrs (but
  ;; less general because it applies only during instruction fetches
  ;; and hence, it is less expensive).
  (implies
   (and
    (syntaxp (not (eq l-addrs-1-subset l-addrs-2)))
    (bind-free (find-l-addrs-from-program-at-or-program-at-alt-term
                'disjoint-p-las-to-pas-subset-p-and-all-xlation-governing-entries-paddrs
                'l-addrs-1 mfc state)
               (l-addrs-1))
    (disjoint-p$
     (mv-nth 1 (las-to-pas l-addrs-1 :x cpl (double-rewrite x86)))
     (all-xlation-governing-entries-paddrs l-addrs-2 (double-rewrite x86)))
    (subset-p l-addrs-1-subset l-addrs-1)
    (not (mv-nth 0 (las-to-pas l-addrs-1 :x cpl (double-rewrite x86)))))
   (disjoint-p (mv-nth 1 (las-to-pas l-addrs-1-subset :x cpl x86))
               (all-xlation-governing-entries-paddrs l-addrs-2 x86)))
  :hints (("Goal" :in-theory (e/d* () (mv-nth-1-las-to-pas-subset-p-disjoint-from-other-p-addrs))
           :use ((:instance mv-nth-1-las-to-pas-subset-p-disjoint-from-other-p-addrs
                            (other-p-addrs (all-xlation-governing-entries-paddrs l-addrs-2 x86))
                            (r-w-x :x)
                            (l-addrs l-addrs-1)
                            (l-addrs-subset l-addrs-1-subset))))))

(defthm mv-nth-1-las-to-pas-subset-p-disjoint-from-other-p-addrs-alt
  ;; This rule is tailored to rewrite terms of the form to t

  ;; (disjoint-p other-p-addrs (mv-nth 1 (las-to-pas l-addrs-subset r-w-x cpl x86)))

  ;; where l-addrs-subset is a subset of l-addrs, and l-addrs is of
  ;; the form (create-canonical-address-list ...).

  ;; Disjointness of l-addrs with other addresses should be expressed
  ;; in terms of disjoint-p$.
  (implies
   (and
    (bind-free (find-l-addrs-like-create-canonical-address-list-from-fn
                'las-to-pas 'l-addrs mfc state)
               (l-addrs))
    (syntaxp (not (eq l-addrs-subset l-addrs)))
    (disjoint-p$ other-p-addrs
                 (mv-nth 1 (las-to-pas l-addrs r-w-x cpl (double-rewrite x86))))
    (subset-p l-addrs-subset l-addrs)
    (not (mv-nth 0 (las-to-pas l-addrs r-w-x cpl (double-rewrite x86)))))
   (disjoint-p other-p-addrs (mv-nth 1 (las-to-pas l-addrs-subset r-w-x cpl x86))))
  :hints (("Goal"
           :use ((:instance mv-nth-1-las-to-pas-subset-p-disjoint-from-other-p-addrs))
           :in-theory (e/d* (disjoint-p-commutative disjoint-p$)
                            (mv-nth-1-las-to-pas-subset-p-disjoint-from-other-p-addrs)))))

(defthm disjoint-p-all-xlation-governing-entries-paddrs-subset-p
  ;; This rule is tailored to rewrite terms of the form to t

  ;; (disjoint-p other-p-addrs (all-xlation-governing-entries-paddrs l-addrs-subset x86))

  ;; where l-addrs-subset is a subset of l-addrs, and l-addrs is of
  ;; the form (create-canonical-address-list ...).

  ;; Disjointness of l-addrs with other addresses should be expressed
  ;; in terms of disjoint-p$.
  (implies (and (bind-free (find-l-addrs-like-create-canonical-address-list-from-fn
                            'all-xlation-governing-entries-paddrs 'l-addrs mfc state)
                           (l-addrs))
                ;; (syntaxp (not (cw "~% l-addrs: ~x0~%" l-addrs)))
                (disjoint-p$ other-p-addrs
                             (all-xlation-governing-entries-paddrs l-addrs (double-rewrite x86)))
                (subset-p l-addrs-subset l-addrs))
           (disjoint-p other-p-addrs (all-xlation-governing-entries-paddrs l-addrs-subset x86)))
  :hints (("Goal" :in-theory (e/d* (subset-p
                                    member-p
                                    disjoint-p
                                    disjoint-p$
                                    all-xlation-governing-entries-paddrs)
                                   ()))))

(defun get-both-l-addrs
  (match-fn l-addrs-subset-1 l-addrs-subset-2 term-1 term-2)
  ;; (get-both-l-addrs
  ;;  'las-to-pas
  ;;  '(create-canonical-address-list 4 rgf)
  ;;  '(create-canonical-address-list 4 start-rip)
  ;;  '(mv-nth 1 (las-to-pas '(create-canonical-address-list 4 rgf) r-w-x cpl (double-rewrite x86)))
  ;;  '(mv-nth 1 (las-to-pas '(create-canonical-address-list 20 start-rip) r-w-x cpl (double-rewrite x86))))
  (if (and (consp term-1)
           (consp (cdr term-1))
           (consp (cddr term-1))
           (consp (caddr term-1))
           (consp term-2)
           (consp (cdr term-2))
           (consp (cddr term-2))
           (consp (caddr term-2)))
      (b* ((fn-1 (car (caddr term-1)))
           (fn-2 (car (caddr term-2)))
           ;; (- (cw "~%fn-1: ~x0 and fn-2: ~x1~%" fn-1 fn-2))
           ((when (or (not (equal fn-1 fn-2))
                      (and (equal fn-1 fn-2)
                           (not (equal fn-1 match-fn)))))
            ;; (cw "~%~x0 and ~x1 unequal or match-fn ~x2 not found.~%" fn-1 fn-2 match-fn)
            nil)
           (l-addrs-1 (second (caddr term-1)))
           (l-addrs-2 (second (caddr term-2)))
           ((when (and (equal `(quote ,l-addrs-subset-1) l-addrs-1)
                       (equal `(quote ,l-addrs-subset-2) l-addrs-2)))
            ;; (cw "~%l-addrs-subsets: ~x0 and ~x1~%~% l-addrs: ~x2 and ~x3~%~%"
            ;;     `(quote ,l-addrs-subset-1) `(quote ,l-addrs-subset-2) l-addrs-1 l-addrs-2)
            ;; (cw "~% equal-1 ~x0~%~% equal-2: ~x1~%~%"
            ;;     (equal `(quote ,l-addrs-subset-1) l-addrs-1)
            ;;     (equal `(quote ,l-addrs-subset-2) l-addrs-2))
            ;; Both l-addrs shouldn't be equal to their subsets,
            ;; though one of them can be.
            nil))
        `(((l-addrs-1 . ,l-addrs-1)
           (l-addrs-2 . ,l-addrs-2))))
    nil))

(defun find-both-l-addrs-from-disjoint-p$-of-las-to-pas-aux
  (l-addrs-subset-1 l-addrs-subset-2 calls)
  ;; The first alist below will be weeded out by
  ;; the syntaxp in the theorem.

  ;; (find-both-l-addrs-from-disjoint-p$-of-las-to-pas-aux
  ;;  '(create-canonical-address-list 4 rgf)
  ;;  '(create-canonical-address-list 4 start-rip)
  ;;  '((disjoint-p
  ;;     (mv-nth 1 (las-to-pas '(create-canonical-address-list 20 start-rip) r-w-x cpl x86))
  ;;     (mv-nth 1 (las-to-pas '(create-canonical-address-list 20 start-rip) r-w-x cpl x86)))
  ;;    (disjoint-p
  ;;     (mv-nth 1 (las-to-pas '(create-canonical-address-list 4 rgf) r-w-x cpl x86))
  ;;     (mv-nth 1 (las-to-pas '(create-canonical-address-list 20 start-rip) r-w-x cpl x86)))
  ;;    (disjoint-p (mv-nth 1 (las-to-pas a b c)) a)
  ;;    (disjoint-p b a)
  ;;    (disjoint-p (mv-nth 1 (las-to-pas 1 2 43)) (mv-nth 1 (las-to-pas 9 8 7)))))
  (if (endp calls)
      nil
    (append (get-both-l-addrs
             'las-to-pas l-addrs-subset-1 l-addrs-subset-2
             (second (car calls)) (third (car calls)))
            (find-both-l-addrs-from-disjoint-p$-of-las-to-pas-aux
             l-addrs-subset-1 l-addrs-subset-2
             (cdr calls)))))

(defun find-both-l-addrs-from-disjoint-p$-of-las-to-pas
  (l-addrs-subset-1 l-addrs-subset-2 mfc state)
  (declare (xargs :stobjs (state) :mode :program)
           (ignorable state))
  (b* ((calls (acl2::find-calls-lst 'disjoint-p$ (acl2::mfc-clause mfc)))
       ((when (not calls)) nil))
    (find-both-l-addrs-from-disjoint-p$-of-las-to-pas-aux
     l-addrs-subset-1 l-addrs-subset-2 calls)))

(defthm two-mv-nth-1-las-to-pas-subset-p-disjoint-from-las-to-pas
  ;; This rule is tailored to rewrite terms of the form to t

  ;; (disjoint-p
  ;;  (mv-nth 1 (las-to-pas l-addrs-subset-1 r-w-x-1 cpl-1 x86))
  ;;  (mv-nth 1 (las-to-pas l-addrs-subset-2 r-w-x-2 cpl-2 x86)))

  ;; where l-addrs-subset-1 is a subset of l-addrs-1, l-addrs-subset-2
  ;; is a subset of l-addrs-2, and l-addrs-1 and l-addrs-2 are of the
  ;; form (create-canonical-address-list ...).
  (implies
   (and
    ;; What if I remove this syntaxp so that I can also infer
    ;; (disjoint-p x y) from (disjoint-p$ x y)? I'll need to change
    ;; get-both-l-addrs... Will this rule be terribly expensive then?
    (syntaxp (not (equal l-addrs-subset-1 l-addrs-subset-2)))
    (bind-free (find-both-l-addrs-from-disjoint-p$-of-las-to-pas
                l-addrs-subset-1 l-addrs-subset-2 mfc state)
               (l-addrs-1 l-addrs-2))
    ;; (syntaxp (not (cw "~%~% !!! l-addrs-1: ~x0 ~% !!! l-addrs-2: ~x0~%~%" l-addrs-1 l-addrs-2)))
    (disjoint-p$
     (mv-nth 1 (las-to-pas l-addrs-1 r-w-x-1 cpl-1 (double-rewrite x86)))
     (mv-nth 1 (las-to-pas l-addrs-2 r-w-x-2 cpl-2 (double-rewrite x86))))
    (subset-p l-addrs-subset-1 l-addrs-1)
    (subset-p l-addrs-subset-2 l-addrs-2)
    (not (mv-nth 0 (las-to-pas l-addrs-1 r-w-x-1 cpl-1 x86)))
    (not (mv-nth 0 (las-to-pas l-addrs-2 r-w-x-2 cpl-2 x86))))
   (disjoint-p
    (mv-nth 1 (las-to-pas l-addrs-subset-1 r-w-x-1 cpl-1 x86))
    (mv-nth 1 (las-to-pas l-addrs-subset-2 r-w-x-2 cpl-2 x86))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance mv-nth-1-las-to-pas-subset-p
                            (l-addrs l-addrs-1)
                            (l-addrs-subset l-addrs-subset-1)
                            (r-w-x r-w-x-1)
                            (cpl cpl-1))
                 (:instance mv-nth-1-las-to-pas-subset-p
                            (l-addrs l-addrs-2)
                            (l-addrs-subset l-addrs-subset-2)
                            (r-w-x r-w-x-2)
                            (cpl cpl-2))
                 (:instance disjoint-p-subset-p
                            (x (mv-nth 1 (las-to-pas l-addrs-1 r-w-x-1 cpl-1 x86)))
                            (y (mv-nth 1 (las-to-pas l-addrs-2 r-w-x-2 cpl-2 x86)))
                            (a (mv-nth 1 (las-to-pas l-addrs-subset-1 r-w-x-1 cpl-1 x86)))
                            (b (mv-nth 1 (las-to-pas l-addrs-subset-2 r-w-x-2 cpl-2 x86)))))
           :in-theory (e/d* (disjoint-p$)
                            (mv-nth-1-las-to-pas-subset-p
                             disjoint-p-subset-p)))))

(defthmd infer-disjointness-with-all-xlation-governing-entries-paddrs-from-gather-all-paging-structure-qword-addresses
  (implies (and
            (disjoint-p
             x
             (open-qword-paddr-list
              (gather-all-paging-structure-qword-addresses (double-rewrite x86))))
            (true-listp x)
            (canonical-address-listp l-addrs))
           (disjoint-p
            x
            (all-xlation-governing-entries-paddrs l-addrs x86)))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance all-xlation-governing-entries-paddrs-subset-of-paging-structures)
                 (:instance disjoint-p-subset-p
                            (x x)
                            (y (open-qword-paddr-list (gather-all-paging-structure-qword-addresses x86)))
                            (a x)
                            (b (all-xlation-governing-entries-paddrs l-addrs x86))))
           :in-theory (e/d* (disjoint-p-commutative)
                            (all-xlation-governing-entries-paddrs-subset-of-paging-structures
                             disjoint-p-subset-p))))
  :rule-classes :rewrite)

(defthm infer-disjointness-with-all-xlation-governing-entries-paddrs-from-gather-all-paging-structure-qword-addresses-with-both-disjoint-p-and-disjoint-p$
  (implies (and
            (disjoint-p$
             x
             (open-qword-paddr-list
              (gather-all-paging-structure-qword-addresses (double-rewrite x86))))
            (true-listp x)
            (canonical-address-listp l-addrs))
           (disjoint-p
            x
            (all-xlation-governing-entries-paddrs l-addrs x86)))
  :hints (("Goal" :in-theory (e/d* (disjoint-p$
                                    infer-disjointness-with-all-xlation-governing-entries-paddrs-from-gather-all-paging-structure-qword-addresses)
                                   ())))
  :rule-classes :rewrite)

(defun find-first-arg-of-disjoint-p$-when-second-arg-matches-aux
  (arg-1-var arg-2 calls)
  ;; (find-first-arg-of-disjoint-p$-when-second-arg-matches-aux
  ;;  'x
  ;;  'y
  ;;  '((disjoint-p a y)
  ;;    (disjoint-p b z)
  ;;    (disjoint-p c y)))
  (if (endp calls)
      nil
    (append
     (if (equal (third (car calls)) arg-2)
         `(((,arg-1-var . ,(second (car calls)))))
       nil)
     (find-first-arg-of-disjoint-p$-when-second-arg-matches-aux
      arg-1-var arg-2 (cdr calls)))))

(defun find-first-arg-of-disjoint-p$-when-second-arg-matches
  (arg-1-var arg-2 mfc state)
  (declare (xargs :stobjs (state) :mode :program)
           (ignorable state))
  (b* ((calls (acl2::find-calls-lst 'disjoint-p$ (acl2::mfc-clause mfc)))
       ((when (not calls)) nil))
    (find-first-arg-of-disjoint-p$-when-second-arg-matches-aux
     arg-1-var arg-2 calls)))

(defthm infer-disjointness-with-all-xlation-governing-entries-paddrs-from-gather-all-paging-structure-qword-addresses-with-disjoint-p$
  (implies (and (bind-free
                 (find-first-arg-of-disjoint-p$-when-second-arg-matches
                  'x
                  '(open-qword-paddr-list
                    (gather-all-paging-structure-qword-addresses x86))
                  mfc state)
                 (x))
                (subset-p y x)
                (disjoint-p$
                 x
                 (open-qword-paddr-list
                  (gather-all-paging-structure-qword-addresses (double-rewrite x86)))))
           (disjoint-p
            y
            (open-qword-paddr-list
             (gather-all-paging-structure-qword-addresses x86))))
  :hints (("Goal" :in-theory (e/d* (disjoint-p$
                                    disjoint-p
                                    subset-p
                                    infer-disjointness-with-all-xlation-governing-entries-paddrs-from-gather-all-paging-structure-qword-addresses)
                                   ())))
  :rule-classes :rewrite)

(defthm infer-disjointness-with-all-xlation-governing-entries-paddrs-from-gather-all-paging-structure-qword-addresses-with-both-disjoint-p-and-disjoint-p$-and-subset-p
  ;; Less general (and less expensive) than
  ;; infer-disjointness-with-all-xlation-governing-entries-paddrs-from-gather-all-paging-structure-qword-addresses-with-both-disjoint-p-and-disjoint-p$
  ;; because this rule applies only during instruction fetches.
  (implies
   (and
    (bind-free (find-l-addrs-from-program-at-or-program-at-alt-term
                'infer-disjointness
                'l-addrs mfc state)
               (l-addrs))
    (disjoint-p$
     (mv-nth 1 (las-to-pas l-addrs :x cpl (double-rewrite x86)))
     (open-qword-paddr-list
      (gather-all-paging-structure-qword-addresses (double-rewrite x86))))
    (not (mv-nth 0 (las-to-pas l-addrs :x cpl (double-rewrite x86))))
    (subset-p l-addrs-subset-1 l-addrs)
    (subset-p l-addrs-subset-2 l-addrs)
    (canonical-address-listp l-addrs))
   (disjoint-p
    (mv-nth 1 (las-to-pas l-addrs-subset-1 :x cpl x86))
    (all-xlation-governing-entries-paddrs l-addrs-subset-2 x86)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (disjoint-p$
                             subset-p)
                            ())
           :use ((:instance infer-disjointness-with-all-xlation-governing-entries-paddrs-from-gather-all-paging-structure-qword-addresses
                            (x (mv-nth 1 (las-to-pas l-addrs :x cpl x86)))
                            (l-addrs l-addrs-subset))
                 (:instance disjoint-p-subset-p
                            (x (mv-nth 1 (las-to-pas l-addrs :x cpl x86)))
                            (y (all-xlation-governing-entries-paddrs l-addrs x86))
                            (a (mv-nth 1 (las-to-pas l-addrs-subset-1 :x cpl x86)))
                            (b (all-xlation-governing-entries-paddrs l-addrs-subset-2 x86))))))

  :rule-classes :rewrite)

;; ======================================================================

(define separate-mapped-mem ((n-1 posp)
                             (l-addr-1 canonical-address-p)
                             (r-x-1 :type (member :r :x))
                             (n-2 posp)
                             (l-addr-2 canonical-address-p)
                             (r-x-2 :type (member :r :x))
                             x86)
  :returns (disjoint-p? booleanp :rule-classes :type-prescription)
  :guard (and (not (programmer-level-mode x86))
              (canonical-address-p (+ -1 n-1 l-addr-1))
              (canonical-address-p (+ -1 n-2 l-addr-2)))

  ;; TODO: Separation of xlate-governing-entries?

  :long "<p>Two linear memory regions are truly separate if their
 corresponding physical memory regions are separate --- the function
 separate-mapped-mem allows us to state this property.  We say
 <i>truly</i> separate because distinct linear memory regions can be
 mapped to the same physical memory region.</p>"

  :non-executable t

  (b* (((mv r-1-err r-1-paddrs)
        (las-to-pas (create-canonical-address-list n-1 l-addr-1) r-x-1 x86))
       ((mv r-2-err r-2-paddrs)
        (las-to-pas (create-canonical-address-list n-2 l-addr-2) r-x-2 x86)))
    (and (not r-1-err)
         (not r-2-err)
         (disjoint-p r-1-paddrs r-2-paddrs)))

  ///

  (defthmd separate-mapped-mem-is-commutative
    (implies (separate-mapped-mem n-1 a-1 r-x-1 n-2 a-2 r-x-2 x86)
             (separate-mapped-mem n-2 a-2 r-x-2 n-1 a-1 r-x-1 x86))
    :hints (("Goal" :in-theory (e/d* (disjoint-p-commutative) ()))))

  (defun separate-mapped-mem-free-var-candidates (calls)
    (if (endp calls)
        nil
      (cons (list (cons 'n-1   (nth 1 (car calls)))
                  (cons 'a-1   (nth 2 (car calls)))
                  ;; (cons 'r-x-1 (nth 3 (car calls)))
                  (cons 'n-2   (nth 4 (car calls)))
                  (cons 'a-2   (nth 5 (car calls)))
                  ;; (cons 'r-x-2 (nth 6 (car calls)))
                  ;; (cons 'x86   (nth 7 (car calls)))
                  )
            (separate-mapped-mem-free-var-candidates (cdr calls)))))

  (defun separate-mapped-mem-bindings (ctx mfc state)
    (declare (xargs :stobjs (state) :mode :program)
             (ignorable ctx state))
    (b* ((calls (acl2::find-calls-lst 'separate-mapped-mem (acl2::mfc-clause mfc)))
         ((when (not calls)) nil))
      (separate-mapped-mem-free-var-candidates calls)))

  (i-am-here) ;; See ../general-memory-utils.lisp.

  (defthm zp-create-canonical-address-list
    (implies (zp n)
             (equal (create-canonical-address-list n a) nil)))

  (defthm no-error-smaller-region
    (implies (and (<= a a-bigger)
                  (<= (+ a-bigger n-smaller) (+ a n))
                  (not (mv-nth 0 (las-to-pas (create-canonical-address-list n a) r-x x86)))
                  (not (xr :programmer-level-mode 0 x86))
                  (canonical-address-p (+ -1 a n))
                  (posp n)
                  (canonical-address-p a))
             (equal (mv-nth 0 (las-to-pas
                               (create-canonical-address-list n-smaller a-bigger)
                               r-x x86))
                    nil))
    :hints (("Goal" :induct (cons (las-to-pas (create-canonical-address-list n-smaller a-bigger) r-x x86)
                                  (las-to-pas (create-canonical-address-list n a) r-x x86))
             :in-theory (e/d* () (signed-byte-p)))))

  (defthm separate-mapped-mem-smaller-regions
    (implies (and
              (bind-free
               (separate-mapped-mem-bindings
                'separate-mapped-mem-smaller-regions mfc state)
               (n-1 a-1 n-2 a-2))
              (<= a-2 a-2-bigger)
              (<= (+ n-2-smaller a-2-bigger) (+ n-2 a-2))
              (<= a-1 a-1-bigger)
              (<= (+ n-1-smaller a-1-bigger) (+ n-1 a-1))
              (separate-mapped-mem n-1 a-1 r-x-1 n-2 a-2 r-x-2 x86)
              (not (programmer-level-mode x86))
              (canonical-address-p (+ -1 n-1 a-1))
              (canonical-address-p (+ -1 n-2 a-2)))
             (separate-mapped-mem n-1-smaller a-1-bigger r-x-1 n-2-smaller a-2-bigger r-x-2 x86))
    :hints (("Goal" :in-theory (e/d* () (signed-byte-p)))))

  (defthm separate-mapped-mem-contiguous-regions
    (and (separate-mapped-mem i (+ (- i) x) j x)
         (implies (<= j i)
                  (separate-mapped-mem i x j (+ (- i) x)))
         (separate-mapped-mem i x j (+ i x))
         (implies (or (<= (+ j k2) k1) (<= (+ i k1) k2))
                  (separate-mapped-mem i (+ k1 x) j (+ k2 x))))
    :hints (("Goal" :in-theory (e/d* (separate-mapped-mem) ()))))
  )

;; ======================================================================
