;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")
(include-book "paging-pml4-table-lemmas" :ttags :all)

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))

(local (in-theory (e/d (entry-found-p-and-lin-addr
                        entry-found-p-and-good-paging-structures-x86p)
                       (unsigned-byte-p
                        signed-byte-p))))

;; ======================================================================

(defsection reasoning-about-page-tables
  :parents (proof-utilities)

  :short "Reasoning about paging data structures"

  :long "<p>WORK IN PROGRESS...</p>

<p>This doc topic will be updated in later commits...</p>"
  )

(local (xdoc::set-default-parents reasoning-about-page-tables))

;; ======================================================================

(defthmd xlate-equiv-x86s-open-for-ctr-and-msr
  (implies (and (xlate-equiv-x86s x86-1 x86-2)
                (good-paging-structures-x86p x86-1))
           (and (equal (cr0-slice :cr0-wp (n32 (ctri *cr0* x86-1)))
                       (cr0-slice :cr0-wp (n32 (ctri *cr0* x86-2))))
                (equal (cr4-slice :cr4-smep (n21 (ctri *cr4* x86-1)))
                       (cr4-slice :cr4-smep (n21 (ctri *cr4* x86-2))))
                (equal
                 (ia32_efer-slice
                  :ia32_efer-nxe (n12 (msri *ia32_efer-idx* x86-1)))
                 (ia32_efer-slice
                  :ia32_efer-nxe (n12 (msri *ia32_efer-idx* x86-2)))))))

(defthmd xlate-equiv-x86s-open-for-not-good-paging-structures-x86p
  (implies (and (not (good-paging-structures-x86p x86-1))
                (xlate-equiv-x86s x86-1 x86-2))
           (not (good-paging-structures-x86p x86-2))))

(in-theory (e/d () (xlate-equiv-x86s)))

;; ======================================================================

(defthm mv-nth-0-ia32e-entries-found-la-to-pa-with-xlate-equiv-x86s
  (implies (xlate-equiv-x86s x86-1 x86-2)
           (equal (mv-nth
                   0
                   (ia32e-entries-found-la-to-pa
                    lin-addr r-w-x cpl x86-1))
                  (mv-nth
                   0
                   (ia32e-entries-found-la-to-pa
                    lin-addr r-w-x cpl x86-2))))
  :hints (("Goal"
           :use ((:instance xlate-equiv-x86s-open-for-ctr-and-msr)
                 (:instance xlate-equiv-x86s-open-for-not-good-paging-structures-x86p))
           :in-theory (e/d* (ia32e-entries-found-la-to-pa
                             not-good-paging-structures-x86p-and-ia32e-la-to-pa-PML4T)
                            ())))
  :rule-classes :congruence)

(defthm mv-nth-1-ia32e-entries-found-la-to-pa-with-xlate-equiv-x86s
  (implies (xlate-equiv-x86s x86-1 x86-2)
           (equal (mv-nth
                   1
                   (ia32e-entries-found-la-to-pa
                    lin-addr r-w-x cpl x86-1))
                  (mv-nth
                   1
                   (ia32e-entries-found-la-to-pa
                    lin-addr r-w-x cpl x86-2))))
  :hints (("Goal"
           :use ((:instance xlate-equiv-x86s-open-for-ctr-and-msr)
                 (:instance xlate-equiv-x86s-open-for-not-good-paging-structures-x86p))
           :in-theory (e/d* (ia32e-entries-found-la-to-pa
                             not-good-paging-structures-x86p-and-ia32e-la-to-pa-PML4T)
                            ())))
  :rule-classes :congruence)

(defthm xlate-equiv-x86s-with-mv-nth-2-ia32e-entries-found-la-to-pa
  (xlate-equiv-x86s
   (mv-nth 2 (ia32e-entries-found-la-to-pa lin-addr r-w-x cpl x86))
   (double-rewrite x86))
  :hints (("Goal"
           :use ((:instance xlate-equiv-x86s-open-for-ctr-and-msr)
                 (:instance xlate-equiv-x86s-open-for-not-good-paging-structures-x86p))
           :in-theory (e/d* (ia32e-entries-found-la-to-pa
                             not-good-paging-structures-x86p-and-ia32e-la-to-pa-PML4T)
                            ()))))

(defthm two-page-table-walks-ia32e-entries-found-la-to-pa
  (and

   (equal
    (mv-nth
     0
     (ia32e-entries-found-la-to-pa
      lin-addr-1 r-w-x-1 cpl-1
      (mv-nth
       2
       (ia32e-entries-found-la-to-pa
        lin-addr-2 r-w-x-2 cpl-2 x86))))
    (mv-nth
     0
     (ia32e-entries-found-la-to-pa
      lin-addr-1 r-w-x-1 cpl-1 x86)))

   (equal
    (mv-nth
     1
     (ia32e-entries-found-la-to-pa
      lin-addr-1 r-w-x-1 cpl-1
      (mv-nth
       2
       (ia32e-entries-found-la-to-pa
        lin-addr-2 r-w-x-2 cpl-2 x86))))
    (mv-nth
     1
     (ia32e-entries-found-la-to-pa
      lin-addr-1 r-w-x-1 cpl-1 x86)))))

;; ======================================================================

(defthm paging-entries-found-p-and-xlate-equiv-x86s
  (implies (xlate-equiv-x86s x86-1 x86-2)
           (equal (paging-entries-found-p lin-addr x86-1)
                  (paging-entries-found-p lin-addr x86-2)))
  :hints (("Goal"
           :in-theory (e/d* (paging-entries-found-p) (xlate-equiv-x86s))
           :use ((:instance xlate-equiv-entries-and-page-size
                            (e-1 (mv-nth 2 (read-page-dir-ptr-table-entry lin-addr x86-1)))
                            (e-2 (mv-nth 2 (read-page-dir-ptr-table-entry lin-addr x86-2))))
                 (:instance xlate-equiv-entries-and-page-size
                            (e-1 (mv-nth 2 (read-page-directory-entry lin-addr x86-1)))
                            (e-2 (mv-nth 2 (read-page-directory-entry lin-addr x86-2)))))))
  :rule-classes :congruence)

(defthm gather-all-paging-structure-qword-addresses-mv-nth-2-ia32e-entries-found-la-to-pa
  (implies (good-paging-structures-x86p x86)
           (equal
            (gather-all-paging-structure-qword-addresses
             (mv-nth 2 (ia32e-entries-found-la-to-pa lin-addr r-w-x cpl x86)))
            (gather-all-paging-structure-qword-addresses x86)))
  :hints (("Goal" :in-theory (e/d* (ia32e-entries-found-la-to-pa) ()))))

;; ======================================================================

;; Memory RoW and WoW lemmas when reads and writes are from addresses
;; that are disjoint from the paging structures:

;; Page Table:

(defthm xr-ia32e-la-to-pa-PT-mem-disjoint
  (implies (and (pairwise-disjoint-p-aux
                 (list index)
                 (open-qword-paddr-list-list
                  (gather-all-paging-structure-qword-addresses x86)))
                (physical-address-p index))
           (equal (xr :mem index
                      (mv-nth 2
                              (ia32e-la-to-pa-PT
                               lin-addr u-s-acc wp smep nxe r-w-x cpl
                               x86)))
                  (xr :mem index x86)))
  :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa-PT
                                    ia32e-la-to-pa-page-table-alt
                                    pairwise-disjoint-p-aux)
                                   (bitops::logand-with-negated-bitmask)))))

;; (i-am-here)

;; (defthm rm-low-64-ia32e-la-to-pa-PT-mem-disjoint
;;   (implies (and (pairwise-disjoint-p-aux
;;                  (addr-range 8 index)
;;                  (open-qword-paddr-list-list
;;                   (gather-all-paging-structure-qword-addresses x86)))
;;                 (physical-address-p index))
;;            (equal (rm-low-64 index
;;                              (mv-nth 2
;;                                      (ia32e-la-to-pa-PT
;;                                       lin-addr u-s-acc wp smep nxe r-w-x cpl
;;                                       x86)))
;;                   (rm-low-64 index x86)))
;;   :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa-PT
;;                                     ia32e-la-to-pa-page-table-alt)
;;                                    (bitops::logand-with-negated-bitmask))))
;;   :otf-flg t)

(defthm ia32e-la-to-pa-PT-xw-mem-disjoint-commute
  (implies (and (page-directory-entry-addr-found-p lin-addr (double-rewrite x86))
                (pairwise-disjoint-p-aux
                 (list index)
                 (open-qword-paddr-list-list
                  (gather-all-paging-structure-qword-addresses x86)))
                (physical-address-p index)
                (unsigned-byte-p 8 val))
           (equal (xw :mem index val
                      (mv-nth 2
                              (ia32e-la-to-pa-PT
                               lin-addr u-s-acc wp smep nxe r-w-x cpl
                               x86)))
                  (mv-nth 2
                          (ia32e-la-to-pa-PT
                           lin-addr u-s-acc wp smep nxe r-w-x cpl
                           (xw :mem index val x86)))))
  :hints (("Goal" :in-theory (e/d* (read-page-table-entry
                                    ia32e-la-to-pa-PT
                                    ia32e-la-to-pa-page-table-alt
                                    pairwise-disjoint-p-aux)
                                   (bitops::logand-with-negated-bitmask)))))

;; (defthm ia32e-la-to-pa-PT-wm-low-64-disjoint-commute
;;   (implies (and (page-directory-entry-addr-found-p lin-addr (double-rewrite x86))
;;                 (pairwise-disjoint-p-aux
;;                  (addr-range 8 index)
;;                  (open-qword-paddr-list-list
;;                   (gather-all-paging-structure-qword-addresses x86)))
;;                 (physical-address-p index)
;;                 (unsigned-byte-p 8 val))
;;            (equal (wm-low-64 index val
;;                              (mv-nth 2
;;                                      (ia32e-la-to-pa-PT
;;                                       lin-addr u-s-acc wp smep nxe r-w-x cpl
;;                                       x86)))
;;                   (mv-nth 2
;;                           (ia32e-la-to-pa-PT
;;                            lin-addr u-s-acc wp smep nxe r-w-x cpl
;;                            (wm-low-64 index val x86)))))
;;   :hints (("Goal" :in-theory (e/d* (read-page-table-entry
;;                                     ia32e-la-to-pa-PT
;;                                     ia32e-la-to-pa-page-table-alt
;;                                     pairwise-disjoint-p-aux)
;;                                    (bitops::logand-with-negated-bitmask)))))

;; Page Directory:

(defthm xr-ia32e-la-to-pa-PD-mem-disjoint
  (implies (and (pairwise-disjoint-p-aux
                 (list index)
                 (open-qword-paddr-list-list
                  (gather-all-paging-structure-qword-addresses x86)))
                (physical-address-p index))
           (equal (xr :mem index
                      (mv-nth 2
                              (ia32e-la-to-pa-PD
                               lin-addr wp smep nxe r-w-x cpl
                               x86)))
                  (xr :mem index x86)))
  :hints (("Goal"
           :use ((:instance xr-ia32e-la-to-pa-PT-mem-disjoint
                            (u-s-acc (page-user-supervisor
                                      (mv-nth 2 (read-page-directory-entry lin-addr x86))))))
           :in-theory (e/d* (ia32e-la-to-pa-PD
                             ia32e-la-to-pa-page-directory-alt
                             pairwise-disjoint-p-aux)
                            (bitops::logand-with-negated-bitmask
                             xr-ia32e-la-to-pa-PT-mem-disjoint)))))

(defthm ia32e-la-to-pa-PD-xw-mem-disjoint-commute
  (implies (and (paging-entries-found-p lin-addr (double-rewrite x86))
                (pairwise-disjoint-p-aux
                 (list index)
                 (open-qword-paddr-list-list
                  (gather-all-paging-structure-qword-addresses x86)))
                (physical-address-p index)
                (unsigned-byte-p 8 val))
           (equal (xw :mem index val
                      (mv-nth 2
                              (ia32e-la-to-pa-PD
                               lin-addr wp smep nxe r-w-x cpl x86)))
                  (mv-nth 2
                          (ia32e-la-to-pa-PD
                           lin-addr wp smep nxe r-w-x cpl
                           (xw :mem index val x86)))))
  :hints (("Goal"
           :use ((:instance ia32e-la-to-pa-PT-xw-mem-disjoint-commute
                            (u-s-acc (page-user-supervisor
                                      (mv-nth 2 (read-page-directory-entry lin-addr x86))))))
           :in-theory (e/d* (read-page-directory-entry
                             ia32e-la-to-pa-PD
                             ia32e-la-to-pa-page-directory-alt
                             pairwise-disjoint-p-aux
                             paging-entries-found-p)
                            (bitops::logand-with-negated-bitmask
                             unsigned-byte-p
                             signed-byte-p
                             not
                             ia32e-la-to-pa-PT-xw-mem-disjoint-commute)))))

;; Page Directory Pointer Table:

(defthm xr-ia32e-la-to-pa-PDPT-mem-disjoint
  (implies (and (pairwise-disjoint-p-aux
                 (list index)
                 (open-qword-paddr-list-list
                  (gather-all-paging-structure-qword-addresses x86)))
                (physical-address-p index))
           (equal (xr :mem index
                      (mv-nth 2
                              (ia32e-la-to-pa-PDPT
                               lin-addr wp smep nxe r-w-x cpl
                               x86)))
                  (xr :mem index x86)))
  :hints (("Goal"
           :use ((:instance xr-ia32e-la-to-pa-PD-mem-disjoint))
           :in-theory (e/d* (ia32e-la-to-pa-PDPT
                             ia32e-la-to-pa-page-dir-ptr-table-alt
                             paging-entries-found-p
                             pairwise-disjoint-p-aux)
                            (bitops::logand-with-negated-bitmask
                             xr-ia32e-la-to-pa-PD-mem-disjoint
                             unsigned-byte-p
                             signed-byte-p)))))

(defthm ia32e-la-to-pa-PDPT-xw-mem-disjoint-commute
  (implies (and (paging-entries-found-p lin-addr (double-rewrite x86))
                (pairwise-disjoint-p-aux
                 (list index)
                 (open-qword-paddr-list-list
                  (gather-all-paging-structure-qword-addresses x86)))
                (physical-address-p index)
                (unsigned-byte-p 8 val))
           (equal (xw :mem index val
                      (mv-nth 2
                              (ia32e-la-to-pa-PDPT
                               lin-addr wp smep nxe r-w-x cpl x86)))
                  (mv-nth 2
                          (ia32e-la-to-pa-PDPT
                           lin-addr wp smep nxe r-w-x cpl
                           (xw :mem index val x86)))))
  :hints (("Goal"
           :use ((:instance ia32e-la-to-pa-PD-xw-mem-disjoint-commute))
           :in-theory (e/d* (read-page-dir-ptr-table-entry
                             ia32e-la-to-pa-PDPT
                             ia32e-la-to-pa-page-dir-ptr-table-alt
                             pairwise-disjoint-p-aux
                             paging-entries-found-p)
                            (bitops::logand-with-negated-bitmask
                             ia32e-la-to-pa-PD-xw-mem-disjoint-commute
                             unsigned-byte-p
                             not
                             signed-byte-p)))))

;; PML4 Table:

(defthm xr-ia32e-la-to-pa-PML4T-mem-disjoint
  (implies (and (pairwise-disjoint-p-aux
                 (list index)
                 (open-qword-paddr-list-list
                  (gather-all-paging-structure-qword-addresses x86)))
                (physical-address-p index))
           (equal (xr :mem index
                      (mv-nth 2 (ia32e-la-to-pa-PML4T lin-addr wp smep nxe r-w-x cpl x86)))
                  (xr :mem index x86)))
  :hints (("Goal"
           :in-theory (e/d* (ia32e-la-to-pa-PML4T
                             paging-entries-found-p
                             pairwise-disjoint-p-aux)
                            (bitops::logand-with-negated-bitmask
                             unsigned-byte-p
                             signed-byte-p)))))

(defthm ia32e-la-to-pa-PML4T-xw-mem-disjoint-commute
  (implies (and (paging-entries-found-p lin-addr (double-rewrite x86))
                (pairwise-disjoint-p-aux
                 (list index)
                 (open-qword-paddr-list-list
                  (gather-all-paging-structure-qword-addresses x86)))
                (physical-address-p index)
                (unsigned-byte-p 8 val))
           (equal (xw :mem index val
                      (mv-nth 2
                              (ia32e-la-to-pa-PML4T
                               lin-addr wp smep nxe r-w-x cpl x86)))
                  (mv-nth 2
                          (ia32e-la-to-pa-PML4T
                           lin-addr wp smep nxe r-w-x cpl
                           (xw :mem index val x86)))))
  :hints (("Goal"
           :use ((:instance ia32e-la-to-pa-PDPT-xw-mem-disjoint-commute))
           :in-theory (e/d* (read-pml4-table-entry
                             ia32e-la-to-pa-PML4T
                             pairwise-disjoint-p-aux
                             paging-entries-found-p)
                            (bitops::logand-with-negated-bitmask
                             ia32e-la-to-pa-PDPT-xw-mem-disjoint-commute
                             unsigned-byte-p
                             signed-byte-p)))))

;; Top-level Paging Translation Function:

(defthm ia32e-entries-found-la-to-pa-xr-mem-disjoint
  (implies (and (paging-entries-found-p lin-addr (double-rewrite x86))
                (pairwise-disjoint-p-aux
                 (list index)
                 (open-qword-paddr-list-list
                  (gather-all-paging-structure-qword-addresses x86)))
                (physical-address-p index))
           (equal (xr :mem index (mv-nth 2 (ia32e-entries-found-la-to-pa lin-addr r-w-x cpl x86)))
                  (xr :mem index x86)))
  :hints (("Goal"
           :in-theory (e/d* (ia32e-entries-found-la-to-pa
                             pairwise-disjoint-p-aux)
                            (bitops::logand-with-negated-bitmask
                             unsigned-byte-p
                             signed-byte-p)))))

(defthm ia32e-entries-found-la-to-pa-xw-mem-disjoint
  (implies (and (paging-entries-found-p lin-addr (double-rewrite x86))
                (pairwise-disjoint-p-aux
                 (list index)
                 (open-qword-paddr-list-list
                  (gather-all-paging-structure-qword-addresses x86)))
                (physical-address-p index)
                (unsigned-byte-p 8 val))
           (and (equal (mv-nth 0
                               (ia32e-entries-found-la-to-pa
                                lin-addr r-w-x cpl
                                (xw :mem index val x86)))
                       (mv-nth 0
                               (ia32e-entries-found-la-to-pa
                                lin-addr r-w-x cpl
                                x86)))
                (equal (mv-nth 1
                               (ia32e-entries-found-la-to-pa
                                lin-addr r-w-x cpl
                                (xw :mem index val x86)))
                       (mv-nth 1
                               (ia32e-entries-found-la-to-pa
                                lin-addr r-w-x cpl
                                x86)))))
  :hints (("Goal" :in-theory (e/d* ()
                                   (bitops::logand-with-negated-bitmask)))))

(defthm ia32e-entries-found-la-to-pa-xw-mem-disjoint-commute
  (implies (and (paging-entries-found-p lin-addr (double-rewrite x86))
                (pairwise-disjoint-p-aux
                 (list index)
                 (open-qword-paddr-list-list
                  (gather-all-paging-structure-qword-addresses x86)))
                (physical-address-p index)
                (unsigned-byte-p 8 val))
           (equal (xw :mem index val (mv-nth 2 (ia32e-entries-found-la-to-pa lin-addr r-w-x cpl x86)))
                  (mv-nth 2 (ia32e-entries-found-la-to-pa lin-addr r-w-x cpl (xw :mem index val x86)))))
  :hints (("Goal"
           :in-theory (e/d* (ia32e-entries-found-la-to-pa
                             pairwise-disjoint-p-aux)
                            (bitops::logand-with-negated-bitmask
                             unsigned-byte-p
                             signed-byte-p)))))

;; ======================================================================
