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
   x86)
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

(defthm gather-all-paging-structure-qword-addresses-mv-nth-2-ia32e-entries-found-la-to-pa
  (implies (good-paging-structures-x86p x86)
           (equal
            (gather-all-paging-structure-qword-addresses
             (mv-nth 2 (ia32e-entries-found-la-to-pa lin-addr r-w-x cpl x86)))
            (gather-all-paging-structure-qword-addresses x86)))
  :hints (("Goal" :in-theory (e/d* (ia32e-entries-found-la-to-pa) ()))))

;; ======================================================================

;; *-entry-addr-found-p and ia32e-entries-found-la-to-pa:

(defthm page-table-entry-addr-found-p-after-a-walk
  (implies (page-table-entry-addr-found-p lin-addr-1 x86)
           (page-table-entry-addr-found-p
            lin-addr-1
            (mv-nth 2 (ia32e-entries-found-la-to-pa lin-addr-2 r-w-x cpl x86))))
  :hints (("Goal"
           :use ((:instance page-table-entry-addr-found-p-and-xlate-equiv-x86s
                            (x86-1 x86)
                            (lin-addr lin-addr-1)
                            (x86-2
                             (mv-nth 2 (ia32e-entries-found-la-to-pa lin-addr-2 r-w-x cpl x86)))))
           :in-theory (e/d* ()
                            (physical-address-p
                             page-table-entry-addr-found-p-and-xlate-equiv-x86s
                             xlate-equiv-x86s-with-mv-nth-2-ia32e-la-to-pa-PML4T
                             xlate-equiv-x86s-and-page-dir-ptr-table-base-addr
                             xlate-equiv-x86s-and-page-dir-ptr-table-entry-addr-address
                             xlate-equiv-x86s-and-page-directory-base-addr
                             xlate-equiv-x86s-and-page-directory-entry-addr-address
                             xlate-equiv-x86s-and-page-table-base-addr
                             xlate-equiv-x86s-and-page-table-entry-addr-address
                             bitops::logand-with-negated-bitmask)))))

(defthm page-directory-entry-addr-found-p-after-a-walk
  (implies (page-directory-entry-addr-found-p lin-addr-1 x86)
           (page-directory-entry-addr-found-p
            lin-addr-1
            (mv-nth 2 (ia32e-entries-found-la-to-pa lin-addr-2 r-w-x cpl x86))))
  :hints (("Goal"
           :use ((:instance page-directory-entry-addr-found-p-and-xlate-equiv-x86s
                            (x86-1 x86)
                            (lin-addr lin-addr-1)
                            (x86-2
                             (mv-nth 2 (ia32e-entries-found-la-to-pa lin-addr-2 r-w-x cpl x86)))))
           :in-theory (e/d* ()
                            (physical-address-p
                             page-directory-entry-addr-found-p-and-xlate-equiv-x86s
                             xlate-equiv-x86s-with-mv-nth-2-ia32e-la-to-pa-PML4T
                             xlate-equiv-x86s-and-page-dir-ptr-table-base-addr
                             xlate-equiv-x86s-and-page-dir-ptr-table-entry-addr-address
                             xlate-equiv-x86s-and-page-directory-base-addr
                             xlate-equiv-x86s-and-page-directory-entry-addr-address
                             xlate-equiv-x86s-and-page-table-base-addr
                             xlate-equiv-x86s-and-page-table-entry-addr-address
                             bitops::logand-with-negated-bitmask)))))

(defthm page-dir-ptr-table-entry-addr-found-p-after-a-walk
  (implies (page-dir-ptr-table-entry-addr-found-p lin-addr-1 x86)
           (page-dir-ptr-table-entry-addr-found-p
            lin-addr-1
            (mv-nth 2 (ia32e-entries-found-la-to-pa lin-addr-2 r-w-x cpl x86))))
  :hints (("Goal"
           :use ((:instance page-dir-ptr-table-entry-addr-found-p-and-xlate-equiv-x86s
                            (x86-1 x86)
                            (lin-addr lin-addr-1)
                            (x86-2
                             (mv-nth 2 (ia32e-entries-found-la-to-pa lin-addr-2 r-w-x cpl x86)))))
           :in-theory (e/d* ()
                            (physical-address-p
                             page-dir-ptr-table-entry-addr-found-p-and-xlate-equiv-x86s
                             xlate-equiv-x86s-with-mv-nth-2-ia32e-la-to-pa-PML4T
                             xlate-equiv-x86s-and-page-dir-ptr-table-base-addr
                             xlate-equiv-x86s-and-page-dir-ptr-table-entry-addr-address
                             xlate-equiv-x86s-and-page-dir-ptr-table-entry-addr-address
                             xlate-equiv-x86s-and-page-table-base-addr
                             xlate-equiv-x86s-and-page-table-entry-addr-address
                             bitops::logand-with-negated-bitmask)))))

(defthm pml4-table-entry-addr-found-p-after-a-walk
  (implies (pml4-table-entry-addr-found-p lin-addr-1 x86)
           (pml4-table-entry-addr-found-p
            lin-addr-1
            (mv-nth 2 (ia32e-entries-found-la-to-pa lin-addr-2 r-w-x cpl x86))))
  :hints (("Goal"
           :use ((:instance pml4-table-entry-addr-found-p-and-xlate-equiv-x86s
                            (x86-1 x86)
                            (lin-addr lin-addr-1)
                            (x86-2
                             (mv-nth 2 (ia32e-entries-found-la-to-pa lin-addr-2 r-w-x cpl x86)))))
           :in-theory (e/d* ()
                            (physical-address-p
                             pml4-table-entry-addr-found-p-and-xlate-equiv-x86s
                             xlate-equiv-x86s-with-mv-nth-2-ia32e-la-to-pa-PML4T
                             xlate-equiv-x86s-and-pml4-table-base-addr
                             xlate-equiv-x86s-and-pml4-table-entry-addr-address
                             xlate-equiv-x86s-and-pml4-table-entry-addr-address
                             xlate-equiv-x86s-and-page-table-base-addr
                             xlate-equiv-x86s-and-page-table-entry-addr-address
                             bitops::logand-with-negated-bitmask)))))

(defthm paging-entries-found-p-after-a-walk
  (implies (and (paging-entries-found-p lin-addr-1 x86)
                (paging-entries-found-p lin-addr-2 x86))
           (paging-entries-found-p
            lin-addr-1
            (mv-nth 2 (ia32e-entries-found-la-to-pa lin-addr-2 r-w-x cpl x86))))
  :hints (("Goal"
           :in-theory (e/d* (paging-entries-found-p
                             page-size
                             xlate-equiv-entries)
                            (xlate-equiv-x86s-and-page-dir-ptr-table-entry-addr-value
                             xlate-equiv-x86s-and-page-directory-entry-addr-value
                             xlate-equiv-x86s-and-page-table-entry-addr-value))
           :use ((:instance xlate-equiv-x86s-and-page-dir-ptr-table-entry-addr-value
                            (x86-1 x86)
                            (lin-addr lin-addr-1)
                            (x86-2 (mv-nth 2 (ia32e-entries-found-la-to-pa lin-addr-2 r-w-x cpl x86))))
                 (:instance xlate-equiv-x86s-and-page-directory-entry-addr-value
                            (x86-1 x86)
                            (lin-addr lin-addr-1)
                            (x86-2 (mv-nth 2 (ia32e-entries-found-la-to-pa lin-addr-2 r-w-x cpl x86))))
                 (:instance logtail-bigger-and-logbitp
                            (e1 (rm-low-64 (page-dir-ptr-table-entry-addr
                                            lin-addr-1
                                            (mv-nth 1 (page-dir-ptr-table-base-addr lin-addr-1 x86)))
                                           x86))
                            (e2 (rm-low-64
                                 (page-dir-ptr-table-entry-addr
                                  lin-addr-1
                                  (mv-nth
                                   1
                                   (page-dir-ptr-table-base-addr
                                    lin-addr-1
                                    (mv-nth 2 (ia32e-entries-found-la-to-pa lin-addr-2 r-w-x cpl x86)))))
                                 (mv-nth 2 (ia32e-entries-found-la-to-pa lin-addr-2 r-w-x cpl x86))))
                            (m 7)
                            (n 7))
                 (:instance logtail-bigger-and-logbitp
                            (e1 (rm-low-64 (page-directory-entry-addr
                                            lin-addr-1
                                            (mv-nth 1 (page-directory-base-addr lin-addr-1 x86)))
                                           x86))
                            (e2 (rm-low-64
                                 (page-directory-entry-addr
                                  lin-addr-1
                                  (mv-nth
                                   1
                                   (page-directory-base-addr
                                    lin-addr-1
                                    (mv-nth 2 (ia32e-entries-found-la-to-pa lin-addr-2 r-w-x cpl x86)))))
                                 (mv-nth 2 (ia32e-entries-found-la-to-pa lin-addr-2 r-w-x cpl x86))))
                            (m 7)
                            (n 7))))))

;; ======================================================================

;; *-base-addr/*-entry-addr-found-p and xw :mem/wm-low-64 RoW Theorems
;; ---- where the writes are disjoint from paging structures:

(local
 (defthm pairwise-disjoint-p-aux-and-disjoint-p-with-addr-range-8-lemma
   (implies
    (and (pairwise-disjoint-p-aux
          (addr-range 8 index)
          (open-qword-paddr-list-list addrs))
         (member-list-p addr addrs))
    (disjoint-p (addr-range 8 index)
                (addr-range 8 addr)))
   :hints (("Goal" :in-theory (e/d* (pairwise-disjoint-p-aux
                                     member-list-p
                                     member-p)
                                    ())))))

(local
 (defthm member-list-p-and-disjoint-p-with-addr-range-8-lemma
   (implies
    (and (member-list-p index addrs)
         (member-list-p addr  addrs)
         (not (equal index addr))
         (mult-8-qword-paddr-list-listp addrs))
    (disjoint-p (addr-range 8 index)
                (addr-range 8 addr)))
   :hints (("Goal" :in-theory (e/d* (disjoint-p
                                     member-list-p
                                     member-p)
                                    ())))))

(defthm good-paging-structures-x86p-and-wm-low-64-disjoint-from-paging-structures
  (implies (and (pairwise-disjoint-p-aux
                 (addr-range 8 index)
                 (open-qword-paddr-list-list
                  (gather-all-paging-structure-qword-addresses x86)))
                (good-paging-structures-x86p x86)
                (physical-address-p index))
           (good-paging-structures-x86p (wm-low-64 index val x86)))
  :hints (("Goal" :in-theory (e/d* (good-paging-structures-x86p)
                                   ()))))

;; PML4 Table:

(defthm pml4-table-base-addr-and-xw-mem-disjoint-from-paging-structures
  (implies (and (pairwise-disjoint-p-aux
                 (list index)
                 (open-qword-paddr-list-list
                  (gather-all-paging-structure-qword-addresses x86)))
                (good-paging-structures-x86p x86)
                (physical-address-p index)
                (unsigned-byte-p 8 val))
           (equal (pml4-table-base-addr (xw :mem index val x86))
                  (pml4-table-base-addr x86)))
  :hints (("Goal" :in-theory (e/d* (pml4-table-base-addr)
                                   ()))))

(defthm pml4-table-base-addr-and-wm-low-64-disjoint-from-paging-structures
  (implies (and (pairwise-disjoint-p-aux
                 (addr-range 8 index)
                 (open-qword-paddr-list-list
                  (gather-all-paging-structure-qword-addresses x86)))
                (physical-address-p index)
                (good-paging-structures-x86p x86))
           (equal (pml4-table-base-addr (wm-low-64 index val x86))
                  (pml4-table-base-addr x86)))
  :hints (("Goal" :in-theory (e/d* (pml4-table-base-addr)
                                   ()))))

(defthm pml4-table-entry-addr-found-p-and-xw-mem-disjoint-from-paging-structures
  (implies (and (pairwise-disjoint-p-aux
                 (list index)
                 (open-qword-paddr-list-list
                  (gather-all-paging-structure-qword-addresses x86)))
                (good-paging-structures-x86p x86)
                (physical-address-p index)
                (unsigned-byte-p 8 val))
           (equal (pml4-table-entry-addr-found-p lin-addr (xw :mem index val x86))
                  (pml4-table-entry-addr-found-p lin-addr x86)))
  :hints (("Goal" :in-theory (e/d* (pml4-table-entry-addr-found-p)
                                   ()))))

(defthm pml4-table-entry-addr-found-p-and-wm-low-64-disjoint-from-paging-structures
  (implies (and (pairwise-disjoint-p-aux
                 (addr-range 8 index)
                 (open-qword-paddr-list-list
                  (gather-all-paging-structure-qword-addresses x86)))
                (good-paging-structures-x86p x86)
                (physical-address-p index))
           (equal (pml4-table-entry-addr-found-p lin-addr (wm-low-64 index val x86))
                  (pml4-table-entry-addr-found-p lin-addr x86)))
  :hints (("Goal" :in-theory (e/d* (pml4-table-entry-addr-found-p)
                                   ()))))

;; Page Directory Pointer Table:

(defthm page-dir-ptr-table-base-addr-and-xw-mem-disjoint-from-paging-structures
  (implies (and (pml4-table-entry-addr-found-p lin-addr x86)
                (pairwise-disjoint-p-aux
                 (list index)
                 (open-qword-paddr-list-list
                  (gather-all-paging-structure-qword-addresses x86)))
                (physical-address-p index)
                (unsigned-byte-p 8 val))
           (equal (page-dir-ptr-table-base-addr lin-addr (xw :mem index val x86))
                  (page-dir-ptr-table-base-addr lin-addr x86)))
  :hints (("Goal" :in-theory (e/d* (page-dir-ptr-table-base-addr)
                                   ()))))

(defthm page-dir-ptr-table-base-addr-and-wm-low-64-disjoint-from-paging-structures
  (implies (and (pairwise-disjoint-p-aux
                 (addr-range 8 index)
                 (open-qword-paddr-list-list
                  (gather-all-paging-structure-qword-addresses x86)))
                (physical-address-p index)
                (pml4-table-entry-addr-found-p lin-addr x86))
           (equal (page-dir-ptr-table-base-addr lin-addr (wm-low-64 index val x86))
                  (page-dir-ptr-table-base-addr lin-addr x86)))
  :hints (("Goal" :in-theory (e/d* (page-dir-ptr-table-base-addr) ()))))

(defthm page-dir-ptr-table-entry-addr-found-p-and-xw-mem-disjoint-from-paging-structures
  (implies (and (pml4-table-entry-addr-found-p lin-addr x86)
                (pairwise-disjoint-p-aux
                 (list index)
                 (open-qword-paddr-list-list
                  (gather-all-paging-structure-qword-addresses x86)))
                (physical-address-p index)
                (unsigned-byte-p 8 val))
           (equal (page-dir-ptr-table-entry-addr-found-p lin-addr (xw :mem index val x86))
                  (page-dir-ptr-table-entry-addr-found-p lin-addr x86)))
  :hints (("Goal" :in-theory (e/d* (page-dir-ptr-table-entry-addr-found-p)
                                   ()))))

(defthm page-dir-ptr-table-entry-addr-found-p-and-wm-low-64-disjoint-from-paging-structures
  (implies (and (pml4-table-entry-addr-found-p lin-addr x86)
                (pairwise-disjoint-p-aux
                 (addr-range 8 index)
                 (open-qword-paddr-list-list
                  (gather-all-paging-structure-qword-addresses x86)))
                (physical-address-p index))
           (equal (page-dir-ptr-table-entry-addr-found-p lin-addr (wm-low-64 index val x86))
                  (page-dir-ptr-table-entry-addr-found-p lin-addr x86)))
  :hints (("Goal" :in-theory (e/d* (page-dir-ptr-table-entry-addr-found-p)
                                   ()))))


;; Page Directory:

(defthm page-directory-base-addr-and-xw-mem-disjoint-from-paging-structures
  (implies (and (page-dir-ptr-table-entry-addr-found-p lin-addr x86)
                (pairwise-disjoint-p-aux
                 (list index)
                 (open-qword-paddr-list-list
                  (gather-all-paging-structure-qword-addresses x86)))
                (physical-address-p index)
                (unsigned-byte-p 8 val))
           (equal (page-directory-base-addr lin-addr (xw :mem index val x86))
                  (page-directory-base-addr lin-addr x86)))
  :hints (("Goal" :in-theory (e/d* (page-directory-base-addr)
                                   ()))))

(defthm page-directory-base-addr-and-wm-low-64-disjoint-from-paging-structures
  (implies (and (pairwise-disjoint-p-aux
                 (addr-range 8 index)
                 (open-qword-paddr-list-list
                  (gather-all-paging-structure-qword-addresses x86)))
                (physical-address-p index)
                (page-dir-ptr-table-entry-addr-found-p lin-addr x86))
           (equal (page-directory-base-addr lin-addr (wm-low-64 index val x86))
                  (page-directory-base-addr lin-addr x86)))
  :hints (("Goal" :in-theory (e/d* (page-directory-base-addr) ()))))

(defthm page-directory-entry-addr-found-p-and-xw-mem-disjoint-from-paging-structures
  (implies (and (page-dir-ptr-table-entry-addr-found-p lin-addr x86)
                (pairwise-disjoint-p-aux
                 (list index)
                 (open-qword-paddr-list-list
                  (gather-all-paging-structure-qword-addresses x86)))
                (physical-address-p index)
                (unsigned-byte-p 8 val))
           (equal (page-directory-entry-addr-found-p lin-addr (xw :mem index val x86))
                  (page-directory-entry-addr-found-p lin-addr x86)))
  :hints (("Goal" :in-theory (e/d* (page-directory-entry-addr-found-p)
                                   ()))))

(defthm page-directory-entry-addr-found-p-and-wm-low-64-disjoint-from-paging-structures
  (implies (and (page-dir-ptr-table-entry-addr-found-p lin-addr x86)
                (pairwise-disjoint-p-aux
                 (addr-range 8 index)
                 (open-qword-paddr-list-list
                  (gather-all-paging-structure-qword-addresses x86)))
                (physical-address-p index))
           (equal (page-directory-entry-addr-found-p lin-addr (wm-low-64 index val x86))
                  (page-directory-entry-addr-found-p lin-addr x86)))
  :hints (("Goal" :in-theory (e/d* (page-directory-entry-addr-found-p)
                                   ()))))

;; Page Table:

(defthm page-table-base-addr-and-xw-mem-disjoint-from-paging-structures
  (implies (and (page-directory-entry-addr-found-p lin-addr x86)
                (pairwise-disjoint-p-aux
                 (list index)
                 (open-qword-paddr-list-list
                  (gather-all-paging-structure-qword-addresses x86)))
                (physical-address-p index)
                (unsigned-byte-p 8 val))
           (equal (page-table-base-addr lin-addr (xw :mem index val x86))
                  (page-table-base-addr lin-addr x86)))
  :hints (("Goal" :in-theory (e/d* (page-table-base-addr)
                                   ()))))

(defthm page-table-base-addr-and-wm-low-64-disjoint-from-paging-structures
  (implies (and (pairwise-disjoint-p-aux
                 (addr-range 8 index)
                 (open-qword-paddr-list-list
                  (gather-all-paging-structure-qword-addresses x86)))
                (physical-address-p index)
                (page-directory-entry-addr-found-p lin-addr x86))
           (equal (page-table-base-addr lin-addr (wm-low-64 index val x86))
                  (page-table-base-addr lin-addr x86)))
  :hints (("Goal" :in-theory (e/d* (page-table-base-addr) ()))))

(defthm page-table-entry-addr-found-p-and-xw-mem-disjoint-from-paging-structures
  (implies (and (page-directory-entry-addr-found-p lin-addr x86)
                (pairwise-disjoint-p-aux
                 (list index)
                 (open-qword-paddr-list-list
                  (gather-all-paging-structure-qword-addresses x86)))
                (physical-address-p index)
                (unsigned-byte-p 8 val))
           (equal (page-table-entry-addr-found-p lin-addr (xw :mem index val x86))
                  (page-table-entry-addr-found-p lin-addr x86)))
  :hints (("Goal" :in-theory (e/d* (page-table-entry-addr-found-p)
                                   ()))))

(defthm page-table-entry-addr-found-p-and-wm-low-64-disjoint-from-paging-structures
  (implies (and (page-directory-entry-addr-found-p lin-addr x86)
                (pairwise-disjoint-p-aux
                 (addr-range 8 index)
                 (open-qword-paddr-list-list
                  (gather-all-paging-structure-qword-addresses x86)))
                (physical-address-p index))
           (equal (page-table-entry-addr-found-p lin-addr (wm-low-64 index val x86))
                  (page-table-entry-addr-found-p lin-addr x86)))
  :hints (("Goal" :in-theory (e/d* (page-table-entry-addr-found-p)
                                   ()))))

;; paging-entries-found-p and xw :mem disjoint from paging structures:

(defthm paging-entries-found-p-and-xw-mem-disjoint-from-paging-structures
  (implies (and (paging-entries-found-p lin-addr x86)
                (pairwise-disjoint-p-aux
                 (list index)
                 (open-qword-paddr-list-list
                  (gather-all-paging-structure-qword-addresses x86)))
                (physical-address-p index)
                (unsigned-byte-p 8 val))
           (paging-entries-found-p lin-addr (xw :mem index val x86)))
  :hints (("Goal" :in-theory (e/d* (paging-entries-found-p)
                                   ()))))

(defthm paging-entries-found-p-and-wm-low-64-disjoint-from-paging-structures
  (implies (and (paging-entries-found-p lin-addr x86)
                (pairwise-disjoint-p-aux
                 (addr-range 8 index)
                 (open-qword-paddr-list-list
                  (gather-all-paging-structure-qword-addresses x86)))
                (physical-address-p index))
           (paging-entries-found-p lin-addr (wm-low-64 index val x86)))
  :hints (("Goal" :in-theory (e/d* (paging-entries-found-p)
                                   ()))))

;; ======================================================================

;; *-base-addr/*-entry-addr-found-p and xw :mem/wm-low-64 RoW Theorems
;; *---- where the writes are to a paging entry:

(defthm good-paging-structures-x86p-and-wm-low-64-entry-addr
  (implies (and (equal addrs (gather-all-paging-structure-qword-addresses x86))
                (member-list-p index addrs)
                (xlate-equiv-entries val (rm-low-64 index x86))
                (unsigned-byte-p 64 val)
                (x86p (wm-low-64 index val x86))
                (good-paging-structures-x86p x86))
           (good-paging-structures-x86p (wm-low-64 index val x86)))
  :hints (("Goal" :in-theory (e/d* (good-paging-structures-x86p)
                                   ()))))

;; PML4 Table:

(defthm pml4-table-base-addr-and-wm-low-64-entry-addr
  (implies (and (equal addrs (gather-all-paging-structure-qword-addresses x86))
                (member-list-p index addrs)
                (xlate-equiv-entries val (rm-low-64 index x86))
                (unsigned-byte-p 64 val)
                (x86p (wm-low-64 index val x86))
                (good-paging-structures-x86p x86))
           (equal (pml4-table-base-addr (wm-low-64 index val x86))
                  (pml4-table-base-addr x86)))
  :hints (("Goal" :in-theory (e/d* (pml4-table-base-addr)
                                   ()))))

(defthm pml4-table-entry-addr-found-p-and-wm-low-64-entry-addr
  (implies (and (equal addrs (gather-all-paging-structure-qword-addresses x86))
                (member-list-p index addrs)
                (xlate-equiv-entries val (rm-low-64 index x86))
                (unsigned-byte-p 64 val)
                (x86p (wm-low-64 index val x86))
                (good-paging-structures-x86p x86))
           (equal (pml4-table-entry-addr-found-p lin-addr (wm-low-64 index val x86))
                  (pml4-table-entry-addr-found-p lin-addr x86)))
  :hints (("Goal" :in-theory (e/d* (pml4-table-entry-addr-found-p)
                                   ()))))

;; Page Directory Pointer Table:

(defthm page-dir-ptr-table-base-addr-and-wm-low-64-entry-addr
  (implies (and
            (equal addrs (gather-all-paging-structure-qword-addresses x86))
            (member-list-p index addrs)
            (xlate-equiv-entries val (rm-low-64 index x86))
            (unsigned-byte-p 64 val)
            (pml4-table-entry-addr-found-p lin-addr x86))
           (equal (page-dir-ptr-table-base-addr lin-addr (wm-low-64 index val x86))
                  (page-dir-ptr-table-base-addr lin-addr x86)))
  :hints (("Goal"
           :use ((:instance member-list-p-and-disjoint-p-with-addr-range-8-lemma
                            (index index)
                            (addr (pml4-table-entry-addr lin-addr (mv-nth 1 (pml4-table-base-addr x86))))
                            (addrs (gather-all-paging-structure-qword-addresses x86)))
                 (:instance member-list-p-and-mult-8-qword-paddr-list-listp
                            (index index)
                            (addrs (gather-all-paging-structure-qword-addresses x86)))
                 (:instance xlate-equiv-entries-and-logtail
                            (e1 val)
                            (e2 (rm-low-64 (pml4-table-entry-addr
                                            lin-addr
                                            (mv-nth 1 (pml4-table-base-addr x86)))
                                           x86))
                            (n 12)))
           :in-theory (e/d* (page-dir-ptr-table-base-addr)
                            (member-list-p-and-disjoint-p-with-addr-range-8-lemma
                             member-list-p-and-mult-8-qword-paddr-list-listp)))))

(defthm page-dir-ptr-table-entry-addr-found-p-and-wm-low-64-entry-addr
  (implies (and
            (equal addrs (gather-all-paging-structure-qword-addresses x86))
            (member-list-p index addrs)
            (xlate-equiv-entries val (rm-low-64 index x86))
            (unsigned-byte-p 64 val)
            (pml4-table-entry-addr-found-p lin-addr x86))
           (equal (page-dir-ptr-table-entry-addr-found-p lin-addr (wm-low-64 index val x86))
                  (page-dir-ptr-table-entry-addr-found-p lin-addr x86)))
  :hints (("Goal"
           :use ((:instance member-list-p-and-disjoint-p-with-addr-range-8-lemma
                            (index index)
                            (addr (pml4-table-entry-addr lin-addr (mv-nth 1 (pml4-table-base-addr x86))))
                            (addrs (gather-all-paging-structure-qword-addresses x86)))
                 (:instance member-list-p-and-mult-8-qword-paddr-list-listp
                            (index index)
                            (addrs (gather-all-paging-structure-qword-addresses x86)))
                 (:instance xlate-equiv-entries-and-page-present
                            (e1 val)
                            (e2 (rm-low-64 (pml4-table-entry-addr
                                            lin-addr
                                            (mv-nth 1 (pml4-table-base-addr x86)))
                                           x86)))
                 (:instance xlate-equiv-entries-and-page-size
                            (e1 val)
                            (e2 (rm-low-64 (pml4-table-entry-addr
                                            lin-addr
                                            (mv-nth 1 (pml4-table-base-addr x86)))
                                           x86)))
                 (:instance xlate-equiv-entries-and-logtail
                            (e1 val)
                            (e2 (rm-low-64 (pml4-table-entry-addr
                                            lin-addr
                                            (mv-nth 1 (pml4-table-base-addr x86)))
                                           x86))
                            (n 12)))
           :in-theory (e/d* (page-dir-ptr-table-entry-addr-found-p)
                            (member-list-p-and-disjoint-p-with-addr-range-8-lemma
                             member-list-p-and-mult-8-qword-paddr-list-listp)))))

;; Page Directory:

(defthm page-directory-base-addr-and-wm-low-64-entry-addr
  (implies (and
            (equal addrs (gather-all-paging-structure-qword-addresses x86))
            (member-list-p index addrs)
            (xlate-equiv-entries val (rm-low-64 index x86))
            (unsigned-byte-p 64 val)
            (page-dir-ptr-table-entry-addr-found-p lin-addr x86))
           (equal (page-directory-base-addr lin-addr (wm-low-64 index val x86))
                  (page-directory-base-addr lin-addr x86)))
  :hints (("Goal"
           :use ((:instance member-list-p-and-disjoint-p-with-addr-range-8-lemma
                            (index index)
                            (addr (page-dir-ptr-table-entry-addr
                                   lin-addr
                                   (mv-nth 1 (page-dir-ptr-table-base-addr lin-addr x86))))
                            (addrs (gather-all-paging-structure-qword-addresses x86)))
                 (:instance member-list-p-and-mult-8-qword-paddr-list-listp
                            (index index)
                            (addrs (gather-all-paging-structure-qword-addresses x86)))
                 (:instance xlate-equiv-entries-and-logtail
                            (e1 val)
                            (e2 (rm-low-64 (page-dir-ptr-table-entry-addr
                                            lin-addr
                                            (mv-nth 1 (page-dir-ptr-table-base-addr lin-addr x86)))
                                           x86))
                            (n 12))
                 (:instance xlate-equiv-entries-and-page-size
                            (e1 val)
                            (e2 (rm-low-64 (page-dir-ptr-table-entry-addr
                                            lin-addr
                                            (mv-nth 1 (page-dir-ptr-table-base-addr lin-addr x86)))
                                           x86))))
           :in-theory (e/d* (page-directory-base-addr)
                            (member-list-p-and-disjoint-p-with-addr-range-8-lemma
                             member-list-p-and-mult-8-qword-paddr-list-listp)))))

(defthm page-directory-entry-addr-found-p-and-wm-low-64-entry-addr
  (implies (and
            (equal addrs (gather-all-paging-structure-qword-addresses x86))
            (member-list-p index addrs)
            (xlate-equiv-entries val (rm-low-64 index x86))
            (unsigned-byte-p 64 val)
            (page-dir-ptr-table-entry-addr-found-p lin-addr x86))
           (equal (page-directory-entry-addr-found-p lin-addr (wm-low-64 index val x86))
                  (page-directory-entry-addr-found-p lin-addr x86)))
  :hints (("Goal"
           :use ((:instance member-list-p-and-disjoint-p-with-addr-range-8-lemma
                            (index index)
                            (addr (page-dir-ptr-table-entry-addr
                                   lin-addr
                                   (mv-nth 1 (page-dir-ptr-table-base-addr lin-addr x86))))
                            (addrs (gather-all-paging-structure-qword-addresses x86)))
                 (:instance member-list-p-and-mult-8-qword-paddr-list-listp
                            (index index)
                            (addrs (gather-all-paging-structure-qword-addresses x86)))
                 (:instance xlate-equiv-entries-and-page-present
                            (e1 val)
                            (e2 (rm-low-64 (page-dir-ptr-table-entry-addr
                                            lin-addr
                                            (mv-nth 1 (page-dir-ptr-table-base-addr lin-addr x86)))
                                           x86)))
                 (:instance xlate-equiv-entries-and-page-size
                            (e1 val)
                            (e2 (rm-low-64 (page-dir-ptr-table-entry-addr
                                            lin-addr
                                            (mv-nth 1 (page-dir-ptr-table-base-addr lin-addr x86)))
                                           x86)))
                 (:instance xlate-equiv-entries-and-logtail
                            (e1 val)
                            (e2 (rm-low-64 (page-dir-ptr-table-entry-addr
                                            lin-addr
                                            (mv-nth 1 (page-dir-ptr-table-base-addr lin-addr x86)))
                                           x86))
                            (n 12)))
           :in-theory (e/d* (page-directory-entry-addr-found-p)
                            (member-list-p-and-disjoint-p-with-addr-range-8-lemma
                             member-list-p-and-mult-8-qword-paddr-list-listp)))))

;; Page Table:

(defthm page-table-base-addr-and-wm-low-64-entry-addr
  (implies (and
            (equal addrs (gather-all-paging-structure-qword-addresses x86))
            (member-list-p index addrs)
            (xlate-equiv-entries val (rm-low-64 index x86))
            (unsigned-byte-p 64 val)
            (page-directory-entry-addr-found-p lin-addr x86))
           (equal (page-table-base-addr lin-addr (wm-low-64 index val x86))
                  (page-table-base-addr lin-addr x86)))
  :hints (("Goal"
           :use ((:instance member-list-p-and-disjoint-p-with-addr-range-8-lemma
                            (index index)
                            (addr (page-directory-entry-addr
                                   lin-addr
                                   (mv-nth 1 (page-directory-base-addr lin-addr x86))))
                            (addrs (gather-all-paging-structure-qword-addresses x86)))
                 (:instance member-list-p-and-mult-8-qword-paddr-list-listp
                            (index index)
                            (addrs (gather-all-paging-structure-qword-addresses x86)))
                 (:instance xlate-equiv-entries-and-logtail
                            (e1 val)
                            (e2 (rm-low-64 (page-directory-entry-addr
                                            lin-addr
                                            (mv-nth 1 (page-directory-base-addr lin-addr x86)))
                                           x86))
                            (n 12))
                 (:instance xlate-equiv-entries-and-page-present
                            (e1 val)
                            (e2 (rm-low-64
                                 (page-directory-entry-addr
                                  lin-addr
                                  (mv-nth 1 (page-directory-base-addr lin-addr x86)))
                                 x86)))
                 (:instance xlate-equiv-entries-and-page-size
                            (e1 val)
                            (e2 (rm-low-64
                                 (page-directory-entry-addr
                                  lin-addr
                                  (mv-nth 1 (page-directory-base-addr lin-addr x86)))
                                 x86))))
           :in-theory (e/d* (page-table-base-addr)
                            (member-list-p-and-disjoint-p-with-addr-range-8-lemma
                             member-list-p-and-mult-8-qword-paddr-list-listp)))))

(defthm page-table-entry-addr-found-p-and-wm-low-64-entry-addr
  (implies (and
            (equal addrs (gather-all-paging-structure-qword-addresses x86))
            (member-list-p index addrs)
            (xlate-equiv-entries val (rm-low-64 index x86))
            (unsigned-byte-p 64 val)
            (page-directory-entry-addr-found-p lin-addr x86))
           (equal (page-table-entry-addr-found-p lin-addr (wm-low-64 index val x86))
                  (page-table-entry-addr-found-p lin-addr x86)))
  :hints (("Goal"
           :use ((:instance member-list-p-and-disjoint-p-with-addr-range-8-lemma
                            (index index)
                            (addr (page-directory-entry-addr
                                   lin-addr
                                   (mv-nth 1 (page-directory-base-addr lin-addr x86))))
                            (addrs (gather-all-paging-structure-qword-addresses x86)))
                 (:instance member-list-p-and-mult-8-qword-paddr-list-listp
                            (index index)
                            (addrs (gather-all-paging-structure-qword-addresses x86)))
                 (:instance xlate-equiv-entries-and-page-present
                            (e1 val)
                            (e2 (rm-low-64 (page-directory-entry-addr
                                            lin-addr
                                            (mv-nth 1 (page-directory-base-addr lin-addr x86)))
                                           x86)))
                 (:instance xlate-equiv-entries-and-page-size
                            (e1 val)
                            (e2 (rm-low-64 (page-directory-entry-addr
                                            lin-addr
                                            (mv-nth 1 (page-directory-base-addr lin-addr x86)))
                                           x86)))
                 (:instance xlate-equiv-entries-and-logtail
                            (e1 val)
                            (e2 (rm-low-64 (page-directory-entry-addr
                                            lin-addr
                                            (mv-nth 1 (page-directory-base-addr lin-addr x86)))
                                           x86))
                            (n 12)))
           :in-theory (e/d* (page-table-entry-addr-found-p)
                            (member-list-p-and-disjoint-p-with-addr-range-8-lemma
                             member-list-p-and-mult-8-qword-paddr-list-listp)))))

;; ======================================================================

;; Page traversals (R/W) and XR/XW RoW and WoW Theorems:

;; Page Table:

(defthm xr-ia32e-la-to-pa-PT-mem-disjoint-from-paging-structures-state
  (implies (and (page-directory-entry-addr-found-p lin-addr x86)
                (pairwise-disjoint-p-aux
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
                                    ia32e-la-to-pa-page-table
                                    pairwise-disjoint-p-aux)
                                   (bitops::logand-with-negated-bitmask)))))

(defthm ia32e-la-to-pa-PT-xw-mem-disjoint-from-paging-structures-values
  (implies (and (page-directory-entry-addr-found-p lin-addr x86)
                (pairwise-disjoint-p-aux
                 (list index)
                 (open-qword-paddr-list-list
                  (gather-all-paging-structure-qword-addresses x86)))
                (physical-address-p index)
                (unsigned-byte-p 8 val))
           (and (equal (mv-nth 0
                               (ia32e-la-to-pa-PT
                                lin-addr u-s-acc wp smep nxe r-w-x cpl
                                (xw :mem index val x86)))
                       (mv-nth 0
                               (ia32e-la-to-pa-PT
                                lin-addr u-s-acc wp smep nxe r-w-x cpl
                                x86)))
                (equal (mv-nth 1
                               (ia32e-la-to-pa-PT
                                lin-addr u-s-acc wp smep nxe r-w-x cpl
                                (xw :mem index val x86)))
                       (mv-nth 1
                               (ia32e-la-to-pa-PT
                                lin-addr u-s-acc wp smep nxe r-w-x cpl
                                x86)))))
  :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa-PT
                                    ia32e-la-to-pa-page-table)
                                   (bitops::logand-with-negated-bitmask)))))

(defthm ia32e-la-to-pa-PT-xw-mem-disjoint-from-paging-structures-state
  (implies (and (page-directory-entry-addr-found-p lin-addr x86)
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
  :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa-PT
                                    ia32e-la-to-pa-page-table
                                    pairwise-disjoint-p-aux)
                                   (bitops::logand-with-negated-bitmask)))))

;; Page Directory:

(defthm xr-ia32e-la-to-pa-PD-mem-disjoint-from-paging-structures-state
  (implies (and (page-directory-entry-addr-found-p lin-addr x86)
                (pairwise-disjoint-p-aux
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
           :use ((:instance xr-ia32e-la-to-pa-PT-mem-disjoint-from-paging-structures-state
                            (u-s-acc (page-user-supervisor
                                      (rm-low-64 (page-directory-entry-addr
                                                  lin-addr
                                                  (mv-nth 1 (page-directory-base-addr lin-addr x86))) x86)))))
           :in-theory (e/d* (ia32e-la-to-pa-PD
                             ia32e-la-to-pa-page-directory
                             pairwise-disjoint-p-aux)
                            (bitops::logand-with-negated-bitmask
                             xr-ia32e-la-to-pa-PT-mem-disjoint-from-paging-structures-state)))))

(defthm ia32e-la-to-pa-PD-xw-mem-disjoint-from-paging-structures-values
  (implies (and (page-directory-entry-addr-found-p lin-addr x86)
                (pairwise-disjoint-p-aux
                 (list index)
                 (open-qword-paddr-list-list
                  (gather-all-paging-structure-qword-addresses x86)))
                (physical-address-p index)
                (unsigned-byte-p 8 val))
           (and (equal (mv-nth 0
                               (ia32e-la-to-pa-PD
                                lin-addr wp smep nxe r-w-x cpl
                                (xw :mem index val x86)))
                       (mv-nth 0
                               (ia32e-la-to-pa-PD
                                lin-addr wp smep nxe r-w-x cpl
                                x86)))
                (equal (mv-nth 1
                               (ia32e-la-to-pa-PD
                                lin-addr wp smep nxe r-w-x cpl
                                (xw :mem index val x86)))
                       (mv-nth 1
                               (ia32e-la-to-pa-PD
                                lin-addr wp smep nxe r-w-x cpl
                                x86)))))
  :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa-PD
                                    ia32e-la-to-pa-page-directory)
                                   (bitops::logand-with-negated-bitmask)))))

(defthm ia32e-la-to-pa-PD-xw-mem-disjoint-from-paging-structures-state
  (implies (and (paging-entries-found-p lin-addr x86)
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
           :use ((:instance ia32e-la-to-pa-PT-xw-mem-disjoint-from-paging-structures-state
                            (u-s-acc (page-user-supervisor
                                      (rm-low-64
                                       (page-directory-entry-addr
                                        lin-addr
                                        (mv-nth 1 (page-directory-base-addr lin-addr x86)))
                                       x86)))))
           :in-theory (e/d* (ia32e-la-to-pa-PD
                             ia32e-la-to-pa-page-directory
                             pairwise-disjoint-p-aux
                             paging-entries-found-p)
                            (bitops::logand-with-negated-bitmask
                             unsigned-byte-p
                             signed-byte-p
                             ia32e-la-to-pa-PT-xw-mem-disjoint-from-paging-structures-state)))))

;; Page Directory Pointer Table:

(defthm xr-ia32e-la-to-pa-PDPT-mem-disjoint-from-paging-structures-state
  (implies (and (paging-entries-found-p lin-addr x86)
                (pairwise-disjoint-p-aux
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
           :use ((:instance xr-ia32e-la-to-pa-PD-mem-disjoint-from-paging-structures-state))
           :in-theory (e/d* (ia32e-la-to-pa-PDPT
                             ia32e-la-to-pa-page-dir-ptr-table
                             paging-entries-found-p
                             pairwise-disjoint-p-aux)
                            (bitops::logand-with-negated-bitmask
                             xr-ia32e-la-to-pa-PD-mem-disjoint-from-paging-structures-state
                             unsigned-byte-p
                             signed-byte-p)))))

(defthm ia32e-la-to-pa-PDPT-xw-mem-disjoint-from-paging-structures-values
  (implies (and (paging-entries-found-p lin-addr x86)
                (pairwise-disjoint-p-aux
                 (list index)
                 (open-qword-paddr-list-list
                  (gather-all-paging-structure-qword-addresses x86)))
                (physical-address-p index)
                (unsigned-byte-p 8 val))
           (and (equal (mv-nth 0
                               (ia32e-la-to-pa-PDPT
                                lin-addr wp smep nxe r-w-x cpl
                                (xw :mem index val x86)))
                       (mv-nth 0
                               (ia32e-la-to-pa-PDPT
                                lin-addr wp smep nxe r-w-x cpl
                                x86)))
                (equal (mv-nth 1
                               (ia32e-la-to-pa-PDPT
                                lin-addr wp smep nxe r-w-x cpl
                                (xw :mem index val x86)))
                       (mv-nth 1
                               (ia32e-la-to-pa-PDPT
                                lin-addr wp smep nxe r-w-x cpl
                                x86)))))
  :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa-PDPT
                                    ia32e-la-to-pa-page-dir-ptr-table
                                    paging-entries-found-p)
                                   (bitops::logand-with-negated-bitmask
                                    unsigned-byte-p
                                    signed-byte-p)))))

(defthm ia32e-la-to-pa-PDPT-xw-mem-disjoint-from-paging-structures-state
  (implies (and (paging-entries-found-p lin-addr x86)
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
           :use ((:instance ia32e-la-to-pa-PD-xw-mem-disjoint-from-paging-structures-state))
           :in-theory (e/d* (ia32e-la-to-pa-PDPT
                             ia32e-la-to-pa-page-dir-ptr-table
                             pairwise-disjoint-p-aux
                             paging-entries-found-p)
                            (bitops::logand-with-negated-bitmask
                             ia32e-la-to-pa-PD-xw-mem-disjoint-from-paging-structures-state
                             unsigned-byte-p
                             signed-byte-p)))))

;; PML4 Table:

(defthm xr-ia32e-la-to-pa-PML4T-mem-disjoint-from-paging-structures-state
  (implies (and (paging-entries-found-p lin-addr x86)
                (pairwise-disjoint-p-aux
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

(defthm ia32e-la-to-pa-PML4T-xw-mem-disjoint-from-paging-structures-values
  (implies (and (paging-entries-found-p lin-addr x86)
                (pairwise-disjoint-p-aux
                 (list index)
                 (open-qword-paddr-list-list
                  (gather-all-paging-structure-qword-addresses x86)))
                (physical-address-p index)
                (unsigned-byte-p 8 val))
           (and (equal (mv-nth 0
                               (ia32e-la-to-pa-PML4T
                                lin-addr wp smep nxe r-w-x cpl
                                (xw :mem index val x86)))
                       (mv-nth 0
                               (ia32e-la-to-pa-PML4T
                                lin-addr wp smep nxe r-w-x cpl
                                x86)))
                (equal (mv-nth 1
                               (ia32e-la-to-pa-PML4T
                                lin-addr wp smep nxe r-w-x cpl
                                (xw :mem index val x86)))
                       (mv-nth 1
                               (ia32e-la-to-pa-PML4T
                                lin-addr wp smep nxe r-w-x cpl
                                x86)))))
  :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa-PML4T)
                                   (bitops::logand-with-negated-bitmask)))))

(defthm ia32e-la-to-pa-PML4T-xw-mem-disjoint-from-paging-structures-state
  (implies (and (paging-entries-found-p lin-addr x86)
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
           :use ((:instance ia32e-la-to-pa-PDPT-xw-mem-disjoint-from-paging-structures-state))
           :in-theory (e/d* (ia32e-la-to-pa-PML4T
                             pairwise-disjoint-p-aux
                             paging-entries-found-p)
                            (bitops::logand-with-negated-bitmask
                             ia32e-la-to-pa-PDPT-xw-mem-disjoint-from-paging-structures-state
                             unsigned-byte-p
                             signed-byte-p)))))

;; Top-level Paging Translation Function:

(defthm ia32e-entries-found-la-to-pa-xr-mem-disjoint-from-paging-structures-state
  (implies (and (paging-entries-found-p lin-addr x86)
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

(defthm ia32e-entries-found-la-to-pa-xw-mem-disjoint-from-paging-structures-values
  (implies (and (paging-entries-found-p lin-addr x86)
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
  :hints (("Goal" :in-theory (e/d* (ia32e-entries-found-la-to-pa)
                                   (bitops::logand-with-negated-bitmask)))))

(defthm ia32e-entries-found-la-to-pa-xw-mem-disjoint-from-paging-structures-state
  (implies (and (paging-entries-found-p lin-addr x86)
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
