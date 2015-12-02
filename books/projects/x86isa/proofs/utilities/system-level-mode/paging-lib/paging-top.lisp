;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")
(include-book "paging-pml4-table-lemmas" :ttags :all)

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))

(local (in-theory (e/d (entry-found-p-and-lin-addr
                        entry-found-p-and-good-paging-structures-x86p)
                       ())))

;; ======================================================================

(defsection reasoning-about-page-tables
  :parents (proof-utilities)

  :short "Reasoning about paging data structures"

  :long "<p>WORK IN PROGRESS...</p>

<p>This doc topic will be updated in later commits...</p>"
  )

(local (xdoc::set-default-parents reasoning-about-page-tables))

;; ======================================================================

(defthmd not-good-paging-structures-x86p-and-ia32e-la-to-pa-PML4T
  (implies (not (good-paging-structures-x86p x86))
           (and (equal (mv-nth
                        0
                        (ia32e-la-to-pa-PML4T
                         lin-addr wp smep nxe r-w-x cpl x86))
                       t)
                (equal (mv-nth
                        1
                        (ia32e-la-to-pa-PML4T
                         lin-addr wp smep nxe r-w-x cpl x86))
                       0)
                (equal (mv-nth
                        2
                        (ia32e-la-to-pa-PML4T
                         lin-addr wp smep nxe r-w-x cpl x86))
                       x86)))
  :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa-PML4T) ()))))

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
                             xlate-equiv-x86s-and-page-dir-ptr-table-base-addr-address
                             xlate-equiv-x86s-and-page-dir-ptr-table-entry-addr-address
                             xlate-equiv-x86s-and-page-directory-base-addr-address
                             xlate-equiv-x86s-and-page-directory-base-addr-error
                             xlate-equiv-x86s-and-page-directory-entry-addr-address
                             xlate-equiv-x86s-and-page-table-base-addr-address
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
                             xlate-equiv-x86s-and-page-dir-ptr-table-base-addr-address
                             xlate-equiv-x86s-and-page-dir-ptr-table-entry-addr-address
                             xlate-equiv-x86s-and-page-directory-base-addr-address
                             xlate-equiv-x86s-and-page-directory-base-addr-error
                             xlate-equiv-x86s-and-page-directory-entry-addr-address
                             xlate-equiv-x86s-and-page-table-base-addr-address
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
                             xlate-equiv-x86s-and-page-dir-ptr-table-base-addr-address
                             xlate-equiv-x86s-and-page-dir-ptr-table-entry-addr-address
                             xlate-equiv-x86s-and-page-dir-ptr-table-base-addr-address
                             xlate-equiv-x86s-and-page-dir-ptr-table-entry-addr-address
                             xlate-equiv-x86s-and-page-table-base-addr-address
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
                             xlate-equiv-x86s-and-pml4-table-base-addr-address
                             xlate-equiv-x86s-and-pml4-table-entry-addr-address
                             xlate-equiv-x86s-and-pml4-table-base-addr-address
                             xlate-equiv-x86s-and-pml4-table-entry-addr-address
                             xlate-equiv-x86s-and-page-table-base-addr-address
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

;; Base addresses and structure traversals:
;; [Shilpi]: Do I even need these?

(defthm pml4-table-base-addr-and-ia32e-la-to-pa-PT
  (implies (page-table-entry-addr-found-p lin-addr x86)
           (equal (mv-nth
                   1
                   (pml4-table-base-addr
                    (mv-nth 2 (ia32e-la-to-pa-PT lin-addr u-s-acc wp smep nxe r-w-x cpl x86))))
                  (mv-nth 1 (pml4-table-base-addr x86))))
  :hints (("Goal" :in-theory (e/d* (pml4-table-base-addr) ()))))

(defthm pml4-table-base-addr-and-ia32e-la-to-pa-PD
  (implies (page-directory-entry-addr-found-p lin-addr x86)
           (equal (mv-nth
                   1
                   (pml4-table-base-addr
                    (mv-nth 2 (ia32e-la-to-pa-PD lin-addr wp smep nxe r-w-x cpl x86))))
                  (mv-nth 1 (pml4-table-base-addr x86))))
  :hints (("Goal" :in-theory (e/d* (pml4-table-base-addr) ()))))

(defthm pml4-table-base-addr-and-ia32e-la-to-pa-PDPT
  (implies (page-dir-ptr-table-entry-addr-found-p lin-addr x86)
           (equal (mv-nth
                   1
                   (pml4-table-base-addr
                    (mv-nth 2 (ia32e-la-to-pa-PDPT lin-addr wp smep nxe r-w-x cpl x86))))
                  (mv-nth 1 (pml4-table-base-addr x86))))
  :hints (("Goal" :in-theory (e/d* (pml4-table-base-addr) ()))))

(defthm pml4-table-base-addr-and-ia32e-la-to-pa-PML4T
  (implies (pml4-table-entry-addr-found-p lin-addr x86)
           (equal (mv-nth
                   1
                   (pml4-table-base-addr
                    (mv-nth 2 (ia32e-la-to-pa-PML4T lin-addr wp smep nxe r-w-x cpl x86))))
                  (mv-nth 1 (pml4-table-base-addr x86))))
  :hints (("Goal" :in-theory (e/d* (pml4-table-base-addr) ()))))

;; (defthm page-dir-ptr-table-base-addr-and-ia32e-la-to-pa-PT
;;   (implies (page-table-entry-addr-found-p lin-addr-2 x86)
;;            (equal (mv-nth
;;                    1
;;                    (page-dir-ptr-table-base-addr
;;                     lin-addr-1
;;                     (mv-nth 2 (ia32e-la-to-pa-PT lin-addr-2 u-s-acc wp smep nxe r-w-x cpl x86))))
;;                   (mv-nth 1 (page-dir-ptr-table-base-addr lin-addr-1 x86))))
;;   :hints (("Goal" :in-theory (e/d* (page-dir-ptr-table-base-addr) ()))))

;; ======================================================================
