;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")
(include-book "paging-page-dir-ptr-table-lemmas")

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))

(local (in-theory (e/d (entry-found-p-and-lin-addr
                        entry-found-p-and-good-paging-structures-x86p)
                       (unsigned-byte-p
                        signed-byte-p))))

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
                       x86))))

(local (in-theory (e/d (not-good-paging-structures-x86p-and-ia32e-la-to-pa-PML4T)
                       ())))

(local
 (defthmd ia32e-la-to-pa-PML4T-with-xlate-equiv-x86s
   (implies (xlate-equiv-x86s x86-1 x86-2)
            (and
             (equal (mv-nth
                     0
                     (ia32e-la-to-pa-PML4T
                      lin-addr wp smep nxe r-w-x cpl x86-1))
                    (mv-nth
                     0
                     (ia32e-la-to-pa-PML4T
                      lin-addr wp smep nxe r-w-x cpl x86-2)))
             (equal (mv-nth
                     1
                     (ia32e-la-to-pa-PML4T
                      lin-addr wp smep nxe r-w-x cpl x86-1))
                    (mv-nth
                     1
                     (ia32e-la-to-pa-PML4T
                      lin-addr wp smep nxe r-w-x cpl x86-2)))))
   :hints (("Goal"
            :in-theory (e/d* (ia32e-la-to-pa-pml4-table
                              entry-found-p-and-lin-addr)
                             (xlate-equiv-x86s
                              bitops::logand-with-negated-bitmask
                              bitops::logior-equal-0))
            :use ((:instance xlate-equiv-entries-and-page-size
                             (e-1 (mv-nth 2 (read-pml4-table-entry lin-addr x86-1)))
                             (e-2 (mv-nth 2 (read-pml4-table-entry lin-addr x86-2)))))))))


(defthm mv-nth-0-ia32e-la-to-pa-PML4T-with-xlate-equiv-x86s
  (implies (xlate-equiv-x86s x86-1 x86-2)
           (equal (mv-nth
                   0
                   (ia32e-la-to-pa-PML4T
                    lin-addr wp smep nxe r-w-x cpl x86-1))
                  (mv-nth
                   0
                   (ia32e-la-to-pa-PML4T
                    lin-addr wp smep nxe r-w-x cpl x86-2))))
  :hints (("Goal"
           :use ((:instance ia32e-la-to-pa-PML4T-with-xlate-equiv-x86s))))
  :rule-classes :congruence)

(defthm mv-nth-1-ia32e-la-to-pa-PML4T-with-xlate-equiv-x86s
  (implies (xlate-equiv-x86s x86-1 x86-2)
           (equal (mv-nth
                   1
                   (ia32e-la-to-pa-PML4T
                    lin-addr wp smep nxe r-w-x cpl x86-1))
                  (mv-nth
                   1
                   (ia32e-la-to-pa-PML4T
                    lin-addr wp smep nxe r-w-x cpl x86-2))))
  :hints (("Goal"
           :use ((:instance ia32e-la-to-pa-PML4T-with-xlate-equiv-x86s))))
  :rule-classes :congruence)

(local (in-theory (e/d* (gather-all-paging-structure-qword-addresses-with-xlate-equiv-x86s
                         xlate-equiv-x86s-and-xlate-equiv-entries-at-qword-addresses?
                         xlate-equiv-entries-at-qword-addresses?-with-wm-low-64-with-different-x86)
                        ())))

(defthm xlate-equiv-x86s-with-mv-nth-2-ia32e-la-to-pa-PML4T
  (xlate-equiv-x86s
   (mv-nth 2 (ia32e-la-to-pa-PML4T lin-addr wp smep nxe r-w-x cpl x86))
   (double-rewrite x86))
  :hints (("Goal"
           :use ((:instance entry-found-p-and-good-paging-structures-x86p)
                 (:instance gather-all-paging-structure-qword-addresses-wm-low-64-different-x86
                            (x86-equiv (mv-nth
                                        2
                                        (ia32e-la-to-pa-PDPT
                                         lin-addr wp smep nxe r-w-x cpl x86)))
                            (index (pml4-table-entry-addr
                                    lin-addr (mv-nth 1 (pml4-table-base-addr x86))))
                            (val (set-accessed-bit
                                  (rm-low-64 (pml4-table-entry-addr
                                              lin-addr (mv-nth 1 (pml4-table-base-addr x86)))
                                             x86)))
                            (addrs (gather-all-paging-structure-qword-addresses x86))
                            (x86 x86)))
           :in-theory (e/d* (ia32e-la-to-pa-pml4-table
                             read-pml4-table-entry
                             entry-found-p-and-lin-addr
                             good-paging-structures-x86p)
                            (bitops::logand-with-negated-bitmask
                             xlate-equiv-x86s
                             entry-found-p-and-good-paging-structures-x86p
                             no-duplicates-list-p
                             gather-all-paging-structure-qword-addresses-wm-low-64-different-x86)))))


(defthm two-page-table-walks-ia32e-la-to-pa-PML4T
  (and

   (equal
    (mv-nth
     0
     (ia32e-la-to-pa-PML4T
      lin-addr-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
      (mv-nth
       2
       (ia32e-la-to-pa-PML4T
        lin-addr-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
    (mv-nth
     0
     (ia32e-la-to-pa-PML4T
      lin-addr-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)))

   (equal
    (mv-nth
     1
     (ia32e-la-to-pa-PML4T
      lin-addr-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
      (mv-nth
       2
       (ia32e-la-to-pa-PML4T
        lin-addr-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
    (mv-nth
     1
     (ia32e-la-to-pa-PML4T
      lin-addr-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86))))

  :hints (("Goal" :in-theory (e/d* () (ia32e-la-to-pa-PML4T)))))

(local (in-theory (e/d* ()
                        (gather-all-paging-structure-qword-addresses-with-xlate-equiv-x86s
                         xlate-equiv-x86s-and-xlate-equiv-entries-at-qword-addresses?
                         xlate-equiv-entries-at-qword-addresses?-with-wm-low-64-with-different-x86))))

(in-theory (e/d* () (ia32e-la-to-pa-PML4T)))

;; ======================================================================

(defthm gather-all-paging-structure-qword-addresses-mv-nth-2-ia32e-la-to-pa-PML4T
  (implies (good-paging-structures-x86p x86)
           (equal (gather-all-paging-structure-qword-addresses
                   (mv-nth 2 (ia32e-la-to-pa-PML4T lin-addr wp smep nxe r-w-x cpl x86)))
                  (gather-all-paging-structure-qword-addresses x86)))
  :hints (("Goal"
           :use ((:instance
                  gather-all-paging-structure-qword-addresses-with-xlate-equiv-x86s
                  (x86-equiv (mv-nth 2 (ia32e-la-to-pa-PML4T lin-addr wp smep nxe r-w-x cpl x86))))))))

(defthm xlate-equiv-entries-at-qword-addresses?-mv-nth-2-ia32e-la-to-pa-PML4T
  (implies (and (equal addrs (gather-all-paging-structure-qword-addresses x86))
                (good-paging-structures-x86p x86))
           (equal (xlate-equiv-entries-at-qword-addresses?
                   addrs addrs
                   x86
                   (mv-nth 2 (ia32e-la-to-pa-PML4T lin-addr wp smep nxe r-w-x cpl x86)))
                  (xlate-equiv-entries-at-qword-addresses? addrs addrs x86 x86)))
  :hints (("Goal"
           :use ((:instance xlate-equiv-x86s-and-xlate-equiv-entries-at-qword-addresses?
                            (addrs addrs)
                            (x86 x86)
                            (x86-equiv
                             (mv-nth 2 (ia32e-la-to-pa-PML4T lin-addr wp smep nxe r-w-x cpl x86))))))))

;; ======================================================================
