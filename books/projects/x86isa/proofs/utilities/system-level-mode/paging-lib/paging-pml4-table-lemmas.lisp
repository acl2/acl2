;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")
(include-book "paging-page-dir-ptr-table-lemmas")

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))

(local (in-theory (e/d (entry-found-p-and-lin-addr
                        entry-found-p-and-good-paging-structures-x86p)
                       ())))

;; ======================================================================

(local
 (defthmd ia32e-la-to-pa-PML4T-with-xlate-equiv-x86s
   ;; TO-DO: Speed this up.
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
                              entry-found-p-and-lin-addr
                              PML4-TABLE-ENTRY-ADDR-FOUND-P
                              PAGING-ENTRY-NO-PAGE-FAULT-P
                              PAGE-FAULT-EXCEPTION)
                             (xlate-equiv-x86s
                              xlate-equiv-x86s-and-page-table-entry-addr-address
                              page-table-entry-addr-found-p-and-xlate-equiv-x86s
                              ia32e-la-to-pa-PT-with-xlate-equiv-x86s
                              xlate-equiv-x86s-and-pml4-table-entry-addr-value
                              xlate-equiv-x86s-and-pml4-table-base-addr-address
                              xlate-equiv-x86s-and-pml4-table-entry-addr-address
                              xlate-equiv-x86s-and-page-table-base-addr-address
                              pml4-table-entry-addr-found-p-and-xlate-equiv-x86s
                              bitops::logand-with-negated-bitmask
                              unsigned-byte-p
                              signed-byte-p
                              bitops::logior-equal-0))
            :use ((:instance xlate-equiv-x86s-and-pml4-table-entry-addr-value)
                  (:instance xlate-equiv-x86s-and-pml4-table-base-addr-address)
                  (:instance pml4-table-entry-addr-found-p-and-xlate-equiv-x86s)
                  (:instance pml4-table-entry-addr-found-p-and-xlate-equiv-x86s
                             (x86-1 x86-2)
                             (x86-2 x86-1))
                  (:instance xlate-equiv-entries-open
                             (e1 (rm-low-64
                                  (pml4-table-entry-addr
                                   lin-addr
                                   (mv-nth 1 (pml4-table-base-addr x86-2)))
                                  x86-1))
                             (e2 (rm-low-64
                                  (pml4-table-entry-addr
                                   lin-addr
                                   (mv-nth 1 (pml4-table-base-addr x86-2)))
                                  x86-2)))
                  ;; (:instance page-table-entry-addr-found-p-and-xlate-equiv-x86s)
                  ;; xlate-equiv-entries-and-loghead
                  (:instance xlate-equiv-entries-and-loghead
                             (e1 (rm-low-64
                                  (pml4-table-entry-addr
                                   lin-addr
                                   (mv-nth 1 (pml4-table-base-addr x86-2)))
                                  x86-1))
                             (e2 (rm-low-64
                                  (pml4-table-entry-addr
                                   lin-addr
                                   (mv-nth 1 (pml4-table-base-addr x86-2)))
                                  x86-2))
                             (n 1))
                  ;; xlate-equiv-entries-and-logtail
                  (:instance xlate-equiv-entries-and-logtail
                             (e1 (rm-low-64
                                  (pml4-table-entry-addr
                                   lin-addr
                                   (mv-nth 1 (pml4-table-base-addr x86-2)))
                                  x86-1))
                             (e2 (rm-low-64
                                  (pml4-table-entry-addr
                                   lin-addr
                                   (mv-nth 1 (pml4-table-base-addr x86-2)))
                                  x86-2))
                             (n 13))
                  (:instance xlate-equiv-entries-and-logtail
                             (e1 (rm-low-64
                                  (pml4-table-entry-addr
                                   lin-addr
                                   (mv-nth 1 (pml4-table-base-addr x86-2)))
                                  x86-1))
                             (e2 (rm-low-64
                                  (pml4-table-entry-addr
                                   lin-addr
                                   (mv-nth 1 (pml4-table-base-addr x86-2)))
                                  x86-2))
                             (n 30))
                  (:instance xlate-equiv-entries-and-logtail
                             (e1 (rm-low-64
                                  (pml4-table-entry-addr
                                   lin-addr
                                   (mv-nth 1 (pml4-table-base-addr x86-2)))
                                  x86-1))
                             (e2 (rm-low-64
                                  (pml4-table-entry-addr
                                   lin-addr
                                   (mv-nth 1 (pml4-table-base-addr x86-2)))
                                  x86-2))
                             (n 52))
                  ;; loghead-smaller-and-logbitp
                  (:instance loghead-smaller-and-logbitp
                             (e1 (rm-low-64
                                  (pml4-table-entry-addr
                                   lin-addr
                                   (mv-nth 1 (pml4-table-base-addr x86-2)))
                                  x86-1))
                             (e2 (rm-low-64
                                  (pml4-table-entry-addr
                                   lin-addr
                                   (mv-nth 1 (pml4-table-base-addr x86-2)))
                                  x86-2))
                             (m 1)
                             (n 5))
                  (:instance loghead-smaller-and-logbitp
                             (e1 (rm-low-64
                                  (pml4-table-entry-addr
                                   lin-addr
                                   (mv-nth 1 (pml4-table-base-addr x86-2)))
                                  x86-1))
                             (e2 (rm-low-64
                                  (pml4-table-entry-addr
                                   lin-addr
                                   (mv-nth 1 (pml4-table-base-addr x86-2)))
                                  x86-2))
                             (m 2)
                             (n 5))
                  ;; logtail-bigger-and-logbitp
                  (:instance logtail-bigger-and-logbitp
                             (e1 (rm-low-64
                                  (pml4-table-entry-addr
                                   lin-addr
                                   (mv-nth 1 (pml4-table-base-addr x86-2)))
                                  x86-1))
                             (e2 (rm-low-64
                                  (pml4-table-entry-addr
                                   lin-addr
                                   (mv-nth 1 (pml4-table-base-addr x86-2)))
                                  x86-2))
                             (m 7)
                             (n 7))
                  (:instance logtail-bigger-and-logbitp
                             (e1 (rm-low-64
                                  (pml4-table-entry-addr
                                   lin-addr
                                   (mv-nth 1 (pml4-table-base-addr x86-2)))
                                  x86-1))
                             (e2 (rm-low-64
                                  (pml4-table-entry-addr
                                   lin-addr
                                   (mv-nth 1 (pml4-table-base-addr x86-2)))
                                  x86-2))
                             (m 7)
                             (n 52))
                  (:instance logtail-bigger-and-logbitp
                             (e1 (rm-low-64
                                  (pml4-table-entry-addr
                                   lin-addr
                                   (mv-nth 1 (pml4-table-base-addr x86-2)))
                                  x86-1))
                             (e2 (rm-low-64
                                  (pml4-table-entry-addr
                                   lin-addr
                                   (mv-nth 1 (pml4-table-base-addr x86-2)))
                                  x86-2))
                             (m 7)
                             (n 63)))))))

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
   x86)
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
                             entry-found-p-and-lin-addr
                             good-paging-structures-x86p)
                            (bitops::logand-with-negated-bitmask
                             entry-found-p-and-good-paging-structures-x86p
                             xlate-equiv-x86s-and-page-table-entry-addr-address
                             xlate-equiv-x86s-and-page-table-base-addr-address
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
  (implies (and (good-paging-structures-x86p x86)
                (equal addrs (gather-all-paging-structure-qword-addresses x86)))
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

;; *-entry-addr-found-p and ia32e-la-to-pa-PML4T:

(defthm page-table-entry-addr-found-p-after-a-pml4-table-walk
  (implies (and (page-table-entry-addr-found-p lin-addr-1 x86)
                (page-table-entry-addr-found-p lin-addr-2 x86))
           (page-table-entry-addr-found-p
            lin-addr-1
            (mv-nth 2
                    (ia32e-la-to-pa-PML4T
                     lin-addr-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
  :hints (("Goal"
           :use ((:instance page-table-entry-addr-found-p-and-xlate-equiv-x86s
                            (x86-1 x86)
                            (lin-addr lin-addr-1)
                            (x86-2
                             (mv-nth 2
                                     (ia32e-la-to-pa-PML4T
                                      lin-addr-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
                 (:instance xlate-equiv-x86s-with-mv-nth-2-ia32e-la-to-pa-PML4T
                            (x86 x86)
                            (lin-addr lin-addr-2)
                            (wp wp-2)
                            (smep smep-2)
                            (nxe nxe-2)
                            (r-w-x r-w-x-2)
                            (cpl cpl-2)))
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

(defthm page-directory-entry-addr-found-p-after-a-pml4-table-walk
  (implies (and (page-directory-entry-addr-found-p lin-addr-1 x86)
                (page-directory-entry-addr-found-p lin-addr-2 x86))
           (page-directory-entry-addr-found-p
            lin-addr-1
            (mv-nth 2
                    (ia32e-la-to-pa-PML4T
                     lin-addr-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
  :hints (("Goal"
           :use ((:instance page-directory-entry-addr-found-p-and-xlate-equiv-x86s
                            (x86-1 x86)
                            (lin-addr lin-addr-1)
                            (x86-2
                             (mv-nth 2
                                     (ia32e-la-to-pa-PML4T
                                      lin-addr-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
                 (:instance xlate-equiv-x86s-with-mv-nth-2-ia32e-la-to-pa-PML4T
                            (x86 x86)
                            (lin-addr lin-addr-2)
                            (wp wp-2)
                            (smep smep-2)
                            (nxe nxe-2)
                            (r-w-x r-w-x-2)
                            (cpl cpl-2)))
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

(defthm page-dir-ptr-table-entry-addr-found-p-after-a-pml4-table-walk
  (implies (and (page-dir-ptr-table-entry-addr-found-p lin-addr-1 x86)
                (page-dir-ptr-table-entry-addr-found-p lin-addr-2 x86))
           (page-dir-ptr-table-entry-addr-found-p
            lin-addr-1
            (mv-nth 2
                    (ia32e-la-to-pa-PML4T
                     lin-addr-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
  :hints (("Goal"
           :use ((:instance page-dir-ptr-table-entry-addr-found-p-and-xlate-equiv-x86s
                            (x86-1 x86)
                            (lin-addr lin-addr-1)
                            (x86-2
                             (mv-nth 2
                                     (ia32e-la-to-pa-PML4T
                                      lin-addr-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
                 (:instance xlate-equiv-x86s-with-mv-nth-2-ia32e-la-to-pa-PML4T
                            (x86 x86)
                            (lin-addr lin-addr-2)
                            (wp wp-2)
                            (smep smep-2)
                            (nxe nxe-2)
                            (r-w-x r-w-x-2)
                            (cpl cpl-2)))
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

(defthm pml4-table-entry-addr-found-p-after-a-pml4-table-walk
  (implies (and (pml4-table-entry-addr-found-p lin-addr-1 x86)
                (pml4-table-entry-addr-found-p lin-addr-2 x86))
           (pml4-table-entry-addr-found-p
            lin-addr-1
            (mv-nth 2
                    (ia32e-la-to-pa-PML4T
                     lin-addr-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
  :hints (("Goal"
           :use ((:instance pml4-table-entry-addr-found-p-and-xlate-equiv-x86s
                            (x86-1 x86)
                            (lin-addr lin-addr-1)
                            (x86-2
                             (mv-nth 2
                                     (ia32e-la-to-pa-PML4T
                                      lin-addr-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
                 (:instance xlate-equiv-x86s-with-mv-nth-2-ia32e-la-to-pa-PML4T
                            (x86 x86)
                            (lin-addr lin-addr-2)
                            (wp wp-2)
                            (smep smep-2)
                            (nxe nxe-2)
                            (r-w-x r-w-x-2)
                            (cpl cpl-2)))
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

;; ======================================================================
