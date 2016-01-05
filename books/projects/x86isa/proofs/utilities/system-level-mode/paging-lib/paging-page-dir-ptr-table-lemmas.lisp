;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")
(include-book "paging-page-directory-lemmas")

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))

(local (in-theory (e/d (entry-found-p-and-lin-addr
                        entry-found-p-and-good-paging-structures-x86p)
                       (unsigned-byte-p
                        signed-byte-p))))

;; ======================================================================

(defthmd not-good-paging-structures-x86p-and-ia32e-la-to-pa-PDPT
  (implies (not (good-paging-structures-x86p x86))
           (and (equal (mv-nth
                        0
                        (ia32e-la-to-pa-PDPT
                         lin-addr wp smep nxe r-w-x cpl x86))
                       t)
                (equal (mv-nth
                        1
                        (ia32e-la-to-pa-PDPT
                         lin-addr wp smep nxe r-w-x cpl x86))
                       0)
                (equal (mv-nth
                        2
                        (ia32e-la-to-pa-PDPT
                         lin-addr wp smep nxe r-w-x cpl x86))
                       x86))))

(local
 (defthmd ia32e-la-to-pa-PDPT-with-xlate-equiv-structures
   (implies (xlate-equiv-structures x86-1 x86-2)
            (and
             (equal (mv-nth
                     0
                     (ia32e-la-to-pa-PDPT
                      lin-addr wp smep nxe r-w-x cpl x86-1))
                    (mv-nth
                     0
                     (ia32e-la-to-pa-PDPT
                      lin-addr wp smep nxe r-w-x cpl x86-2)))
             (equal (mv-nth
                     1
                     (ia32e-la-to-pa-PDPT
                      lin-addr wp smep nxe r-w-x cpl x86-1))
                    (mv-nth
                     1
                     (ia32e-la-to-pa-PDPT
                      lin-addr wp smep nxe r-w-x cpl x86-2)))))
   :hints (("Goal"
            :in-theory (e/d* (ia32e-la-to-pa-page-dir-ptr-table-alt
                              entry-found-p-and-lin-addr)
                             (xlate-equiv-x86s
                              bitops::logand-with-negated-bitmask
                              bitops::logior-equal-0))
            :use ((:instance xlate-equiv-entries-and-logtail
                             (e-1 (mv-nth 2 (read-page-dir-ptr-table-entry lin-addr x86-1)))
                             (e-2 (mv-nth 2 (read-page-dir-ptr-table-entry lin-addr x86-2)))
                             (n 30))
                  (:instance xlate-equiv-entries-and-page-size
                             (e-1 (mv-nth 2 (read-page-dir-ptr-table-entry lin-addr x86-1)))
                             (e-2 (mv-nth 2 (read-page-dir-ptr-table-entry lin-addr x86-2)))))))))

(defthm mv-nth-0-ia32e-la-to-pa-PDPT-with-xlate-equiv-structures
  (implies (xlate-equiv-structures x86-1 x86-2)
           (equal (mv-nth
                   0
                   (ia32e-la-to-pa-PDPT
                    lin-addr wp smep nxe r-w-x cpl x86-1))
                  (mv-nth
                   0
                   (ia32e-la-to-pa-PDPT
                    lin-addr wp smep nxe r-w-x cpl x86-2))))
  :hints (("Goal"
           :use ((:instance ia32e-la-to-pa-PDPT-with-xlate-equiv-structures))))
  :rule-classes :congruence)

(defthm mv-nth-1-ia32e-la-to-pa-PDPT-with-xlate-equiv-structures
  (implies (xlate-equiv-structures x86-1 x86-2)
           (equal (mv-nth
                   1
                   (ia32e-la-to-pa-PDPT
                    lin-addr wp smep nxe r-w-x cpl x86-1))
                  (mv-nth
                   1
                   (ia32e-la-to-pa-PDPT
                    lin-addr wp smep nxe r-w-x cpl x86-2))))
  :hints (("Goal"
           :use ((:instance ia32e-la-to-pa-PDPT-with-xlate-equiv-structures))))
  :rule-classes :congruence)

(local (in-theory (e/d* (gather-all-paging-structure-qword-addresses-with-xlate-equiv-structures
                         xlate-equiv-structures-and-xlate-equiv-entries-at-qword-addresses?
                         xlate-equiv-entries-at-qword-addresses?-with-wm-low-64-with-different-x86)
                        ())))

(defthm xlate-equiv-x86s-with-mv-nth-2-ia32e-la-to-pa-PDPT
  (xlate-equiv-x86s
   (mv-nth 2 (ia32e-la-to-pa-PDPT lin-addr wp smep nxe r-w-x cpl x86))
   (double-rewrite x86))
  :hints (("Goal"
           :use ((:instance entry-found-p-and-good-paging-structures-x86p))
           :in-theory (e/d* (ia32e-la-to-pa-page-dir-ptr-table-alt
                             entry-found-p-and-lin-addr
                             read-page-dir-ptr-table-entry
                             xlate-equiv-x86s
                             good-paging-structures-x86p)
                            (bitops::logand-with-negated-bitmask
                             not
                             entry-found-p-and-good-paging-structures-x86p
                             no-duplicates-list-p
                             xlate-equiv-entries-at-qword-addresses?-implies-xlate-equiv-entries
                             mult-8-qword-paddr-listp
                             physical-address-p
                             good-paging-structures-x86p-and-wm-low-64-disjoint
                             (:linear acl2::loghead-upper-bound)
                             (:rewrite greater-logbitp-of-unsigned-byte-p . 2)
                             (:linear n64p-rm-low-64-paging-entry))))))


(defthm two-page-table-walks-ia32e-la-to-pa-PDPT
  (and

   (equal
    (mv-nth
     0
     (ia32e-la-to-pa-PDPT
      lin-addr-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
      (mv-nth
       2
       (ia32e-la-to-pa-PDPT
        lin-addr-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
    (mv-nth
     0
     (ia32e-la-to-pa-PDPT
      lin-addr-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)))

   (equal
    (mv-nth
     1
     (ia32e-la-to-pa-PDPT
      lin-addr-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
      (mv-nth
       2
       (ia32e-la-to-pa-PDPT
        lin-addr-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
    (mv-nth
     1
     (ia32e-la-to-pa-PDPT
      lin-addr-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86))))

  :hints (("Goal" :in-theory (e/d* () (ia32e-la-to-pa-PDPT)))))

(local (in-theory (e/d* ()
                        (gather-all-paging-structure-qword-addresses-with-xlate-equiv-structures
                         xlate-equiv-structures-and-xlate-equiv-entries-at-qword-addresses?
                         xlate-equiv-entries-at-qword-addresses?-with-wm-low-64-with-different-x86))))

(in-theory (e/d* () (ia32e-la-to-pa-PDPT)))

;; ======================================================================

;; The following come in useful when reasoning about higher paging
;; structure traversals...

(defthm gather-all-paging-structure-qword-addresses-mv-nth-2-ia32e-la-to-pa-PDPT
  (implies (good-paging-structures-x86p x86)
           (equal (gather-all-paging-structure-qword-addresses
                   (mv-nth 2 (ia32e-la-to-pa-PDPT lin-addr wp smep nxe r-w-x cpl x86)))
                  (gather-all-paging-structure-qword-addresses x86)))
  :hints (("Goal" :in-theory (e/d* () (xlate-equiv-x86s))
           :use ((:instance
                  gather-all-paging-structure-qword-addresses-with-xlate-equiv-structures
                  (x86-equiv (mv-nth 2 (ia32e-la-to-pa-PDPT lin-addr wp smep nxe r-w-x cpl x86))))))))

(defthm xlate-equiv-entries-at-qword-addresses?-mv-nth-2-ia32e-la-to-pa-PDPT
  (implies (and (equal addrs (gather-all-paging-structure-qword-addresses x86))
                (good-paging-structures-x86p x86))
           (equal (xlate-equiv-entries-at-qword-addresses?
                   addrs addrs
                   x86
                   (mv-nth 2 (ia32e-la-to-pa-PDPT lin-addr wp smep nxe r-w-x cpl x86)))
                  (xlate-equiv-entries-at-qword-addresses? addrs addrs x86 x86)))
  :hints (("Goal"
           :in-theory (e/d* ()
                            (booleanp-xlate-equiv-entries-at-qword-addresses?
                             xlate-equiv-structures-and-xlate-equiv-entries-at-qword-addresses?
                             xlate-equiv-x86s))
           :use ((:instance xlate-equiv-structures-and-xlate-equiv-entries-at-qword-addresses?
                            (addrs addrs)
                            (x86 x86)
                            (x86-equiv
                             (mv-nth 2 (ia32e-la-to-pa-PDPT lin-addr wp smep nxe r-w-x cpl x86))))
                 (:instance booleanp-xlate-equiv-entries-at-qword-addresses?
                            (addrs (gather-all-paging-structure-qword-addresses x86))
                            (x x86)
                            (y x86))
                 (:instance booleanp-xlate-equiv-entries-at-qword-addresses?
                            (addrs (gather-all-paging-structure-qword-addresses x86))
                            (x x86)
                            (y (mv-nth 2 (ia32e-la-to-pa-PDPT lin-addr wp smep nxe r-w-x cpl x86))))))))

;; ======================================================================
