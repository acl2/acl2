;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

;; WORK IN PROGRESS (Thursday, December 10 2015)

;; This book will be folded into books under paging-top. For now, this
;; is a "hanging" book --- not included by anything else.

(in-package "X86ISA")
(include-book "paging-top" :ttags :all)

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))

(local (in-theory (e/d (entry-found-p-and-lin-addr
                        entry-found-p-and-good-paging-structures-x86p)
                       (signed-byte-p
                        unsigned-byte-p))))

;; ======================================================================

;; *-base-addr and wm-low-64, with write to both a *-entry-addr and an
;; *-address disjoint from the paging structures:

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

(defthm good-paging-structures-x86p-implies-mult-8-qword-paddr-list-listp-paging-structure-addrs
  ;; From system-level-memory-utils.lisp
  ;; Make this non-local.
  (implies (good-paging-structures-x86p x86)
           (mult-8-qword-paddr-list-listp
            (gather-all-paging-structure-qword-addresses x86)))
  :hints (("Goal" :in-theory (e/d* (good-paging-structures-x86p) ()))))

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

;; ======================================================================

;; (i-am-here)

;; (defthm ia32e-la-to-pa-PT-state-WoW-no-page-fault
;;   (implies (and (page-table-entry-addr-found-p lin-addr-1 x86)
;;                 (page-directory-entry-addr-found-p lin-addr-1 x86) ;;
;;                 (page-table-entry-addr-found-p lin-addr-2 x86)
;;                 (page-directory-entry-addr-found-p lin-addr-2 x86) ;;
;;                 (not
;;                  (mv-nth 0
;;                          (page-table-entry-no-page-fault-p
;;                           lin-addr-1
;;                           (rm-low-64
;;                            (page-table-entry-addr
;;                             lin-addr-1
;;                             (mv-nth 1 (page-table-base-addr lin-addr-1 x86)))
;;                            x86)
;;                           u-s-acc-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)))
;;                 (not
;;                  (mv-nth
;;                   0
;;                   (page-table-entry-no-page-fault-p
;;                    lin-addr-2
;;                    (rm-low-64
;;                     (page-table-entry-addr
;;                      lin-addr-2
;;                      (mv-nth 1 (page-table-base-addr lin-addr-2 x86)))
;;                     x86)
;;                    u-s-acc-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
;;            (equal
;;             (mv-nth
;;              2
;;              (ia32e-la-to-pa-PT
;;               lin-addr-1 u-s-acc-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
;;               (mv-nth
;;                2
;;                (ia32e-la-to-pa-PT
;;                 lin-addr-2 u-s-acc-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
;;             (mv-nth
;;              2
;;              (ia32e-la-to-pa-PT
;;               lin-addr-2 u-s-acc-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2
;;               (mv-nth
;;                2
;;                (ia32e-la-to-pa-PT
;;                 lin-addr-1 u-s-acc-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86))))))
;;   :hints (("Goal"
;;            :in-theory (e/d* (ia32e-la-to-pa-PT
;;                              ia32e-la-to-pa-page-table)
;;                             (bitops::logand-with-negated-bitmask
;;                              bitops::logior-equal-0)))))

;; (defthm ia32e-entries-found-la-to-pa-WoW-self
;;   (implies
;;    (and
;;     (paging-entries-found-p lin-addr-1 x86)
;;     (paging-entries-found-p lin-addr-2 x86)
;;     (not (mv-nth 0 (ia32e-entries-found-la-to-pa lin-addr-1 r-w-x-1 cpl-1 x86)))
;;     (not (mv-nth 0 (ia32e-entries-found-la-to-pa lin-addr-2 r-w-x-2 cpl-2 x86)))
;;     (not (programmer-level-mode x86)))
;;    (equal
;;     (mv-nth
;;      2
;;      (ia32e-entries-found-la-to-pa
;;       lin-addr-1 r-w-x-1 cpl-1
;;       (mv-nth 2 (ia32e-entries-found-la-to-pa lin-addr-2 r-w-x-2 cpl-2 x86))))
;;     (mv-nth
;;      2
;;      (ia32e-entries-found-la-to-pa
;;       lin-addr-2 r-w-x-2 cpl-2
;;       (mv-nth 2 (ia32e-entries-found-la-to-pa lin-addr-1 r-w-x-1 cpl-1 x86)))))))
