;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")
(include-book "x86-ia32e-paging-alt" :ttags :all)

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))

(local (xdoc::set-default-parents gather-paging-structures))

(local (in-theory (e/d (entry-found-p-and-lin-addr
                        entry-found-p-and-good-paging-structures-x86p)
                       ())))

;; ======================================================================

;; Driver rules (as Dave Greve says) involving xlate-equiv-x86s,
;; xlate-equiv-structures, and xlate-equiv-entries:

(defthm xlate-equiv-structures-and-xw-mem-disjoint
  (implies (and (bind-free
                 (find-an-xlate-equiv-x86
                  'xlate-equiv-structures-and-xw-mem-disjoint
                  'x86-1 x86-2)
                 (x86-1))
                (xlate-equiv-structures x86-1 (double-rewrite x86-2))
                (pairwise-disjoint-p-aux
                 (list index)
                 (open-qword-paddr-list-list
                  (gather-all-paging-structure-qword-addresses x86-1)))
                (good-paging-structures-x86p x86-1)
                (physical-address-p index)
                (unsigned-byte-p 8 val))
           (xlate-equiv-structures (xw :mem index val x86-2) x86-1))
  :hints (("Goal" :in-theory (e/d* (xlate-equiv-structures
                                    good-paging-structures-x86p)
                                   (all-mem-except-paging-structures-equal)))))

(defthm xlate-equiv-structures-and-wm-low-64-disjoint
  (implies (and (bind-free
                 (find-an-xlate-equiv-x86
                  'xlate-equiv-structures-and-wm-low-64-disjoint
                  'x86-1 x86-2)
                 (x86-1))
                (xlate-equiv-structures x86-1 (double-rewrite x86-2))
                (pairwise-disjoint-p-aux
                 (addr-range 8 index)
                 (open-qword-paddr-list-list
                  (gather-all-paging-structure-qword-addresses x86-1)))
                (good-paging-structures-x86p x86-1)
                (physical-address-p index))
           (xlate-equiv-structures (wm-low-64 index val x86-2) x86-1))
  :hints (("Goal" :in-theory (e/d* (xlate-equiv-structures good-paging-structures-x86p)
                                   (all-mem-except-paging-structures-equal)))))

(defthm xlate-equiv-structures-and-wm-low-64-entry-addr
  (implies (and (bind-free (find-an-xlate-equiv-x86
                            'xlate-equiv-structures-and-wm-low-64-entry-addr
                            'x86 x86-equiv)
                           (x86))
                (xlate-equiv-structures x86 (double-rewrite x86-equiv))
                (xlate-equiv-entries (double-rewrite val) (rm-low-64 index x86))
                (member-list-p index (gather-all-paging-structure-qword-addresses x86))
                (good-paging-structures-x86p x86)
                (x86p (wm-low-64 index val x86-equiv))
                (unsigned-byte-p 64 val))
           (xlate-equiv-structures (wm-low-64 index val x86-equiv) x86))
  :hints (("Goal"
           :use ((:instance
                  xlate-equiv-entries-at-qword-addresses?-with-wm-low-64-with-different-x86
                  (addrs (gather-all-paging-structure-qword-addresses x86))
                  (x86-1 x86)
                  (x86-2 x86-equiv)))
           :in-theory
           (e/d*
            (xlate-equiv-structures
             good-paging-structures-x86p)
            (xlate-equiv-entries-at-qword-addresses?-with-wm-low-64-with-different-x86)))))

(defthmd xlate-equiv-entries-open
  (implies (and (xlate-equiv-entries e-1 e-2)
                (unsigned-byte-p 64 e-1)
                (unsigned-byte-p 64 e-2))
           (and (equal (loghead 5 e-1) (loghead 5 e-2))
                (equal (logtail 7 e-1) (logtail 7 e-2))))
  :hints (("Goal" :in-theory (e/d* (xlate-equiv-entries) ()))))

;; (defthm xlate-equiv-structures-implies-both-or-neither-good-paging-structures
;;   ;; I could make this a congruence rule, but then I'd have to put a
;;   ;; double-rewrite everywhere I use
;;   ;; good-paging-structures-x86p. Won't that slow things down? I need
;;   ;; to try and see...
;;   (implies (and (xlate-equiv-structures x86-1 x86-2)
;;                 (good-paging-structures-x86p x86-1))
;;            (good-paging-structures-x86p x86-2))
;;   :hints (("Goal" :in-theory (e/d* (xlate-equiv-structures) ()))))

(defthm xlate-equiv-structures-and-xlate-equiv-entries-at-qword-addresses?
  (implies (and (equal addrs (gather-all-paging-structure-qword-addresses x86))
                (good-paging-structures-x86p (double-rewrite x86))
                (xlate-equiv-structures (double-rewrite x86) (double-rewrite x86-equiv)))
           (xlate-equiv-entries-at-qword-addresses?
            addrs addrs x86 x86-equiv))
  :hints (("Goal" :in-theory (e/d* (xlate-equiv-structures xlate-equiv-structures)
                                   ()))))

(local
 (defthmd xlate-equiv-structures-and-xlate-equiv-entries
   (implies (and
             (xlate-equiv-structures x86-1 x86-2)
             (member-list-p index (gather-all-paging-structure-qword-addresses x86-1))
             (good-paging-structures-x86p (double-rewrite x86-1)))
            (xlate-equiv-entries (rm-low-64 index x86-1) (rm-low-64 index x86-2)))
   :hints (("Goal" :in-theory (e/d* (xlate-equiv-structures xlate-equiv-structures)
                                    ())))))

(local
 (defthm xlate-equiv-structures-and-superior-entry-points-to-an-inferior-one-p
   (implies (and (bind-free '((x86-2 . x86-2)))
                 (xlate-equiv-structures (double-rewrite x86-1) x86-2)
                 (good-paging-structures-x86p (double-rewrite x86-1))
                 (member-list-p entry-addr
                                (gather-all-paging-structure-qword-addresses x86-1)))
            (equal (superior-entry-points-to-an-inferior-one-p entry-addr x86-1)
                   (superior-entry-points-to-an-inferior-one-p entry-addr x86-2)))
   :hints (("Goal"
            :use ((:instance xlate-equiv-structures-and-xlate-equiv-entries
                             (x86-1 x86-1)
                             (x86-2 x86-2)
                             (index entry-addr))
                  (:instance xlate-equiv-entries-and-logtail
                             (n 12)
                             (e-1 (rm-low-64 entry-addr x86-1))
                             (e-2 (rm-low-64 entry-addr x86-2)))
                  (:instance xlate-equiv-entries-and-page-size
                             (e-1 (rm-low-64 entry-addr x86-1))
                             (e-2 (rm-low-64 entry-addr x86-2))))
            :in-theory (e/d* (superior-entry-points-to-an-inferior-one-p
                              xlate-equiv-structures)
                             ())))))

;; ======================================================================

;; Some general lemmas about the gather functions:

(defthm non-nil-gather-pml4-table-qword-addresses
  (implies (and (equal pml4-table-base-addr
                       (mv-nth 1 (pml4-table-base-addr x86)))
                (physical-address-p (+ (ash 512 3) pml4-table-base-addr))
                (good-paging-structures-x86p x86))
           (gather-pml4-table-qword-addresses x86))
  :hints (("Goal"
           :in-theory (e/d* (pml4-table-base-addr
                             pml4-table-entry-addr
                             gather-pml4-table-qword-addresses)
                            ()))))

(defthm consp-gather-pml4-table-qword-addresses
  (implies (and (equal pml4-table-base-addr
                       (mv-nth 1 (pml4-table-base-addr x86)))
                (physical-address-p (+ (ash 512 3) pml4-table-base-addr))
                (good-paging-structures-x86p x86))
           (consp (gather-pml4-table-qword-addresses x86)))
  :hints (("Goal"
           :in-theory (e/d* (pml4-table-base-addr
                             pml4-table-entry-addr
                             gather-pml4-table-qword-addresses)
                            ())))
  :rule-classes (:type-prescription :rewrite))

(defthm car-gather-pml4-table-qword-addresses
  (implies (and (equal pml4-table-base-addr
                       (mv-nth 1 (pml4-table-base-addr x86)))
                (physical-address-p (+ (ash 512 3) pml4-table-base-addr))
                (good-paging-structures-x86p x86))
           (equal (car (gather-pml4-table-qword-addresses x86))
                  pml4-table-base-addr))
  :hints (("Goal"
           :expand (create-qword-address-list
                    512
                    (ash (loghead 40 (logtail 12 (xr :ctr *cr3* x86)))
                         12))
           :in-theory (e/d* (pml4-table-base-addr
                             pml4-table-entry-addr
                             gather-pml4-table-qword-addresses)
                            ()))))

(defthm non-nil-gather-qword-addresses-corresponding-to-1-entry
  (implies (and (equal (page-present (rm-low-64 paddr x86)) 1)
                (equal (page-size (rm-low-64 paddr x86)) 0)
                (physical-address-p
                 (+ (ash 512 3)
                    (ash (ia32e-page-tables-slice :reference-addr (rm-low-64 paddr x86))
                         12))))
           (gather-qword-addresses-corresponding-to-1-entry paddr x86))
  :hints (("Goal"
           :in-theory (e/d* (gather-qword-addresses-corresponding-to-1-entry)
                            ()))))

(defthm consp-gather-qword-addresses-corresponding-to-1-entry
  (implies (and (equal (page-present (rm-low-64 paddr x86)) 1)
                (equal (page-size (rm-low-64 paddr x86)) 0)
                (physical-address-p
                 (+ (ash 512 3)
                    (ash (ia32e-page-tables-slice :reference-addr (rm-low-64 paddr x86))
                         12))))
           (consp (gather-qword-addresses-corresponding-to-1-entry paddr x86)))
  :hints (("Goal"
           :in-theory (e/d* (gather-qword-addresses-corresponding-to-1-entry)
                            ())))
  :rule-classes (:type-prescription :rewrite))

(defthm car-gather-qword-addresses-corresponding-to-1-entry
  (implies (and (equal (page-present (rm-low-64 paddr x86)) 1)
                (equal (page-size (rm-low-64 paddr x86)) 0)
                (physical-address-p
                 (+ (ash 512 3)
                    (ash (ia32e-page-tables-slice :reference-addr (rm-low-64 paddr x86))
                         12))))
           (equal (car (gather-qword-addresses-corresponding-to-1-entry paddr x86))
                  (ash (ia32e-page-tables-slice :reference-addr (rm-low-64 paddr x86))
                       12)))
  :hints (("Goal"
           :expand (create-qword-address-list
                    512
                    (ash (loghead 40 (logtail 12 (rm-low-64 paddr x86)))
                         12))
           :in-theory (e/d* (gather-qword-addresses-corresponding-to-1-entry)
                            ()))))

(defthm consp-gather-qword-addresses-corresponding-to-entries
  (implies (and (consp paddr-list)
                (qword-paddr-listp paddr-list)
                (equal (page-present (rm-low-64 (car paddr-list) x86)) 1)
                (equal (page-size (rm-low-64 (car paddr-list) x86)) 0)
                (physical-address-p
                 (+ (ash 512 3)
                    (ash (ia32e-page-tables-slice :reference-addr (rm-low-64 (car paddr-list) x86))
                         12))))
           (consp
            (gather-qword-addresses-corresponding-to-entries
             paddr-list
             x86)))
  :hints (("Goal"
           :in-theory (e/d* (gather-qword-addresses-corresponding-to-entries)
                            ())))
  :rule-classes (:type-prescription :rewrite))

(defthm car-gather-qword-addresses-corresponding-to-entries
  (implies (and (consp paddr-list)
                (qword-paddr-listp paddr-list)
                (equal (page-present (rm-low-64 (car paddr-list) x86)) 1)
                (equal (page-size (rm-low-64 (car paddr-list) x86)) 0)
                (physical-address-p
                 (+ (ash 512 3)
                    (ash (ia32e-page-tables-slice :reference-addr (rm-low-64 (car paddr-list) x86))
                         12))))
           (equal
            (car (gather-qword-addresses-corresponding-to-entries paddr-list x86))
            (gather-qword-addresses-corresponding-to-1-entry (car paddr-list) x86)))
  :hints (("Goal"
           :in-theory (e/d* (gather-qword-addresses-corresponding-to-entries)
                            ()))))

(defthm gather-qword-addresses-corresponding-to-1-entry-and-to-entries
  (implies (and (physical-address-p
                 (+ (ash 512 3)
                    (ash (ia32e-page-tables-slice :reference-addr (rm-low-64 paddr x86))
                         12)))
                (qword-paddr-listp paddrs)
                (equal (page-present (rm-low-64 paddr x86)) 1)
                (equal (page-size (rm-low-64 paddr x86)) 0)
                (member-p paddr paddrs))
           (subset-list-p
            (gather-qword-addresses-corresponding-to-1-entry paddr x86)
            (gather-qword-addresses-corresponding-to-entries paddrs x86)))

  :hints (("Goal" :in-theory (e/d* (gather-qword-addresses-corresponding-to-1-entry
                                    gather-qword-addresses-corresponding-to-entries
                                    subset-p)
                                   ()))))

(defthm gather-qword-addresses-corresponding-to-entries-and-to-list-of-entries
  (implies (and (physical-address-p
                 (+ (ash 512 3)
                    (ash (ia32e-page-tables-slice :reference-addr (rm-low-64 paddr x86))
                         12)))
                (qword-paddr-list-listp paddrs-list)
                (equal (page-present (rm-low-64 paddr x86)) 1)
                (equal (page-size (rm-low-64 paddr x86)) 0)
                (member-list-p paddr paddrs-list))
           (subset-list-p
            (gather-qword-addresses-corresponding-to-1-entry paddr x86)
            (gather-qword-addresses-corresponding-to-list-of-entries
             paddrs-list x86)))

  :hints (("Goal" :in-theory (e/d* (gather-qword-addresses-corresponding-to-entries
                                    gather-qword-addresses-corresponding-to-list-of-entries
                                    subset-p)
                                   ()))))

;; ======================================================================

(local (in-theory (e/d () (unsigned-byte-p signed-byte-p))))

;; ======================================================================

;; PML4 Table:

;; PML4 Table Base and Entry Addresses are present in the output from
;; gather-all-paging-structure-qword-addresses.

(defthm pml4-table-base-addr-is-a-member-of-gather-pml4-table-qword-addresses
  (implies (and (physical-address-p (+ (ash 512 3)
                                       (mv-nth 1 (pml4-table-base-addr x86))))
                (good-paging-structures-x86p x86))
           (member-p (mv-nth 1 (pml4-table-base-addr x86))
                     (gather-pml4-table-qword-addresses x86)))
  :hints (("Goal"
           :in-theory (e/d* (pml4-table-base-addr
                             gather-pml4-table-qword-addresses)
                            ()))))

(defthm pml4-table-entry-addr-is-a-member-of-gather-pml4-table-qword-addresses
  (implies (pml4-table-entry-addr-found-p lin-addr x86)
           (member-p (pml4-table-entry-addr lin-addr (mv-nth 1 (pml4-table-base-addr x86)))
                     (gather-pml4-table-qword-addresses x86)))
  :hints (("Goal"
           :in-theory (e/d* (pml4-table-base-addr
                             pml4-table-entry-addr
                             gather-pml4-table-qword-addresses)
                            ()))))

(defthm pml4-table-base-addr-is-in-gather-all-paging-structure-qword-addresses
  (implies (and (physical-address-p
                 (+ (ash 512 3)
                    (mv-nth 1 (pml4-table-base-addr x86))))
                (good-paging-structures-x86p x86))
           (member-list-p (mv-nth 1 (pml4-table-base-addr x86))
                          (gather-all-paging-structure-qword-addresses x86)))
  :hints (("Goal"
           :in-theory (e/d* (gather-all-paging-structure-qword-addresses)
                            ()))))

(defthm pml4-table-entry-addr-is-in-gather-all-paging-structure-qword-addresses
  (implies (pml4-table-entry-addr-found-p lin-addr x86)
           (member-list-p (pml4-table-entry-addr lin-addr (mv-nth 1 (pml4-table-base-addr x86)))
                          (gather-all-paging-structure-qword-addresses x86)))
  :hints (("Goal"
           :in-theory (e/d* (gather-all-paging-structure-qword-addresses)
                            ()))))

;; Relationship of PML4 Table with xlate-equiv-structures:

(defthm xlate-equiv-structures-and-pml4-table-base-addr
  (implies (xlate-equiv-structures x86-1 x86-2)
           (equal (pml4-table-base-addr x86-1)
                  (pml4-table-base-addr x86-2)))
  :hints (("Goal" :in-theory (e/d* (pml4-table-base-addr
                                    xlate-equiv-structures)
                                   ())))
  :rule-classes :congruence)

(defthm xlate-equiv-structures-and-pml4-table-entry-addr-found-p
  (implies (xlate-equiv-structures x86-1 x86-2)
           (equal (pml4-table-entry-addr-found-p lin-addr x86-1)
                  (pml4-table-entry-addr-found-p lin-addr x86-2)))
  :hints (("Goal"
           :use ((:instance xlate-equiv-structures-and-pml4-table-base-addr))
           :in-theory (e/d* (pml4-table-entry-addr-found-p
                             xlate-equiv-structures)
                            (physical-address-p
                             xlate-equiv-structures-and-pml4-table-base-addr
                             bitops::logand-with-negated-bitmask))))
  :rule-classes :congruence)

(defthm xlate-equiv-entries-of-pml4-table
  (implies (xlate-equiv-structures x86-1 x86-2)
           (xlate-equiv-entries
            (mv-nth 2 (read-pml4-table-entry lin-addr x86-1))
            (mv-nth 2 (read-pml4-table-entry lin-addr x86-2))))
  :hints (("Goal"
           :use ((:instance pml4-table-entry-addr-is-in-gather-all-paging-structure-qword-addresses
                            (x86 x86-1))
                 (:instance xlate-equiv-entries-at-qword-addresses?-implies-xlate-equiv-entries
                            (index (pml4-table-entry-addr
                                    lin-addr (mv-nth 1 (pml4-table-base-addr x86-1))))
                            (addrs (gather-all-paging-structure-qword-addresses x86-1))))
           :in-theory
           (e/d* (read-pml4-table-entry)
                 (xlate-equiv-entries-at-qword-addresses?-implies-xlate-equiv-entries
                  xlate-equiv-x86s
                  xlate-equiv-structures
                  pml4-table-entry-addr-is-in-gather-all-paging-structure-qword-addresses
                  physical-address-p))))
  :rule-classes :congruence)

;; ======================================================================

;; Page Directory Pointer Table:

;; PDPT Base and Entry Addresses are present in the output from
;; gather-all-paging-structure-qword-addresses.

(defthm page-dir-ptr-table-base-addr-is-in-a-table-pointed-to-by-a-pml4e
  (implies (and (equal pml4-table-entry-addr
                       (pml4-table-entry-addr
                        lin-addr (mv-nth 1 (pml4-table-base-addr x86))))
                (page-dir-ptr-table-entry-addr-found-p lin-addr x86))
           (member-p
            (mv-nth 1 (page-dir-ptr-table-base-addr lin-addr x86))
            (gather-qword-addresses-corresponding-to-1-entry
             pml4-table-entry-addr x86)))
  :hints (("Goal"
           :in-theory (e/d* (gather-qword-addresses-corresponding-to-1-entry
                             read-pml4-table-entry
                             page-dir-ptr-table-entry-addr
                             page-dir-ptr-table-base-addr)
                            ()))))

(defthm page-dir-ptr-table-entry-addr-is-in-a-table-pointed-to-by-a-pml4e
  (implies (and (equal pml4-table-entry-addr
                       (pml4-table-entry-addr
                        lin-addr
                        (mv-nth 1 (pml4-table-base-addr x86))))
                (page-dir-ptr-table-entry-addr-found-p lin-addr x86))
           (member-p
            (page-dir-ptr-table-entry-addr
             lin-addr
             (mv-nth 1 (page-dir-ptr-table-base-addr lin-addr x86)))
            (gather-qword-addresses-corresponding-to-1-entry
             pml4-table-entry-addr x86)))
  :hints (("Goal"
           :in-theory (e/d* (gather-qword-addresses-corresponding-to-1-entry
                             read-pml4-table-entry
                             good-paging-structures-x86p
                             page-dir-ptr-table-entry-addr
                             page-dir-ptr-table-base-addr)
                            ()))))

(defthm pdpt-qword-paddrs-referred-to-by-pml4-base-addr-are-a-subset-of-those-by-all-pml4es
  (implies (and (equal pml4-table-base-addr (mv-nth 1 (pml4-table-base-addr x86)))
                (physical-address-p (+ (ash 512 3) pml4-table-base-addr))
                (superior-entry-points-to-an-inferior-one-p pml4-table-base-addr x86)
                (good-paging-structures-x86p x86))
           (subset-list-p
            (gather-qword-addresses-corresponding-to-1-entry pml4-table-base-addr x86)
            (gather-qword-addresses-corresponding-to-entries
             (gather-pml4-table-qword-addresses x86)
             x86))))

(defthm pdpt-qword-paddrs-referred-to-by-a-pml4e-addr-are-a-subset-of-those-by-all-pml4es
  (implies (and (equal pml4-table-base-addr (mv-nth 1 (pml4-table-base-addr x86)))
                (physical-address-p (+ (ash 512 3) pml4-table-base-addr))
                (equal pml4-table-entry-addr (pml4-table-entry-addr lin-addr pml4-table-base-addr))
                (superior-entry-points-to-an-inferior-one-p pml4-table-entry-addr x86)
                (good-paging-structures-x86p x86)
                (canonical-address-p lin-addr))
           (subset-list-p
            (gather-qword-addresses-corresponding-to-1-entry pml4-table-entry-addr x86)
            (gather-qword-addresses-corresponding-to-entries
             (gather-pml4-table-qword-addresses x86) x86)))
  :hints (("Goal" :in-theory (e/d* () (subset-list-p)))))

(defthm page-dir-ptr-table-base-addr-is-in-gather-all-paging-structure-qword-addresses
  (implies (and (equal pml4-table-base-addr (mv-nth 1 (pml4-table-base-addr x86)))
                (page-dir-ptr-table-entry-addr-found-p lin-addr x86))
           (member-list-p (mv-nth 1 (page-dir-ptr-table-base-addr lin-addr x86))
                          (gather-all-paging-structure-qword-addresses x86)))
  :hints (("Goal"
           :use ((:instance subset-list-p-and-member-list-p
                            (e (mv-nth 1 (page-dir-ptr-table-base-addr lin-addr x86)))
                            (xs (gather-qword-addresses-corresponding-to-1-entry
                                 (pml4-table-entry-addr lin-addr pml4-table-base-addr)
                                 x86))
                            (xss (gather-qword-addresses-corresponding-to-entries
                                  (gather-pml4-table-qword-addresses x86)
                                  x86))))
           :in-theory (e/d* (gather-all-paging-structure-qword-addresses)
                            (subset-list-p-and-member-list-p)))))

(defthm page-dir-ptr-table-entry-addr-is-in-gather-all-paging-structure-qword-addresses
  (implies (page-dir-ptr-table-entry-addr-found-p lin-addr x86)
           (member-list-p
            (page-dir-ptr-table-entry-addr
             lin-addr
             (mv-nth 1 (page-dir-ptr-table-base-addr lin-addr x86)))
            (gather-all-paging-structure-qword-addresses x86)))
  :hints (("Goal"
           :use ((:instance subset-list-p-and-member-list-p
                            (e (page-dir-ptr-table-entry-addr
                                lin-addr
                                (mv-nth 1 (page-dir-ptr-table-base-addr lin-addr x86))))
                            (xs (gather-qword-addresses-corresponding-to-1-entry
                                 (pml4-table-entry-addr lin-addr (mv-nth 1 (pml4-table-base-addr x86)))
                                 x86))
                            (xss (gather-qword-addresses-corresponding-to-entries
                                  (gather-pml4-table-qword-addresses x86)
                                  x86))))
           :in-theory (e/d* (gather-all-paging-structure-qword-addresses)
                            (subset-list-p-and-member-list-p)))))

;; Relationship of PDPT with xlate-equiv-structures:

(defthm xlate-equiv-structures-and-page-dir-ptr-table-base-addr
  (implies (xlate-equiv-structures x86-1 x86-2)
           (equal (page-dir-ptr-table-base-addr lin-addr x86-1)
                  (page-dir-ptr-table-base-addr lin-addr x86-2)))
  :hints (("Goal"
           :use ((:instance xlate-equiv-entries-and-logtail
                            (n 12)
                            (e-1 (mv-nth 2 (read-pml4-table-entry lin-addr x86-1)))
                            (e-2 (mv-nth 2 (read-pml4-table-entry lin-addr x86-2)))))
           :in-theory (e/d* (page-dir-ptr-table-base-addr)
                            (xlate-equiv-structures
                             xlate-equiv-entries
                             pml4-table-entry-addr-found-p
                             page-dir-ptr-table-entry-addr-found-p
                             canonical-address-p
                             physical-address-p))))
  :rule-classes :congruence)

(defthm xlate-equiv-structures-and-page-dir-ptr-table-entry-addr-found-p
  (implies (xlate-equiv-structures x86-1 x86-2)
           (equal (page-dir-ptr-table-entry-addr-found-p lin-addr x86-1)
                  (page-dir-ptr-table-entry-addr-found-p lin-addr x86-2)))
  :hints (("Goal"
           :in-theory (e/d* (page-dir-ptr-table-entry-addr-found-p)
                            (xlate-equiv-entries
                             xlate-equiv-structures
                             superior-entry-points-to-an-inferior-one-p
                             physical-address-p
                             bitops::logand-with-negated-bitmask))))
  :rule-classes :congruence)

(defthm xlate-equiv-entries-of-page-dir-ptr-table
  (implies (xlate-equiv-structures x86-1 x86-2)
           (xlate-equiv-entries
            (mv-nth 2 (read-page-dir-ptr-table-entry lin-addr x86-1))
            (mv-nth 2 (read-page-dir-ptr-table-entry lin-addr x86-2))))
  :hints (("Goal"
           :in-theory
           (e/d* (read-page-dir-ptr-table-entry)
                 (xlate-equiv-structures
                  superior-entry-points-to-an-inferior-one-p
                  xlate-equiv-entries-at-qword-addresses?-implies-xlate-equiv-entries
                  page-dir-ptr-table-entry-addr-is-in-gather-all-paging-structure-qword-addresses
                  physical-address-p))
           :use ((:instance page-dir-ptr-table-entry-addr-is-in-gather-all-paging-structure-qword-addresses
                            (x86 x86-1))
                 (:instance xlate-equiv-entries-at-qword-addresses?-implies-xlate-equiv-entries
                            (index (page-dir-ptr-table-entry-addr
                                    lin-addr (mv-nth 1 (page-dir-ptr-table-base-addr lin-addr x86-1))))
                            (addrs (gather-all-paging-structure-qword-addresses x86-1))))))
  :rule-classes :congruence)

;; ======================================================================

;; Page Directory:

;; PD Base and Entry Addresses are present in the output from
;; gather-all-paging-structure-qword-addresses.

(defthm page-directory-base-addr-is-in-a-table-pointed-to-by-a-pdpte
  (implies (and (equal page-dir-ptr-table-base-addr
                       (mv-nth 1 (page-dir-ptr-table-base-addr lin-addr x86)))
                (equal page-dir-ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr page-dir-ptr-table-base-addr))
                (page-directory-entry-addr-found-p lin-addr x86))
           (member-p
            (mv-nth 1 (page-directory-base-addr lin-addr x86))
            (gather-qword-addresses-corresponding-to-1-entry
             page-dir-ptr-table-entry-addr x86)))
  :hints (("Goal"
           :in-theory (e/d* (gather-qword-addresses-corresponding-to-1-entry
                             read-page-dir-ptr-table-entry
                             page-directory-entry-addr
                             page-directory-base-addr)
                            ()))))

(defthm page-directory-entry-addr-is-in-a-table-pointed-to-by-a-pdpte
  (implies (and (equal page-dir-ptr-table-base-addr
                       (mv-nth 1 (page-dir-ptr-table-base-addr lin-addr x86)))
                (equal page-dir-ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr page-dir-ptr-table-base-addr))
                (page-directory-entry-addr-found-p lin-addr x86))
           (member-p
            (page-directory-entry-addr
             lin-addr (mv-nth 1 (page-directory-base-addr lin-addr x86)))
            (gather-qword-addresses-corresponding-to-1-entry page-dir-ptr-table-entry-addr x86)))
  :hints (("Goal"
           :in-theory (e/d* (gather-qword-addresses-corresponding-to-1-entry
                             read-page-dir-ptr-table-entry
                             good-paging-structures-x86p
                             page-directory-entry-addr
                             page-directory-base-addr)
                            ()))))

(defthm page-dir-ptr-table-entry-addr-is-in-a-table-pointed-to-by-a-pml4e-alt
  (implies (and (equal pml4-table-base-addr (mv-nth 1 (pml4-table-base-addr x86)))
                (physical-address-p (+ (ash 512 3) pml4-table-base-addr))
                (equal pml4-table-entry-addr (pml4-table-entry-addr lin-addr pml4-table-base-addr))
                (superior-entry-points-to-an-inferior-one-p pml4-table-entry-addr x86)
                (canonical-address-p lin-addr)
                (good-paging-structures-x86p x86))
           (member-list-p
            (page-dir-ptr-table-entry-addr
             lin-addr
             (mv-nth 1 (page-dir-ptr-table-base-addr lin-addr x86)))
            (gather-qword-addresses-corresponding-to-entries
             (gather-pml4-table-qword-addresses x86)
             x86)))
  :hints (("Goal"
           :use ((:instance subset-list-p-and-member-list-p
                            (e (page-dir-ptr-table-entry-addr
                                lin-addr
                                (mv-nth 1 (page-dir-ptr-table-base-addr lin-addr x86))))
                            (xs (gather-qword-addresses-corresponding-to-1-entry
                                 (pml4-table-entry-addr lin-addr pml4-table-base-addr)
                                 x86))
                            (xss (gather-qword-addresses-corresponding-to-entries
                                  (gather-pml4-table-qword-addresses x86)
                                  x86))))
           :in-theory (e/d* (gather-qword-addresses-corresponding-to-entries)
                            (subset-list-p-and-member-list-p)))))

(defthm page-directory-base-addr-is-in-gather-all-paging-structure-qword-addresses
  (implies (and (equal pml4-table-base-addr
                       (mv-nth 1 (pml4-table-base-addr x86)))
                (physical-address-p (+ (ash 512 3) pml4-table-base-addr))
                (equal pml4-table-entry-addr (pml4-table-entry-addr lin-addr pml4-table-base-addr))
                (superior-entry-points-to-an-inferior-one-p pml4-table-entry-addr x86)
                (equal page-dir-ptr-table-base-addr
                       (mv-nth 1 (page-dir-ptr-table-base-addr lin-addr x86)))
                (equal page-dir-ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr page-dir-ptr-table-base-addr))
                (superior-entry-points-to-an-inferior-one-p page-dir-ptr-table-entry-addr x86)
                (canonical-address-p lin-addr)
                (good-paging-structures-x86p x86))
           (member-list-p (mv-nth 1 (page-directory-base-addr lin-addr x86))
                          (gather-all-paging-structure-qword-addresses x86)))
  :hints (("Goal"
           :use ((:instance subset-list-p-and-member-list-p
                            (e (mv-nth 1 (page-directory-base-addr lin-addr x86)))
                            (xs (gather-qword-addresses-corresponding-to-1-entry
                                 (page-dir-ptr-table-entry-addr lin-addr page-dir-ptr-table-base-addr)
                                 x86))
                            (xss (gather-all-paging-structure-qword-addresses x86))))
           :in-theory (e/d* (gather-all-paging-structure-qword-addresses)
                            (subset-list-p-and-member-list-p)))))

(defthm page-directory-entry-addr-is-in-gather-all-paging-structure-qword-addresses
  (implies (page-directory-entry-addr-found-p lin-addr x86)
           (member-list-p
            (page-directory-entry-addr
             lin-addr
             (mv-nth 1 (page-directory-base-addr lin-addr x86)))
            (gather-all-paging-structure-qword-addresses x86)))
  :hints (("Goal"
           :use ((:instance subset-list-p-and-member-list-p
                            (e (page-directory-entry-addr
                                lin-addr
                                (mv-nth 1 (page-directory-base-addr lin-addr x86))))
                            (xs (gather-qword-addresses-corresponding-to-1-entry
                                 (page-dir-ptr-table-entry-addr
                                  lin-addr
                                  (mv-nth 1 (page-dir-ptr-table-base-addr lin-addr x86)))
                                 x86))
                            (xss (gather-all-paging-structure-qword-addresses x86))))
           :in-theory (e/d* (gather-all-paging-structure-qword-addresses)
                            (subset-list-p-and-member-list-p)))))

;; Relationship of PD with xlate-equiv-structures:

(defthm xlate-equiv-structures-and-page-directory-base-addr
  (implies (xlate-equiv-structures x86-1 x86-2)
           (equal (page-directory-base-addr lin-addr x86-1)
                  (page-directory-base-addr lin-addr x86-2)))
  :hints (("Goal"
           :use ((:instance xlate-equiv-entries-and-logtail
                            (n 12)
                            (e-1 (mv-nth 2 (read-page-dir-ptr-table-entry lin-addr x86-1)))
                            (e-2 (mv-nth 2 (read-page-dir-ptr-table-entry lin-addr x86-2))))
                 (:instance xlate-equiv-entries-and-page-size
                            (e-1 (mv-nth 2 (read-page-dir-ptr-table-entry lin-addr x86-1)))
                            (e-2 (mv-nth 2 (read-page-dir-ptr-table-entry lin-addr x86-2)))))
           :in-theory (e/d* (page-directory-base-addr)
                            (xlate-equiv-structures
                             xlate-equiv-entries
                             page-directory-entry-addr-found-p
                             page-dir-ptr-table-entry-addr-found-p
                             canonical-address-p
                             physical-address-p))))
  :rule-classes :congruence)

(defthm xlate-equiv-structures-and-page-directory-entry-addr-found-p
  (implies (xlate-equiv-structures x86-1 x86-2)
           (equal (page-directory-entry-addr-found-p lin-addr x86-1)
                  (page-directory-entry-addr-found-p lin-addr x86-2)))
  :hints (("Goal"
           :in-theory (e/d* (page-directory-entry-addr-found-p)
                            (xlate-equiv-entries
                             xlate-equiv-structures
                             superior-entry-points-to-an-inferior-one-p
                             physical-address-p
                             bitops::logand-with-negated-bitmask))))
  :rule-classes :congruence)

(defthm xlate-equiv-entries-of-page-directory
  (implies (xlate-equiv-structures x86-1 x86-2)
           (xlate-equiv-entries
            (mv-nth 2 (read-page-directory-entry lin-addr x86-1))
            (mv-nth 2 (read-page-directory-entry lin-addr x86-2))))
  :hints (("Goal"
           :in-theory
           (e/d* (read-page-directory-entry)
                 (xlate-equiv-structures
                  superior-entry-points-to-an-inferior-one-p
                  xlate-equiv-entries-at-qword-addresses?-implies-xlate-equiv-entries
                  page-directory-entry-addr-is-in-gather-all-paging-structure-qword-addresses
                  physical-address-p))
           :use ((:instance page-directory-entry-addr-is-in-gather-all-paging-structure-qword-addresses
                            (x86 x86-1))
                 (:instance xlate-equiv-entries-at-qword-addresses?-implies-xlate-equiv-entries
                            (index (page-directory-entry-addr
                                    lin-addr (mv-nth 1 (page-directory-base-addr lin-addr x86-1))))
                            (addrs (gather-all-paging-structure-qword-addresses x86-1))))))
  :rule-classes :congruence)

;; ======================================================================

;; Page Table:

;; PT Base and Entry Addresses are present in the output from
;; gather-all-paging-structure-qword-addresses.

(defthm page-table-base-addr-is-in-a-table-pointed-to-by-a-pde
  (implies (and (equal page-directory-base-addr
                       (mv-nth 1 (page-directory-base-addr lin-addr x86)))
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr page-directory-base-addr))
                (page-table-entry-addr-found-p lin-addr x86))
           (member-p
            (mv-nth 1 (page-table-base-addr lin-addr x86))
            (gather-qword-addresses-corresponding-to-1-entry
             page-directory-entry-addr x86)))
  :hints (("Goal"
           :in-theory (e/d* (gather-qword-addresses-corresponding-to-1-entry
                             read-page-directory-entry
                             page-directory-entry-addr
                             page-directory-base-addr
                             page-table-entry-addr
                             page-table-base-addr)
                            ()))))

(defthm page-table-entry-addr-is-in-a-table-pointed-to-by-a-pde
  (implies (and (equal page-directory-base-addr
                       (mv-nth 1 (page-directory-base-addr lin-addr x86)))
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr page-directory-base-addr))
                (page-table-entry-addr-found-p lin-addr x86))
           (member-p
            (page-table-entry-addr
             lin-addr (mv-nth 1 (page-table-base-addr lin-addr x86)))
            (gather-qword-addresses-corresponding-to-1-entry
             (page-directory-entry-addr lin-addr page-directory-base-addr)
             x86)))
  :hints (("Goal"
           :in-theory (e/d* (gather-qword-addresses-corresponding-to-1-entry
                             read-page-directory-entry
                             good-paging-structures-x86p
                             page-directory-entry-addr
                             page-directory-base-addr
                             page-table-entry-addr
                             page-table-base-addr)
                            ()))))

(defthm page-directory-entry-addr-is-in-a-table-pointed-to-by-a-pdpte-alt
  (implies
   (and
    (equal pml4-table-base-addr
           (mv-nth 1 (pml4-table-base-addr x86)))
    (physical-address-p (+ (ash 512 3) pml4-table-base-addr))
    (equal pml4-table-entry-addr
           (pml4-table-entry-addr lin-addr pml4-table-base-addr))
    (superior-entry-points-to-an-inferior-one-p pml4-table-entry-addr x86)
    (equal page-dir-ptr-table-base-addr
           (mv-nth 1 (page-dir-ptr-table-base-addr lin-addr x86)))
    (equal page-dir-ptr-table-entry-addr
           (page-dir-ptr-table-entry-addr lin-addr page-dir-ptr-table-base-addr))
    (superior-entry-points-to-an-inferior-one-p page-dir-ptr-table-entry-addr x86)
    (equal page-directory-base-addr
           (mv-nth 1 (page-directory-base-addr lin-addr x86)))
    (equal page-directory-entry-addr
           (page-directory-entry-addr lin-addr page-directory-base-addr))
    (canonical-address-p lin-addr)
    (good-paging-structures-x86p x86))
   (member-list-p
    page-directory-entry-addr
    (gather-qword-addresses-corresponding-to-list-of-entries
     (gather-qword-addresses-corresponding-to-entries
      (gather-pml4-table-qword-addresses x86)
      x86)
     x86)))
  :hints (("Goal"
           :use ((:instance subset-list-p-and-member-list-p
                            (e (page-directory-entry-addr lin-addr page-directory-base-addr))
                            (xs (gather-qword-addresses-corresponding-to-1-entry
                                 (page-dir-ptr-table-entry-addr
                                  lin-addr page-dir-ptr-table-base-addr)
                                 x86))
                            (xss (gather-qword-addresses-corresponding-to-list-of-entries
                                  (gather-qword-addresses-corresponding-to-entries
                                   (gather-pml4-table-qword-addresses x86)
                                   x86)
                                  x86))))
           :in-theory (e/d* (gather-qword-addresses-corresponding-to-entries
                             gather-qword-addresses-corresponding-to-list-of-entries)
                            (subset-list-p-and-member-list-p)))))

(defthm page-table-addresses-pointed-to-by-a-pde-are-in-those-pointed-to-by-all-pdes
  (implies
   (and (equal pml4-table-base-addr
               (mv-nth 1 (pml4-table-base-addr x86)))
        (physical-address-p (+ (ash 512 3) pml4-table-base-addr))
        (equal pml4-table-entry-addr
               (pml4-table-entry-addr lin-addr pml4-table-base-addr))
        (superior-entry-points-to-an-inferior-one-p
         pml4-table-entry-addr x86)
        (equal page-dir-ptr-table-base-addr
               (mv-nth 1 (page-dir-ptr-table-base-addr lin-addr x86)))
        (equal page-dir-ptr-table-entry-addr
               (page-dir-ptr-table-entry-addr lin-addr page-dir-ptr-table-base-addr))
        (superior-entry-points-to-an-inferior-one-p page-dir-ptr-table-entry-addr x86)
        (equal page-directory-base-addr
               (mv-nth 1 (page-directory-base-addr lin-addr x86)))
        (equal page-directory-entry-addr
               (page-directory-entry-addr lin-addr page-directory-base-addr))
        (superior-entry-points-to-an-inferior-one-p page-directory-entry-addr x86)
        (canonical-address-p lin-addr)
        (good-paging-structures-x86p x86))
   (subset-list-p
    ;; PT qword addresses corresponding to a PDE.
    (gather-qword-addresses-corresponding-to-1-entry
     (page-directory-entry-addr lin-addr page-directory-base-addr)
     x86)
    ;; All PT qword addresses.
    (gather-qword-addresses-corresponding-to-list-of-entries
     ;; All PD qword addresses.
     (gather-qword-addresses-corresponding-to-list-of-entries
      ;; All PDPT qword addresses.
      (gather-qword-addresses-corresponding-to-entries
       ;; ALL PML4 qword addresses.
       (gather-pml4-table-qword-addresses x86)
       x86)
      x86)
     x86)))
  :hints (("Goal"
           :in-theory (e/d* ()
                            (page-directory-entry-addr-is-in-a-table-pointed-to-by-a-pdpte-alt))
           :use ((:instance page-directory-entry-addr-is-in-a-table-pointed-to-by-a-pdpte-alt)))))

(defthm page-table-base-addr-is-in-gather-all-paging-structure-qword-addresses
  (implies (and (equal pml4-table-base-addr (mv-nth 1 (pml4-table-base-addr x86)))
                (physical-address-p (+ (ash 512 3) pml4-table-base-addr))
                (equal pml4-table-entry-addr
                       (pml4-table-entry-addr lin-addr pml4-table-base-addr))
                (superior-entry-points-to-an-inferior-one-p pml4-table-entry-addr x86)
                (equal page-dir-ptr-table-base-addr
                       (mv-nth 1 (page-dir-ptr-table-base-addr lin-addr x86)))
                (equal page-dir-ptr-table-entry-addr
                       (page-dir-ptr-table-entry-addr lin-addr page-dir-ptr-table-base-addr))
                (superior-entry-points-to-an-inferior-one-p page-dir-ptr-table-entry-addr x86)
                (equal page-directory-base-addr
                       (mv-nth 1 (page-directory-base-addr lin-addr x86)))
                (equal page-directory-entry-addr
                       (page-directory-entry-addr lin-addr page-directory-base-addr))
                (superior-entry-points-to-an-inferior-one-p page-directory-entry-addr x86)
                (canonical-address-p lin-addr)
                (good-paging-structures-x86p x86))
           (member-list-p (mv-nth 1 (page-table-base-addr lin-addr x86))
                          (gather-all-paging-structure-qword-addresses x86)))
  :hints (("Goal"
           :use ((:instance subset-list-p-and-member-list-p
                            (e (mv-nth 1 (page-table-base-addr lin-addr x86)))
                            (xs (gather-qword-addresses-corresponding-to-1-entry
                                 (page-directory-entry-addr lin-addr page-directory-base-addr)
                                 x86))
                            (xss (gather-all-paging-structure-qword-addresses x86))))
           :in-theory (e/d* (gather-all-paging-structure-qword-addresses)
                            (subset-list-p-and-member-list-p)))))

(defthm page-table-entry-addr-is-in-gather-all-paging-structure-qword-addresses
  (implies (page-table-entry-addr-found-p lin-addr x86)
           (member-list-p
            (page-table-entry-addr
             lin-addr
             (mv-nth 1 (page-table-base-addr lin-addr x86)))
            (gather-all-paging-structure-qword-addresses x86)))
  :hints (("Goal"
           :use ((:instance subset-list-p-and-member-list-p
                            (e (page-table-entry-addr
                                lin-addr
                                (mv-nth 1 (page-table-base-addr lin-addr x86))))
                            (xs (gather-qword-addresses-corresponding-to-1-entry
                                 (page-directory-entry-addr
                                  lin-addr (mv-nth 1 (page-directory-base-addr lin-addr x86)))
                                 x86))
                            (xss (gather-all-paging-structure-qword-addresses x86))))
           :in-theory (e/d* (gather-all-paging-structure-qword-addresses)
                            (subset-list-p-and-member-list-p)))))

;; Relationship of PT with xlate-equiv-structures:

(defthm xlate-equiv-structures-and-page-table-base-addr
  (implies (xlate-equiv-structures x86-1 x86-2)
           (equal (page-table-base-addr lin-addr x86-1)
                  (page-table-base-addr lin-addr x86-2)))
  :hints (("Goal"
           :use ((:instance xlate-equiv-entries-and-logtail
                            (n 12)
                            (e-1 (mv-nth 2 (read-page-directory-entry lin-addr x86-1)))
                            (e-2 (mv-nth 2 (read-page-directory-entry lin-addr x86-2))))
                 (:instance xlate-equiv-entries-and-page-size
                            (e-1 (mv-nth 2 (read-page-directory-entry lin-addr x86-1)))
                            (e-2 (mv-nth 2 (read-page-directory-entry lin-addr x86-2)))))
           :in-theory (e/d* (page-table-base-addr)
                            (xlate-equiv-structures
                             xlate-equiv-entries
                             page-directory-entry-addr-found-p
                             page-table-entry-addr-found-p
                             canonical-address-p
                             physical-address-p))))
  :rule-classes :congruence)

(defthm xlate-equiv-structures-and-page-table-entry-addr-found-p
  (implies (xlate-equiv-structures x86-1 x86-2)
           (equal (page-table-entry-addr-found-p lin-addr x86-1)
                  (page-table-entry-addr-found-p lin-addr x86-2)))
  :hints (("Goal"
           :use ((:instance xlate-equiv-structures-and-superior-entry-points-to-an-inferior-one-p
                            (x86-1 x86-1)
                            (x86-2 x86-2)
                            (entry-addr (pml4-table-entry-addr
                                         lin-addr
                                         (mv-nth 1 (pml4-table-base-addr x86-1)))))
                 (:instance xlate-equiv-structures-and-superior-entry-points-to-an-inferior-one-p
                            (x86-1 x86-1)
                            (x86-2 x86-2)
                            (entry-addr (page-dir-ptr-table-entry-addr
                                         lin-addr
                                         (mv-nth 1 (page-dir-ptr-table-base-addr lin-addr x86-1)))))
                 (:instance xlate-equiv-structures-and-superior-entry-points-to-an-inferior-one-p
                            (x86-1 x86-1)
                            (x86-2 x86-2)
                            (entry-addr (page-directory-entry-addr
                                         lin-addr
                                         (mv-nth 1 (page-directory-base-addr lin-addr x86-1))))))
           :in-theory (e/d* (page-table-entry-addr-found-p)
                            (xlate-equiv-entries
                             xlate-equiv-structures-and-superior-entry-points-to-an-inferior-one-p
                             xlate-equiv-structures
                             superior-entry-points-to-an-inferior-one-p
                             physical-address-p
                             bitops::logand-with-negated-bitmask))))
  :rule-classes :congruence)


(defthm xlate-equiv-entries-of-page-table
  (implies (xlate-equiv-structures x86-1 x86-2)
           (xlate-equiv-entries
            (mv-nth 2 (read-page-table-entry lin-addr x86-1))
            (mv-nth 2 (read-page-table-entry lin-addr x86-2))))
  :hints (("Goal"
           :in-theory
           (e/d* (read-page-table-entry)
                 (xlate-equiv-structures
                  superior-entry-points-to-an-inferior-one-p
                  xlate-equiv-structures-and-superior-entry-points-to-an-inferior-one-p
                  xlate-equiv-entries-at-qword-addresses?-implies-xlate-equiv-entries
                  physical-address-p))
           :use ((:instance xlate-equiv-structures-and-superior-entry-points-to-an-inferior-one-p
                            (x86-1 x86-1)
                            (x86-2 x86-2)
                            (entry-addr (pml4-table-entry-addr
                                         lin-addr
                                         (mv-nth 1 (pml4-table-base-addr x86-1)))))
                 (:instance xlate-equiv-structures-and-superior-entry-points-to-an-inferior-one-p
                            (x86-1 x86-1)
                            (x86-2 x86-2)
                            (entry-addr (page-dir-ptr-table-entry-addr
                                         lin-addr
                                         (mv-nth 1 (page-dir-ptr-table-base-addr lin-addr x86-1)))))
                 (:instance xlate-equiv-structures-and-superior-entry-points-to-an-inferior-one-p
                            (x86-1 x86-1)
                            (x86-2 x86-2)
                            (entry-addr (page-directory-entry-addr
                                         lin-addr
                                         (mv-nth 1 (page-directory-base-addr lin-addr x86-1)))))
                 (:instance xlate-equiv-entries-at-qword-addresses?-implies-xlate-equiv-entries
                            (index (page-table-entry-addr
                                    lin-addr (mv-nth 1 (page-table-base-addr lin-addr x86-1))))
                            (addrs (gather-all-paging-structure-qword-addresses x86-1))))))
  :rule-classes :congruence)

;; ======================================================================

;; Some more misc. rules:

(defthmd gather-all-paging-structure-qword-addresses-with-xlate-equiv-structures
  (implies (and (good-paging-structures-x86p x86)
                (xlate-equiv-structures (double-rewrite x86) (double-rewrite x86-equiv)))
           (equal (gather-all-paging-structure-qword-addresses x86-equiv)
                  (gather-all-paging-structure-qword-addresses x86)))
  :hints
  (("Goal" :in-theory (e/d* (gather-all-paging-structure-qword-addresses
                             xlate-equiv-structures)
                            ()))))


(defthm-usb n64p-rm-low-64-paging-entry
  :hyp (and (good-paging-structures-x86p (double-rewrite x86))
            (member-list-p addr (gather-all-paging-structure-qword-addresses x86)))
  :bound 64
  :concl (rm-low-64 addr x86)
  :hints (("Goal"
           :in-theory
           (e/d* (good-paging-structures-x86p)
                 ())))
  :gen-linear t)

(defthm all-mem-except-paging-structures-equal-and-wm-low-64-entry-addr
  (implies (and (xlate-equiv-entries (double-rewrite entry) (rm-low-64 entry-addr x86))
                (member-list-p entry-addr (gather-all-paging-structure-qword-addresses x86))
                (good-paging-structures-x86p (double-rewrite x86))
                (x86p (wm-low-64 entry-addr entry x86))
                (unsigned-byte-p 64 entry))
           (all-mem-except-paging-structures-equal
            (wm-low-64 entry-addr entry x86)
            (double-rewrite x86)))
  :hints (("Goal" :in-theory (e/d* (all-mem-except-paging-structures-equal
                                    good-paging-structures-x86p
                                    all-mem-except-paging-structures-equal-aux
                                    xlate-equiv-structures)
                                   ()))))

(in-theory (e/d* ()
                 (pml4-table-entry-addr-found-p
                  page-dir-ptr-table-entry-addr-found-p
                  page-directory-entry-addr-found-p
                  page-table-entry-addr-found-p)))

;; ======================================================================
