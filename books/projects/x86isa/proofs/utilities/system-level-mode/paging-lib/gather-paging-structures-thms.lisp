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

;; Driver rules (as Dave Greve says) involving xlate-equiv-x86s and
;; xlate-equiv-entries:

(defun find-an-xlate-equiv-x86-aux (thm-name x86-term)
  ;; Finds a "smaller" x86 that is xlate-equiv to x86-term.
  (if (atom x86-term)
      x86-term
    (b* ((outer-fn (car x86-term))
         ((when (and (not (equal outer-fn 'MV-NTH))
                     (not (equal outer-fn 'WM-LOW-64))
                     (not (and (equal outer-fn 'XW)
                               (equal (second x86-term) '':MEM)))))
          (cw "~%~p0: Unexpected x86-term encountered:~p1~%" thm-name x86-term)
          x86-term))
      (cond ((equal outer-fn 'MV-NTH)
             ;; We expect x86-term to be a function related to page
             ;; traversals.
             (b* ((mv-nth-index (second x86-term))
                  (inner-fn-call (third x86-term))
                  (inner-fn (first inner-fn-call))
                  ((when (or (not (equal mv-nth-index ''2))
                             (not (member-p inner-fn
                                            '(IA32E-LA-TO-PA-PT
                                              IA32E-LA-TO-PA-PD
                                              IA32E-LA-TO-PA-PDPT
                                              IA32E-LA-TO-PA-PML4T
                                              IA32E-ENTRIES-FOUND-LA-TO-PA
                                              PAGE-TABLE-ENTRY-NO-PAGE-FAULT-P$INLINE
                                              PAGING-ENTRY-NO-PAGE-FAULT-P$INLINE)))))
                   (cw "~%~p0: Unexpected mv-nth x86-term encountered:~p1~%" thm-name x86-term)
                   x86-term)
                  (sub-x86 (first (last inner-fn-call))))
               sub-x86))
            ((or (equal outer-fn 'WM-LOW-64)
                 (equal outer-fn 'XW))
             ;; We expect x86-term to be of the form (wm-low-64 index
             ;; val sub-x86) or (xw :mem val index).
             (b* ((sub-x86 (first (last x86-term))))
               sub-x86))))))

(defun find-an-xlate-equiv-x86 (thm-name x86-var x86-term)
  ;; bind-free for an x86 in xlate-equiv-x86s: should check just for the
  ;; page traversal functions and wm-low-64.
  ;; TO-DO: Logic mode...
  (declare (xargs :mode :program))
  (b* ((equiv-x86-1 (find-an-xlate-equiv-x86-aux thm-name x86-term))
       (equiv-x86-2 (find-an-xlate-equiv-x86-aux thm-name equiv-x86-1)))
    (if (equal equiv-x86-1 equiv-x86-2)
        `((,x86-var . ,equiv-x86-1))
      (find-an-xlate-equiv-x86 thm-name x86-var equiv-x86-2))))

(defthm xlate-equiv-x86s-and-xw-mem-disjoint
  (implies (and (bind-free
                 (find-an-xlate-equiv-x86
                  'xlate-equiv-x86s-and-xw-mem-disjoint
                  'x86-1 x86-2)
                 (x86-1))
                (xlate-equiv-x86s x86-1 (double-rewrite x86-2))
                (pairwise-disjoint-p-aux
                 (list index)
                 (open-qword-paddr-list-list
                  (gather-all-paging-structure-qword-addresses x86-1)))
                (good-paging-structures-x86p x86-1)
                (physical-address-p index)
                (unsigned-byte-p 8 val))
           (xlate-equiv-x86s (xw :mem index val x86-2) x86-1))
  :hints (("Goal" :in-theory (e/d* (xlate-equiv-x86s good-paging-structures-x86p)
                                   ()))))

(defthm xlate-equiv-x86s-and-wm-low-64-disjoint
  (implies (and (bind-free
                 (find-an-xlate-equiv-x86
                  'xlate-equiv-x86s-and-wm-low-64-disjoint
                  'x86-1 x86-2)
                 (x86-1))
                (xlate-equiv-x86s x86-1 (double-rewrite x86-2))
                (pairwise-disjoint-p-aux
                 (addr-range 8 index)
                 (open-qword-paddr-list-list
                  (gather-all-paging-structure-qword-addresses x86-1)))
                (good-paging-structures-x86p x86-1)
                (physical-address-p index))
           (xlate-equiv-x86s (wm-low-64 index val x86-2) x86-1))
  :hints (("Goal" :in-theory (e/d* (xlate-equiv-x86s good-paging-structures-x86p)
                                   ()))))

(defthm xlate-equiv-x86s-and-wm-low-64-entry-addr
  (implies (and (bind-free (find-an-xlate-equiv-x86
                            'xlate-equiv-x86s-and-wm-low-64-entry-addr
                            'x86 x86-equiv)
                           (x86))
                (xlate-equiv-x86s x86 (double-rewrite x86-equiv))
                (xlate-equiv-entries (double-rewrite val) (rm-low-64 index x86))
                (member-list-p index (gather-all-paging-structure-qword-addresses x86))
                (good-paging-structures-x86p x86)
                (x86p (wm-low-64 index val x86-equiv))
                (unsigned-byte-p 64 val))
           (xlate-equiv-x86s (wm-low-64 index val x86-equiv) x86))
  :hints (("Goal"
           :use ((:instance
                  xlate-equiv-entries-at-qword-addresses?-with-wm-low-64-with-different-x86
                  (addrs (gather-all-paging-structure-qword-addresses x86))
                  (x86-1 x86)
                  (x86-2 x86-equiv)))
           :in-theory
           (e/d*
            (xlate-equiv-x86s
             good-paging-structures-x86p)
            (xlate-equiv-entries-at-qword-addresses?-with-wm-low-64-with-different-x86)))))

(defthmd xlate-equiv-entries-open
  (implies (and (xlate-equiv-entries e-1 e-2)
                (unsigned-byte-p 64 e-1)
                (unsigned-byte-p 64 e-2))
           (and (equal (loghead 5 e-1) (loghead 5 e-2))
                (equal (logtail 7 e-1) (logtail 7 e-2))))
  :hints (("Goal" :in-theory (e/d* (xlate-equiv-entries) ()))))

(defthm xlate-equiv-x86s-implies-both-or-neither-good-paging-structures
  (implies (and (xlate-equiv-x86s x86-1 x86-2)
                (good-paging-structures-x86p x86-1))
           (good-paging-structures-x86p x86-2)))

(defthm xlate-equiv-x86s-implies-xlate-equiv-entries-at-qword-addresses?
  (implies (and (equal addrs (gather-all-paging-structure-qword-addresses x86-1))
                (xlate-equiv-x86s x86-1 x86-2)
                (good-paging-structures-x86p x86-1))
           (xlate-equiv-entries-at-qword-addresses? addrs addrs x86-1 x86-2)))

(local
 (defthmd xlate-equiv-x86s-and-xlate-equiv-entries
   (implies (and
             (xlate-equiv-x86s x86-1 x86-2)
             (member-list-p index (gather-all-paging-structure-qword-addresses x86-1))
             (good-paging-structures-x86p x86-1))
            (xlate-equiv-entries (rm-low-64 index x86-1) (rm-low-64 index x86-2)))
   :hints (("Goal" :in-theory (e/d* (xlate-equiv-x86s)
                                    ())))))

(defthm superior-entry-points-to-an-inferior-one-p-and-xlate-equiv-x86s
  (implies (and (xlate-equiv-x86s x86-1 x86-2)
                (good-paging-structures-x86p x86-1)
                (member-list-p entry-addr
                               (gather-all-paging-structure-qword-addresses x86-1)))
           (equal (superior-entry-points-to-an-inferior-one-p entry-addr x86-1)
                  (superior-entry-points-to-an-inferior-one-p entry-addr x86-2)))
  :hints (("Goal"
           :use ((:instance xlate-equiv-x86s-and-xlate-equiv-entries
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
           :in-theory (e/d* (superior-entry-points-to-an-inferior-one-p)
                            (xlate-equiv-x86s)))))

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

;; Relationship of PML4 Table with xlate-equiv-x86s:

(defthm xlate-equiv-x86s-and-pml4-table-base-addr
  (implies (xlate-equiv-x86s x86-1 x86-2)
           (equal (pml4-table-base-addr x86-1)
                  (pml4-table-base-addr x86-2)))
  :hints (("Goal" :in-theory (e/d* (pml4-table-base-addr) ())))
  :rule-classes :congruence)

(defthm pml4-table-entry-addr-found-p-and-xlate-equiv-x86s
  (implies (xlate-equiv-x86s x86-1 x86-2)
           (equal (pml4-table-entry-addr-found-p lin-addr x86-1)
                  (pml4-table-entry-addr-found-p lin-addr x86-2)))
  :hints (("Goal"
           :use ((:instance xlate-equiv-x86s-and-pml4-table-base-addr))
           :in-theory (e/d* (pml4-table-entry-addr-found-p)
                            (physical-address-p
                             xlate-equiv-x86s-and-pml4-table-base-addr
                             bitops::logand-with-negated-bitmask))))
  :rule-classes :congruence)

(defthm xlate-equiv-entries-of-pml4-table
  (implies (xlate-equiv-x86s x86-1 x86-2)
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
                 (xlate-equiv-x86s
                  xlate-equiv-entries-at-qword-addresses?-implies-xlate-equiv-entries
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

;; Relationship of PDPT with xlate-equiv-x86s:

(defthm xlate-equiv-x86s-and-page-dir-ptr-table-base-addr
  (implies (xlate-equiv-x86s x86-1 x86-2)
           (equal (page-dir-ptr-table-base-addr lin-addr x86-1)
                  (page-dir-ptr-table-base-addr lin-addr x86-2)))
  :hints (("Goal"
           :use ((:instance xlate-equiv-entries-and-logtail
                            (n 12)
                            (e-1 (mv-nth 2 (read-pml4-table-entry lin-addr x86-1)))
                            (e-2 (mv-nth 2 (read-pml4-table-entry lin-addr x86-2)))))
           :in-theory (e/d* (page-dir-ptr-table-base-addr)
                            (xlate-equiv-x86s
                             xlate-equiv-entries
                             pml4-table-entry-addr-found-p
                             page-dir-ptr-table-entry-addr-found-p
                             canonical-address-p
                             physical-address-p))))
  :rule-classes :congruence)

(defthm page-dir-ptr-table-entry-addr-found-p-and-xlate-equiv-x86s
  (implies (xlate-equiv-x86s x86-1 x86-2)
           (equal (page-dir-ptr-table-entry-addr-found-p lin-addr x86-1)
                  (page-dir-ptr-table-entry-addr-found-p lin-addr x86-2)))
  :hints (("Goal"
           :in-theory (e/d* (page-dir-ptr-table-entry-addr-found-p)
                            (xlate-equiv-entries
                             xlate-equiv-x86s
                             superior-entry-points-to-an-inferior-one-p
                             physical-address-p
                             bitops::logand-with-negated-bitmask))))
  :rule-classes :congruence)

(defthm xlate-equiv-entries-of-page-dir-ptr-table
  (implies (xlate-equiv-x86s x86-1 x86-2)
           (xlate-equiv-entries
            (mv-nth 2 (read-page-dir-ptr-table-entry lin-addr x86-1))
            (mv-nth 2 (read-page-dir-ptr-table-entry lin-addr x86-2))))
  :hints (("Goal"
           :in-theory
           (e/d* (read-page-dir-ptr-table-entry)
                 (xlate-equiv-x86s
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

;; Relationship of PD with xlate-equiv-x86s:

(defthm xlate-equiv-x86s-and-page-directory-base-addr
  (implies (xlate-equiv-x86s x86-1 x86-2)
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
                            (xlate-equiv-x86s
                             xlate-equiv-entries
                             page-directory-entry-addr-found-p
                             page-dir-ptr-table-entry-addr-found-p
                             canonical-address-p
                             physical-address-p))))
  :rule-classes :congruence)

(defthm page-directory-entry-addr-found-p-and-xlate-equiv-x86s
  (implies (xlate-equiv-x86s x86-1 x86-2)
           (equal (page-directory-entry-addr-found-p lin-addr x86-1)
                  (page-directory-entry-addr-found-p lin-addr x86-2)))
  :hints (("Goal"
           :in-theory (e/d* (page-directory-entry-addr-found-p)
                            (xlate-equiv-entries
                             xlate-equiv-x86s
                             superior-entry-points-to-an-inferior-one-p
                             physical-address-p
                             bitops::logand-with-negated-bitmask))))
  :rule-classes :congruence)

(defthm xlate-equiv-entries-of-page-directory
  (implies (xlate-equiv-x86s x86-1 x86-2)
           (xlate-equiv-entries
            (mv-nth 2 (read-page-directory-entry lin-addr x86-1))
            (mv-nth 2 (read-page-directory-entry lin-addr x86-2))))
  :hints (("Goal"
           :in-theory
           (e/d* (read-page-directory-entry)
                 (xlate-equiv-x86s
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

;; Relationship of PT with xlate-equiv-x86s:

(defthm xlate-equiv-x86s-and-page-table-base-addr
  (implies (xlate-equiv-x86s x86-1 x86-2)
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
                            (xlate-equiv-x86s
                             xlate-equiv-entries
                             page-directory-entry-addr-found-p
                             page-table-entry-addr-found-p
                             canonical-address-p
                             physical-address-p))))
  :rule-classes :congruence)

(defthm page-table-entry-addr-found-p-and-xlate-equiv-x86s
  (implies (xlate-equiv-x86s x86-1 x86-2)
           (equal (page-table-entry-addr-found-p lin-addr x86-1)
                  (page-table-entry-addr-found-p lin-addr x86-2)))
  :hints (("Goal"
           :use ((:instance superior-entry-points-to-an-inferior-one-p-and-xlate-equiv-x86s
                            (x86-1 x86-1)
                            (x86-2 x86-2)
                            (entry-addr (pml4-table-entry-addr
                                         lin-addr
                                         (mv-nth 1 (pml4-table-base-addr x86-1)))))
                 (:instance superior-entry-points-to-an-inferior-one-p-and-xlate-equiv-x86s
                            (x86-1 x86-1)
                            (x86-2 x86-2)
                            (entry-addr (page-dir-ptr-table-entry-addr
                                         lin-addr
                                         (mv-nth 1 (page-dir-ptr-table-base-addr lin-addr x86-1)))))
                 (:instance superior-entry-points-to-an-inferior-one-p-and-xlate-equiv-x86s
                            (x86-1 x86-1)
                            (x86-2 x86-2)
                            (entry-addr (page-directory-entry-addr
                                         lin-addr
                                         (mv-nth 1 (page-directory-base-addr lin-addr x86-1))))))
           :in-theory (e/d* (page-table-entry-addr-found-p)
                            (xlate-equiv-entries
                             superior-entry-points-to-an-inferior-one-p-and-xlate-equiv-x86s
                             xlate-equiv-x86s
                             superior-entry-points-to-an-inferior-one-p
                             physical-address-p
                             bitops::logand-with-negated-bitmask))))
  :rule-classes :congruence)


(defthm xlate-equiv-entries-of-page-table
  (implies (xlate-equiv-x86s x86-1 x86-2)
           (xlate-equiv-entries
            (mv-nth 2 (read-page-table-entry lin-addr x86-1))
            (mv-nth 2 (read-page-table-entry lin-addr x86-2))))
  :hints (("Goal"
           :in-theory
           (e/d* (read-page-table-entry)
                 (xlate-equiv-x86s
                  superior-entry-points-to-an-inferior-one-p
                  superior-entry-points-to-an-inferior-one-p-and-xlate-equiv-x86s
                  xlate-equiv-entries-at-qword-addresses?-implies-xlate-equiv-entries
                  physical-address-p))
           :use ((:instance superior-entry-points-to-an-inferior-one-p-and-xlate-equiv-x86s
                            (x86-1 x86-1)
                            (x86-2 x86-2)
                            (entry-addr (pml4-table-entry-addr
                                         lin-addr
                                         (mv-nth 1 (pml4-table-base-addr x86-1)))))
                 (:instance superior-entry-points-to-an-inferior-one-p-and-xlate-equiv-x86s
                            (x86-1 x86-1)
                            (x86-2 x86-2)
                            (entry-addr (page-dir-ptr-table-entry-addr
                                         lin-addr
                                         (mv-nth 1 (page-dir-ptr-table-base-addr lin-addr x86-1)))))
                 (:instance superior-entry-points-to-an-inferior-one-p-and-xlate-equiv-x86s
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

(defthmd gather-all-paging-structure-qword-addresses-with-xlate-equiv-x86s
  (implies (and (good-paging-structures-x86p x86)
                (xlate-equiv-x86s x86 x86-equiv))
           (equal (gather-all-paging-structure-qword-addresses x86-equiv)
                  (gather-all-paging-structure-qword-addresses x86)))
  :hints
  (("Goal" :in-theory (e/d* (gather-all-paging-structure-qword-addresses) ()))))

(defthmd xlate-equiv-x86s-and-xlate-equiv-entries-at-qword-addresses?
  (implies (and (equal addrs (gather-all-paging-structure-qword-addresses x86))
                (good-paging-structures-x86p x86)
                (xlate-equiv-x86s x86 x86-equiv))
           (xlate-equiv-entries-at-qword-addresses?
            addrs addrs x86 x86-equiv))
  :hints
  (("Goal" :in-theory (e/d* (xlate-equiv-entries-at-qword-addresses?
                             good-paging-structures-x86p)
                            ()))))

(defthm-usb n64p-rm-low-64-paging-entry
  :hyp (and (good-paging-structures-x86p x86)
            (member-list-p addr (gather-all-paging-structure-qword-addresses x86)))
  :bound 64
  :concl (rm-low-64 addr x86)
  :hints (("Goal"
           :in-theory
           (e/d* (good-paging-structures-x86p)
                 ())))
  :gen-linear t)

(in-theory (e/d* ()
                 (pml4-table-entry-addr-found-p
                  page-dir-ptr-table-entry-addr-found-p
                  page-directory-entry-addr-found-p
                  page-table-entry-addr-found-p)))

;; ======================================================================
