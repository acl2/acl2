;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")
(include-book "gather-paging-structures" :ttags :all)
(include-book "x86-ia32e-paging-alt" :ttags :all)

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))

;; ======================================================================

;; RoW Theorems with R = gather functions:

;; (defthm gather-pml4-table-qword-addresses-xw-1
;;   (implies (not (equal fld :ctr))
;;            (equal (gather-pml4-table-qword-addresses (xw fld index val x86))
;;                   (gather-pml4-table-qword-addresses x86)))
;;   :hints (("Goal"
;;            :cases ((equal fld :ctr))
;;            :in-theory (e/d* (gather-pml4-table-qword-addresses)
;;                             ()))))

;; (defthm gather-pml4-table-qword-addresses-xw-2
;;   (implies (and (equal fld :ctr)
;;                 (not (equal index *cr3*)))
;;            (equal (gather-pml4-table-qword-addresses (xw fld index val x86))
;;                   (gather-pml4-table-qword-addresses x86)))
;;   :hints (("Goal"
;;            :cases ((equal fld :ctr))
;;            :in-theory (e/d* (gather-pml4-table-qword-addresses)
;;                             ()))))

;; (defthm gather-qword-addresses-corresponding-to-1-entry-xw-1
;;   (implies (and (not (equal fld :mem))
;;                 (natp n))
;;            (equal (gather-qword-addresses-corresponding-to-1-entry n (xw fld index val x86))
;;                   (gather-qword-addresses-corresponding-to-1-entry n x86)))
;;   :hints (("Goal"
;;            :in-theory (e/d* (gather-qword-addresses-corresponding-to-1-entry)
;;                             ()))))

;; (defthm gather-qword-addresses-corresponding-to-1-entry-xw-2
;;   (implies (and (equal fld :mem)
;;                 (disjoint-p (addr-range 1 index)
;;                             (addr-range 8 addr))
;;                 (natp addr))
;;            (equal (gather-qword-addresses-corresponding-to-1-entry addr (xw :mem index val x86))
;;                   (gather-qword-addresses-corresponding-to-1-entry addr x86)))
;;   :hints (("Goal"
;;            :in-theory (e/d* (gather-qword-addresses-corresponding-to-1-entry)
;;                             (addr-range
;;                              addr-range-1)))))

;; (defthm gather-qword-addresses-corresponding-to-entries-xw-1
;;   (implies (and (not (equal fld :mem))
;;                 (qword-paddr-listp addrs))
;;            (equal (gather-qword-addresses-corresponding-to-entries addrs (xw fld index val x86))
;;                   (gather-qword-addresses-corresponding-to-entries addrs x86)))
;;   :hints (("Goal"
;;            :in-theory (e/d* (gather-qword-addresses-corresponding-to-entries)
;;                             ()))))

;; ;; TO-DO: gather-qword-addresses-corresponding-to-entries-xw-2

;; (defthm gather-qword-addresses-corresponding-to-list-of-entries-xw-1
;;   (implies (and (not (equal fld :mem))
;;                 (qword-paddr-list-listp addrs))
;;            (equal (gather-qword-addresses-corresponding-to-list-of-entries addrs (xw fld index val x86))
;;                   (gather-qword-addresses-corresponding-to-list-of-entries addrs x86)))
;;   :hints (("Goal"
;;            :in-theory (e/d* (gather-qword-addresses-corresponding-to-list-of-entries)
;;                             ()))))

;; ;; TO-DO: gather-qword-addresses-corresponding-to-list-of-entries-xw-2

;; (defthm gather-all-paging-structure-qword-addresses-xw-1
;;   (implies (and (not (equal fld :mem))
;;                 (not (equal fld :ctr)))
;;            (equal (gather-all-paging-structure-qword-addresses (xw fld index val x86))
;;                   (gather-all-paging-structure-qword-addresses x86)))
;;   :hints (("Goal"
;;            :in-theory (e/d* (gather-all-paging-structure-qword-addresses)
;;                             ()))))

;; ;; ======================================================================

;; ;; RoW Theorems with R = xlate-equiv functions

;; (defthm xlate-equiv-entries-at-qword-addresses-aux?-with-xw
;;   (implies (not (equal fld :mem))
;;            (equal (xlate-equiv-entries-at-qword-addresses-aux?
;;                    addrs addrs
;;                    x86
;;                    (xw fld index val x86))
;;                   (xlate-equiv-entries-at-qword-addresses-aux?
;;                    addrs addrs
;;                    x86
;;                    x86)))
;;   :hints (("Goal" :in-theory (e/d* (xlate-equiv-entries-at-qword-addresses-aux?)
;;                                    ()))))

;; (defthm xlate-equiv-entries-at-qword-addresses?-with-xw
;;   (implies (not (equal fld :mem))
;;            (equal (xlate-equiv-entries-at-qword-addresses?
;;                    addrs addrs
;;                    x86
;;                    (xw fld index val x86))
;;                   (xlate-equiv-entries-at-qword-addresses?
;;                    addrs addrs
;;                    x86
;;                    x86)))
;;   :hints (("Goal" :in-theory (e/d* (xlate-equiv-entries-at-qword-addresses?)
;;                                    ()))))

;; ;; ======================================================================

;; (i-am-here) ;; From here...

(local (include-book "centaur/gl/gl" :dir :system))

(define member-list-p (e xs)
  :guard (true-list-listp xs)
  :enabled t
  (if (endp xs)
      nil
    (if (member-p e (car xs))
        t
      (member-list-p e (cdr xs))))

  ///

  (defthm member-list-p-append
    (equal (member-list-p e (append xs ys))
           (or (member-list-p e xs)
               (member-list-p e ys)))))

(define subset-list-p (xs xss)
  :guard (and (true-listp xs)
              (true-list-listp xss))
  :enabled t
  (if (endp xss)
      nil
    (if (subset-p xs (car xss))
        t
      (subset-list-p xs (cdr xss))))

  ///

  (defthm subset-list-p-append
    (equal (subset-list-p xs (append xss yss))
           (or (subset-list-p xs xss)
               (subset-list-p xs yss)))))

(defthm subset-list-p-and-member-list-p
  (implies (and (member-p e xs)
                (subset-list-p xs xss))
           (member-list-p e xss))
  :hints (("Goal" :in-theory (e/d* (subset-p) ()))))

(defthm create-qword-address-list-1
  (implies (and (physical-address-p (+ 7 addr))
                (physical-address-p addr))
           (equal (create-qword-address-list 1 addr)
                  (list addr)))
  :hints (("Goal" :expand (create-qword-address-list 1 addr))))

(defthm non-nil-create-qword-address-list
  (implies (and (posp count)
                (physical-address-p addr)
                (physical-address-p (+ 7 addr)))
           (create-qword-address-list count addr)))

(defthm consp-create-qword-address-list
  (implies (and (physical-address-p addr)
                (physical-address-p (+ 7 addr))
                (posp count))
           (consp (create-qword-address-list count addr)))
  :rule-classes (:type-prescription :rewrite))

(defthm car-of-create-qword-address-list
  (implies (and (posp count)
                (physical-address-p addr)
                (physical-address-p (+ 7 addr)))
           (equal (car (create-qword-address-list count addr))
                  addr)))

(encapsulate
 ()

 (local (include-book "arithmetic-5/top" :dir :system))

 (defthm member-p-create-qword-address-list
   (implies (and (<= addr x)
                 (< x (+ (ash count 3) addr))
                 (equal (loghead 3 addr) 0)
                 (equal (loghead 3 x) 0)
                 (physical-address-p x)
                 (physical-address-p addr))
            (equal (member-p x (create-qword-address-list count addr))
                   t))
   :hints (("Goal"
            :induct (create-qword-address-list count addr)
            :in-theory (e/d* (loghead) ())))))

;; ======================================================================

(defthm non-nil-gather-pml4-table-qword-addresses
  (implies (and (equal pml4-table-base-addr
                       (mv-nth 1 (pml4-table-base-addr x86)))
                (physical-address-p (+ (ash 512 3) pml4-table-base-addr)))
           (gather-pml4-table-qword-addresses x86))
  :hints (("Goal"
           :in-theory (e/d* (pml4-table-base-addr
                             pml4-table-entry-addr
                             gather-pml4-table-qword-addresses)
                            ()))))

(defthm consp-gather-pml4-table-qword-addresses
  (implies (and (equal pml4-table-base-addr
                       (mv-nth 1 (pml4-table-base-addr x86)))
                (physical-address-p (+ (ash 512 3) pml4-table-base-addr)))
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
                (physical-address-p (+ (ash 512 3) pml4-table-base-addr)))
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

(defthm pml4-table-base-addr-is-a-member-of-gather-pml4-table-qword-addresses
  (implies (physical-address-p (+ (ash 512 3)
                                  (mv-nth 1 (pml4-table-base-addr x86))))
           (member-p (mv-nth 1 (pml4-table-base-addr x86))
                     (gather-pml4-table-qword-addresses x86)))
  :hints (("Goal"
           :in-theory (e/d* (pml4-table-base-addr
                             gather-pml4-table-qword-addresses)
                            ()))))

(local
 (def-gl-thm pml4-table-entry-addr-and-gather-pml4-table-qword-addresses-helper-1
   :hyp (and (unsigned-byte-p 52 x)
             (equal (loghead 12 x) 0))
   :concl (equal (logand 18446744073709547527 x)
                 x)
   :g-bindings `((x (:g-number ,(gl-int 0 1 53))))))

(local
 (def-gl-thm pml4-table-entry-addr-and-gather-pml4-table-qword-addresses-helper-2
   :hyp (and (canonical-address-p lin-addr)
             (unsigned-byte-p 52 x))
   :concl (< (logior (ash (loghead 9 (logtail 39 lin-addr))
                          3)
                     x)
             (+ 4096 x))
   :g-bindings `((lin-addr (:g-number ,(gl-int 0 2 65)))
                 (x        (:g-number ,(gl-int 1 2 65))))))

(defthm pml4-table-entry-addr-is-a-member-of-gather-pml4-table-qword-addresses
  (implies (and (canonical-address-p lin-addr)
                (equal pml4-table-base-addr
                       (mv-nth 1 (pml4-table-base-addr x86)))
                (physical-address-p (+ (ash 512 3) pml4-table-base-addr)))
           (member-p (pml4-table-entry-addr lin-addr pml4-table-base-addr)
                     (gather-pml4-table-qword-addresses x86)))
  :hints (("Goal"
           :in-theory (e/d* (pml4-table-base-addr
                             pml4-table-entry-addr
                             gather-pml4-table-qword-addresses)
                            ()))))

(defthm pml4-table-base-addr-is-in-gather-all-paging-structure-qword-addresses
  (implies (physical-address-p
            (+ (ash 512 3)
               (mv-nth 1 (pml4-table-base-addr x86))))
           (member-list-p (mv-nth 1 (pml4-table-base-addr x86))
                          (gather-all-paging-structure-qword-addresses x86)))
  :hints (("Goal"
           :in-theory (e/d* (gather-all-paging-structure-qword-addresses)
                            ()))))

(defthm pml4-table-entry-addr-is-in-gather-all-paging-structure-qword-addresses
  (implies (and (canonical-address-p lin-addr)
                (equal pml4-table-base-addr
                       (mv-nth 1 (pml4-table-base-addr x86)))
                (physical-address-p (+ (ash 512 3) pml4-table-base-addr)))
           (member-list-p (pml4-table-entry-addr lin-addr pml4-table-base-addr)
                          (gather-all-paging-structure-qword-addresses x86)))
  :hints (("Goal"
           :in-theory (e/d* (gather-all-paging-structure-qword-addresses)
                            ()))))

;; ======================================================================

(defthm non-nil-gather-qword-addresses-corresponding-to-1-entry
  (implies (and (equal (ia32e-page-tables-slice :p (rm-low-64 paddr x86)) 1)
                (equal (ia32e-page-tables-slice :ps (rm-low-64 paddr x86)) 0)
                (physical-address-p
                 (+ (ash 512 3)
                    (ash (ia32e-page-tables-slice :reference-addr (rm-low-64 paddr x86))
                         12))))
           (gather-qword-addresses-corresponding-to-1-entry paddr x86))
  :hints (("Goal"
           :in-theory (e/d* (gather-qword-addresses-corresponding-to-1-entry)
                            ()))))

(defthm consp-gather-qword-addresses-corresponding-to-1-entry
  (implies (and (equal (ia32e-page-tables-slice :p (rm-low-64 paddr x86)) 1)
                (equal (ia32e-page-tables-slice :ps (rm-low-64 paddr x86)) 0)
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
  (implies (and (equal (ia32e-page-tables-slice :p (rm-low-64 paddr x86)) 1)
                (equal (ia32e-page-tables-slice :ps (rm-low-64 paddr x86)) 0)
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

;; ======================================================================

(defthm consp-gather-qword-addresses-corresponding-to-entries
  (implies (and (consp paddr-list)
                (qword-paddr-listp paddr-list)
                (equal (ia32e-page-tables-slice :p (rm-low-64 (car paddr-list) x86)) 1)
                (equal (ia32e-page-tables-slice :ps (rm-low-64 (car paddr-list) x86)) 0)
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
                (equal (ia32e-page-tables-slice :p (rm-low-64 (car paddr-list) x86)) 1)
                (equal (ia32e-page-tables-slice :ps (rm-low-64 (car paddr-list) x86)) 0)
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

;; ======================================================================

(local
 (def-gl-thm page-dir-ptr-table-entry-addr-is-in-a-table-pointed-to-by-a-pml4e-helper-1-1
   :hyp (and (unsigned-byte-p 64 x)
             (canonical-address-p l))
   :concl (<=
           (ash (loghead 40 (logtail 12 x)) 12)
           (logior (ash (loghead 9 (logtail 30 l)) 3)
                   (logand 18446744073709547527
                           (ash (loghead 40 (logtail 12 x)) 12))))
   :g-bindings `((x (:g-number ,(gl-int 0 2 65)))
                 (l (:g-number ,(gl-int 1 2 65))))
   :rule-classes :linear))

(local
 (def-gl-thm page-dir-ptr-table-entry-addr-is-in-a-table-pointed-to-by-a-pml4e-helper-2-1
   :hyp (and (unsigned-byte-p 64 x)
             (canonical-address-p l))
   :concl (<
           (logior (ash (loghead 9 (logtail 30 l)) 3)
                   (ash (loghead 40 (logtail 12 x)) 12))
           (+ 4096 (ash (loghead 40 (logtail 12 x)) 12)))
   :g-bindings `((x (:g-number ,(gl-int 0 2 65)))
                 (l (:g-number ,(gl-int 1 2 65))))
   :rule-classes :linear))

(defthm page-dir-ptr-table-base-addr-is-in-a-table-pointed-to-by-a-pml4e
  (implies (and (equal pml4-table-base-addr
                       (mv-nth 1 (pml4-table-base-addr x86)))
                (equal
                 (ia32e-page-tables-slice
                  :p (rm-low-64 (pml4-table-entry-addr lin-addr pml4-table-base-addr)
                                x86))
                 1)
                (equal
                 (ia32e-page-tables-slice
                  :ps (rm-low-64 (pml4-table-entry-addr lin-addr pml4-table-base-addr)
                                 x86))
                 0)
                (physical-address-p
                 (+
                  (ash 512 3)
                  (ash
                   (ia32e-page-tables-slice
                    :reference-addr
                    (rm-low-64 (pml4-table-entry-addr lin-addr pml4-table-base-addr)
                               x86))
                   12))))
           (member-p
            (mv-nth 1 (page-dir-ptr-table-base-addr lin-addr x86))
            (gather-qword-addresses-corresponding-to-1-entry
             (pml4-table-entry-addr lin-addr pml4-table-base-addr)
             x86)))
  :hints (("Goal"
           :in-theory (e/d* (gather-qword-addresses-corresponding-to-1-entry
                             page-dir-ptr-table-entry-addr
                             page-dir-ptr-table-base-addr)
                            ()))))

(defthm page-dir-ptr-table-entry-addr-is-in-a-table-pointed-to-by-a-pml4e
  (implies (and (x86p x86)
                (canonical-address-p lin-addr)
                (equal pml4-table-base-addr
                       (mv-nth 1 (pml4-table-base-addr x86)))
                (equal
                 (ia32e-page-tables-slice
                  :p (rm-low-64 (pml4-table-entry-addr lin-addr pml4-table-base-addr)
                                x86))
                 1)
                (equal
                 (ia32e-page-tables-slice
                  :ps (rm-low-64 (pml4-table-entry-addr lin-addr pml4-table-base-addr)
                                 x86))
                 0)
                (physical-address-p
                 (+
                  (ash 512 3)
                  (ash
                   (ia32e-page-tables-slice
                    :reference-addr
                    (rm-low-64 (pml4-table-entry-addr lin-addr pml4-table-base-addr)
                               x86))
                   12))))
           (member-p
            (page-dir-ptr-table-entry-addr
             lin-addr
             (mv-nth 1 (page-dir-ptr-table-base-addr lin-addr x86)))
            (gather-qword-addresses-corresponding-to-1-entry
             (pml4-table-entry-addr lin-addr pml4-table-base-addr)
             x86)))
  :hints (("Goal"
           :in-theory (e/d* (gather-qword-addresses-corresponding-to-1-entry
                             page-dir-ptr-table-entry-addr
                             page-dir-ptr-table-base-addr)
                            ()))))

(defthm gather-qword-addresses-corresponding-to-1-entry-and-to-entries
  (implies (and (physical-address-p
                 (+ (ash 512 3)
                    (ash (ia32e-page-tables-slice :reference-addr (rm-low-64 paddr x86))
                         12)))
                (qword-paddr-listp paddrs)
                (equal (ia32e-page-tables-slice :p (rm-low-64 paddr x86)) 1)
                (equal (ia32e-page-tables-slice :ps (rm-low-64 paddr x86)) 0)
                (member-p paddr paddrs))
           (subset-list-p
            (gather-qword-addresses-corresponding-to-1-entry paddr x86)
            (gather-qword-addresses-corresponding-to-entries paddrs x86)))

  :hints (("Goal" :in-theory (e/d* (gather-qword-addresses-corresponding-to-1-entry
                                    gather-qword-addresses-corresponding-to-entries
                                    gather-pml4-table-qword-addresses
                                    pml4-table-base-addr
                                    pml4-table-entry-addr
                                    subset-p)
                                   ()))))

(defthm qword-paddrs-for-pml4-table-base-addr-are-a-subset-of-those-for-all-entries
  (implies (and (equal pml4-table-base-addr
                       (mv-nth 1 (pml4-table-base-addr x86)))
                (physical-address-p (+ (ash 512 3) pml4-table-base-addr))
                (physical-address-p
                 (+ (ash 512 3)
                    (ash (ia32e-page-tables-slice
                          :reference-addr (rm-low-64 pml4-table-base-addr x86))
                         12)))
                (equal (ia32e-page-tables-slice :p (rm-low-64 pml4-table-base-addr x86))
                       1)
                (equal (ia32e-page-tables-slice :ps (rm-low-64 pml4-table-base-addr x86))
                       0))
           (subset-list-p
            (gather-qword-addresses-corresponding-to-1-entry pml4-table-base-addr x86)
            (gather-qword-addresses-corresponding-to-entries
             (gather-pml4-table-qword-addresses x86)
             x86)))
  :hints (("Goal"
           :in-theory (e/d* (gather-qword-addresses-corresponding-to-1-entry
                             gather-qword-addresses-corresponding-to-entries
                             gather-pml4-table-qword-addresses
                             pml4-table-base-addr
                             pml4-table-entry-addr
                             subset-p)
                            ()))))

(defthm qword-paddrs-for-pml4-table-entry-addr-are-a-subset-of-those-for-all-entries
  (implies (and (equal pml4-table-base-addr (mv-nth 1 (pml4-table-base-addr x86)))
                (physical-address-p (+ (ash 512 3) pml4-table-base-addr))
                (canonical-address-p lin-addr)
                (physical-address-p
                 (+
                  (ash 512 3)
                  (ash
                   (ia32e-page-tables-slice
                    :reference-addr
                    (rm-low-64 pml4-table-base-addr x86))
                   12)))
                (equal
                 (ia32e-page-tables-slice
                  :p (rm-low-64 (pml4-table-entry-addr lin-addr pml4-table-base-addr)
                                x86))
                 1)
                (equal
                 (ia32e-page-tables-slice
                  :ps (rm-low-64 (pml4-table-entry-addr lin-addr pml4-table-base-addr)
                                 x86))
                 0)
                (physical-address-p
                 (+
                  (ash 512 3)
                  (ash
                   (ia32e-page-tables-slice
                    :reference-addr
                    (rm-low-64 (pml4-table-entry-addr lin-addr pml4-table-base-addr)
                               x86))
                   12))))
           (subset-list-p
            (gather-qword-addresses-corresponding-to-1-entry
             (pml4-table-entry-addr lin-addr pml4-table-base-addr)
             x86)
            (gather-qword-addresses-corresponding-to-entries
             (gather-pml4-table-qword-addresses x86)
             x86)))
  :hints (("Goal" :in-theory (e/d* () (subset-list-p)))))

(defthm page-dir-ptr-table-base-addr-is-in-gather-all-paging-structure-qword-addresses
  (implies
   (and (canonical-address-p lin-addr)
        (physical-address-p (+ (ash 512 3) pml4-table-base-addr))
        (equal pml4-table-base-addr (mv-nth 1 (pml4-table-base-addr x86)))
        (equal
         (ia32e-page-tables-slice
          :p (rm-low-64 (pml4-table-entry-addr lin-addr pml4-table-base-addr)
                        x86))
         1)
        (equal
         (ia32e-page-tables-slice
          :ps (rm-low-64 (pml4-table-entry-addr lin-addr pml4-table-base-addr)
                         x86))
         0)
        (physical-address-p
         (+
          (ash 512 3)
          (ash
           (ia32e-page-tables-slice
            :reference-addr
            (rm-low-64 (pml4-table-entry-addr lin-addr pml4-table-base-addr)
                       x86))
           12))))
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
  (implies (and (x86p x86)
                (equal pml4-table-base-addr
                       (mv-nth 1 (pml4-table-base-addr x86)))
                (physical-address-p (+ (ash 512 3) pml4-table-base-addr))
                (canonical-address-p lin-addr)
                (equal
                 (ia32e-page-tables-slice
                  :p (rm-low-64 (pml4-table-entry-addr lin-addr pml4-table-base-addr)
                                x86))
                 1)
                (equal
                 (ia32e-page-tables-slice
                  :ps (rm-low-64 (pml4-table-entry-addr lin-addr pml4-table-base-addr)
                                 x86))
                 0)
                (physical-address-p
                 (+
                  (ash 512 3)
                  (ash
                   (ia32e-page-tables-slice
                    :reference-addr
                    (rm-low-64 (pml4-table-entry-addr lin-addr pml4-table-base-addr)
                               x86))
                   12))))
           (member-list-p (page-dir-ptr-table-entry-addr
                           lin-addr
                           (mv-nth 1 (page-dir-ptr-table-base-addr lin-addr x86)))
                          (gather-all-paging-structure-qword-addresses x86)))
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
           :in-theory (e/d* (gather-all-paging-structure-qword-addresses)
                            (subset-list-p-and-member-list-p)))))

;; ======================================================================

(defthm page-directory-base-addr-is-in-a-table-pointed-to-by-a-pdpte
  (implies (and (equal page-dir-ptr-table-base-addr
                       (mv-nth 1 (page-dir-ptr-table-base-addr lin-addr x86)))
                (equal
                 (ia32e-page-tables-slice
                  :p (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr page-dir-ptr-table-base-addr)
                                x86))
                 1)
                (equal
                 (ia32e-page-tables-slice
                  :ps (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr page-dir-ptr-table-base-addr)
                                 x86))
                 0)
                (physical-address-p
                 (+
                  (ash 512 3)
                  (ash
                   (ia32e-page-tables-slice
                    :reference-addr
                    (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr page-dir-ptr-table-base-addr)
                               x86))
                   12))))
           (member-p
            (mv-nth 1 (page-directory-base-addr lin-addr x86))
            (gather-qword-addresses-corresponding-to-1-entry
             (page-dir-ptr-table-entry-addr lin-addr page-dir-ptr-table-base-addr)
             x86)))
  :hints (("Goal"
           :in-theory (e/d* (gather-qword-addresses-corresponding-to-1-entry
                             page-directory-entry-addr
                             page-directory-base-addr)
                            ()))))

(local
 (def-gl-thm page-directory-entry-addr-is-in-a-table-pointed-to-by-a-pdpte-helper-1
   :hyp (and (unsigned-byte-p 64 x)
             (canonical-address-p l))
   :concl (<
           (logior (ash (loghead 9 (logtail 21 l)) 3)
                   (ash (loghead 40 (logtail 12 x)) 12))
           (+ 4096 (ash (loghead 40 (logtail 12 x)) 12)))
   :g-bindings `((x (:g-number ,(gl-int 0 2 65)))
                 (l (:g-number ,(gl-int 1 2 65))))
   :rule-classes :linear))

(defthm page-directory-entry-addr-is-in-a-table-pointed-to-by-a-pdpte
  (implies (and (x86p x86)
                (canonical-address-p lin-addr)
                (equal page-dir-ptr-table-base-addr
                       (mv-nth 1 (page-dir-ptr-table-base-addr lin-addr x86)))
                (equal
                 (ia32e-page-tables-slice
                  :p (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr page-dir-ptr-table-base-addr)
                                x86))
                 1)
                (equal
                 (ia32e-page-tables-slice
                  :ps (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr page-dir-ptr-table-base-addr)
                                 x86))
                 0)
                (physical-address-p
                 (+
                  (ash 512 3)
                  (ash
                   (ia32e-page-tables-slice
                    :reference-addr
                    (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr page-dir-ptr-table-base-addr)
                               x86))
                   12))))
           (member-p
            (page-directory-entry-addr
             lin-addr
             (mv-nth 1 (page-directory-base-addr lin-addr x86)))
            (gather-qword-addresses-corresponding-to-1-entry
             (page-dir-ptr-table-entry-addr lin-addr page-dir-ptr-table-base-addr)
             x86)))
  :hints (("Goal"
           :in-theory (e/d* (gather-qword-addresses-corresponding-to-1-entry
                             page-directory-entry-addr
                             page-directory-base-addr)
                            ()))))

(defthm gather-qword-addresses-corresponding-to-entries-and-to-list-of-entries
  (implies (and (physical-address-p
                 (+ (ash 512 3)
                    (ash (ia32e-page-tables-slice :reference-addr (rm-low-64 paddr x86))
                         12)))
                (qword-paddr-list-listp paddrs-list)
                (equal (ia32e-page-tables-slice :p (rm-low-64 paddr x86)) 1)
                (equal (ia32e-page-tables-slice :ps (rm-low-64 paddr x86)) 0)
                (member-list-p paddr paddrs-list))
           (subset-list-p
            (gather-qword-addresses-corresponding-to-1-entry paddr x86)
            (gather-qword-addresses-corresponding-to-list-of-entries
             paddrs-list x86)))

  :hints (("Goal" :in-theory (e/d* (gather-qword-addresses-corresponding-to-entries
                                    gather-qword-addresses-corresponding-to-list-of-entries
                                    gather-pml4-table-qword-addresses
                                    pml4-table-base-addr
                                    pml4-table-entry-addr
                                    subset-p)
                                   ()))))

(defthm page-dir-ptr-table-entry-addr-is-in-a-table-pointed-to-by-a-pml4e-alt-helper-1
  (implies (and
            (equal pml4-table-base-addr
                   (mv-nth 1 (pml4-table-base-addr x86)))
            (physical-address-p (+ (ash 512 3) pml4-table-base-addr))
            (canonical-address-p lin-addr)
            (equal
             (ia32e-page-tables-slice
              :p (rm-low-64 (pml4-table-entry-addr lin-addr pml4-table-base-addr)
                            x86))
             1)
            (equal
             (ia32e-page-tables-slice
              :ps (rm-low-64 (pml4-table-entry-addr lin-addr pml4-table-base-addr)
                             x86))
             0)
            (physical-address-p
             (+
              (ash 512 3)
              (ash
               (ia32e-page-tables-slice
                :reference-addr
                (rm-low-64 (pml4-table-entry-addr lin-addr pml4-table-base-addr)
                           x86))
               12))))
           (subset-list-p
            (gather-qword-addresses-corresponding-to-1-entry
             (pml4-table-entry-addr lin-addr pml4-table-base-addr)
             x86)
            (gather-qword-addresses-corresponding-to-entries
             (gather-pml4-table-qword-addresses x86)
             x86)))
  :hints (("Goal" :in-theory (e/d* (gather-qword-addresses-corresponding-to-entries
                                    subset-p)
                                   ()))))

(defthm page-dir-ptr-table-entry-addr-is-in-a-table-pointed-to-by-a-pml4e-alt
  (implies (and
            (physical-address-p (+ (ash 512 3) pml4-table-base-addr))
            (x86p x86)
            (canonical-address-p lin-addr)
            (equal pml4-table-base-addr
                   (mv-nth 1 (pml4-table-base-addr x86)))
            (equal
             (ia32e-page-tables-slice
              :p (rm-low-64 (pml4-table-entry-addr lin-addr pml4-table-base-addr)
                            x86))
             1)
            (equal
             (ia32e-page-tables-slice
              :ps (rm-low-64 (pml4-table-entry-addr lin-addr pml4-table-base-addr)
                             x86))
             0)
            (physical-address-p
             (+
              (ash 512 3)
              (ash
               (ia32e-page-tables-slice
                :reference-addr
                (rm-low-64 (pml4-table-entry-addr lin-addr pml4-table-base-addr)
                           x86))
               12))))
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

(defthm page-directory-base-addr-is-in-gather-all-paging-structure-qword-addresses-helper
  (implies
   (and (x86p x86)
        (canonical-address-p lin-addr)
        (equal pml4-table-base-addr
               (mv-nth 1 (pml4-table-base-addr x86)))
        (physical-address-p (+ (ash 512 3) pml4-table-base-addr))
        (equal
         (ia32e-page-tables-slice
          :p (rm-low-64 (pml4-table-entry-addr lin-addr pml4-table-base-addr)
                        x86))
         1)
        (equal
         (ia32e-page-tables-slice
          :ps (rm-low-64 (pml4-table-entry-addr lin-addr pml4-table-base-addr)
                         x86))
         0)
        (physical-address-p
         (+
          (ash 512 3)
          (ash
           (ia32e-page-tables-slice
            :reference-addr
            (rm-low-64 (pml4-table-entry-addr lin-addr pml4-table-base-addr)
                       x86))
           12)))
        (equal page-dir-ptr-table-base-addr
               (mv-nth 1 (page-dir-ptr-table-base-addr lin-addr x86)))
        (equal
         (ia32e-page-tables-slice
          :p (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr page-dir-ptr-table-base-addr)
                        x86))
         1)
        (equal
         (ia32e-page-tables-slice
          :ps (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr page-dir-ptr-table-base-addr)
                         x86))
         0)
        (physical-address-p
         (+
          (ash 512 3)
          (ash
           (ia32e-page-tables-slice
            :reference-addr
            (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr page-dir-ptr-table-base-addr)
                       x86))
           12))))
   (subset-list-p
    ;; PD qword addresses corresponding to a PDPTE.
    (gather-qword-addresses-corresponding-to-1-entry
     (page-dir-ptr-table-entry-addr lin-addr page-dir-ptr-table-base-addr)
     x86)
    ;; All PD qword addresses.
    (gather-qword-addresses-corresponding-to-list-of-entries
     ;; All PDPTE qword addresses.
     (gather-qword-addresses-corresponding-to-entries
      (gather-pml4-table-qword-addresses x86)
      x86)
     x86)))
  :hints (("Goal" :in-theory (e/d* ()
                                   (page-dir-ptr-table-entry-addr-is-in-a-table-pointed-to-by-a-pml4e-alt))
           :use ((:instance page-dir-ptr-table-entry-addr-is-in-a-table-pointed-to-by-a-pml4e-alt)))))

(defthm page-directory-base-addr-is-in-gather-all-paging-structure-qword-addresses
  (implies (and (x86p x86)
                (canonical-address-p lin-addr)
                (equal pml4-table-base-addr
                       (mv-nth 1 (pml4-table-base-addr x86)))
                (physical-address-p (+ (ash 512 3) pml4-table-base-addr))
                (equal
                 (ia32e-page-tables-slice
                  :p (rm-low-64 (pml4-table-entry-addr lin-addr pml4-table-base-addr)
                                x86))
                 1)
                (equal
                 (ia32e-page-tables-slice
                  :ps (rm-low-64 (pml4-table-entry-addr lin-addr pml4-table-base-addr)
                                 x86))
                 0)
                (physical-address-p
                 (+
                  (ash 512 3)
                  (ash
                   (ia32e-page-tables-slice
                    :reference-addr
                    (rm-low-64 (pml4-table-entry-addr lin-addr pml4-table-base-addr)
                               x86))
                   12)))
                (equal page-dir-ptr-table-base-addr
                       (mv-nth 1 (page-dir-ptr-table-base-addr lin-addr x86)))
                (equal
                 (ia32e-page-tables-slice
                  :p (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr page-dir-ptr-table-base-addr)
                                x86))
                 1)
                (equal
                 (ia32e-page-tables-slice
                  :ps (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr page-dir-ptr-table-base-addr)
                                 x86))
                 0)
                (physical-address-p
                 (+
                  (ash 512 3)
                  (ash
                   (ia32e-page-tables-slice
                    :reference-addr
                    (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr page-dir-ptr-table-base-addr)
                               x86))
                   12))))
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
  (implies (and (x86p x86)
                (canonical-address-p lin-addr)
                (equal pml4-table-base-addr
                       (mv-nth 1 (pml4-table-base-addr x86)))
                (physical-address-p (+ (ash 512 3) pml4-table-base-addr))
                (equal
                 (ia32e-page-tables-slice
                  :p (rm-low-64 (pml4-table-entry-addr lin-addr pml4-table-base-addr)
                                x86))
                 1)
                (equal
                 (ia32e-page-tables-slice
                  :ps (rm-low-64 (pml4-table-entry-addr lin-addr pml4-table-base-addr)
                                 x86))
                 0)
                (physical-address-p
                 (+
                  (ash 512 3)
                  (ash
                   (ia32e-page-tables-slice
                    :reference-addr
                    (rm-low-64 (pml4-table-entry-addr lin-addr pml4-table-base-addr)
                               x86))
                   12)))
                (equal page-dir-ptr-table-base-addr
                       (mv-nth 1 (page-dir-ptr-table-base-addr lin-addr x86)))
                (equal
                 (ia32e-page-tables-slice
                  :p (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr page-dir-ptr-table-base-addr)
                                x86))
                 1)
                (equal
                 (ia32e-page-tables-slice
                  :ps (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr page-dir-ptr-table-base-addr)
                                 x86))
                 0)
                (physical-address-p
                 (+
                  (ash 512 3)
                  (ash
                   (ia32e-page-tables-slice
                    :reference-addr
                    (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr page-dir-ptr-table-base-addr)
                               x86))
                   12))))
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
                                 (page-dir-ptr-table-entry-addr lin-addr page-dir-ptr-table-base-addr)
                                 x86))
                            (xss (gather-all-paging-structure-qword-addresses x86))))
           :in-theory (e/d* (gather-all-paging-structure-qword-addresses)
                            (subset-list-p-and-member-list-p)))))

;; ======================================================================

(defthm page-table-base-addr-is-in-a-table-pointed-to-by-a-pde
  (implies (and
            (equal page-dir-ptr-table-base-addr
                   (mv-nth 1 (page-dir-ptr-table-base-addr lin-addr x86)))
            (equal
             (ia32e-page-tables-slice
              :ps
              (rm-low-64
               (page-dir-ptr-table-entry-addr lin-addr page-dir-ptr-table-base-addr)
               x86))
             0)
            (equal page-directory-base-addr
                   (mv-nth 1 (page-directory-base-addr lin-addr x86)))
            (equal
             (ia32e-page-tables-slice
              :p
              (rm-low-64 (page-directory-entry-addr lin-addr page-directory-base-addr)
                         x86))
             1)
            (equal
             (ia32e-page-tables-slice
              :ps
              (rm-low-64 (page-directory-entry-addr lin-addr page-directory-base-addr)
                         x86))
             0)
            (physical-address-p
             (+
              (ash 512 3)
              (ash
               (ia32e-page-tables-slice
                :reference-addr
                (rm-low-64
                 (page-directory-entry-addr lin-addr page-directory-base-addr)
                 x86))
               12))))
           (member-p
            (mv-nth 1 (page-table-base-addr lin-addr x86))
            (gather-qword-addresses-corresponding-to-1-entry
             (page-directory-entry-addr lin-addr page-directory-base-addr)
             x86)))
  :hints (("Goal"
           :in-theory (e/d* (gather-qword-addresses-corresponding-to-1-entry
                             page-directory-entry-addr
                             page-directory-base-addr
                             page-table-entry-addr
                             page-table-base-addr)
                            ()))))

(local
 (def-gl-thm page-table-entry-addr-is-in-a-table-pointed-to-by-a-pde-helper-1
   :hyp (and (unsigned-byte-p 64 x)
             (canonical-address-p l))
   :concl (<
           (logior (ash (loghead 9 (logtail 12 l)) 3)
                   (ash (loghead 40 (logtail 12 x)) 12))
           (+ 4096 (ash (loghead 40 (logtail 12 x)) 12)))
   :g-bindings `((x (:g-number ,(gl-int 0 2 65)))
                 (l (:g-number ,(gl-int 1 2 65))))
   :rule-classes :linear))

(defthm page-table-entry-addr-is-in-a-table-pointed-to-by-a-pde
  (implies (and
            (x86p x86)
            (canonical-address-p lin-addr)

            (equal page-dir-ptr-table-base-addr
                   (mv-nth 1 (page-dir-ptr-table-base-addr lin-addr x86)))
            (equal
             (ia32e-page-tables-slice
              :ps
              (rm-low-64
               (page-dir-ptr-table-entry-addr lin-addr page-dir-ptr-table-base-addr)
               x86))
             0)
            (equal page-directory-base-addr
                   (mv-nth 1 (page-directory-base-addr lin-addr x86)))
            (equal
             (ia32e-page-tables-slice
              :p
              (rm-low-64 (page-directory-entry-addr lin-addr page-directory-base-addr)
                         x86))
             1)
            (equal
             (ia32e-page-tables-slice
              :ps
              (rm-low-64 (page-directory-entry-addr lin-addr page-directory-base-addr)
                         x86))
             0)
            (physical-address-p
             (+
              (ash 512 3)
              (ash
               (ia32e-page-tables-slice
                :reference-addr
                (rm-low-64
                 (page-directory-entry-addr lin-addr page-directory-base-addr)
                 x86))
               12))))
           (member-p
            (page-table-entry-addr
             lin-addr (mv-nth 1 (page-table-base-addr lin-addr x86)))
            (gather-qword-addresses-corresponding-to-1-entry
             (page-directory-entry-addr lin-addr page-directory-base-addr)
             x86)))
  :hints (("Goal"
           :in-theory (e/d* (gather-qword-addresses-corresponding-to-1-entry
                             page-directory-entry-addr
                             page-directory-base-addr
                             page-table-entry-addr
                             page-table-base-addr)
                            ()))))

(defthm page-directory-entry-addr-is-in-a-table-pointed-to-by-a-pdpte-alt
  (implies
   (and (x86p x86)
        (canonical-address-p lin-addr)
        (equal pml4-table-base-addr
               (mv-nth 1 (pml4-table-base-addr x86)))
        (physical-address-p (+ (ash 512 3) pml4-table-base-addr))
        (equal
         (ia32e-page-tables-slice
          :p (rm-low-64 (pml4-table-entry-addr lin-addr pml4-table-base-addr)
                        x86))
         1)
        (equal
         (ia32e-page-tables-slice
          :ps (rm-low-64 (pml4-table-entry-addr lin-addr pml4-table-base-addr)
                         x86))
         0)
        (physical-address-p
         (+
          (ash 512 3)
          (ash
           (ia32e-page-tables-slice
            :reference-addr
            (rm-low-64 (pml4-table-entry-addr lin-addr pml4-table-base-addr)
                       x86))
           12)))
        (equal page-dir-ptr-table-base-addr
               (mv-nth 1 (page-dir-ptr-table-base-addr lin-addr x86)))
        (equal
         (ia32e-page-tables-slice
          :p
          (rm-low-64
           (page-dir-ptr-table-entry-addr lin-addr page-dir-ptr-table-base-addr) x86))
         1)
        (equal
         (ia32e-page-tables-slice
          :ps
          (rm-low-64
           (page-dir-ptr-table-entry-addr lin-addr page-dir-ptr-table-base-addr)
           x86))
         0)
        (physical-address-p
         (+
          (ash 512 3)
          (ash
           (ia32e-page-tables-slice
            :reference-addr
            (rm-low-64
             (page-dir-ptr-table-entry-addr lin-addr page-dir-ptr-table-base-addr)
             x86))
           12)))
        (equal page-directory-base-addr (mv-nth 1 (page-directory-base-addr lin-addr x86))))
   (member-list-p
    (page-directory-entry-addr lin-addr page-directory-base-addr)
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

(defthm page-table-base-addr-is-in-gather-all-paging-structure-qword-addresses-helper
  (implies
   (and (x86p x86)
        (canonical-address-p lin-addr)
        (equal pml4-table-base-addr
               (mv-nth 1 (pml4-table-base-addr x86)))
        (physical-address-p (+ (ash 512 3) pml4-table-base-addr))
        (equal
         (ia32e-page-tables-slice
          :p (rm-low-64 (pml4-table-entry-addr lin-addr pml4-table-base-addr)
                        x86))
         1)
        (equal
         (ia32e-page-tables-slice
          :ps (rm-low-64 (pml4-table-entry-addr lin-addr pml4-table-base-addr)
                         x86))
         0)
        (physical-address-p
         (+
          (ash 512 3)
          (ash
           (ia32e-page-tables-slice
            :reference-addr
            (rm-low-64 (pml4-table-entry-addr lin-addr pml4-table-base-addr)
                       x86))
           12)))
        (equal page-dir-ptr-table-base-addr
               (mv-nth 1 (page-dir-ptr-table-base-addr lin-addr x86)))
        (equal
         (ia32e-page-tables-slice
          :p (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr page-dir-ptr-table-base-addr)
                        x86))
         1)
        (equal
         (ia32e-page-tables-slice
          :ps (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr page-dir-ptr-table-base-addr)
                         x86))
         0)
        (physical-address-p
         (+
          (ash 512 3)
          (ash
           (ia32e-page-tables-slice
            :reference-addr
            (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr page-dir-ptr-table-base-addr)
                       x86))
           12)))
        (equal page-directory-base-addr
               (mv-nth 1 (page-directory-base-addr lin-addr x86)))
        (equal
         (ia32e-page-tables-slice
          :p (rm-low-64 (page-directory-entry-addr lin-addr page-directory-base-addr)
                        x86))
         1)
        (equal
         (ia32e-page-tables-slice
          :ps (rm-low-64 (page-directory-entry-addr lin-addr page-directory-base-addr)
                         x86))
         0)
        (physical-address-p
         (+
          (ash 512 3)
          (ash
           (ia32e-page-tables-slice
            :reference-addr
            (rm-low-64 (page-directory-entry-addr lin-addr page-directory-base-addr)
                       x86))
           12))))
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
     x86))))

(defthm page-table-base-addr-is-in-gather-all-paging-structure-qword-addresses
  (implies (and (x86p x86)
                (canonical-address-p lin-addr)
                (equal pml4-table-base-addr
                       (mv-nth 1 (pml4-table-base-addr x86)))
                (physical-address-p (+ (ash 512 3) pml4-table-base-addr))
                (equal
                 (ia32e-page-tables-slice
                  :p (rm-low-64 (pml4-table-entry-addr lin-addr pml4-table-base-addr)
                                x86))
                 1)
                (equal
                 (ia32e-page-tables-slice
                  :ps (rm-low-64 (pml4-table-entry-addr lin-addr pml4-table-base-addr)
                                 x86))
                 0)
                (physical-address-p
                 (+
                  (ash 512 3)
                  (ash
                   (ia32e-page-tables-slice
                    :reference-addr
                    (rm-low-64 (pml4-table-entry-addr lin-addr pml4-table-base-addr)
                               x86))
                   12)))
                (equal page-dir-ptr-table-base-addr
                       (mv-nth 1 (page-dir-ptr-table-base-addr lin-addr x86)))
                (equal
                 (ia32e-page-tables-slice
                  :p (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr page-dir-ptr-table-base-addr)
                                x86))
                 1)
                (equal
                 (ia32e-page-tables-slice
                  :ps (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr page-dir-ptr-table-base-addr)
                                 x86))
                 0)
                (physical-address-p
                 (+
                  (ash 512 3)
                  (ash
                   (ia32e-page-tables-slice
                    :reference-addr
                    (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr page-dir-ptr-table-base-addr)
                               x86))
                   12)))
                (equal page-directory-base-addr
                       (mv-nth 1 (page-directory-base-addr lin-addr x86)))
                (equal
                 (ia32e-page-tables-slice
                  :p (rm-low-64 (page-directory-entry-addr lin-addr page-directory-base-addr)
                                x86))
                 1)
                (equal
                 (ia32e-page-tables-slice
                  :ps (rm-low-64 (page-directory-entry-addr lin-addr page-directory-base-addr)
                                 x86))
                 0)
                (physical-address-p
                 (+
                  (ash 512 3)
                  (ash
                   (ia32e-page-tables-slice
                    :reference-addr
                    (rm-low-64 (page-directory-entry-addr lin-addr page-directory-base-addr)
                               x86))
                   12))))
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
  (implies (and (x86p x86)
                (canonical-address-p lin-addr)
                (equal pml4-table-base-addr
                       (mv-nth 1 (pml4-table-base-addr x86)))
                (physical-address-p (+ (ash 512 3) pml4-table-base-addr))
                (equal
                 (ia32e-page-tables-slice
                  :p (rm-low-64 (pml4-table-entry-addr lin-addr pml4-table-base-addr)
                                x86))
                 1)
                (equal
                 (ia32e-page-tables-slice
                  :ps (rm-low-64 (pml4-table-entry-addr lin-addr pml4-table-base-addr)
                                 x86))
                 0)
                (physical-address-p
                 (+
                  (ash 512 3)
                  (ash
                   (ia32e-page-tables-slice
                    :reference-addr
                    (rm-low-64 (pml4-table-entry-addr lin-addr pml4-table-base-addr)
                               x86))
                   12)))
                (equal page-dir-ptr-table-base-addr
                       (mv-nth 1 (page-dir-ptr-table-base-addr lin-addr x86)))
                (equal
                 (ia32e-page-tables-slice
                  :p (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr page-dir-ptr-table-base-addr)
                                x86))
                 1)
                (equal
                 (ia32e-page-tables-slice
                  :ps (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr page-dir-ptr-table-base-addr)
                                 x86))
                 0)
                (physical-address-p
                 (+
                  (ash 512 3)
                  (ash
                   (ia32e-page-tables-slice
                    :reference-addr
                    (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr page-dir-ptr-table-base-addr)
                               x86))
                   12)))
                (equal page-directory-base-addr
                       (mv-nth 1 (page-directory-base-addr lin-addr x86)))
                (equal
                 (ia32e-page-tables-slice
                  :p (rm-low-64 (page-directory-entry-addr lin-addr page-directory-base-addr)
                                x86))
                 1)
                (equal
                 (ia32e-page-tables-slice
                  :ps (rm-low-64 (page-directory-entry-addr lin-addr page-directory-base-addr)
                                 x86))
                 0)
                (physical-address-p
                 (+
                  (ash 512 3)
                  (ash
                   (ia32e-page-tables-slice
                    :reference-addr
                    (rm-low-64 (page-directory-entry-addr lin-addr page-directory-base-addr)
                               x86))
                   12))))
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
                                 (page-directory-entry-addr lin-addr page-directory-base-addr)
                                 x86))
                            (xss (gather-all-paging-structure-qword-addresses x86))))
           :in-theory (e/d* (gather-all-paging-structure-qword-addresses)
                            (subset-list-p-and-member-list-p)))))

;; ======================================================================

;; (gather-all-paging-structure-qword-addresses
;;  (wm-low-64
;;   (page-table-entry-addr
;;    (logext 48 lin-addr)
;;    (bitops::logsquash
;;     12
;;     (loghead 52
;;              (mv-nth 1
;;                      (page-table-base-addr lin-addr x86)))))
;;   (set-accessed-bit
;;    (rm-low-64
;;     (page-table-entry-addr
;;      (logext 48 lin-addr)
;;      (bitops::logsquash
;;       12
;;       (loghead 52
;;                (mv-nth 1
;;                        (page-table-base-addr lin-addr x86)))))
;;     x86))
;;   x86))

;; (xlate-equiv-entries-at-qword-addresses?
;;  (gather-all-paging-structure-qword-addresses
;;   (wm-low-64
;;    (page-table-entry-addr
;;     (logext 48 lin-addr)
;;     (bitops::logsquash
;;      12
;;      (loghead 52
;;               (mv-nth 1
;;                       (page-table-base-addr lin-addr x86)))))
;;    (set-accessed-bit
;;     (rm-low-64
;;      (page-table-entry-addr
;;       (logext 48 lin-addr)
;;       (bitops::logsquash
;;        12
;;        (loghead 52
;;                 (mv-nth 1
;;                         (page-table-base-addr lin-addr x86)))))
;;      x86))
;;    x86))
;;  (gather-all-paging-structure-qword-addresses x86)
;;  (wm-low-64
;;   (page-table-entry-addr
;;    (logext 48 lin-addr)
;;    (bitops::logsquash
;;     12
;;     (loghead 52
;;              (mv-nth 1
;;                      (page-table-base-addr lin-addr x86)))))
;;   (set-accessed-bit
;;    (rm-low-64
;;     (page-table-entry-addr
;;      (logext 48 lin-addr)
;;      (bitops::logsquash
;;       12
;;       (loghead 52
;;                (mv-nth 1
;;                        (page-table-base-addr lin-addr x86)))))
;;     x86))
;;   x86)
;;  x86)
