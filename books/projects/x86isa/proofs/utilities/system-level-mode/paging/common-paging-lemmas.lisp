;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")
(include-book "paging-basics" :ttags :all)

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))

(local (in-theory (e/d () (unsigned-byte-p signed-byte-p))))

(local (xdoc::set-default-parents gather-paging-structures))

;; ======================================================================

;; Defining xlation-governing-entries-paddrs of linear addresses:

(defthm |(logand -4096 base-addr) = base-addr when low 12 bits are 0|
  (implies (and (equal (loghead 12 base-addr) 0)
                (physical-address-p base-addr))
           (equal (logand -4096 base-addr) base-addr))
  :hints (("Goal" :in-theory (e/d* (bitops::ihsext-recursive-redefs
                                    bitops::ihsext-inductions)
                                   (bitops::logand-with-negated-bitmask)))))

(defthm page-present=0-and-paging-entry-no-page-fault-p
  (implies
   (equal (page-present entry) 0)
   (equal (mv-nth 0
                  (paging-entry-no-page-fault-p
                   structure-type lin-addr
                   entry u-s-acc r/w-acc x/d-acc wp
                   smep smap ac nxe r-w-x cpl x86 ignored))
          t))
  :hints
  (("Goal"
    :in-theory (e/d* (paging-entry-no-page-fault-p
                      page-fault-exception page-present)
                     ()))))

(defthm page-size=1-and-paging-entry-no-page-fault-p-for-structure-type=3
  (implies
   (equal (page-size entry) 1)
   (equal (mv-nth 0
                  (paging-entry-no-page-fault-p
                   3 lin-addr
                   entry u-s-acc r/w-acc x/d-acc wp
                   smep smap ac nxe r-w-x cpl x86 ignored))
          t))
  :hints
  (("Goal"
    :in-theory (e/d* (paging-entry-no-page-fault-p
                      page-fault-exception page-size)
                     ()))))

(i-am-here)

;; TODO: xlation-governing-entries-paddrs-* do not talk about validity
;; of paging entries.  Do we want that or not?

(define xlation-governing-entries-paddrs-for-page-table
  ((lin-addr             :type (signed-byte   #.*max-linear-address-size*))
   (page-table-base-addr :type (unsigned-byte #.*physical-address-size*))
   (x86))
  :guard (and (not (programmer-level-mode x86))
              (canonical-address-p lin-addr)
              (equal (loghead 12 page-table-base-addr) 0))
  :ignore-ok t

  (b* ((page-table-entry-addr
        (page-table-entry-addr lin-addr page-table-base-addr)))
    ;; 4K pages
    (addr-range 8 page-table-entry-addr))

  ///

  (defthm xlation-governing-entries-paddrs-for-page-table-and-xw-not-mem
    (implies (and (not (equal fld :mem))
                  (not (equal fld :programmer-level-mode)))
             (equal (xlation-governing-entries-paddrs-for-page-table lin-addr base-addr (xw fld index value x86))
                    (xlation-governing-entries-paddrs-for-page-table lin-addr base-addr (double-rewrite x86)))))

  (defthm xlation-governing-entries-paddrs-for-page-table-and-xw-mem-not-member
    (implies (not (member-p index (xlation-governing-entries-paddrs-for-page-table lin-addr base-addr (double-rewrite x86))))
             (equal (xlation-governing-entries-paddrs-for-page-table lin-addr base-addr (xw :mem index value x86))
                    (xlation-governing-entries-paddrs-for-page-table lin-addr base-addr (double-rewrite x86))))
    :hints (("Goal" :in-theory (e/d* (disjoint-p member-p)
                                     ()))))

  (defthm ia32e-la-to-pa-page-table-values-and-xw-mem-not-member
    (implies (and (not (member-p index
                                 (xlation-governing-entries-paddrs-for-page-table
                                  lin-addr base-addr (double-rewrite x86))))
                  (physical-address-p base-addr)
                  (equal (loghead 12 base-addr) 0)
                  (canonical-address-p lin-addr))
             (and (equal (mv-nth 0 (ia32e-la-to-pa-page-table
                                    lin-addr
                                    base-addr u/s-acc r/w-acc x/d-acc
                                    wp smep smap ac nxe r-w-x cpl (xw :mem index value x86)))
                         (mv-nth 0 (ia32e-la-to-pa-page-table
                                    lin-addr
                                    base-addr u/s-acc r/w-acc x/d-acc
                                    wp smep smap ac nxe r-w-x cpl (double-rewrite x86))))
                  (equal (mv-nth 1 (ia32e-la-to-pa-page-table
                                    lin-addr
                                    base-addr u/s-acc r/w-acc x/d-acc
                                    wp smep smap ac nxe r-w-x cpl (xw :mem index value x86)))
                         (mv-nth 1 (ia32e-la-to-pa-page-table
                                    lin-addr
                                    base-addr u/s-acc r/w-acc x/d-acc
                                    wp smep smap ac nxe r-w-x cpl (double-rewrite x86))))))
    :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa-page-table disjoint-p member-p)
                                     (bitops::logand-with-negated-bitmask
                                      negative-logand-to-positive-logand-with-integerp-x))))))

(define xlation-governing-entries-paddrs-for-page-directory
  ((lin-addr                 :type (signed-byte   #.*max-linear-address-size*))
   (page-directory-base-addr :type (unsigned-byte #.*physical-address-size*))
   (x86))
  :guard (and (not (programmer-level-mode x86))
              (canonical-address-p lin-addr)
              (equal (loghead 12 page-directory-base-addr) 0))
  :guard-hints (("Goal" :in-theory (e/d* (canonical-address-p)
                                         (xlation-governing-entries-paddrs-for-page-table
                                          unsigned-byte-p
                                          signed-byte-p
                                          acl2::commutativity-of-logior))))

  (b* (
       ;; 2M pages:
       (page-directory-entry-addr
        (page-directory-entry-addr lin-addr page-directory-base-addr))
       (page-directory-entry (rm-low-64 page-directory-entry-addr x86))

       (pde-ps? (equal (page-size page-directory-entry) 1))
       ((when pde-ps?)
        (addr-range 8 page-directory-entry-addr))

       ;; 4K pages:
       (page-table-base-addr
        (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
       (page-table-addresses
        (xlation-governing-entries-paddrs-for-page-table
         lin-addr page-table-base-addr x86)))

    (append
     (addr-range 8 page-directory-entry-addr) page-table-addresses))

  ///

  (defthm xlation-governing-entries-paddrs-for-page-directory-and-xw-not-mem
    (implies (and (not (equal fld :mem))
                  (not (equal fld :programmer-level-mode)))
             (equal (xlation-governing-entries-paddrs-for-page-directory lin-addr base-addr (xw fld index value x86))
                    (xlation-governing-entries-paddrs-for-page-directory lin-addr base-addr (double-rewrite x86))))
    :hints (("Goal" :in-theory (e/d* () (xlation-governing-entries-paddrs-for-page-table)))))

  (defthm xlation-governing-entries-paddrs-for-page-directory-and-xw-mem-not-member
    (implies (not (member-p index (xlation-governing-entries-paddrs-for-page-directory lin-addr base-addr (double-rewrite x86))))
             (equal (xlation-governing-entries-paddrs-for-page-directory lin-addr base-addr (xw :mem index value x86))
                    (xlation-governing-entries-paddrs-for-page-directory lin-addr base-addr (double-rewrite x86))))
    :hints (("Goal" :in-theory (e/d* (disjoint-p member-p)
                                     (xlation-governing-entries-paddrs-for-page-table)))))

  (defthm ia32e-la-to-pa-page-directory-values-and-xw-mem-not-member
    (implies (and (not (member-p index
                                 (xlation-governing-entries-paddrs-for-page-directory
                                  lin-addr
                                  base-addr (double-rewrite x86))))
                  (physical-address-p base-addr)
                  (equal (loghead 12 base-addr) 0)
                  (canonical-address-p lin-addr))
             (and (equal (mv-nth 0 (ia32e-la-to-pa-page-directory
                                    lin-addr
                                    base-addr u/s-acc r/w-acc x/d-acc
                                    wp smep smap ac nxe r-w-x cpl (xw :mem index value x86)))
                         (mv-nth 0 (ia32e-la-to-pa-page-directory
                                    lin-addr
                                    base-addr u/s-acc r/w-acc x/d-acc
                                    wp smep smap ac nxe r-w-x cpl (double-rewrite x86))))
                  (equal (mv-nth 1 (ia32e-la-to-pa-page-directory
                                    lin-addr
                                    base-addr u/s-acc r/w-acc x/d-acc
                                    wp smep smap ac nxe r-w-x cpl (xw :mem index value x86)))
                         (mv-nth 1 (ia32e-la-to-pa-page-directory
                                    lin-addr
                                    base-addr u/s-acc r/w-acc x/d-acc
                                    wp smep smap ac nxe r-w-x cpl (double-rewrite x86))))))
    :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa-page-directory member-p disjoint-p)
                                     (bitops::logand-with-negated-bitmask
                                      negative-logand-to-positive-logand-with-integerp-x
                                      force (force)))))))

(define xlation-governing-entries-paddrs-for-page-dir-ptr-table
  ((lin-addr                 :type (signed-byte   #.*max-linear-address-size*))
   (ptr-table-base-addr :type (unsigned-byte #.*physical-address-size*))
   (x86))
  :guard (and (not (programmer-level-mode x86))
              (canonical-address-p lin-addr)
              (equal (loghead 12 ptr-table-base-addr) 0))
  :guard-hints (("Goal" :in-theory (e/d* (canonical-address-p)
                                         (xlation-governing-entries-paddrs-for-page-directory
                                          unsigned-byte-p
                                          signed-byte-p
                                          acl2::commutativity-of-logior))))

  (b* ((page-dir-ptr-table-entry-addr
        (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
       (page-dir-ptr-table-entry (rm-low-64 page-dir-ptr-table-entry-addr x86))

       (pdpte-ps? (equal (page-size page-dir-ptr-table-entry) 1))

       ;; 1G pages:
       ((when pdpte-ps?)
        (addr-range 8 page-dir-ptr-table-entry-addr))

       ;; 2M or 4K pages:

       (page-directory-base-addr (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd page-dir-ptr-table-entry) 12))
       (page-directory-addresses
        (xlation-governing-entries-paddrs-for-page-directory
         lin-addr page-directory-base-addr x86)))

    (append (addr-range 8 page-dir-ptr-table-entry-addr) page-directory-addresses))

  ///

  (defthm xlation-governing-entries-paddrs-for-page-dir-ptr-table-and-xw-not-mem
    (implies (and (not (equal fld :mem))
                  (not (equal fld :programmer-level-mode)))
             (equal (xlation-governing-entries-paddrs-for-page-dir-ptr-table lin-addr base-addr (xw fld index value x86))
                    (xlation-governing-entries-paddrs-for-page-dir-ptr-table lin-addr base-addr (double-rewrite x86))))
    :hints (("Goal" :in-theory (e/d* () (xlation-governing-entries-paddrs-for-page-directory)))))

  (defthm xlation-governing-entries-paddrs-for-page-dir-ptr-table-and-xw-mem-not-member
    (implies (not (member-p index (xlation-governing-entries-paddrs-for-page-dir-ptr-table lin-addr base-addr (double-rewrite x86))))
             (equal (xlation-governing-entries-paddrs-for-page-dir-ptr-table lin-addr base-addr (xw :mem index value x86))
                    (xlation-governing-entries-paddrs-for-page-dir-ptr-table lin-addr base-addr (double-rewrite x86))))
    :hints (("Goal" :in-theory (e/d* (disjoint-p member-p)
                                     (xlation-governing-entries-paddrs-for-page-directory)))))

  (defthm ia32e-la-to-pa-page-dir-ptr-table-values-and-xw-mem-not-member
    (implies (and
              (not
               (member-p
                index
                (xlation-governing-entries-paddrs-for-page-dir-ptr-table lin-addr base-addr (double-rewrite x86))))
              (physical-address-p base-addr)
              (equal (loghead 12 base-addr) 0)
              (canonical-address-p lin-addr))
             (and (equal (mv-nth 0 (ia32e-la-to-pa-page-dir-ptr-table
                                    lin-addr
                                    base-addr u/s-acc r/w-acc x/d-acc
                                    wp smep smap ac nxe r-w-x cpl (xw :mem index value x86)))
                         (mv-nth 0 (ia32e-la-to-pa-page-dir-ptr-table
                                    lin-addr
                                    base-addr u/s-acc r/w-acc x/d-acc
                                    wp smep smap ac nxe r-w-x cpl (double-rewrite x86))))
                  (equal (mv-nth 1 (ia32e-la-to-pa-page-dir-ptr-table
                                    lin-addr
                                    base-addr u/s-acc r/w-acc x/d-acc
                                    wp smep smap ac nxe r-w-x cpl (xw :mem index value x86)))
                         (mv-nth 1 (ia32e-la-to-pa-page-dir-ptr-table
                                    lin-addr
                                    base-addr u/s-acc r/w-acc x/d-acc
                                    wp smep smap ac nxe r-w-x cpl (double-rewrite x86))))))
    :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa-page-dir-ptr-table
                                      member-p disjoint-p)
                                     (bitops::logand-with-negated-bitmask
                                      negative-logand-to-positive-logand-with-integerp-x
                                      force (force)))))))

(define xlation-governing-entries-paddrs-for-pml4-table
  ((lin-addr       :type (signed-byte   #.*max-linear-address-size*))
   (pml4-base-addr :type (unsigned-byte #.*physical-address-size*))
   (x86))

  :guard (and (not (programmer-level-mode x86))
              (canonical-address-p lin-addr)
              (equal (loghead 12 pml4-base-addr) 0))
  :guard-hints (("Goal" :in-theory (e/d* (canonical-address-p)
                                         (xlation-governing-entries-paddrs-for-page-dir-ptr-table
                                          unsigned-byte-p
                                          signed-byte-p
                                          acl2::commutativity-of-logior))))

  (b* ((pml4-entry-addr
        (pml4-table-entry-addr lin-addr pml4-base-addr))
       (pml4-entry (rm-low-64 pml4-entry-addr x86))
       (pml4te-ps? (equal (page-size pml4-entry) 1))

       ((when pml4te-ps?) (addr-range 8 pml4-entry-addr))

       ;; Page Directory Pointer Table:
       (ptr-table-base-addr
        (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))

       (ptr-table-addresses
        (xlation-governing-entries-paddrs-for-page-dir-ptr-table
         lin-addr ptr-table-base-addr x86)))

    (append (addr-range 8 pml4-entry-addr) ptr-table-addresses))

  ///

  (defthm xlation-governing-entries-paddrs-for-pml4-table-and-xw-not-mem
    (implies (and (not (equal fld :mem))
                  (not (equal fld :programmer-level-mode)))
             (equal (xlation-governing-entries-paddrs-for-pml4-table lin-addr base-addr (xw fld index value x86))
                    (xlation-governing-entries-paddrs-for-pml4-table lin-addr base-addr (double-rewrite x86))))
    :hints (("Goal" :in-theory (e/d* () (xlation-governing-entries-paddrs-for-page-table)))))

  (defthm xlation-governing-entries-paddrs-for-pml4-table-and-xw-mem-not-member
    (implies (not (member-p index (xlation-governing-entries-paddrs-for-pml4-table lin-addr base-addr (double-rewrite x86))))
             (equal (xlation-governing-entries-paddrs-for-pml4-table lin-addr base-addr (xw :mem index value x86))
                    (xlation-governing-entries-paddrs-for-pml4-table lin-addr base-addr (double-rewrite x86))))
    :hints (("Goal" :in-theory (e/d* (disjoint-p member-p)
                                     (xlation-governing-entries-paddrs-for-page-dir-ptr-table)))))

  (defthm ia32e-la-to-pa-pml4-table-values-and-xw-mem-not-member
    (implies (and
              (not
               (member-p
                index
                (xlation-governing-entries-paddrs-for-pml4-table lin-addr base-addr (double-rewrite x86))))
              (physical-address-p base-addr)
              (equal (loghead 12 base-addr) 0)
              (canonical-address-p lin-addr))
             (and (equal (mv-nth 0 (ia32e-la-to-pa-pml4-table
                                    lin-addr base-addr
                                    wp smep smap ac nxe r-w-x cpl (xw :mem index value x86)))
                         (mv-nth 0 (ia32e-la-to-pa-pml4-table
                                    lin-addr base-addr
                                    wp smep smap ac nxe r-w-x cpl (double-rewrite x86))))
                  (equal (mv-nth 1 (ia32e-la-to-pa-pml4-table
                                    lin-addr base-addr
                                    wp smep smap ac nxe r-w-x cpl (xw :mem index value x86)))
                         (mv-nth 1 (ia32e-la-to-pa-pml4-table
                                    lin-addr base-addr
                                    wp smep smap ac nxe r-w-x cpl (double-rewrite x86))))))
    :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa-pml4-table
                                      member-p disjoint-p)
                                     (bitops::logand-with-negated-bitmask
                                      negative-logand-to-positive-logand-with-integerp-x
                                      force (force)))))))

(define xlation-governing-entries-paddrs
  ((lin-addr :type (signed-byte   #.*max-linear-address-size*)
             "Canonical linear address to be mapped to a physical address")
   (x86 "x86 state"))


  :long "<p>@('xlation-governing-entries-paddrs') returns a
  @('true-listp') of physical addresses that govern the translation of
  a linear address @('lin-addr') to its corresponding physical address
  @('p-addr').  Addresses that can be a part of the
  output (depending on the page configurations, i.e., 4K, 2M, or 1G
  pages) include:</p>

<ol>
<li>The addresses of the relevant PML4 entry</li>

<li>The addresses of the relevant PDPT entry</li>

<li>The addresses of the relevant PD entry</li>

<li>The addresses of the relevant PT entry</li>

</ol>"

  :guard (not (xr :programmer-level-mode 0 x86))
  :guard-hints (("Goal" :in-theory (e/d* (canonical-address-p)
                                         (xlation-governing-entries-paddrs-for-pml4-table
                                          unsigned-byte-p
                                          signed-byte-p
                                          acl2::commutativity-of-logior))))

  (if (mbt (not (programmer-level-mode x86)))
      (b* ((cr3       (ctri *cr3* x86))
           ;; PML4 Table:
           (pml4-base-addr (ash (cr3-slice :cr3-pdb cr3) 12)))

        (xlation-governing-entries-paddrs-for-pml4-table
         lin-addr pml4-base-addr x86))
    nil)

  ///

  (defthm xlation-governing-entries-paddrs-and-xw-not-mem
    (implies (and (not (equal fld :mem))
                  (not (equal fld :ctr))
                  (not (equal fld :programmer-level-mode)))
             (equal (xlation-governing-entries-paddrs lin-addr (xw fld index value x86))
                    (xlation-governing-entries-paddrs lin-addr (double-rewrite x86))))
    :hints (("Goal" :in-theory (e/d* () (xlation-governing-entries-paddrs-for-pml4-table)))))

  (defthm xlation-governing-entries-paddrs-and-xw-mem-not-member
    (implies (not (member-p index (xlation-governing-entries-paddrs lin-addr (double-rewrite x86))))
             (equal (xlation-governing-entries-paddrs lin-addr (xw :mem index value x86))
                    (xlation-governing-entries-paddrs lin-addr (double-rewrite x86))))
    :hints (("Goal"
             :in-theory (e/d* () (xlation-governing-entries-paddrs-for-pml4-table)))))

  (defthm ia32e-la-to-pa-values-and-xw-mem-not-member
    (implies (and (not (member-p index (xlation-governing-entries-paddrs lin-addr (double-rewrite x86))))
                  (canonical-address-p lin-addr))
             (and (equal (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x cpl (xw :mem index value x86)))
                         (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x cpl (double-rewrite x86))))
                  (equal (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x cpl (xw :mem index value x86)))
                         (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x cpl (double-rewrite x86))))))
    :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa) (xlation-governing-entries-paddrs-for-pml4-table)))))

  (defthm xlation-governing-entries-paddrs-and-!flgi
    (equal (xlation-governing-entries-paddrs lin-addr (!flgi index value x86))
           (xlation-governing-entries-paddrs lin-addr (double-rewrite x86)))
    :hints (("Goal" :in-theory (e/d* (!flgi) (xlation-governing-entries-paddrs force (force))))))

  (defthm xlation-governing-entries-paddrs-and-!flgi-undefined
    (equal (xlation-governing-entries-paddrs lin-addr (!flgi-undefined index x86))
           (xlation-governing-entries-paddrs lin-addr (double-rewrite x86)))
    :hints (("Goal" :in-theory (e/d* (!flgi-undefined) (xlation-governing-entries-paddrs force (force))))))

  (defthm xlation-governing-entries-paddrs-and-write-to-physical-memory-disjoint
    (implies (and (disjoint-p (xlation-governing-entries-paddrs lin-addr (double-rewrite x86)) p-addrs)
                  (physical-address-listp p-addrs))
             (equal (xlation-governing-entries-paddrs lin-addr (write-to-physical-memory p-addrs bytes x86))
                    (xlation-governing-entries-paddrs lin-addr (double-rewrite x86))))
    :hints (("Goal" :induct (write-to-physical-memory p-addrs bytes x86)
             :in-theory (e/d* (disjoint-p disjoint-p-commutative) (xlation-governing-entries-paddrs))))))

(define all-xlation-governing-entries-paddrs
  ((l-addrs canonical-address-listp)
   x86)
  :guard (not (xr :programmer-level-mode 0 x86))
  :enabled t
  (if (endp l-addrs)
      nil
    (append (xlation-governing-entries-paddrs (car l-addrs) x86)
            (all-xlation-governing-entries-paddrs (cdr l-addrs)  x86)))
  ///

  (defthm all-xlation-governing-entries-paddrs-and-nil
    (equal (all-xlation-governing-entries-paddrs nil x86) nil))

  (defthm xlation-governing-entries-paddrs-subset-p-all-xlation-governing-entries-paddrs
    (implies (member-p addr l-addrs)
             (equal (subset-p (xlation-governing-entries-paddrs addr x86)
                              (all-xlation-governing-entries-paddrs l-addrs x86))
                    t))
    :hints (("Goal" :in-theory (e/d* (subset-p) ()))))

  (defthm all-xlation-governing-entries-paddrs-subset-p-all-xlation-governing-entries-paddrs
    (implies (subset-p l-addrs-subset l-addrs)
             (equal
              (subset-p (all-xlation-governing-entries-paddrs l-addrs-subset x86)
                        (all-xlation-governing-entries-paddrs l-addrs x86))
              t))
    :hints (("Goal" :in-theory (e/d* (subset-p member-p) ()))))

  (defthm all-xlation-governing-entries-paddrs-and-xw-not-mem
    (implies (and (not (equal fld :mem))
                  (not (equal fld :ctr))
                  (not (equal fld :programmer-level-mode)))
             (equal (all-xlation-governing-entries-paddrs l-addrs (xw fld index value x86))
                    (all-xlation-governing-entries-paddrs l-addrs (double-rewrite x86))))
    :hints (("Goal" :in-theory (e/d* () (xlation-governing-entries-paddrs)))))

  (defthm all-xlation-governing-entries-paddrs-and-xw-mem-not-member
    (implies (and (not (member-p index (all-xlation-governing-entries-paddrs l-addrs (double-rewrite x86))))
                  (integerp index))
             (equal (all-xlation-governing-entries-paddrs l-addrs (xw :mem index value x86))
                    (all-xlation-governing-entries-paddrs l-addrs (double-rewrite x86))))
    :hints (("Goal" :in-theory (e/d* () (xlation-governing-entries-paddrs)))))

  (defthm all-xlation-governing-entries-paddrs-and-!flgi
    (equal (all-xlation-governing-entries-paddrs l-addrs (!flgi index value x86))
           (all-xlation-governing-entries-paddrs l-addrs (double-rewrite x86)))
    :hints (("Goal" :in-theory (e/d* () (xlation-governing-entries-paddrs force (force))))))

  (defthm all-xlation-governing-entries-paddrs-and-!flgi-undefined
    (equal (all-xlation-governing-entries-paddrs l-addrs (!flgi-undefined index x86))
           (all-xlation-governing-entries-paddrs l-addrs (double-rewrite x86)))
    :hints (("Goal" :in-theory (e/d* () (xlation-governing-entries-paddrs force (force)))))))

;; ======================================================================

(defthm disjointness-of-xlation-governing-entries-paddrs-from-all-xlation-governing-entries-paddrs
  (implies (and (bind-free
                 (find-l-addrs-from-fn 'all-xlation-governing-entries-paddrs 'l-addrs mfc state)
                 (l-addrs))
                (disjoint-p (all-xlation-governing-entries-paddrs l-addrs (double-rewrite x86)) other-p-addrs)
                (member-p lin-addr l-addrs))
           (disjoint-p (xlation-governing-entries-paddrs lin-addr x86) other-p-addrs))
  :hints (("Goal" :in-theory (e/d* (member-p) ()))))

;; (defthm disjointness-of-all-xlation-governing-entries-paddrs-from-all-xlation-governing-entries-paddrs-subset-p
;;   (implies (and (bind-free
;;               (find-l-addrs-from-fn 'all-xlation-governing-entries-paddrs 'l-addrs mfc state)
;;               (l-addrs))
;;              (syntaxp (not (eq l-addrs-subset l-addrs)))
;;              (disjoint-p (all-xlation-governing-entries-paddrs l-addrs (double-rewrite x86)) other-p-addrs)
;;              (subset-p l-addrs-subset l-addrs))
;;         (disjoint-p (all-xlation-governing-entries-paddrs l-addrs-subset x86) other-p-addrs))
;;   :hints (("Goal" :in-theory (e/d* (subset-p member-p) (xlation-governing-entries-paddrs)))))

(defthm disjointness-of-all-xlation-governing-entries-paddrs-from-all-xlation-governing-entries-paddrs-subset-p
  (implies
   (and
    (bind-free
     (find-l-addrs-from-fn 'all-xlation-governing-entries-paddrs 'l-addrs mfc state)
     (l-addrs))
    (bind-free
     (find-arg-of-fn 'disjoint-p 2 'other-p-addrs mfc state)
     (other-p-addrs))
    (syntaxp (not (eq l-addrs-subset l-addrs)))
    ;; (syntaxp (not (eq other-p-addrs-subset other-p-addrs)))
    (disjoint-p (all-xlation-governing-entries-paddrs l-addrs (double-rewrite x86))
                other-p-addrs)
    (subset-p other-p-addrs-subset other-p-addrs)
    (subset-p l-addrs-subset l-addrs))
   (disjoint-p (all-xlation-governing-entries-paddrs l-addrs-subset x86)
               other-p-addrs-subset))
  :hints
  (("Goal" :in-theory (e/d* (subset-p member-p)
                            (xlation-governing-entries-paddrs)))))

;; ======================================================================

;; Other misc. events:

(defthm ia32e-la-to-pa-values-and-write-to-physical-memory-disjoint
  (implies (and (disjoint-p p-addrs (xlation-governing-entries-paddrs lin-addr (double-rewrite x86)))
                (physical-address-listp p-addrs)
                (canonical-address-p lin-addr))
           (and (equal (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x cpl (write-to-physical-memory p-addrs bytes x86)))
                       (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x cpl (double-rewrite x86))))
                (equal (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x cpl (write-to-physical-memory p-addrs bytes x86)))
                       (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x cpl (double-rewrite x86))))))
  :hints (("Goal"
           :induct (write-to-physical-memory p-addrs bytes x86)
           :in-theory (e/d* (disjoint-p) (xlation-governing-entries-paddrs)))))


(local
 (defthm nth-0-xs
   (equal (nth 0 xs) (car xs))))

(defthm ia32e-la-to-pa-values-and-write-to-physical-memory-disjoint
  (implies (and (disjoint-p p-addrs (xlation-governing-entries-paddrs lin-addr (double-rewrite x86)))
                (physical-address-listp p-addrs)
                (canonical-address-p lin-addr))
           (and (equal (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x cpl (write-to-physical-memory p-addrs bytes x86)))
                       (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x cpl (double-rewrite x86))))
                (equal (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x cpl (write-to-physical-memory p-addrs bytes x86)))
                       (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x cpl (double-rewrite x86))))))
  :hints (("Goal"
           :induct (write-to-physical-memory p-addrs bytes x86)
           :in-theory (e/d* (disjoint-p) (xlation-governing-entries-paddrs)))))

(defthm rm-low-64-and-paging-entry-no-page-fault-p
  (equal (rm-low-64 index
                    (mv-nth
                     2
                     (paging-entry-no-page-fault-p structure-type lin-addr
                                                   entry u/s-acc r/w-acc x/d-acc wp smep
                                                   smap ac nxe r-w-x cpl x86 ignored)))
         (rm-low-64 index x86))
  :hints (("Goal" :in-theory (e/d* (rm-low-64 rm-low-32) ()))))

(defthm mv-nth-0-paging-entry-no-page-fault-p-and-wm-low-64
  (equal (mv-nth
          0
          (paging-entry-no-page-fault-p
           structure-type lin-addr
           entry u/s-acc r/w-acc x/d-acc
           wp smep smap ac nxe r-w-x cpl
           (wm-low-64 index value x86)
           ignored))
         (mv-nth
          0
          (paging-entry-no-page-fault-p
           structure-type lin-addr
           entry u/s-acc r/w-acc x/d-acc
           wp smep smap ac nxe r-w-x cpl
           x86
           ignored)))
  :hints (("Goal" :in-theory (e/d* (paging-entry-no-page-fault-p
                                    page-fault-exception)
                                   ()))))

(defthm mv-nth-2-paging-entry-no-page-fault-p-and-wm-low-64-if-no-error
  (implies (not (mv-nth
                 0
                 (paging-entry-no-page-fault-p
                  structure-type lin-addr
                  entry u/s-acc r/w-acc x/d-acc
                  wp smep smap ac nxe r-w-x cpl x86 ignored)))
           (equal (mv-nth
                   2
                   (paging-entry-no-page-fault-p
                    structure-type lin-addr
                    entry u/s-acc r/w-acc x/d-acc
                    wp smep smap ac nxe r-w-x cpl
                    (wm-low-64 index value x86)
                    ignored))
                  (wm-low-64 index value x86)))
  :hints (("Goal" :in-theory (e/d* (paging-entry-no-page-fault-p) ()))))


(defthm mv-nth-0-paging-entry-no-page-fault-p-and-write-to-physical-memory
  (equal (mv-nth 0
                 (paging-entry-no-page-fault-p
                  structure-type lin-addr entry
                  u/s-acc r/w-acc x/d-acc
                  wp smep smap ac nxe r-w-x cpl
                  (write-to-physical-memory p-addrs bytes x86)
                  ignored))
         (mv-nth 0
                 (paging-entry-no-page-fault-p
                  structure-type lin-addr entry
                  u/s-acc r/w-acc x/d-acc
                  wp smep smap ac nxe r-w-x cpl
                  x86 ignored)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (disjoint-p
                             member-p
                             paging-entry-no-page-fault-p
                             page-fault-exception)
                            (bitops::logand-with-negated-bitmask
                             (:meta acl2::mv-nth-cons-meta)
                             force (force))))))

(defthm mv-nth-0-paging-entry-no-page-fault-p-and-mv-nth-1-wb
  (equal (mv-nth 0
                 (paging-entry-no-page-fault-p
                  structure-type lin-addr
                  entry u/s-acc r/w-acc x/d-acc wp
                  smep smap ac nxe r-w-x cpl
                  (mv-nth 1 (wb addr-lst w x86))
                  access-type))
         (mv-nth 0
                 (paging-entry-no-page-fault-p
                  structure-type lin-addr
                  entry u/s-acc r/w-acc x/d-acc wp
                  smep smap ac nxe r-w-x cpl x86
                  access-type)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (paging-entry-no-page-fault-p
                             page-fault-exception)
                            (wb
                             (:meta acl2::mv-nth-cons-meta)
                             force (force))))))

(defthm ia32e-la-to-pa-page-table-values-and-write-to-translation-governing-address
  ;; Similar lemmas can be found in proofs/zero-copy/zero-copy.lisp.
  (b* ((p-addrs (xlation-governing-entries-paddrs-for-page-table lin-addr base-addr x86))
       (page-table-entry (rm-low-64 (page-table-entry-addr lin-addr base-addr) x86))
       (value (combine-bytes bytes)))
    (implies (and (not (mv-nth 0
                               (ia32e-la-to-pa-page-table
                                lin-addr base-addr u/s-acc r/w-acc x/d-acc
                                wp smep smap ac nxe r-w-x cpl x86)))
                  (equal (page-present page-table-entry)
                         (page-present value))
                  (equal (page-read-write page-table-entry)
                         (page-read-write value))
                  (equal (page-user-supervisor page-table-entry)
                         (page-user-supervisor value))
                  (equal (page-execute-disable page-table-entry)
                         (page-execute-disable value))
                  (equal (page-size page-table-entry)
                         (page-size value))

                  (equal (len bytes) (len p-addrs))
                  (byte-listp bytes)
                  (canonical-address-p lin-addr)
                  (physical-address-p base-addr)
                  (equal (loghead 12 base-addr) 0)
                  (x86p x86))
             (and (equal
                   (mv-nth 0 (ia32e-la-to-pa-page-table
                              lin-addr base-addr u/s-acc r/w-acc x/d-acc
                              wp smep smap ac nxe r-w-x cpl
                              (write-to-physical-memory p-addrs bytes x86)))
                   nil)
                  (equal (mv-nth 1 (ia32e-la-to-pa-page-table
                                    lin-addr base-addr u/s-acc r/w-acc x/d-acc
                                    wp smep smap ac nxe r-w-x cpl
                                    (write-to-physical-memory p-addrs bytes x86)))
                         (logior (loghead 12 lin-addr)
                                 (ash (loghead 40 (logtail 12 value))
                                      12))))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (disjoint-p
                             member-p
                             ia32e-la-to-pa-page-table
                             page-table-entry-addr
                             xlation-governing-entries-paddrs-for-page-table)
                            (wb
                             bitops::logand-with-negated-bitmask
                             (:meta acl2::mv-nth-cons-meta)
                             force (force))))))

;; ======================================================================
