;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")
(include-book "la-to-pa-lemmas" :ttags :all)

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))

(local (in-theory (e/d () (unsigned-byte-p signed-byte-p))))

;; ======================================================================

;; Defining translation-governing-addresses of linear addresses:

(defthm |(logand -4096 base-addr) = base-addr when low 12 bits are 0|
  (implies (and (equal (loghead 12 base-addr) 0)
                (physical-address-p base-addr))
           (equal (logand -4096 base-addr) base-addr))
  :hints (("Goal" :in-theory (e/d* (bitops::ihsext-recursive-redefs
                                    bitops::ihsext-inductions)
                                   (bitops::logand-with-negated-bitmask)))))

(define translation-governing-addresses-for-page-table
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

  (defthm translation-governing-addresses-for-page-table-and-xlate-equiv-memory
    (implies (xlate-equiv-memory x86-1 x86-2)
             (equal (translation-governing-addresses-for-page-table lin-addr base-addr x86-1)
                    (translation-governing-addresses-for-page-table lin-addr base-addr x86-2)))
    :rule-classes :congruence)

  (defthm translation-governing-addresses-for-page-table-and-xw
    (equal (translation-governing-addresses-for-page-table lin-addr base-addr (xw fld index value x86))
           (translation-governing-addresses-for-page-table lin-addr base-addr x86)))

  (defthm ia32e-la-to-pa-page-table-values-and-xw-mem-not-member
    (implies (and
              ;; (disjoint-p
              ;;  (addr-range 1 index)
              ;;  (translation-governing-addresses-for-page-table lin-addr base-addr x86))
              (not
               (member-p
                index
                (translation-governing-addresses-for-page-table lin-addr base-addr x86)))
              (integerp index)
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
                                    wp smep smap ac nxe r-w-x cpl x86)))
                  (equal (mv-nth 1 (ia32e-la-to-pa-page-table
                                    lin-addr
                                    base-addr u/s-acc r/w-acc x/d-acc
                                    wp smep smap ac nxe r-w-x cpl (xw :mem index value x86)))
                         (mv-nth 1 (ia32e-la-to-pa-page-table
                                    lin-addr
                                    base-addr u/s-acc r/w-acc x/d-acc
                                    wp smep smap ac nxe r-w-x cpl x86)))))
    :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa-page-table disjoint-p member-p)
                                     (bitops::logand-with-negated-bitmask
                                      negative-logand-to-positive-logand-with-integerp-x))))))

(define translation-governing-addresses-for-page-directory
  ((lin-addr                 :type (signed-byte   #.*max-linear-address-size*))
   (page-directory-base-addr :type (unsigned-byte #.*physical-address-size*))
   (x86))
  :guard (and (not (programmer-level-mode x86))
              (canonical-address-p lin-addr)
              (equal (loghead 12 page-directory-base-addr) 0))
  :guard-hints (("Goal" :in-theory (e/d* (canonical-address-p)
                                         (translation-governing-addresses-for-page-table
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
        (translation-governing-addresses-for-page-table
         lin-addr page-table-base-addr x86)))

    (append
     (addr-range 8 page-directory-entry-addr) page-table-addresses))

  ///

  (defthm translation-governing-addresses-for-page-directory-and-xlate-equiv-memory
    (implies (xlate-equiv-memory x86-1 x86-2)
             (equal (translation-governing-addresses-for-page-directory lin-addr base-addr x86-1)
                    (translation-governing-addresses-for-page-directory lin-addr base-addr x86-2)))
    :hints (("Goal" :in-theory (e/d* () (xlate-equiv-memory-and-xlate-equiv-entries-rm-low-64-with-page-directory-entry-addr))
             :use ((:instance xlate-equiv-memory-and-xlate-equiv-entries-rm-low-64-with-page-directory-entry-addr)
                   (:instance xlate-equiv-entries-and-page-size
                              (e-1 (rm-low-64 (page-directory-entry-addr lin-addr base-addr) x86-1))
                              (e-2 (rm-low-64 (page-directory-entry-addr lin-addr base-addr) x86-2))))))
    :rule-classes :congruence)

  (defthm translation-governing-addresses-for-page-directory-and-xw-not-mem
    (implies (and (not (equal fld :mem))
                  (not (equal fld :programmer-level-mode)))
             (equal (translation-governing-addresses-for-page-directory lin-addr base-addr (xw fld index value x86))
                    (translation-governing-addresses-for-page-directory lin-addr base-addr x86)))
    :hints (("Goal" :in-theory (e/d* () (translation-governing-addresses-for-page-table)))))

  (defthm translation-governing-addresses-for-page-directory-and-xw-mem-not-member
    (implies (and
              (not (member-p index (translation-governing-addresses-for-page-directory lin-addr base-addr x86)))
              ;; (not (member-p index (addr-range 8 (page-directory-entry-addr lin-addr base-addr))))
              (integerp index))
             (equal (translation-governing-addresses-for-page-directory lin-addr base-addr (xw :mem index value x86))
                    (translation-governing-addresses-for-page-directory lin-addr base-addr x86)))
    :hints (("Goal" :in-theory (e/d* (page-size disjoint-p member-p) (translation-governing-addresses-for-page-table)))))

  (defthm ia32e-la-to-pa-page-directory-values-and-xw-mem-not-member
    (implies (and
              (not (member-p
                    index
                    (translation-governing-addresses-for-page-directory lin-addr base-addr x86)))
              (integerp index)
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
                                    wp smep smap ac nxe r-w-x cpl x86)))
                  (equal (mv-nth 1 (ia32e-la-to-pa-page-directory
                                    lin-addr
                                    base-addr u/s-acc r/w-acc x/d-acc
                                    wp smep smap ac nxe r-w-x cpl (xw :mem index value x86)))
                         (mv-nth 1 (ia32e-la-to-pa-page-directory
                                    lin-addr
                                    base-addr u/s-acc r/w-acc x/d-acc
                                    wp smep smap ac nxe r-w-x cpl x86)))))
    :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa-page-directory member-p disjoint-p)
                                     (bitops::logand-with-negated-bitmask
                                      negative-logand-to-positive-logand-with-integerp-x
                                      force (force)))))))

(define translation-governing-addresses-for-page-dir-ptr-table
  ((lin-addr                 :type (signed-byte   #.*max-linear-address-size*))
   (ptr-table-base-addr :type (unsigned-byte #.*physical-address-size*))
   (x86))
  :guard (and (not (programmer-level-mode x86))
              (canonical-address-p lin-addr)
              (equal (loghead 12 ptr-table-base-addr) 0))
  :guard-hints (("Goal" :in-theory (e/d* (canonical-address-p)
                                         (translation-governing-addresses-for-page-directory
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
        (translation-governing-addresses-for-page-directory
         lin-addr page-directory-base-addr x86)))

    (append (addr-range 8 page-dir-ptr-table-entry-addr) page-directory-addresses))

  ///

  (defthm translation-governing-addresses-for-page-dir-ptr-table-and-xlate-equiv-memory
    (implies (xlate-equiv-memory x86-1 x86-2)
             (equal (translation-governing-addresses-for-page-dir-ptr-table lin-addr base-addr x86-1)
                    (translation-governing-addresses-for-page-dir-ptr-table lin-addr base-addr x86-2)))
    :hints (("Goal" :in-theory (e/d* () (xlate-equiv-memory-and-xlate-equiv-entries-rm-low-64-with-page-dir-ptr-table-entry-addr))
             :use ((:instance xlate-equiv-memory-and-xlate-equiv-entries-rm-low-64-with-page-dir-ptr-table-entry-addr)
                   (:instance xlate-equiv-entries-and-page-size
                              (e-1 (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr) x86-1))
                              (e-2 (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr) x86-2))))))
    :rule-classes :congruence)

  (defthm translation-governing-addresses-for-page-dir-ptr-table-and-xw-not-mem
    (implies (and (not (equal fld :mem))
                  (not (equal fld :programmer-level-mode)))
             (equal (translation-governing-addresses-for-page-dir-ptr-table lin-addr base-addr (xw fld index value x86))
                    (translation-governing-addresses-for-page-dir-ptr-table lin-addr base-addr x86)))
    :hints (("Goal" :in-theory (e/d* () (translation-governing-addresses-for-page-table)))))

  (defthm translation-governing-addresses-for-page-dir-ptr-table-and-xw-mem-not-member
    (implies (and (not (member-p index (translation-governing-addresses-for-page-dir-ptr-table lin-addr base-addr x86)))
                  ;; (not (member-p index (addr-range 8 (page-dir-ptr-table-entry-addr lin-addr base-addr))))
                  ;; (not (member-p index (addr-range 8 (page-directory-entry-addr
                  ;;                                     lin-addr
                  ;;                                     (ash (loghead 40
                  ;;                                                   (logtail 12
                  ;;                                                            (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr) x86)))
                  ;;                                          12)))))
                  (integerp index))
             (equal (translation-governing-addresses-for-page-dir-ptr-table lin-addr base-addr (xw :mem index value x86))
                    (translation-governing-addresses-for-page-dir-ptr-table lin-addr base-addr x86)))
    :hints (("Goal" :in-theory (e/d* (page-size disjoint-p member-p) (translation-governing-addresses-for-page-directory)))))

  (defthm ia32e-la-to-pa-page-dir-ptr-table-values-and-xw-mem-not-member
    (implies (and
              (not
               (member-p
                index
                (translation-governing-addresses-for-page-dir-ptr-table lin-addr base-addr x86)))
              (integerp index)
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
                                    wp smep smap ac nxe r-w-x cpl x86)))
                  (equal (mv-nth 1 (ia32e-la-to-pa-page-dir-ptr-table
                                    lin-addr
                                    base-addr u/s-acc r/w-acc x/d-acc
                                    wp smep smap ac nxe r-w-x cpl (xw :mem index value x86)))
                         (mv-nth 1 (ia32e-la-to-pa-page-dir-ptr-table
                                    lin-addr
                                    base-addr u/s-acc r/w-acc x/d-acc
                                    wp smep smap ac nxe r-w-x cpl x86)))))
    :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa-page-dir-ptr-table
                                      member-p disjoint-p)
                                     (bitops::logand-with-negated-bitmask
                                      negative-logand-to-positive-logand-with-integerp-x
                                      force (force)))))))

(define translation-governing-addresses-for-pml4-table
  ((lin-addr       :type (signed-byte   #.*max-linear-address-size*))
   (pml4-base-addr :type (unsigned-byte #.*physical-address-size*))
   (x86))

  :guard (and (not (programmer-level-mode x86))
              (canonical-address-p lin-addr)
              (equal (loghead 12 pml4-base-addr) 0))
  :guard-hints (("Goal" :in-theory (e/d* (canonical-address-p)
                                         (translation-governing-addresses-for-page-dir-ptr-table
                                          unsigned-byte-p
                                          signed-byte-p
                                          acl2::commutativity-of-logior))))

  (b* ((pml4-entry-addr
        (pml4-table-entry-addr lin-addr pml4-base-addr))
       (pml4-entry (rm-low-64 pml4-entry-addr x86))

       ;; Page Directory Pointer Table:
       (ptr-table-base-addr
        (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))

       (ptr-table-addresses
        (translation-governing-addresses-for-page-dir-ptr-table
         lin-addr ptr-table-base-addr x86)))

    (append (addr-range 8 pml4-entry-addr) ptr-table-addresses))

  ///

  (defthm translation-governing-addresses-for-pml4-table-and-xlate-equiv-memory
    (implies (xlate-equiv-memory x86-1 x86-2)
             (equal (translation-governing-addresses-for-pml4-table lin-addr base-addr x86-1)
                    (translation-governing-addresses-for-pml4-table lin-addr base-addr x86-2)))
    :hints (("Goal" :in-theory (e/d* () (xlate-equiv-memory-and-xlate-equiv-entries-rm-low-64-with-pml4-table-entry-addr))
             :use ((:instance xlate-equiv-memory-and-xlate-equiv-entries-rm-low-64-with-pml4-table-entry-addr)
                   (:instance xlate-equiv-entries-and-page-size
                              (e-1 (rm-low-64 (pml4-table-entry-addr lin-addr base-addr) x86-1))
                              (e-2 (rm-low-64 (pml4-table-entry-addr lin-addr base-addr) x86-2))))))
    :rule-classes :congruence)

  (defthm translation-governing-addresses-for-pml4-table-and-xw-not-mem
    (implies (and (not (equal fld :mem))
                  (not (equal fld :programmer-level-mode)))
             (equal (translation-governing-addresses-for-pml4-table lin-addr base-addr (xw fld index value x86))
                    (translation-governing-addresses-for-pml4-table lin-addr base-addr x86)))
    :hints (("Goal" :in-theory (e/d* () (translation-governing-addresses-for-page-table)))))

  (defthm translation-governing-addresses-for-pml4-table-and-xw-mem-not-member
    (implies (and
              (not (member-p index (translation-governing-addresses-for-pml4-table lin-addr base-addr x86)))
              (integerp index))
             (equal (translation-governing-addresses-for-pml4-table lin-addr base-addr (xw :mem index value x86))
                    (translation-governing-addresses-for-pml4-table lin-addr base-addr x86)))
    :hints (("Goal" :in-theory (e/d* (page-size disjoint-p member-p) (translation-governing-addresses-for-page-dir-ptr-table)))))

  (defthm ia32e-la-to-pa-pml4-table-values-and-xw-mem-not-member
    (implies (and
              (not
               (member-p
                index
                (translation-governing-addresses-for-pml4-table lin-addr base-addr x86)))
              (integerp index)
              (physical-address-p base-addr)
              (equal (loghead 12 base-addr) 0)
              (canonical-address-p lin-addr))
             (and (equal (mv-nth 0 (ia32e-la-to-pa-pml4-table
                                    lin-addr base-addr
                                    wp smep smap ac nxe r-w-x cpl (xw :mem index value x86)))
                         (mv-nth 0 (ia32e-la-to-pa-pml4-table
                                    lin-addr base-addr
                                    wp smep smap ac nxe r-w-x cpl x86)))
                  (equal (mv-nth 1 (ia32e-la-to-pa-pml4-table
                                    lin-addr base-addr
                                    wp smep smap ac nxe r-w-x cpl (xw :mem index value x86)))
                         (mv-nth 1 (ia32e-la-to-pa-pml4-table
                                    lin-addr base-addr
                                    wp smep smap ac nxe r-w-x cpl x86)))))
    :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa-pml4-table
                                      member-p disjoint-p)
                                     (bitops::logand-with-negated-bitmask
                                      negative-logand-to-positive-logand-with-integerp-x
                                      force (force)))))))

(define translation-governing-addresses
  ((lin-addr :type (signed-byte   #.*max-linear-address-size*)
             "Canonical linear address to be mapped to a physical address")
   (x86 "x86 state"))


  :long "<p>@('translation-governing-addresses') returns a
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
                                         (translation-governing-addresses-for-pml4-table
                                          unsigned-byte-p
                                          signed-byte-p
                                          acl2::commutativity-of-logior))))

  (if (mbt (not (programmer-level-mode x86)))
      (b* ((cr3       (ctri *cr3* x86))
           ;; PML4 Table:
           (pml4-base-addr (ash (cr3-slice :cr3-pdb cr3) 12)))

        (translation-governing-addresses-for-pml4-table
         lin-addr pml4-base-addr x86))
    nil)

  ///

  (defthm translation-governing-addresses-and-xlate-equiv-memory
    (implies (xlate-equiv-memory x86-1 x86-2)
             (equal (translation-governing-addresses lin-addr x86-1)
                    (translation-governing-addresses lin-addr x86-2)))
    :hints (("Goal" :use ((:instance xlate-equiv-memory-and-cr3))))
    :rule-classes :congruence)

  (defthm translation-governing-addresses-and-xw-not-mem
    (implies (and (not (equal fld :mem))
                  (not (equal fld :ctr))
                  (not (equal fld :programmer-level-mode)))
             (equal (translation-governing-addresses lin-addr (xw fld index value x86))
                    (translation-governing-addresses lin-addr x86)))
    :hints (("Goal" :in-theory (e/d* () (translation-governing-addresses-for-pml4-table)))))

  (defthm translation-governing-addresses-and-xw-mem-not-member
    (implies (and (not (member-p index (translation-governing-addresses lin-addr x86)))
                  (integerp index))
             (equal (translation-governing-addresses lin-addr (xw :mem index value x86))
                    (translation-governing-addresses lin-addr x86)))
    :hints (("Goal" :in-theory (e/d* () (translation-governing-addresses-for-pml4-table)))))

  (defthm ia32e-la-to-pa-values-and-xw-mem-not-member
    (implies (and (not (member-p index (translation-governing-addresses lin-addr x86)))
                  (integerp index)
                  (canonical-address-p lin-addr))
             (and (equal (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x cpl (xw :mem index value x86)))
                         (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x cpl x86)))
                  (equal (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x cpl (xw :mem index value x86)))
                         (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x cpl x86)))))
    :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa) (translation-governing-addresses-for-pml4-table)))))

  (defthm translation-governing-addresses-and-!flgi
    (equal (translation-governing-addresses lin-addr (!flgi index value x86))
           (translation-governing-addresses lin-addr x86))
    :hints (("Goal" :in-theory (e/d* (!flgi) (translation-governing-addresses force (force))))))

  (defthm translation-governing-addresses-and-!flgi-undefined
    (equal (translation-governing-addresses lin-addr (!flgi-undefined index x86))
           (translation-governing-addresses lin-addr x86))
    :hints (("Goal" :in-theory (e/d* (!flgi-undefined) (translation-governing-addresses force (force))))))

  (defthm translation-governing-addresses-and-write-to-physical-memory-disjoint
    (implies (and (disjoint-p (translation-governing-addresses lin-addr x86) p-addrs)
                  (physical-address-listp p-addrs))
             (equal (translation-governing-addresses lin-addr (write-to-physical-memory p-addrs bytes x86))
                    (translation-governing-addresses lin-addr x86)))
    :hints (("Goal" :induct (write-to-physical-memory p-addrs bytes x86)
             :in-theory (e/d* (disjoint-p disjoint-p-commutative) (translation-governing-addresses))))))

(define all-translation-governing-addresses
  ((l-addrs canonical-address-listp)
   x86)
  :guard (not (xr :programmer-level-mode 0 x86))
  :enabled t
  (if (endp l-addrs)
      nil
    (append (translation-governing-addresses (car l-addrs) x86)
            (all-translation-governing-addresses (cdr l-addrs)  x86)))
  ///

  (defthm all-translation-governing-addresses-and-xlate-equiv-memory
    (implies (xlate-equiv-memory x86-1 x86-2)
             (equal (all-translation-governing-addresses lin-addr x86-1)
                    (all-translation-governing-addresses lin-addr x86-2)))
    :rule-classes :congruence)

  (defthm all-translation-governing-addresses-and-xw-not-mem
    (implies (and (not (equal fld :mem))
                  (not (equal fld :ctr))
                  (not (equal fld :programmer-level-mode)))
             (equal (all-translation-governing-addresses l-addrs (xw fld index value x86))
                    (all-translation-governing-addresses l-addrs x86)))
    :hints (("Goal" :in-theory (e/d* () (translation-governing-addresses)))))

  (defthm all-translation-governing-addresses-and-xw-mem-not-member
    (implies (and (not (member-p index (all-translation-governing-addresses l-addrs x86)))
                  (integerp index))
             (equal (all-translation-governing-addresses l-addrs (xw :mem index value x86))
                    (all-translation-governing-addresses l-addrs x86)))
    :hints (("Goal" :in-theory (e/d* () (translation-governing-addresses)))))

  (defthm all-translation-governing-addresses-and-!flgi
    (equal (all-translation-governing-addresses l-addrs (!flgi index value x86))
           (all-translation-governing-addresses l-addrs x86))
    :hints (("Goal" :in-theory (e/d* () (translation-governing-addresses force (force))))))

  (defthm all-translation-governing-addresses-and-!flgi-undefined
    (equal (all-translation-governing-addresses l-addrs (!flgi-undefined index x86))
           (all-translation-governing-addresses l-addrs x86))
    :hints (("Goal" :in-theory (e/d* () (translation-governing-addresses force (force)))))))

;; ======================================================================

;; Proof of
;; all-translation-governing-addresses-and-mv-nth-1-wb-disjoint and
;; translation-governing-addresses-and-mv-nth-1-wb-disjoint-p:

(defthm xr-mem-disjoint-ia32e-la-to-pa-page-table-in-marking-mode
  (implies (and (disjoint-p (list index)
                            (translation-governing-addresses-for-page-table
                             lin-addr base-addr x86))
                (canonical-address-p lin-addr)
                (physical-address-p base-addr)
                (equal (loghead 12 base-addr) 0))
           (equal (xr :mem index (mv-nth 2 (ia32e-la-to-pa-page-table
                                            lin-addr
                                            base-addr u/s-acc r/w-acc x/d-acc
                                            wp smep smap ac nxe r-w-x cpl x86)))
                  (xr :mem index x86)))
  :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa-page-table
                                    translation-governing-addresses-for-page-table)
                                   (negative-logand-to-positive-logand-with-integerp-x
                                    bitops::logand-with-negated-bitmask)))))

(defthm xr-mem-disjoint-ia32e-la-to-pa-page-directory-in-marking-mode
  (implies (and (disjoint-p (list index)
                            (translation-governing-addresses-for-page-directory
                             lin-addr base-addr x86))
                (canonical-address-p lin-addr)
                (physical-address-p base-addr)
                (equal (loghead 12 base-addr) 0))
           (equal (xr :mem index (mv-nth 2 (ia32e-la-to-pa-page-directory
                                            lin-addr
                                            base-addr u/s-acc r/w-acc x/d-acc
                                            wp smep smap ac nxe r-w-x cpl x86)))
                  (xr :mem index x86)))
  :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa-page-directory
                                    translation-governing-addresses-for-page-directory)
                                   (negative-logand-to-positive-logand-with-integerp-x
                                    bitops::logand-with-negated-bitmask)))))

(defthm xr-mem-disjoint-ia32e-la-to-pa-page-dir-ptr-table-in-marking-mode
  (implies (and (disjoint-p (list index)
                            (translation-governing-addresses-for-page-dir-ptr-table
                             lin-addr base-addr x86))
                (canonical-address-p lin-addr)
                (physical-address-p base-addr)
                (equal (loghead 12 base-addr) 0))
           (equal (xr :mem index (mv-nth 2 (ia32e-la-to-pa-page-dir-ptr-table
                                            lin-addr
                                            base-addr u/s-acc r/w-acc x/d-acc
                                            wp smep smap ac nxe r-w-x cpl x86)))
                  (xr :mem index x86)))
  :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa-page-dir-ptr-table
                                    translation-governing-addresses-for-page-dir-ptr-table)
                                   (negative-logand-to-positive-logand-with-integerp-x
                                    bitops::logand-with-negated-bitmask)))))

(defthm xr-mem-disjoint-ia32e-la-to-pa-pml4-table-in-marking-mode
  (implies (and (disjoint-p (list index)
                            (translation-governing-addresses-for-pml4-table
                             lin-addr base-addr x86))
                (canonical-address-p lin-addr)
                (physical-address-p base-addr)
                (equal (loghead 12 base-addr) 0))
           (equal (xr :mem index (mv-nth 2 (ia32e-la-to-pa-pml4-table
                                            lin-addr base-addr
                                            wp smep smap ac nxe r-w-x cpl x86)))
                  (xr :mem index x86)))
  :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa-pml4-table
                                    translation-governing-addresses-for-pml4-table)
                                   (negative-logand-to-positive-logand-with-integerp-x
                                    bitops::logand-with-negated-bitmask)))))

(defthm xr-mem-disjoint-ia32e-la-to-pa-in-marking-mode
  (implies (and (disjoint-p (list index)
                            (translation-governing-addresses lin-addr x86))
                (canonical-address-p lin-addr))
           (equal (xr :mem index (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x cpl x86)))
                  (xr :mem index x86)))
  :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa
                                    translation-governing-addresses)
                                   (negative-logand-to-positive-logand-with-integerp-x
                                    bitops::logand-with-negated-bitmask
                                    force (force))))))

(defthm rm-low-64-disjoint-ia32e-la-to-pa-in-marking-mode
  (implies (and (disjoint-p (addr-range 8 index)
                            (translation-governing-addresses lin-addr x86))
                (canonical-address-p lin-addr))
           (equal (rm-low-64 index (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x cpl x86)))
                  (rm-low-64 index x86)))
  :hints (("Goal" :in-theory (e/d* (rm-low-64 rm-low-32 disjoint-p)
                                   (translation-governing-addresses
                                    negative-logand-to-positive-logand-with-integerp-x
                                    bitops::logand-with-negated-bitmask
                                    force (force))))))

;; For the proof of rm-low-64-disjoint-las-to-pas-in-marking-mode-disjoint:

;; (defthm translation-governing-addresses-for-page-table-and-mv-nth-2-ia32e-la-to-pa
;;   (equal (translation-governing-addresses-for-page-table
;;           lin-addr-1 base-addr-1 (mv-nth 2 (ia32e-la-to-pa lin-addr-2 r-w-x cpl x86)))
;;          (translation-governing-addresses-for-page-table
;;           lin-addr-1 base-addr-1 x86))
;;   :hints (("Goal" :in-theory (e/d* (translation-governing-addresses-for-page-table) ()))))

;; (defthm translation-governing-addresses-for-page-directory-and-mv-nth-2-ia32e-la-to-pa
;;   (implies (x86p x86)
;;            (equal (translation-governing-addresses-for-page-directory
;;                    lin-addr-1 base-addr-1 (mv-nth 2 (ia32e-la-to-pa lin-addr-2 r-w-x cpl x86)))
;;                   (translation-governing-addresses-for-page-directory
;;                    lin-addr-1 base-addr-1 x86)))
;;   :hints (("Goal"
;;            :use ((:instance xlate-equiv-memory-and-xlate-equiv-entries-rm-low-64-with-page-directory-entry-addr
;;                             (lin-addr lin-addr-1)
;;                             (base-addr base-addr-1)
;;                             (x86-1 (mv-nth 2 (ia32e-la-to-pa lin-addr-2 r-w-x cpl x86)))
;;                             (x86-2 x86))
;;                  (:instance xlate-equiv-entries-and-page-size
;;                             (e-1 (rm-low-64 (page-directory-entry-addr lin-addr-1 base-addr-1)
;;                                             (mv-nth 2 (ia32e-la-to-pa lin-addr-2 r-w-x cpl x86))))
;;                             (e-2 (rm-low-64 (page-directory-entry-addr lin-addr-1 base-addr-1)
;;                                             x86))))
;;            :in-theory (e/d* (translation-governing-addresses-for-page-directory
;;                              translation-governing-addresses
;;                              translation-governing-addresses-for-page-table
;;                              translation-governing-addresses-for-page-dir-ptr-table
;;                              translation-governing-addresses-for-pml4-table
;;                              disjoint-p
;;                              member-p)
;;                             (xlate-equiv-memory-and-xlate-equiv-entries-rm-low-64-with-page-directory-entry-addr)))))

;; (defthm translation-governing-addresses-for-page-dir-ptr-table-and-mv-nth-2-ia32e-la-to-pa
;;   (implies (x86p x86)
;;            (equal (translation-governing-addresses-for-page-dir-ptr-table
;;                    lin-addr-1 base-addr-1 (mv-nth 2 (ia32e-la-to-pa lin-addr-2 r-w-x cpl x86)))
;;                   (translation-governing-addresses-for-page-dir-ptr-table
;;                    lin-addr-1 base-addr-1 x86)))
;;   :hints (("Goal"
;;            :use ((:instance xlate-equiv-memory-and-xlate-equiv-entries-rm-low-64-with-page-dir-ptr-table-entry-addr
;;                             (lin-addr lin-addr-1)
;;                             (base-addr base-addr-1)
;;                             (x86-1 (mv-nth 2 (ia32e-la-to-pa lin-addr-2 r-w-x cpl x86)))
;;                             (x86-2 x86))
;;                  (:instance xlate-equiv-entries-and-page-size
;;                             (e-1 (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr-1 base-addr-1)
;;                                             (mv-nth 2 (ia32e-la-to-pa lin-addr-2 r-w-x cpl x86))))
;;                             (e-2 (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr-1 base-addr-1)
;;                                             x86))))
;;            :in-theory (e/d* (translation-governing-addresses-for-page-dir-ptr-table
;;                              translation-governing-addresses-for-pml4-table
;;                              translation-governing-addresses
;;                              disjoint-p
;;                              member-p)
;;                             (xlate-equiv-memory-and-xlate-equiv-entries-rm-low-64-with-page-dir-ptr-table-entry-addr)))))

;; (defthm translation-governing-addresses-for-pml4-table-and-mv-nth-2-ia32e-la-to-pa
;;   (implies (x86p x86)
;;            (equal (translation-governing-addresses-for-pml4-table
;;                    lin-addr-1 base-addr-1 (mv-nth 2 (ia32e-la-to-pa lin-addr-2 r-w-x cpl x86)))
;;                   (translation-governing-addresses-for-pml4-table
;;                    lin-addr-1 base-addr-1 x86)))
;;   :hints (("Goal"
;;            :use ((:instance xlate-equiv-memory-and-xlate-equiv-entries-rm-low-64-with-pml4-table-entry-addr
;;                             (lin-addr lin-addr-1)
;;                             (base-addr base-addr-1)
;;                             (x86-1 (mv-nth 2 (ia32e-la-to-pa lin-addr-2 r-w-x cpl x86)))
;;                             (x86-2 x86))
;;                  (:instance xlate-equiv-entries-and-page-size
;;                             (e-1 (rm-low-64 (pml4-table-entry-addr lin-addr-1 base-addr-1)
;;                                             (mv-nth 2 (ia32e-la-to-pa lin-addr-2 r-w-x cpl x86))))
;;                             (e-2 (rm-low-64 (pml4-table-entry-addr lin-addr-1 base-addr-1)
;;                                             x86))))
;;            :in-theory (e/d* (translation-governing-addresses-for-pml4-table
;;                              translation-governing-addresses
;;                              disjoint-p
;;                              member-p)
;;                             (xlate-equiv-memory-and-xlate-equiv-entries-rm-low-64-with-pml4-table-entry-addr)))))

;; (defthm translation-governing-addresses-and-mv-nth-2-ia32e-la-to-pa
;;   (implies (x86p x86)
;;            (equal (translation-governing-addresses
;;                    lin-addr-1 (mv-nth 2 (ia32e-la-to-pa lin-addr-2 r-w-x cpl x86)))
;;                   (translation-governing-addresses
;;                    lin-addr-1 x86)))
;;   :hints (("Goal" :in-theory (e/d* (translation-governing-addresses) ()))))

;; (defthm all-translation-governing-addresses-and-mv-nth-2-ia32e-la-to-pa
;;   (implies (x86p x86)
;;            (equal (all-translation-governing-addresses
;;                    l-addrs-1 (mv-nth 2 (ia32e-la-to-pa lin-addr-2 r-w-x cpl x86)))
;;                   (all-translation-governing-addresses
;;                    l-addrs-1 x86)))
;;   :hints (("Goal" :in-theory (e/d* (all-translation-governing-addresses) ()))))


(defthm rm-low-64-disjoint-las-to-pas-in-marking-mode-disjoint
  (implies (and (disjoint-p (addr-range 8 index)
                            (all-translation-governing-addresses l-addrs x86))
                (canonical-address-listp l-addrs)
                (x86p x86))
           (equal (rm-low-64 index (mv-nth 2 (las-to-pas l-addrs r-w-x cpl x86)))
                  (rm-low-64 index x86)))
  :hints (("Goal" :induct (las-to-pas l-addrs r-w-x cpl x86)
           :in-theory (e/d* (las-to-pas
                             disjoint-p)
                            (translation-governing-addresses
                             negative-logand-to-positive-logand-with-integerp-x
                             bitops::logand-with-negated-bitmask
                             force (force))))))

(defthm xr-mem-write-to-physical-memory-disjoint
  (implies (not (member-p index p-addrs))
           (equal (xr :mem index (write-to-physical-memory p-addrs bytes x86))
                  (xr :mem index x86)))
  :hints (("Goal" :in-theory (e/d* (member-p) (force (force))))))

(defthm rm-low-64-and-write-to-physical-memory-disjoint
  (implies (disjoint-p (addr-range 8 p-addr-1) p-addrs-2)
           (equal (rm-low-64 p-addr-1 (write-to-physical-memory p-addrs-2 bytes x86))
                  (rm-low-64 p-addr-1 x86)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (rm-low-64
                             rm-low-32
                             disjoint-p
                             rm-low-64-and-write-to-physical-memory-equal-helper-2)
                            (force (force))))))

;; ----------------------------------------------------------------------

(defthm translation-governing-addresses-for-page-table-and-write-to-physical-memory
  (equal (translation-governing-addresses-for-page-table
          lin-addr page-table-base-addr
          (write-to-physical-memory p-addrs bytes x86))
         (translation-governing-addresses-for-page-table
          lin-addr page-table-base-addr x86))
  :hints (("Goal" :in-theory (e/d* (translation-governing-addresses-for-page-table)
                                   ()))))

(defthm translation-governing-addresses-for-page-table-and-mv-nth-2-las-to-pas
  (equal (translation-governing-addresses-for-page-table
          lin-addr page-table-base-addr
          (mv-nth 2 (las-to-pas l-addrs r-w-x cpl x86)))
         (translation-governing-addresses-for-page-table
          lin-addr page-table-base-addr x86))
  :hints (("Goal" :in-theory (e/d* (translation-governing-addresses-for-page-table)
                                   ()))))

(defthm translation-governing-addresses-for-page-table-and-mv-nth-1-wb
  (equal (translation-governing-addresses-for-page-table
          lin-addr page-table-base-addr
          (mv-nth 1 (wb addr-lst x86)))
         (translation-governing-addresses-for-page-table
          lin-addr page-table-base-addr x86))
  :hints (("Goal" :in-theory (e/d* (wb
                                    translation-governing-addresses-for-page-table)
                                   ()))))


;; ----------------------------------------------------------------------

(defthm translation-governing-addresses-for-page-directory-and-write-to-physical-memory-disjoint-p
  (implies (disjoint-p (translation-governing-addresses-for-page-directory
                        lin-addr page-directory-base-addr x86)
                       p-addrs)
           (equal (translation-governing-addresses-for-page-directory
                   lin-addr page-directory-base-addr
                   (write-to-physical-memory p-addrs bytes x86))
                  (translation-governing-addresses-for-page-directory
                   lin-addr page-directory-base-addr x86)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (disjoint-p
                             translation-governing-addresses-for-page-directory)
                            ()))))

(defthm translation-governing-addresses-for-page-directory-and-mv-nth-2-las-to-pas
  (implies (x86p x86)
           (equal (translation-governing-addresses-for-page-directory
                   lin-addr page-directory-base-addr
                   (mv-nth 2 (las-to-pas l-addrs r-w-x cpl x86)))
                  (translation-governing-addresses-for-page-directory
                   lin-addr page-directory-base-addr x86))))

(defthm translation-governing-addresses-for-page-directory-and-mv-nth-1-wb-disjoint-p
  (implies (and (disjoint-p
                 (translation-governing-addresses-for-page-directory
                  lin-addr page-directory-base-addr x86)
                 (all-translation-governing-addresses (strip-cars addr-lst) x86))
                (disjoint-p
                 (translation-governing-addresses-for-page-directory
                  lin-addr page-directory-base-addr x86)
                 (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w (cpl x86) x86)))
                (addr-byte-alistp addr-lst)
                (not (programmer-level-mode x86))
                (x86p x86))
           (equal (translation-governing-addresses-for-page-directory
                   lin-addr page-directory-base-addr
                   (mv-nth 1 (wb addr-lst x86)))
                  (translation-governing-addresses-for-page-directory
                   lin-addr page-directory-base-addr x86)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (disjoint-p
                             wb
                             translation-governing-addresses-for-page-directory)
                            ()))))

;; ----------------------------------------------------------------------

(defthm translation-governing-addresses-for-page-dir-ptr-table-and-write-to-physical-memory-disjoint-p
  (implies (and (disjoint-p (translation-governing-addresses-for-page-dir-ptr-table
                             lin-addr page-dir-ptr-table-base-addr x86)
                            p-addrs)
                (x86p x86))
           (equal (translation-governing-addresses-for-page-dir-ptr-table
                   lin-addr page-dir-ptr-table-base-addr
                   (write-to-physical-memory p-addrs bytes x86))
                  (translation-governing-addresses-for-page-dir-ptr-table
                   lin-addr page-dir-ptr-table-base-addr x86)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (disjoint-p
                             translation-governing-addresses-for-page-dir-ptr-table)
                            ()))))

(defthm translation-governing-addresses-for-page-dir-ptr-table-and-mv-nth-2-las-to-pas-disjoint-p
  (implies (x86p x86)
           (equal (translation-governing-addresses-for-page-dir-ptr-table
                   lin-addr page-dir-ptr-table-base-addr
                   (mv-nth 2 (las-to-pas l-addrs r-w-x cpl x86)))
                  (translation-governing-addresses-for-page-dir-ptr-table
                   lin-addr page-dir-ptr-table-base-addr x86))))

(defthm translation-governing-addresses-for-page-dir-ptr-table-and-mv-nth-1-wb-disjoint-p
  (implies (and (disjoint-p
                 (translation-governing-addresses-for-page-dir-ptr-table
                  lin-addr page-dir-ptr-table-base-addr x86)
                 (all-translation-governing-addresses (strip-cars addr-lst) x86))
                (disjoint-p
                 (translation-governing-addresses-for-page-dir-ptr-table
                  lin-addr page-dir-ptr-table-base-addr x86)
                 (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w (cpl x86) x86)))
                (addr-byte-alistp addr-lst)
                (not (programmer-level-mode x86))
                (x86p x86))
           (equal (translation-governing-addresses-for-page-dir-ptr-table
                   lin-addr page-dir-ptr-table-base-addr
                   (mv-nth 1 (wb addr-lst x86)))
                  (translation-governing-addresses-for-page-dir-ptr-table
                   lin-addr page-dir-ptr-table-base-addr x86)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (disjoint-p
                             disjoint-p-commutative
                             wb
                             translation-governing-addresses-for-page-dir-ptr-table)
                            ()))))

;; ----------------------------------------------------------------------

(defthm translation-governing-addresses-for-pml4-table-and-write-to-physical-memory-disjoint-p
  (implies (and (disjoint-p (translation-governing-addresses-for-pml4-table
                             lin-addr pml4-table-base-addr x86)
                            p-addrs)
                (x86p x86))
           (equal (translation-governing-addresses-for-pml4-table
                   lin-addr pml4-table-base-addr
                   (write-to-physical-memory p-addrs bytes x86))
                  (translation-governing-addresses-for-pml4-table
                   lin-addr pml4-table-base-addr x86)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (disjoint-p
                             disjoint-p-commutative
                             translation-governing-addresses-for-pml4-table)
                            ()))))

(defthm translation-governing-addresses-for-pml4-table-and-mv-nth-2-las-to-pas-disjoint-p
  (implies (x86p x86)
           (equal (translation-governing-addresses-for-pml4-table
                   lin-addr pml4-table-base-addr
                   (mv-nth 2 (las-to-pas l-addrs r-w-x cpl x86)))
                  (translation-governing-addresses-for-pml4-table
                   lin-addr pml4-table-base-addr x86))))

(defthm translation-governing-addresses-for-pml4-table-and-mv-nth-1-wb-disjoint-p
  (implies (and (disjoint-p
                 (translation-governing-addresses-for-pml4-table
                  lin-addr pml4-table-base-addr x86)
                 (all-translation-governing-addresses (strip-cars addr-lst) x86))
                (disjoint-p
                 (translation-governing-addresses-for-pml4-table
                  lin-addr pml4-table-base-addr x86)
                 (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w (cpl x86) x86)))
                (not (programmer-level-mode x86))
                (addr-byte-alistp addr-lst)
                (x86p x86))
           (equal (translation-governing-addresses-for-pml4-table
                   lin-addr pml4-table-base-addr
                   (mv-nth 1 (wb addr-lst x86)))
                  (translation-governing-addresses-for-pml4-table
                   lin-addr pml4-table-base-addr x86)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (disjoint-p
                             wb
                             translation-governing-addresses-for-pml4-table)
                            (force (force))))))

;; ----------------------------------------------------------------------

(defthm translation-governing-addresses-and-write-to-physical-memory-disjoint-p
  (implies (and (disjoint-p (translation-governing-addresses lin-addr x86)
                            p-addrs)
                (x86p x86))
           (equal (translation-governing-addresses
                   lin-addr (write-to-physical-memory p-addrs bytes x86))
                  (translation-governing-addresses lin-addr x86)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (disjoint-p translation-governing-addresses) ()))))

(defthm translation-governing-addresses-and-mv-nth-2-las-to-pas-disjoint-p
  (implies (x86p x86)
           (equal (translation-governing-addresses
                   lin-addr (mv-nth 2 (las-to-pas l-addrs r-w-x cpl x86)))
                  (translation-governing-addresses lin-addr x86))))

(defthm translation-governing-addresses-and-mv-nth-1-wb-disjoint-p
  (implies (and
            (disjoint-p (translation-governing-addresses lin-addr x86)
                        (all-translation-governing-addresses (strip-cars addr-lst) x86))
            (disjoint-p (translation-governing-addresses lin-addr x86)
                        (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w (cpl x86) x86)))
            (not (programmer-level-mode x86))
            (addr-byte-alistp addr-lst)
            (x86p x86))
           (equal (translation-governing-addresses lin-addr (mv-nth 1 (wb addr-lst x86)))
                  (translation-governing-addresses lin-addr x86)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (disjoint-p
                             translation-governing-addresses)
                            (wb)))))

(defthm all-translation-governing-addresses-and-write-to-physical-memory-disjoint-p
  (implies (and (disjoint-p (all-translation-governing-addresses l-addrs x86)
                            p-addrs)
                (physical-address-listp p-addrs)
                (byte-listp bytes)
                (equal (len p-addrs) (len bytes)))
           (equal (all-translation-governing-addresses
                   l-addrs (write-to-physical-memory p-addrs bytes x86))
                  (all-translation-governing-addresses l-addrs x86)))
  :hints (("Goal"
           :in-theory (e/d* (disjoint-p
                             disjoint-p-commutative
                             all-translation-governing-addresses)
                            ()))))

(defthm all-translation-governing-addresses-and-mv-nth-2-las-to-pas
  (implies (x86p x86)
           (equal (all-translation-governing-addresses
                   l-addrs-1 (mv-nth 2 (las-to-pas l-addrs-2 r-w-x cpl x86)))
                  (all-translation-governing-addresses l-addrs-1 x86)))
  :hints (("Goal"
           :in-theory (e/d* (disjoint-p all-translation-governing-addresses) ()))))

(defthm all-translation-governing-addresses-and-mv-nth-1-wb-disjoint
  (implies (and
            (disjoint-p (all-translation-governing-addresses l-addrs x86)
                        (all-translation-governing-addresses (strip-cars addr-lst) x86))
            (disjoint-p (all-translation-governing-addresses l-addrs x86)
                        (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w (cpl x86) x86)))
            (not (programmer-level-mode x86))
            (addr-byte-alistp addr-lst)
            (x86p x86))
           (equal (all-translation-governing-addresses l-addrs (mv-nth 1 (wb addr-lst x86)))
                  (all-translation-governing-addresses l-addrs x86)))
  :hints (("Goal"
           :in-theory (e/d* (all-translation-governing-addresses)
                            (translation-governing-addresses
                             wb))
           :induct (all-translation-governing-addresses l-addrs x86))))

;; ======================================================================
