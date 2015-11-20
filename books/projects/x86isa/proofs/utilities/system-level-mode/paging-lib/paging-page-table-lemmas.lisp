;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")
(include-book "x86-ia32e-paging-alt" :ttags :all)
(include-book "gather-paging-structures-thms" :ttags :all)

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))
(local (include-book "centaur/gl/gl" :dir :system))

;; ======================================================================

;; PML4 table:

(defthm xlate-equiv-x86s-and-pml4-table-base-addr-address
  (implies (equal (ctri *cr3* x86-1) (ctri *cr3* x86-2))
           (equal (mv-nth 1 (pml4-table-base-addr x86-1))
                  (mv-nth 1 (pml4-table-base-addr x86-2))))
  :hints (("Goal" :in-theory (e/d* (pml4-table-base-addr) ()))))

(defthm xlate-equiv-x86s-and-pml4-table-entry-addr-address
  (implies (and (xlate-equiv-x86s x86-1 x86-2)
                (x86p x86-2))
           (equal (pml4-table-entry-addr lin-addr (mv-nth 1 (pml4-table-base-addr x86-1)))
                  (pml4-table-entry-addr lin-addr (mv-nth 1 (pml4-table-base-addr x86-2)))))
  :hints (("Goal"
           :use ((:instance xlate-equiv-x86s-and-pml4-table-base-addr-address))
           :in-theory (e/d* (pml4-table-entry-addr
                             xlate-equiv-x86s)
                            (xlate-equiv-x86s-and-pml4-table-base-addr-address)))))

(defthmd remove-logext-from-pml4-table-entry-addr
  (implies (pml4-table-entry-addr-found-p lin-addr x86)
           (canonical-address-p lin-addr))
  :hints
  (("Goal"
    :in-theory (e/d* (page-table-entry-addr-found-p
                      pml4-table-entry-addr-found-p
                      page-directory-entry-addr-found-p
                      pml4-table-entry-addr-found-p)
                     ()))))

(defthm xlate-equiv-x86s-and-pml4-table-entry-addr-value
  (implies (and
            ;;
            (x86p x86-1)
            (x86p x86-2)
            (equal (xr :ctr *cr3* x86-1) (xr :ctr *cr3* x86-2))
            (equal (gather-all-paging-structure-qword-addresses x86-1)
                   (gather-all-paging-structure-qword-addresses x86-2))
            (xlate-equiv-entries-at-qword-addresses?
             (gather-all-paging-structure-qword-addresses x86-1)
             (gather-all-paging-structure-qword-addresses x86-2)
             x86-1 x86-2)
            ;;
            (pml4-table-entry-addr-found-p lin-addr x86-1))
           (xlate-equiv-entries
            (rm-low-64
             (pml4-table-entry-addr
              (logext 48 lin-addr) (mv-nth 1 (pml4-table-base-addr x86-1)))
             x86-1)
            (rm-low-64
             (pml4-table-entry-addr
              (logext 48 lin-addr) (mv-nth 1 (pml4-table-base-addr x86-2)))
             x86-2)))
  :hints (("Goal"
           :use ((:instance xlate-equiv-entries-at-qword-addresses?-implies-xlate-equiv-entries
                            (index (pml4-table-entry-addr
                                    lin-addr (mv-nth 1 (pml4-table-base-addr x86-1))))
                            (addrs (gather-all-paging-structure-qword-addresses x86-1)))
                 (:instance pml4-table-entry-addr-is-in-gather-all-paging-structure-qword-addresses
                            (x86 x86-1))
                 (:instance remove-logext-from-pml4-table-entry-addr
                            (x86 x86-1))
                 (:instance xlate-equiv-x86s-and-pml4-table-base-addr-address))
           :in-theory
           (e/d* ()
                 (xlate-equiv-entries-at-qword-addresses?-implies-xlate-equiv-entries
                  xlate-equiv-x86s-and-pml4-table-base-addr-address
                  pml4-table-entry-addr-is-in-gather-all-paging-structure-qword-addresses
                  xlate-equiv-x86s
                  physical-address-p)))))

(defthm pml4-table-entry-addr-found-p-and-xlate-equiv-x86s
  (implies (and (xlate-equiv-x86s x86-1 x86-2)
                (pml4-table-entry-addr-found-p lin-addr x86-1)
                (canonical-address-p lin-addr)
                (x86p x86-1)
                (x86p x86-2))
           (pml4-table-entry-addr-found-p lin-addr x86-2))
  :hints (("Goal"
           :use ((:instance xlate-equiv-x86s-and-pml4-table-base-addr-address))
           :in-theory (e/d* (pml4-table-entry-addr-found-p)
                            (physical-address-p
                             xlate-equiv-x86s-and-pml4-table-base-addr-address
                             bitops::logand-with-negated-bitmask)))))

;; ======================================================================

;; Page directory pointer table:

(defthm xlate-equiv-x86s-and-page-dir-ptr-table-base-addr-error
  (implies (and (xlate-equiv-x86s x86-1 x86-2)
                (x86p x86-2))
           (equal (mv-nth 0 (page-dir-ptr-table-base-addr lin-addr x86-1))
                  (mv-nth 0 (page-dir-ptr-table-base-addr lin-addr x86-2))))
  :hints (("Goal" :in-theory (e/d* (page-dir-ptr-table-base-addr)
                                   (xlate-equiv-x86s
                                    xlate-equiv-x86s-and-pml4-table-base-addr-address))
           :use ((:instance xlate-equiv-x86s-and-pml4-table-base-addr-address)))))

(defthm xlate-equiv-x86s-and-page-dir-ptr-table-base-addr-address
  (implies (and
            ;;
            (x86p x86-1)
            (x86p x86-2)
            (equal (xr :ctr *cr3* x86-1) (xr :ctr *cr3* x86-2))
            (equal (gather-all-paging-structure-qword-addresses x86-1)
                   (gather-all-paging-structure-qword-addresses x86-2))
            (xlate-equiv-entries-at-qword-addresses?
             (gather-all-paging-structure-qword-addresses x86-1)
             (gather-all-paging-structure-qword-addresses x86-2)
             x86-1 x86-2)
            ;;
            (pml4-table-entry-addr-found-p lin-addr x86-1))
           (equal (mv-nth 1 (page-dir-ptr-table-base-addr lin-addr x86-1))
                  (mv-nth 1 (page-dir-ptr-table-base-addr lin-addr x86-2))))
  :hints (("Goal" :in-theory (e/d* (page-dir-ptr-table-base-addr)
                                   (xlate-equiv-x86s-and-pml4-table-entry-addr-address
                                    xlate-equiv-x86s-and-pml4-table-base-addr-address
                                    xlate-equiv-entries-at-qword-addresses?-implies-xlate-equiv-entries
                                    pml4-table-entry-addr-is-in-gather-all-paging-structure-qword-addresses
                                    canonical-address-p
                                    physical-address-p))
           :use ((:instance logtail-bigger
                            (m 7)
                            (n 12)
                            (e1 (rm-low-64
                                 (pml4-table-entry-addr
                                  lin-addr (mv-nth 1 (pml4-table-base-addr x86-1)))
                                 x86-1))
                            (e2 (rm-low-64
                                 (pml4-table-entry-addr
                                  lin-addr (mv-nth 1 (pml4-table-base-addr x86-1)))
                                 x86-2)))
                 (:instance xlate-equiv-x86s-and-pml4-table-entry-addr-address)
                 (:instance pml4-table-entry-addr-is-in-gather-all-paging-structure-qword-addresses
                            (x86 x86-1))
                 (:instance xlate-equiv-entries-at-qword-addresses?-implies-xlate-equiv-entries
                            (index (pml4-table-entry-addr lin-addr (mv-nth 1 (pml4-table-base-addr x86-1))))
                            (addrs (gather-all-paging-structure-qword-addresses x86-1)))))))

(defthm xlate-equiv-x86s-and-page-dir-ptr-table-entry-addr-address
  (implies (and
            ;;
            (x86p x86-1)
            (x86p x86-2)
            (equal (xr :ctr *cr3* x86-1) (xr :ctr *cr3* x86-2))
            (equal (gather-all-paging-structure-qword-addresses x86-1)
                   (gather-all-paging-structure-qword-addresses x86-2))
            (xlate-equiv-entries-at-qword-addresses?
             (gather-all-paging-structure-qword-addresses x86-1)
             (gather-all-paging-structure-qword-addresses x86-2)
             x86-1 x86-2)
            ;;
            (pml4-table-entry-addr-found-p lin-addr x86-1))
           (equal (page-dir-ptr-table-entry-addr
                   lin-addr (mv-nth 1 (page-dir-ptr-table-base-addr lin-addr x86-1)))
                  (page-dir-ptr-table-entry-addr
                   lin-addr (mv-nth 1 (page-dir-ptr-table-base-addr lin-addr x86-2)))))
  :hints (("Goal" :in-theory (e/d* (page-dir-ptr-table-base-addr)
                                   (xlate-equiv-x86s-and-page-dir-ptr-table-base-addr-address))
           :use (xlate-equiv-x86s-and-page-dir-ptr-table-base-addr-address))))

(defthmd remove-logext-from-page-dir-ptr-table-entry-addr
  (implies (page-dir-ptr-table-entry-addr-found-p lin-addr x86)
           (canonical-address-p lin-addr))
  :hints
  (("Goal" :in-theory (e/d* (page-table-entry-addr-found-p
                             page-dir-ptr-table-entry-addr-found-p
                             page-directory-entry-addr-found-p
                             pml4-table-entry-addr-found-p)
                            ()))))

(defthm xlate-equiv-x86s-and-page-dir-ptr-table-entry-addr-value
  (implies (and
            ;;
            (x86p x86-1)
            (x86p x86-2)
            (equal (xr :ctr *cr3* x86-1) (xr :ctr *cr3* x86-2))
            (equal (gather-all-paging-structure-qword-addresses x86-1)
                   (gather-all-paging-structure-qword-addresses x86-2))
            (xlate-equiv-entries-at-qword-addresses?
             (gather-all-paging-structure-qword-addresses x86-1)
             (gather-all-paging-structure-qword-addresses x86-2)
             x86-1 x86-2)
            ;;
            (page-dir-ptr-table-entry-addr-found-p lin-addr x86-1))
           (xlate-equiv-entries
            (rm-low-64
             (page-dir-ptr-table-entry-addr
              (logext 48 lin-addr) (mv-nth 1 (page-dir-ptr-table-base-addr lin-addr x86-1)))
             x86-1)
            (rm-low-64
             (page-dir-ptr-table-entry-addr
              (logext 48 lin-addr) (mv-nth 1 (page-dir-ptr-table-base-addr lin-addr x86-2)))
             x86-2)))
  :hints (("Goal"
           :use ((:instance xlate-equiv-entries-at-qword-addresses?-implies-xlate-equiv-entries
                            (index (page-dir-ptr-table-entry-addr
                                    lin-addr (mv-nth 1 (page-dir-ptr-table-base-addr lin-addr x86-2))))
                            (addrs (gather-all-paging-structure-qword-addresses x86-2)))
                 (:instance page-dir-ptr-table-entry-addr-is-in-gather-all-paging-structure-qword-addresses
                            (x86 x86-1))
                 (:instance remove-logext-from-page-dir-ptr-table-entry-addr
                            (x86 x86-1)))
           :in-theory
           (e/d* ()
                 (xlate-equiv-entries-at-qword-addresses?-implies-xlate-equiv-entries
                  page-dir-ptr-table-entry-addr-is-in-gather-all-paging-structure-qword-addresses
                  xlate-equiv-x86s
                  physical-address-p)))))

(defthm page-dir-ptr-table-entry-addr-found-p-and-xlate-equiv-x86s
  (implies (and (xlate-equiv-x86s x86-1 x86-2)
                (equal (xr :ctr *cr3* x86-1) (xr :ctr *cr3* x86-2))
                (equal (gather-all-paging-structure-qword-addresses x86-1)
                       (gather-all-paging-structure-qword-addresses x86-2))
                (xlate-equiv-entries-at-qword-addresses?
                 (gather-all-paging-structure-qword-addresses x86-1)
                 (gather-all-paging-structure-qword-addresses x86-2)
                 x86-1 x86-2)
                (page-dir-ptr-table-entry-addr-found-p lin-addr x86-1)
                (canonical-address-p lin-addr)
                (x86p x86-2))
           (page-dir-ptr-table-entry-addr-found-p lin-addr x86-2))
  :hints (("Goal"
           :use ((:instance pml4-table-entry-addr-found-p-and-xlate-equiv-x86s)
                 (:instance xlate-equiv-x86s-and-pml4-table-entry-addr-value)
                 (:instance logtail-bigger-and-logbitp
                            (e1 (rm-low-64
                                 (pml4-table-entry-addr lin-addr
                                                        (mv-nth 1 (pml4-table-base-addr x86-1)))
                                 x86-1))
                            (e2 (rm-low-64 (pml4-table-entry-addr lin-addr (mv-nth 1 (pml4-table-base-addr x86-2)))
                                           x86-2))
                            (m 7)
                            (n  7))
                 (:instance xlate-equiv-entries-and-loghead
                            (e1 (rm-low-64
                                 (pml4-table-entry-addr lin-addr
                                                        (mv-nth 1 (pml4-table-base-addr x86-1)))
                                 x86-1))
                            (e2 (rm-low-64 (pml4-table-entry-addr lin-addr (mv-nth 1 (pml4-table-base-addr x86-2)))
                                           x86-2))
                            (n 1))
                 (:instance xlate-equiv-entries-and-logtail
                            (e1 (rm-low-64
                                 (pml4-table-entry-addr lin-addr
                                                        (mv-nth 1 (pml4-table-base-addr x86-1)))
                                 x86-1))
                            (e2 (rm-low-64 (pml4-table-entry-addr lin-addr (mv-nth 1 (pml4-table-base-addr x86-2)))
                                           x86-2))
                            (n 12))
                 (:instance remove-logext-from-pml4-table-entry-addr
                            (x86 x86-1))
                 (:instance remove-logext-from-pml4-table-entry-addr
                            (x86 x86-2)))
           :in-theory (e/d* (page-dir-ptr-table-entry-addr-found-p)
                            (physical-address-p
                             xlate-equiv-x86s-and-pml4-table-entry-addr-value
                             pml4-table-entry-addr-found-p-and-xlate-equiv-x86s
                             bitops::logand-with-negated-bitmask)))))

;; ======================================================================

;; Page directory:

(defthm xlate-equiv-x86s-and-page-directory-base-addr-error
  (implies (and
            ;;
            (x86p x86-1)
            (x86p x86-2)
            (equal (xr :ctr *cr3* x86-1) (xr :ctr *cr3* x86-2))
            (equal (gather-all-paging-structure-qword-addresses x86-1)
                   (gather-all-paging-structure-qword-addresses x86-2))
            (xlate-equiv-entries-at-qword-addresses?
             (gather-all-paging-structure-qword-addresses x86-1)
             (gather-all-paging-structure-qword-addresses x86-2)
             x86-1 x86-2)
            ;;
            (page-dir-ptr-table-entry-addr-found-p lin-addr x86-1))
           (equal (mv-nth 0 (page-directory-base-addr lin-addr x86-1))
                  (mv-nth 0 (page-directory-base-addr lin-addr x86-2))))
  :hints (("Goal" :in-theory
           (e/d* (page-directory-base-addr)
                 (xlate-equiv-x86s
                  xlate-equiv-x86s-and-page-dir-ptr-table-entry-addr-address
                  xlate-equiv-x86s-and-page-dir-ptr-table-base-addr-address
                  page-dir-ptr-table-entry-addr-is-in-gather-all-paging-structure-qword-addresses
                  xlate-equiv-entries-at-qword-addresses?-implies-xlate-equiv-entries
                  canonical-address-p
                  physical-address-p))
           :use ((:instance xlate-equiv-x86s-and-page-dir-ptr-table-entry-addr-address)
                 (:instance page-dir-ptr-table-entry-addr-is-in-gather-all-paging-structure-qword-addresses
                            (x86 x86-1))
                 (:instance xlate-equiv-entries-at-qword-addresses?-implies-xlate-equiv-entries
                            (index (page-dir-ptr-table-entry-addr
                                    lin-addr
                                    (mv-nth 1 (page-dir-ptr-table-base-addr lin-addr x86-1))))
                            (addrs (gather-all-paging-structure-qword-addresses x86-1)))
                 (:instance logtail-bigger-and-logbitp
                            (e1 (rm-low-64
                                 (page-dir-ptr-table-entry-addr
                                  lin-addr
                                  (mv-nth 1 (page-dir-ptr-table-base-addr lin-addr x86-1)))
                                 x86-1))
                            (e2 (rm-low-64
                                 (page-dir-ptr-table-entry-addr
                                  lin-addr
                                  (mv-nth 1 (page-dir-ptr-table-base-addr lin-addr x86-1)))
                                 x86-2))
                            (m 7)
                            (n 7))))))

(defthm xlate-equiv-x86s-and-page-directory-base-addr-address
  (implies (and
            ;;
            (x86p x86-1)
            (x86p x86-2)
            (equal (xr :ctr *cr3* x86-1) (xr :ctr *cr3* x86-2))
            (equal (gather-all-paging-structure-qword-addresses x86-1)
                   (gather-all-paging-structure-qword-addresses x86-2))
            (xlate-equiv-entries-at-qword-addresses?
             (gather-all-paging-structure-qword-addresses x86-1)
             (gather-all-paging-structure-qword-addresses x86-2)
             x86-1 x86-2)
            ;;
            (page-dir-ptr-table-entry-addr-found-p lin-addr x86-1))
           (equal (mv-nth 1 (page-directory-base-addr lin-addr x86-1))
                  (mv-nth 1 (page-directory-base-addr lin-addr x86-2))))
  :hints (("Goal" :in-theory
           (e/d* (page-directory-base-addr)
                 (xlate-equiv-x86s
                  xlate-equiv-x86s-and-page-dir-ptr-table-entry-addr-address
                  xlate-equiv-x86s-and-page-dir-ptr-table-base-addr-address
                  page-dir-ptr-table-entry-addr-is-in-gather-all-paging-structure-qword-addresses
                  xlate-equiv-entries-at-qword-addresses?-implies-xlate-equiv-entries
                  canonical-address-p
                  physical-address-p))
           :use ((:instance xlate-equiv-x86s-and-page-dir-ptr-table-entry-addr-address)
                 (:instance page-dir-ptr-table-entry-addr-is-in-gather-all-paging-structure-qword-addresses
                            (x86 x86-1))
                 (:instance xlate-equiv-entries-at-qword-addresses?-implies-xlate-equiv-entries
                            (index (page-dir-ptr-table-entry-addr
                                    lin-addr
                                    (mv-nth 1 (page-dir-ptr-table-base-addr lin-addr x86-1))))
                            (addrs (gather-all-paging-structure-qword-addresses x86-1)))
                 (:instance logtail-bigger-and-logbitp
                            (e1 (rm-low-64
                                 (page-dir-ptr-table-entry-addr
                                  lin-addr
                                  (mv-nth 1 (page-dir-ptr-table-base-addr lin-addr x86-1)))
                                 x86-1))
                            (e2 (rm-low-64
                                 (page-dir-ptr-table-entry-addr
                                  lin-addr
                                  (mv-nth 1 (page-dir-ptr-table-base-addr lin-addr x86-1)))
                                 x86-2))
                            (m 7)
                            (n 7))
                 (:instance logtail-bigger
                            (e1 (rm-low-64
                                 (page-dir-ptr-table-entry-addr
                                  lin-addr
                                  (mv-nth 1 (page-dir-ptr-table-base-addr lin-addr x86-1)))
                                 x86-1))
                            (e2 (rm-low-64
                                 (page-dir-ptr-table-entry-addr
                                  lin-addr
                                  (mv-nth 1 (page-dir-ptr-table-base-addr lin-addr x86-1)))
                                 x86-2))
                            (m 7)
                            (n 12))))))

(defthm xlate-equiv-x86s-and-page-directory-entry-addr-address
  (implies (and
            ;;
            (x86p x86-1)
            (x86p x86-2)
            (equal (xr :ctr *cr3* x86-1) (xr :ctr *cr3* x86-2))
            (equal (gather-all-paging-structure-qword-addresses x86-1)
                   (gather-all-paging-structure-qword-addresses x86-2))
            (xlate-equiv-entries-at-qword-addresses?
             (gather-all-paging-structure-qword-addresses x86-1)
             (gather-all-paging-structure-qword-addresses x86-2)
             x86-1 x86-2)
            ;;
            (page-dir-ptr-table-entry-addr-found-p lin-addr x86-1))
           (equal (page-directory-entry-addr
                   lin-addr
                   (mv-nth 1 (page-directory-base-addr lin-addr x86-1)))
                  (page-directory-entry-addr
                   lin-addr
                   (mv-nth 1 (page-directory-base-addr lin-addr x86-2)))))
  :hints (("Goal" :in-theory
           (e/d* (page-directory-base-addr)
                 (xlate-equiv-x86s
                  xlate-equiv-x86s-and-page-directory-base-addr-address
                  canonical-address-p
                  physical-address-p))
           :use ((:instance xlate-equiv-x86s-and-page-directory-base-addr-address)))))

(defthmd remove-logext-from-page-directory-entry-addr
  (implies (page-directory-entry-addr-found-p lin-addr x86)
           (canonical-address-p lin-addr))
  :hints
  (("Goal" :in-theory (e/d* (page-table-entry-addr-found-p
                             page-directory-entry-addr-found-p
                             page-dir-ptr-table-entry-addr-found-p
                             pml4-table-entry-addr-found-p)
                            ()))))

(defthm xlate-equiv-x86s-and-page-directory-entry-addr-value
  (implies (and
            ;;
            (x86p x86-1)
            (x86p x86-2)
            (equal (xr :ctr *cr3* x86-1) (xr :ctr *cr3* x86-2))
            (equal (gather-all-paging-structure-qword-addresses x86-1)
                   (gather-all-paging-structure-qword-addresses x86-2))
            (xlate-equiv-entries-at-qword-addresses?
             (gather-all-paging-structure-qword-addresses x86-1)
             (gather-all-paging-structure-qword-addresses x86-2)
             x86-1 x86-2)
            ;;
            (page-directory-entry-addr-found-p lin-addr x86-1))
           (xlate-equiv-entries
            (rm-low-64
             (page-directory-entry-addr
              (logext 48 lin-addr) (mv-nth 1 (page-directory-base-addr lin-addr x86-1)))
             x86-1)
            (rm-low-64
             (page-directory-entry-addr
              (logext 48 lin-addr) (mv-nth 1 (page-directory-base-addr lin-addr x86-2)))
             x86-2)))
  :hints (("Goal"
           :use ((:instance xlate-equiv-entries-at-qword-addresses?-implies-xlate-equiv-entries
                            (index (page-directory-entry-addr
                                    lin-addr (mv-nth 1 (page-directory-base-addr lin-addr x86-2))))
                            (addrs (gather-all-paging-structure-qword-addresses x86-2)))
                 (:instance page-directory-entry-addr-is-in-gather-all-paging-structure-qword-addresses
                            (x86 x86-1))
                 (:instance remove-logext-from-page-directory-entry-addr
                            (x86 x86-1)))
           :in-theory
           (e/d* ()
                 (xlate-equiv-entries-at-qword-addresses?-implies-xlate-equiv-entries
                  page-directory-entry-addr-is-in-gather-all-paging-structure-qword-addresses
                  xlate-equiv-x86s
                  xlate-equiv-x86s-and-page-directory-entry-addr-address
                  physical-address-p)))))

(defthm page-directory-entry-addr-found-p-and-xlate-equiv-x86s
  (implies (and (xlate-equiv-x86s x86-1 x86-2)
                (equal (gather-all-paging-structure-qword-addresses x86-1)
                       (gather-all-paging-structure-qword-addresses x86-2))
                (xlate-equiv-entries-at-qword-addresses?
                 (gather-all-paging-structure-qword-addresses x86-1)
                 (gather-all-paging-structure-qword-addresses x86-2)
                 x86-1 x86-2)
                (page-directory-entry-addr-found-p lin-addr x86-1)
                (canonical-address-p lin-addr)
                (x86p x86-2))
           (page-directory-entry-addr-found-p lin-addr x86-2))
  :hints (("Goal"
           :use ((:instance page-dir-ptr-table-entry-addr-found-p-and-xlate-equiv-x86s)
                 (:instance xlate-equiv-x86s-and-page-dir-ptr-table-entry-addr-value)
                 (:instance logtail-bigger-and-logbitp
                            (e1 (rm-low-64
                                 (page-dir-ptr-table-entry-addr lin-addr (mv-nth 1 (page-dir-ptr-table-base-addr lin-addr x86-1)))
                                 x86-1))
                            (e2 (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr (mv-nth 1 (page-dir-ptr-table-base-addr lin-addr x86-2)))
                                           x86-2))
                            (m 7)
                            (n  7))
                 (:instance xlate-equiv-entries-and-loghead
                            (e1 (rm-low-64
                                 (page-dir-ptr-table-entry-addr lin-addr
                                                                (mv-nth 1 (page-dir-ptr-table-base-addr lin-addr x86-1)))
                                 x86-1))
                            (e2 (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr (mv-nth 1 (page-dir-ptr-table-base-addr lin-addr x86-2)))
                                           x86-2))
                            (n 1))
                 (:instance xlate-equiv-entries-and-logtail
                            (e1 (rm-low-64
                                 (page-dir-ptr-table-entry-addr lin-addr
                                                                (mv-nth 1 (page-dir-ptr-table-base-addr lin-addr x86-1)))
                                 x86-1))
                            (e2 (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr (mv-nth 1 (page-dir-ptr-table-base-addr lin-addr x86-2)))
                                           x86-2))
                            (n 12))
                 (:instance remove-logext-from-page-dir-ptr-table-entry-addr
                            (x86 x86-1))
                 (:instance remove-logext-from-page-dir-ptr-table-entry-addr
                            (x86 x86-2)))
           :in-theory (e/d* (page-directory-entry-addr-found-p)
                            (physical-address-p
                             xlate-equiv-x86s-and-page-dir-ptr-table-entry-addr-value
                             page-dir-ptr-table-entry-addr-found-p-and-xlate-equiv-x86s
                             xlate-equiv-x86s-and-page-dir-ptr-table-base-addr-address
                             xlate-equiv-x86s-and-page-dir-ptr-table-entry-addr-address
                             bitops::logand-with-negated-bitmask)))))

;; ======================================================================

;; Page table:

(defthm xlate-equiv-x86s-and-page-table-base-addr-error
  (implies (and
            ;;
            (x86p x86-1)
            (x86p x86-2)
            (equal (xr :ctr *cr3* x86-1) (xr :ctr *cr3* x86-2))
            (equal (gather-all-paging-structure-qword-addresses x86-1)
                   (gather-all-paging-structure-qword-addresses x86-2))
            (xlate-equiv-entries-at-qword-addresses?
             (gather-all-paging-structure-qword-addresses x86-1)
             (gather-all-paging-structure-qword-addresses x86-2)
             x86-1 x86-2)
            ;;
            (page-directory-entry-addr-found-p lin-addr x86-1))
           (equal (mv-nth 0 (page-table-base-addr lin-addr x86-1))
                  (mv-nth 0 (page-table-base-addr lin-addr x86-2))))
  :hints (("Goal" :in-theory
           (e/d* (page-table-base-addr)
                 (xlate-equiv-x86s
                  xlate-equiv-x86s-and-page-directory-entry-addr-address
                  xlate-equiv-x86s-and-page-directory-base-addr-address
                  page-directory-entry-addr-is-in-gather-all-paging-structure-qword-addresses
                  xlate-equiv-entries-at-qword-addresses?-implies-xlate-equiv-entries
                  canonical-address-p
                  physical-address-p))
           :use ((:instance xlate-equiv-x86s-and-page-directory-entry-addr-address)
                 (:instance page-directory-entry-addr-is-in-gather-all-paging-structure-qword-addresses
                            (x86 x86-1))
                 (:instance xlate-equiv-entries-at-qword-addresses?-implies-xlate-equiv-entries
                            (index (page-directory-entry-addr
                                    lin-addr
                                    (mv-nth 1 (page-directory-base-addr lin-addr x86-1))))
                            (addrs (gather-all-paging-structure-qword-addresses x86-1)))
                 (:instance logtail-bigger-and-logbitp
                            (e1 (rm-low-64
                                 (page-directory-entry-addr
                                  lin-addr
                                  (mv-nth 1 (page-directory-base-addr lin-addr x86-1)))
                                 x86-1))
                            (e2 (rm-low-64
                                 (page-directory-entry-addr
                                  lin-addr
                                  (mv-nth 1 (page-directory-base-addr lin-addr x86-2)))
                                 x86-2))
                            (m 7)
                            (n 7))))))

(defthm xlate-equiv-x86s-and-page-table-base-addr-address
  (implies (and
            ;;
            (x86p x86-1)
            (x86p x86-2)
            (equal (xr :ctr *cr3* x86-1) (xr :ctr *cr3* x86-2))
            (equal (gather-all-paging-structure-qword-addresses x86-1)
                   (gather-all-paging-structure-qword-addresses x86-2))
            (xlate-equiv-entries-at-qword-addresses?
             (gather-all-paging-structure-qword-addresses x86-1)
             (gather-all-paging-structure-qword-addresses x86-2)
             x86-1 x86-2)
            ;;
            (page-directory-entry-addr-found-p lin-addr x86-1))
           (equal (mv-nth 1 (page-table-base-addr lin-addr x86-1))
                  (mv-nth 1 (page-table-base-addr lin-addr x86-2))))
  :hints (("Goal" :in-theory
           (e/d* (page-table-base-addr)
                 (xlate-equiv-x86s
                  xlate-equiv-x86s-and-page-directory-entry-addr-address
                  xlate-equiv-x86s-and-page-directory-base-addr-address
                  page-directory-entry-addr-is-in-gather-all-paging-structure-qword-addresses
                  xlate-equiv-entries-at-qword-addresses?-implies-xlate-equiv-entries
                  canonical-address-p
                  physical-address-p))
           :use ((:instance xlate-equiv-x86s-and-page-directory-entry-addr-address)
                 (:instance page-directory-entry-addr-is-in-gather-all-paging-structure-qword-addresses
                            (x86 x86-1))
                 (:instance xlate-equiv-entries-at-qword-addresses?-implies-xlate-equiv-entries
                            (index (page-directory-entry-addr
                                    lin-addr
                                    (mv-nth 1 (page-directory-base-addr lin-addr x86-1))))
                            (addrs (gather-all-paging-structure-qword-addresses x86-1)))
                 (:instance logtail-bigger-and-logbitp
                            (e1 (rm-low-64
                                 (page-directory-entry-addr
                                  lin-addr
                                  (mv-nth 1 (page-directory-base-addr lin-addr x86-1)))
                                 x86-1))
                            (e2 (rm-low-64
                                 (page-directory-entry-addr
                                  lin-addr
                                  (mv-nth 1 (page-directory-base-addr lin-addr x86-2)))
                                 x86-2))
                            (m 7)
                            (n 7))
                 (:instance logtail-bigger
                            (e1 (rm-low-64
                                 (page-directory-entry-addr
                                  lin-addr
                                  (mv-nth 1 (page-directory-base-addr lin-addr x86-1)))
                                 x86-1))
                            (e2 (rm-low-64
                                 (page-directory-entry-addr
                                  lin-addr
                                  (mv-nth 1 (page-directory-base-addr lin-addr x86-2)))
                                 x86-2))
                            (m 7)
                            (n 12))))))

(defthm xlate-equiv-x86s-and-page-table-entry-addr-address
  (implies (and
            ;;
            (x86p x86-1)
            (x86p x86-2)
            (equal (xr :ctr *cr3* x86-1) (xr :ctr *cr3* x86-2))
            (equal (gather-all-paging-structure-qword-addresses x86-1)
                   (gather-all-paging-structure-qword-addresses x86-2))
            (xlate-equiv-entries-at-qword-addresses?
             (gather-all-paging-structure-qword-addresses x86-1)
             (gather-all-paging-structure-qword-addresses x86-2)
             x86-1 x86-2)
            ;;
            (page-directory-entry-addr-found-p lin-addr x86-1))
           (equal (page-table-entry-addr
                   lin-addr (mv-nth 1 (page-table-base-addr lin-addr x86-1)))
                  (page-table-entry-addr
                   lin-addr (mv-nth 1 (page-table-base-addr lin-addr x86-2)))))
  :hints (("Goal" :in-theory
           (e/d* (page-table-base-addr)
                 (xlate-equiv-x86s
                  xlate-equiv-x86s-and-page-directory-entry-addr-address
                  xlate-equiv-x86s-and-page-table-base-addr-address
                  canonical-address-p
                  physical-address-p))
           :use (:instance xlate-equiv-x86s-and-page-table-base-addr-address))))

(local
 (defthmd remove-logext-from-page-table-entry-addr
   (implies (page-table-entry-addr-found-p lin-addr x86)
            (canonical-address-p lin-addr))
   :hints (("Goal" :in-theory (e/d* (page-table-entry-addr-found-p
                                     page-directory-entry-addr-found-p
                                     page-dir-ptr-table-entry-addr-found-p
                                     pml4-table-entry-addr-found-p)
                                    (xlate-equiv-x86s-and-page-dir-ptr-table-base-addr-address
                                     xlate-equiv-x86s-and-page-dir-ptr-table-entry-addr-address
                                     xlate-equiv-x86s-and-page-directory-base-addr-address
                                     xlate-equiv-x86s-and-page-directory-entry-addr-address
                                     xlate-equiv-x86s-and-page-table-base-addr-address
                                     xlate-equiv-x86s-and-page-table-entry-addr-address))))))

(defthm xlate-equiv-x86s-and-page-table-entry-addr-value
  (implies (and
            ;;
            (x86p x86-1)
            (x86p x86-2)
            (equal (xr :ctr *cr3* x86-1) (xr :ctr *cr3* x86-2))
            (equal (gather-all-paging-structure-qword-addresses x86-1)
                   (gather-all-paging-structure-qword-addresses x86-2))
            (xlate-equiv-entries-at-qword-addresses?
             (gather-all-paging-structure-qword-addresses x86-1)
             (gather-all-paging-structure-qword-addresses x86-2)
             x86-1 x86-2)
            ;;
            (page-table-entry-addr-found-p lin-addr x86-1))
           (xlate-equiv-entries
            (rm-low-64
             (page-table-entry-addr
              (logext 48 lin-addr) (mv-nth 1 (page-table-base-addr lin-addr x86-1)))
             x86-1)
            (rm-low-64
             (page-table-entry-addr
              (logext 48 lin-addr) (mv-nth 1 (page-table-base-addr lin-addr x86-2)))
             x86-2)))
  :hints (("Goal"
           :use ((:instance xlate-equiv-entries-at-qword-addresses?-implies-xlate-equiv-entries
                            (index (page-table-entry-addr lin-addr (mv-nth 1 (page-table-base-addr lin-addr x86-2))))
                            (addrs (gather-all-paging-structure-qword-addresses x86-2)))
                 (:instance page-table-entry-addr-is-in-gather-all-paging-structure-qword-addresses
                            (x86 x86-1))
                 (:instance remove-logext-from-page-table-entry-addr
                            (x86 x86-1)))
           :in-theory
           (e/d* ()
                 (xlate-equiv-entries-at-qword-addresses?-implies-xlate-equiv-entries
                  page-table-entry-addr-is-in-gather-all-paging-structure-qword-addresses
                  xlate-equiv-x86s
                  xlate-equiv-x86s-and-page-directory-entry-addr-address
                  xlate-equiv-x86s-and-page-table-base-addr-address
                  physical-address-p)))))

(defthm page-table-entry-addr-found-p-and-xlate-equiv-x86s
  (implies (and (xlate-equiv-x86s x86-1 x86-2)
                (equal (gather-all-paging-structure-qword-addresses x86-1)
                       (gather-all-paging-structure-qword-addresses x86-2))
                (xlate-equiv-entries-at-qword-addresses?
                 (gather-all-paging-structure-qword-addresses x86-1)
                 (gather-all-paging-structure-qword-addresses x86-2)
                 x86-1 x86-2)
                (page-table-entry-addr-found-p lin-addr x86-1)
                (canonical-address-p lin-addr)
                (x86p x86-2))
           (page-table-entry-addr-found-p lin-addr x86-2))
  :hints (("Goal"
           :use ((:instance page-directory-entry-addr-found-p-and-xlate-equiv-x86s)
                 (:instance xlate-equiv-x86s-and-page-directory-entry-addr-value)
                 (:instance logtail-bigger-and-logbitp
                            (e1 (rm-low-64
                                 (page-directory-entry-addr lin-addr (mv-nth 1 (page-directory-base-addr lin-addr x86-1)))
                                 x86-1))
                            (e2 (rm-low-64
                                 (page-directory-entry-addr lin-addr (mv-nth 1 (page-directory-base-addr lin-addr x86-2)))
                                 x86-2))
                            (m 7)
                            (n 7))
                 (:instance xlate-equiv-entries-and-loghead
                            (e1 (rm-low-64
                                 (page-directory-entry-addr lin-addr (mv-nth 1 (page-directory-base-addr lin-addr x86-1)))
                                 x86-1))
                            (e2 (rm-low-64
                                 (page-directory-entry-addr lin-addr (mv-nth 1 (page-directory-base-addr lin-addr x86-2)))
                                 x86-2))
                            (n 1))
                 (:instance xlate-equiv-entries-and-logtail
                            (e1 (rm-low-64
                                 (page-directory-entry-addr lin-addr (mv-nth 1 (page-directory-base-addr lin-addr x86-1)))
                                 x86-1))
                            (e2 (rm-low-64
                                 (page-directory-entry-addr lin-addr (mv-nth 1 (page-directory-base-addr lin-addr x86-2)))
                                 x86-2))
                            (n 12))
                 (:instance remove-logext-from-page-directory-entry-addr
                            (x86 x86-1))
                 (:instance remove-logext-from-page-directory-entry-addr
                            (x86 x86-2)))
           :in-theory (e/d* (page-table-entry-addr-found-p)
                            (physical-address-p
                             xlate-equiv-x86s-and-page-directory-entry-addr-value
                             pml4-table-entry-addr-found-p-and-xlate-equiv-x86s
                             xlate-equiv-x86s-and-page-directory-base-addr-address
                             xlate-equiv-x86s-and-page-directory-base-addr-error
                             xlate-equiv-x86s-and-page-directory-entry-addr-address
                             xlate-equiv-x86s-and-page-table-base-addr-address
                             xlate-equiv-x86s-and-page-table-base-addr-error
                             xlate-equiv-x86s-and-page-table-entry-addr-address
                             bitops::logand-with-negated-bitmask)))))

;; ======================================================================
;; ======================================================================

(local
 (def-gl-thm logand-loghead-and-page-table-base-addr-helper
   :hyp (unsigned-byte-p 64 x)
   :concl (equal (logand 18446744073709547520 (ash (loghead 40 (logtail 12 x)) 12))
                 (ash (loghead 40 (logtail 12 x)) 12))
   :g-bindings `((x (:g-number ,(gl-int 0 1 65))))))

(defthm logand-loghead-and-page-table-base-addr
  (implies (x86p x86)
           (equal (logand 18446744073709547520 (loghead 52 (mv-nth 1 (page-table-base-addr lin-addr x86))))
                  (mv-nth 1 (page-table-base-addr lin-addr x86))))
  :hints (("Goal" :in-theory (e/d* (page-table-base-addr) ()))))

(defthm mv-nth-1-ia32e-la-to-pa-PT-with-xlate-equiv-x86s
  (implies
   (and (xlate-equiv-x86s x86-1 x86-2)
        ;;
        (x86p x86-1)
        (x86p x86-2)
        (equal (xr :ctr *cr3* x86-1) (xr :ctr *cr3* x86-2))
        (equal (gather-all-paging-structure-qword-addresses x86-1)
               (gather-all-paging-structure-qword-addresses x86-2))
        (xlate-equiv-entries-at-qword-addresses?
         (gather-all-paging-structure-qword-addresses x86-1)
         (gather-all-paging-structure-qword-addresses x86-2)
         x86-1 x86-2)
        ;;
        (page-table-entry-addr-found-p lin-addr x86-1))
   (equal (mv-nth
           1
           (ia32e-la-to-pa-PT
            lin-addr u-s-acc wp smep nxe r-w-x cpl x86-1))
          (mv-nth
           1
           (ia32e-la-to-pa-PT
            lin-addr u-s-acc wp smep nxe r-w-x cpl x86-2))))
  :hints (("Goal"
           :in-theory (e/d* (ia32e-la-to-pa-page-table)
                            (xlate-equiv-x86s-and-page-table-entry-addr-value
                             bitops::logand-with-negated-bitmask))
           :use ((:instance xlate-equiv-x86s-and-page-table-entry-addr-value)
                 ;; xlate-equiv-entries-and-loghead
                 (:instance xlate-equiv-entries-and-loghead
                            (e1 (rm-low-64 (page-table-entry-addr
                                            (logext 48 lin-addr)
                                            (mv-nth 1 (page-table-base-addr lin-addr x86-2)))
                                           x86-1))
                            (e2 (rm-low-64
                                 (page-table-entry-addr
                                  (logext 48 lin-addr)
                                  (mv-nth 1 (page-table-base-addr lin-addr x86-2)))
                                 x86-2))
                            (n 1))
                 ;; xlate-equiv-entries-and-logtail
                 (:instance xlate-equiv-entries-and-logtail
                            (e1 (rm-low-64 (page-table-entry-addr
                                            (logext 48 lin-addr)
                                            (mv-nth 1 (page-table-base-addr lin-addr x86-2)))
                                           x86-1))
                            (e2 (rm-low-64
                                 (page-table-entry-addr
                                  (logext 48 lin-addr)
                                  (mv-nth 1 (page-table-base-addr lin-addr x86-2)))
                                 x86-2))
                            (n 12))
                 (:instance xlate-equiv-entries-and-logtail
                            (e1 (rm-low-64 (page-table-entry-addr
                                            (logext 48 lin-addr)
                                            (mv-nth 1 (page-table-base-addr lin-addr x86-2)))
                                           x86-1))
                            (e2 (rm-low-64
                                 (page-table-entry-addr
                                  (logext 48 lin-addr)
                                  (mv-nth 1 (page-table-base-addr lin-addr x86-2)))
                                 x86-2))
                            (n 52))
                 ;; loghead-smaller-and-logbitp
                 (:instance loghead-smaller-and-logbitp
                            (e1 (rm-low-64 (page-table-entry-addr
                                            (logext 48 lin-addr)
                                            (mv-nth 1 (page-table-base-addr lin-addr x86-2)))
                                           x86-1))
                            (e2 (rm-low-64
                                 (page-table-entry-addr
                                  (logext 48 lin-addr)
                                  (mv-nth 1 (page-table-base-addr lin-addr x86-2)))
                                 x86-2))
                            (m 1)
                            (n 5))
                 (:instance loghead-smaller-and-logbitp
                            (e1 (rm-low-64 (page-table-entry-addr
                                            (logext 48 lin-addr)
                                            (mv-nth 1 (page-table-base-addr lin-addr x86-2)))
                                           x86-1))
                            (e2 (rm-low-64
                                 (page-table-entry-addr
                                  (logext 48 lin-addr)
                                  (mv-nth 1 (page-table-base-addr lin-addr x86-2)))
                                 x86-2))
                            (m 2)
                            (n 5))
                 ;; logtail-bigger-and-logbitp
                 (:instance logtail-bigger-and-logbitp
                            (e1 (rm-low-64 (page-table-entry-addr
                                            (logext 48 lin-addr)
                                            (mv-nth 1 (page-table-base-addr lin-addr x86-2)))
                                           x86-1))
                            (e2 (rm-low-64
                                 (page-table-entry-addr
                                  (logext 48 lin-addr)
                                  (mv-nth 1 (page-table-base-addr lin-addr x86-2)))
                                 x86-2))
                            (m 7)
                            (n 52))
                 (:instance logtail-bigger-and-logbitp
                            (e1 (rm-low-64 (page-table-entry-addr
                                            (logext 48 lin-addr)
                                            (mv-nth 1 (page-table-base-addr lin-addr x86-2)))
                                           x86-1))
                            (e2 (rm-low-64
                                 (page-table-entry-addr
                                  (logext 48 lin-addr)
                                  (mv-nth 1 (page-table-base-addr lin-addr x86-2)))
                                 x86-2))
                            (m 7)
                            (n 63))))))


(local
 (defthmd page-table-entry-addr-found-p-and-x86p
   (implies (page-table-entry-addr-found-p lin-addr x86)
            (x86p x86))
   :hints (("Goal" :in-theory (e/d* (page-table-entry-addr-found-p
                                     page-directory-entry-addr-found-p
                                     page-dir-ptr-table-entry-addr-found-p
                                     pml4-table-entry-addr-found-p)
                                    (xlate-equiv-x86s-and-page-dir-ptr-table-base-addr-address
                                     xlate-equiv-x86s-and-page-dir-ptr-table-entry-addr-address
                                     xlate-equiv-x86s-and-page-directory-base-addr-address
                                     xlate-equiv-x86s-and-page-directory-entry-addr-address
                                     xlate-equiv-x86s-and-page-table-base-addr-address
                                     xlate-equiv-x86s-and-page-table-entry-addr-address))))))

(defrule xlate-equiv-x86s-with-mv-nth-2-ia32e-la-to-pa-PT
  (implies
   (and (page-table-entry-addr-found-p lin-addr x86)
        (mult-8-qword-paddr-list-listp (gather-all-paging-structure-qword-addresses x86))
        (no-duplicates-list-p (gather-all-paging-structure-qword-addresses x86)))
   (xlate-equiv-x86s
    (mv-nth
     2
     (ia32e-la-to-pa-PT
      lin-addr u-s-acc wp smep nxe r-w-x cpl x86))
    x86))
  :use ((:instance remove-logext-from-page-table-entry-addr)
        (:instance page-table-entry-addr-found-p-and-x86p))
  :in-theory (e/d* (ia32e-la-to-pa-page-table
                    page-fault-exception)
                   (bitops::logand-with-negated-bitmask
                    xlate-equiv-x86s-and-page-table-base-addr-error
                    xlate-equiv-x86s-and-page-table-entry-addr-address
                    xlate-equiv-x86s-and-page-table-base-addr-address)))


(defrule two-page-table-walks-ia32e-la-to-pa-page-table-helper
  (implies (and (page-table-entry-addr-found-p lin-addr-1 x86)
                (page-table-entry-addr-found-p lin-addr-2 x86)
                ;; Remove the following hyp...
                (PAGE-TABLE-ENTRY-ADDR-FOUND-P
                 LIN-ADDR-1
                 (MV-NTH 2
                         (IA32E-LA-TO-PA-PAGE-TABLE
                          LIN-ADDR-2
                          (MV-NTH 1 (PAGE-TABLE-BASE-ADDR LIN-ADDR-2 X86))
                          U-S-ACC-2
                          WP-2 SMEP-2 NXE-2 R-W-X-2 CPL-2 X86)))
                (mult-8-qword-paddr-list-listp (gather-all-paging-structure-qword-addresses x86))
                (no-duplicates-list-p (gather-all-paging-structure-qword-addresses x86)))
           (equal
            (mv-nth
             1
             (ia32e-la-to-pa-PT
              lin-addr-1 u-s-acc-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
              (mv-nth
               2
               (ia32e-la-to-pa-PT
                lin-addr-2 u-s-acc-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
            (mv-nth
             1
             (ia32e-la-to-pa-PT
              lin-addr-1 u-s-acc-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86))))
  :use ((:instance xlate-equiv-x86s-with-mv-nth-2-ia32e-la-to-pa-PT
                   (lin-addr lin-addr-2)
                   (u-s-acc u-s-acc-2)
                   (wp wp-2)
                   (smep smep-2)
                   (nxe nxe-2)
                   (r-w-x r-w-x-2)
                   (cpl cpl-2)
                   (x86 x86))
        (:instance mv-nth-1-ia32e-la-to-pa-PT-with-xlate-equiv-x86s
                   (x86-1 (mv-nth 2
                                  (ia32e-la-to-pa-page-table
                                   lin-addr-2
                                   (mv-nth 1 (page-table-base-addr lin-addr-2 x86))
                                   u-s-acc-2
                                   wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)))
                   (x86-2 x86)
                   (lin-addr lin-addr-1)
                   (u-s-acc u-s-acc-1)
                   (wp wp-1)
                   (smep smep-1)
                   (nxe nxe-1)
                   (r-w-x r-w-x-1)
                   (cpl cpl-1)))
  :in-theory (e/d ()
                  (xlate-equiv-x86s-with-mv-nth-2-ia32e-la-to-pa-PT
                   mv-nth-1-ia32e-la-to-pa-PT-with-xlate-equiv-x86s
                   xlate-equiv-x86s-and-page-table-base-addr-error
                   xlate-equiv-x86s-and-page-table-base-addr-address
                   unsigned-byte-p
                   signed-byte-p
                   member-p-cons
                   disjoint-p-cons)))

(defthm page-table-entry-addr-found-p-and-page-table-base-addr-error
  (implies (page-table-entry-addr-found-p lin-addr x86)
           (not (mv-nth 0 (page-table-base-addr lin-addr x86))))
  :hints (("Goal" :in-theory (e/d* (page-table-entry-addr-found-p
                                    page-directory-entry-addr-found-p
                                    page-table-base-addr
                                    page-directory-base-addr)
                                   ()))))

(defthm page-table-entry-addr-found-p-after-a-page-walk
  (implies (and (page-table-entry-addr-found-p lin-addr-1 x86)
                (page-table-entry-addr-found-p lin-addr-2 x86)
                (mult-8-qword-paddr-list-listp (gather-all-paging-structure-qword-addresses x86))
                (no-duplicates-list-p (gather-all-paging-structure-qword-addresses x86)))
           (page-table-entry-addr-found-p
            lin-addr-1
            (mv-nth 2
                    (ia32e-la-to-pa-page-table
                     lin-addr-2
                     (mv-nth 1 (page-table-base-addr lin-addr-2 x86))
                     u-s-acc-2
                     wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
  :hints (("Goal"
           :use ((:instance remove-logext-from-page-table-entry-addr
                            (lin-addr lin-addr-2))
                 (:instance remove-logext-from-page-table-entry-addr
                            (lin-addr lin-addr-1))
                 (:instance page-table-entry-addr-found-p-and-x86p
                            (lin-addr lin-addr-2))
                 (:instance logand-loghead-and-page-table-base-addr
                            (lin-addr lin-addr-2))
                 (:instance page-table-entry-addr-found-p-and-xlate-equiv-x86s
                            (x86-1 x86)
                            (lin-addr lin-addr-1)
                            (x86-2
                             (mv-nth 2
                                     (ia32e-la-to-pa-page-table
                                      lin-addr-2
                                      (mv-nth 1 (page-table-base-addr lin-addr-2 x86))
                                      u-s-acc-2
                                      wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
                 (:instance xlate-equiv-x86s-with-mv-nth-2-ia32e-la-to-pa-PT
                            (x86 x86)
                            (lin-addr lin-addr-2)
                            (u-s-acc u-s-acc-2)
                            (wp wp-2)
                            (smep smep-2)
                            (nxe nxe-2)
                            (r-w-x r-w-x-2)
                            (cpl cpl-2)))
           :in-theory (e/d* ()
                            (physical-address-p
                             page-table-entry-addr-found-p-and-xlate-equiv-x86s
                             xlate-equiv-x86s-with-mv-nth-2-ia32e-la-to-pa-PT
                             xlate-equiv-x86s-and-page-dir-ptr-table-base-addr-address
                             xlate-equiv-x86s-and-page-dir-ptr-table-base-addr-error
                             xlate-equiv-x86s-and-page-dir-ptr-table-entry-addr-address
                             xlate-equiv-x86s-and-page-directory-base-addr-address
                             xlate-equiv-x86s-and-page-directory-base-addr-error
                             xlate-equiv-x86s-and-page-directory-entry-addr-address
                             xlate-equiv-x86s-and-page-table-base-addr-address
                             xlate-equiv-x86s-and-page-table-base-addr-error
                             xlate-equiv-x86s-and-page-table-entry-addr-address
                             bitops::logand-with-negated-bitmask)))))

(defrule two-page-table-walks-ia32e-la-to-pa-page-table
  (implies (and (page-table-entry-addr-found-p lin-addr-1 x86)
                (page-table-entry-addr-found-p lin-addr-2 x86)
                (mult-8-qword-paddr-list-listp (gather-all-paging-structure-qword-addresses x86))
                (no-duplicates-list-p (gather-all-paging-structure-qword-addresses x86)))
           (equal
            (mv-nth
             1
             (ia32e-la-to-pa-PT
              lin-addr-1 u-s-acc-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
              (mv-nth
               2
               (ia32e-la-to-pa-PT
                lin-addr-2 u-s-acc-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
            (mv-nth
             1
             (ia32e-la-to-pa-PT
              lin-addr-1 u-s-acc-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86))))
  :use ((:instance two-page-table-walks-ia32e-la-to-pa-page-table-helper)
        (:instance page-table-entry-addr-found-p-after-a-page-walk))
  :in-theory (e/d ()
                  (two-page-table-walks-ia32e-la-to-pa-page-table-helper
                   page-table-entry-addr-found-p-after-a-page-walk
                   xlate-equiv-x86s-with-mv-nth-2-ia32e-la-to-pa-PT
                   mv-nth-1-ia32e-la-to-pa-PT-with-xlate-equiv-x86s
                   xlate-equiv-x86s-and-page-table-base-addr-error
                   xlate-equiv-x86s-and-page-table-base-addr-address
                   unsigned-byte-p
                   signed-byte-p
                   member-p-cons
                   disjoint-p-cons)))

;; ======================================================================
