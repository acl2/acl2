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

(defthmd loghead-smaller-and-logbitp
  (implies (and (equal (loghead n e1) (loghead n e2))
                (natp n)
                (natp m)
                (< m n))
           (equal (logbitp m e1) (logbitp m e2)))
  :hints (("Goal" :in-theory (e/d* (bitops::ihsext-inductions
                                    bitops::ihsext-recursive-redefs)
                                   ()))))

;; (defun my-lexord-greater (x y)
;;   (if (atom x)
;;       nil
;;     (or (> (car x) (car y))
;;         (and (eql (car x) (car y))
;;              (my-lexord-greater (cdr x) (cdr y))))))

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
  :hints ( ;; (b* ((cases (acl2::access acl2::clause-id id :case-lst))
          ;;      (case '(12)))
          ;;     (and (my-lexord-greater cases case)
          ;;          '(:by nil)))
          ("Goal"
           :use ((:instance xlate-equiv-x86s-and-page-table-entry-addr-value))
           :in-theory (e/d* (ia32e-la-to-pa-page-table)
                            (xlate-equiv-x86s-and-page-table-entry-addr-value
                             xlate-equiv-entries
                             bitops::logand-with-negated-bitmask)))
          ("Subgoal 19"
           :use ((:instance xlate-equiv-x86s-and-page-table-entry-addr-value)
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
                            (n 1)))
           :in-theory (e/d* (ia32e-la-to-pa-page-table)
                            (xlate-equiv-x86s-and-page-table-entry-addr-value
                             xlate-equiv-entries
                             bitops::logand-with-negated-bitmask)))
          ("Subgoal 18"
           :use ((:instance xlate-equiv-x86s-and-page-table-entry-addr-value)
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
                            (n 52)))
           :in-theory (e/d* (ia32e-la-to-pa-page-table)
                            (xlate-equiv-x86s-and-page-table-entry-addr-value
                             xlate-equiv-entries
                             bitops::logand-with-negated-bitmask)))
          ("Subgoal 17"
           :use ((:instance xlate-equiv-x86s-and-page-table-entry-addr-value)
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
                            (n 5)))
           :in-theory (e/d* (ia32e-la-to-pa-page-table)
                            (not
                             xlate-equiv-x86s-and-page-table-entry-addr-value
                             ;; xlate-equiv-entries
                             bitops::logand-with-negated-bitmask)))
          ("Subgoal 16"
           :use ((:instance xlate-equiv-x86s-and-page-table-entry-addr-value)
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
                            (n 63)))
           :in-theory (e/d* (ia32e-la-to-pa-page-table)
                            (not
                             xlate-equiv-x86s-and-page-table-entry-addr-value
                             ;; xlate-equiv-entries
                             bitops::logand-with-negated-bitmask)))
          ("Subgoal 14"
           :use ((:instance xlate-equiv-x86s-and-page-table-entry-addr-value)
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
                            (n 52)))
           :in-theory (e/d* (ia32e-la-to-pa-page-table)
                            (xlate-equiv-x86s-and-page-table-entry-addr-value
                             xlate-equiv-entries
                             bitops::logand-with-negated-bitmask)))
          ("Subgoal 13"
           :use ((:instance xlate-equiv-x86s-and-page-table-entry-addr-value)
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
                            (n 63)))
           :in-theory (e/d* (ia32e-la-to-pa-page-table)
                            (xlate-equiv-x86s-and-page-table-entry-addr-value
                             ;; xlate-equiv-entries
                             bitops::logand-with-negated-bitmask
                             not)))
          ("Subgoal 12"
           :use ((:instance xlate-equiv-x86s-and-page-table-entry-addr-value)
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
                            (n 52)))
           :in-theory (e/d* (ia32e-la-to-pa-page-table)
                            (xlate-equiv-x86s-and-page-table-entry-addr-value
                             xlate-equiv-entries
                             bitops::logand-with-negated-bitmask
                             not)))
          ("Subgoal 11"
           :use ((:instance xlate-equiv-x86s-and-page-table-entry-addr-value)
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
                            (n 52)))
           :in-theory (e/d* (ia32e-la-to-pa-page-table)
                            (xlate-equiv-x86s-and-page-table-entry-addr-value
                             xlate-equiv-entries
                             bitops::logand-with-negated-bitmask
                             not)))
          ("Subgoal 10"
           :use ((:instance xlate-equiv-x86s-and-page-table-entry-addr-value)
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
                            (n 1)))
           :in-theory (e/d* (ia32e-la-to-pa-page-table)
                            (xlate-equiv-x86s-and-page-table-entry-addr-value
                             xlate-equiv-entries
                             bitops::logand-with-negated-bitmask)))
          ("Subgoal 7"
           :use ((:instance xlate-equiv-x86s-and-page-table-entry-addr-value)
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
                            (n 1)))
           :in-theory (e/d* (ia32e-la-to-pa-page-table)
                            (xlate-equiv-x86s-and-page-table-entry-addr-value
                             xlate-equiv-entries
                             bitops::logand-with-negated-bitmask)))
          ("Subgoal 5"
           :use ((:instance xlate-equiv-x86s-and-page-table-entry-addr-value)
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
                            (n 63)))
           :in-theory (e/d* (ia32e-la-to-pa-page-table)
                            (xlate-equiv-x86s-and-page-table-entry-addr-value
                             ;; xlate-equiv-entries
                             bitops::logand-with-negated-bitmask)))
          ("Subgoal 4"
           :use ((:instance xlate-equiv-x86s-and-page-table-entry-addr-value)
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
                            (n 1)))
           :in-theory (e/d* (ia32e-la-to-pa-page-table)
                            (xlate-equiv-x86s-and-page-table-entry-addr-value
                             xlate-equiv-entries
                             bitops::logand-with-negated-bitmask))))
  ;; :rule-classes :congruence
  ;; :otf-flg t
  )

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

;; (i-am-here)

(defthm page-table-entry-addr-found-p-and-page-table-base-addr-error
  (implies (page-table-entry-addr-found-p lin-addr x86)
           (not (mv-nth 0 (page-table-base-addr lin-addr x86))))
  :hints (("Goal" :in-theory (e/d* (page-table-entry-addr-found-p
                                    page-directory-entry-addr-found-p
                                    page-table-base-addr
                                    page-directory-base-addr)
                                   ()))))

(defthm page-table-entry-addr-found-p-after-a-page-fault-exception
  (implies (page-table-entry-addr-found-p lin-addr-1 x86)
           (page-table-entry-addr-found-p
            lin-addr-1
            (mv-nth 2 (page-fault-exception lin-addr-2 err-no x86))))
  :hints (("Goal" :in-theory (e/d* (pml4-table-base-addr
                                    pml4-table-entry-addr
                                    page-dir-ptr-table-entry-addr
                                    page-dir-ptr-table-base-addr
                                    page-directory-base-addr
                                    page-directory-entry-addr
                                    page-table-base-addr
                                    page-table-entry-addr
                                    page-table-entry-addr-found-p
                                    page-directory-entry-addr-found-p
                                    page-dir-ptr-table-entry-addr-found-p
                                    pml4-table-entry-addr-found-p
                                    ia32e-la-to-pa-page-table
                                    page-fault-exception)
                                   (canonical-address-p
                                    physical-address-p
                                    xlate-equiv-x86s-and-page-dir-ptr-table-base-addr-address
                                    xlate-equiv-x86s-and-page-dir-ptr-table-base-addr-error
                                    xlate-equiv-x86s-and-page-dir-ptr-table-entry-addr-address
                                    xlate-equiv-x86s-and-page-directory-base-addr-address
                                    xlate-equiv-x86s-and-page-directory-base-addr-error
                                    xlate-equiv-x86s-and-page-directory-entry-addr-address
                                    xlate-equiv-x86s-and-page-table-base-addr-address
                                    xlate-equiv-x86s-and-page-table-base-addr-error
                                    xlate-equiv-x86s-and-page-table-entry-addr-address)))))

(defthm rm-low-64-and-page-fault-exception
  (equal (rm-low-64 addr (mv-nth 2 (page-fault-exception lin-addr err-no x86)))
         (rm-low-64 addr x86))
  :hints (("Goal" :in-theory (e/d* (page-fault-exception
                                    rm-low-64)
                                   ()))))

(defthm rm-low-64-and-xw-fault
  (equal (rm-low-64 addr (xw :fault index val x86))
         (rm-low-64 addr x86))
  :hints (("Goal" :in-theory (e/d* (page-fault-exception
                                    rm-low-64
                                    rm-low-32)
                                   ()))))

(defthm pml4-table-base-addr-and-page-fault-exception
  (equal (pml4-table-base-addr (mv-nth 2 (page-fault-exception lin-addr err-no x86)))
         (pml4-table-base-addr x86))
  :hints (("Goal" :in-theory (e/d* (page-fault-exception
                                    pml4-table-base-addr)
                                   ()))))

(defthm pml4-table-base-addr-and-xw-not-ctr
  (implies (not (equal fld :ctr))
           (equal (pml4-table-base-addr (xw fld index val x86))
                  (pml4-table-base-addr x86)))
  :hints (("Goal" :in-theory (e/d* (pml4-table-base-addr)
                                   ()))))

(defthm page-dir-ptr-table-base-addr-and-page-fault-exception
  (equal (page-dir-ptr-table-base-addr addr (mv-nth 2 (page-fault-exception lin-addr err-no x86)))
         (page-dir-ptr-table-base-addr addr x86))
  :hints (("Goal" :in-theory (e/d* (page-dir-ptr-table-base-addr
                                    page-fault-exception)
                                   ()))))

(defthm page-dir-ptr-table-base-addr-and-xw-fault
  (implies (not (equal fld :ctr))
           (equal (page-dir-ptr-table-base-addr addr (xw :fault index val x86))
                  (page-dir-ptr-table-base-addr addr x86)))
  :hints (("Goal" :in-theory (e/d* (page-dir-ptr-table-base-addr)
                                   ()))))

(defthm page-directory-base-addr-and-page-fault-exception
  (equal (page-directory-base-addr addr (mv-nth 2 (page-fault-exception lin-addr err-no x86)))
         (page-directory-base-addr addr x86))
  :hints (("Goal" :in-theory (e/d* (page-fault-exception
                                    page-directory-base-addr
                                    page-dir-ptr-table-base-addr)
                                   ()))))

(defthm page-directory-base-addr-and-xw-fault
  (equal (page-directory-base-addr addr (xw :fault index val x86))
         (page-directory-base-addr addr x86))
  :hints (("Goal" :in-theory (e/d* (page-directory-base-addr
                                    page-dir-ptr-table-base-addr)
                                   ()))))

(defthm page-table-base-addr-and-page-fault-exception
  (equal (page-table-base-addr addr (mv-nth 2 (page-fault-exception lin-addr err-no x86)))
         (page-table-base-addr addr x86))
  :hints (("Goal" :in-theory (e/d* (page-fault-exception
                                    page-table-base-addr)
                                   ()))))

(i-am-here)

(skip-proofs
 (defthm page-table-entry-addr-found-p-after-wm-low-64
   (implies (and (page-table-entry-addr-found-p lin-addr-1 x86)
                 (page-table-entry-addr-found-p lin-addr-2 x86)
                 (mult-8-qword-paddr-list-listp (gather-all-paging-structure-qword-addresses x86))
                 (no-duplicates-list-p (gather-all-paging-structure-qword-addresses x86))
                 (equal page-table-entry-addr-2
                        (page-table-entry-addr lin-addr-2 (mv-nth 1 (page-table-base-addr lin-addr-2 x86))))
                 ;; (equal val (set-accessed-bit (rm-low-64 page-table-entry-addr-2 x86)))
                 (or (equal val (set-accessed-bit (rm-low-64 page-table-entry-addr-2 x86)))
                     (equal val (set-dirty-bit (rm-low-64 page-table-entry-addr-2 x86)))
                     (equal val (set-dirty-bit (set-accessed-bit (rm-low-64 page-table-entry-addr-2 x86)))))
                 )
            (page-table-entry-addr-found-p
             lin-addr-1
             (wm-low-64 page-table-entry-addr-2 val x86)))
   :hints (("Goal" :in-theory (e/d* ( ;; pml4-table-base-addr
                                     ;; pml4-table-entry-addr
                                     ;; page-dir-ptr-table-entry-addr
                                     ;; page-dir-ptr-table-base-addr
                                     ;; page-directory-base-addr
                                     ;; page-directory-entry-addr
                                     ;; page-table-base-addr
                                     ;; page-table-entry-addr
                                     page-table-entry-addr-found-p
                                     page-directory-entry-addr-found-p
                                     page-dir-ptr-table-entry-addr-found-p
                                     ;; pml4-table-entry-addr-found-p
                                     )
                                    (canonical-address-p
                                     physical-address-p
                                     xlate-equiv-x86s-and-page-dir-ptr-table-base-addr-address
                                     xlate-equiv-x86s-and-page-dir-ptr-table-base-addr-error
                                     xlate-equiv-x86s-and-page-dir-ptr-table-entry-addr-address
                                     xlate-equiv-x86s-and-page-directory-base-addr-address
                                     xlate-equiv-x86s-and-page-directory-base-addr-error
                                     xlate-equiv-x86s-and-page-directory-entry-addr-address
                                     xlate-equiv-x86s-and-page-table-base-addr-address
                                     xlate-equiv-x86s-and-page-table-base-addr-error
                                     xlate-equiv-x86s-and-page-table-entry-addr-address))))
   :otf-flg t))

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
                 (:instance page-table-entry-addr-found-p-and-x86p
                            (lin-addr lin-addr-2))
                 (:instance logand-loghead-and-page-table-base-addr
                            (lin-addr lin-addr-2)))
           :in-theory (e/d* (ia32e-la-to-pa-page-table)
                            (physical-address-p
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

(defmacro ia32e-la-to-pa-page-table-entry-components-equal-p-body
  (page-table-entry-1 page-table-entry-2)
  `(and (equal (ia32e-pte-4k-page-slice :pte-p   ,page-table-entry-1)
               (ia32e-pte-4k-page-slice :pte-p   ,page-table-entry-2))
        (equal (ia32e-pte-4k-page-slice :pte-r/w ,page-table-entry-1)
               (ia32e-pte-4k-page-slice :pte-r/w ,page-table-entry-2))
        (equal (ia32e-pte-4k-page-slice :pte-u/s ,page-table-entry-1)
               (ia32e-pte-4k-page-slice :pte-u/s ,page-table-entry-2))
        (equal (ia32e-pte-4k-page-slice :pte-xd  ,page-table-entry-1)
               (ia32e-pte-4k-page-slice :pte-xd  ,page-table-entry-2))
        ;; Reserved bits are zero.
        ;; (equal (loghead 11 (logtail 52 ,page-table-entry-2)) 0)
        (equal (loghead 11 (logtail 52 ,page-table-entry-1))
               (loghead 11 (logtail 52 ,page-table-entry-2)))))

(define ia32e-la-to-pa-page-table-entry-components-equal-p
  (page-table-entry-1 page-table-entry-2)
  :verify-guards nil
  :non-executable t
  (ia32e-la-to-pa-page-table-entry-components-equal-p-body page-table-entry-1 page-table-entry-2))

(defmacro ia32e-la-to-pa-page-table-entry-components-equal-p-macro (x y)
  `(ia32e-la-to-pa-page-table-entry-components-equal-p-body ,x ,y))

(defthm ia32e-la-to-pa-page-table-entry-components-equal-p-reflexive
  (ia32e-la-to-pa-page-table-entry-components-equal-p b b)
  :hints (("Goal" :in-theory (e/d
                              (ia32e-la-to-pa-page-table-entry-components-equal-p)
                              ()))))

(defthm ia32e-la-to-pa-page-table-entry-components-equal-p-accessed-bit-set
  (ia32e-la-to-pa-page-table-entry-components-equal-p
   b ;; (logior 32 (logand 18446744073709551583 b))
   (set-accessed-bit b))
  :hints (("Goal" :in-theory (e/d
                              (ia32e-la-to-pa-page-table-entry-components-equal-p
                               set-accessed-bit)
                              ()))))

(defthm ia32e-la-to-pa-page-table-entry-components-equal-p-dirty-bit-set
  (ia32e-la-to-pa-page-table-entry-components-equal-p
   b ;; (logior 64 (logand 18446744073709551551 b))
   (set-dirty-bit b))
  :hints (("Goal" :in-theory (e/d
                              (ia32e-la-to-pa-page-table-entry-components-equal-p
                               set-dirty-bit)
                              ()))))

(defthm ia32e-la-to-pa-page-table-entry-components-equal-p-accessed-and-dirty-bits-set
  (ia32e-la-to-pa-page-table-entry-components-equal-p
   b
   ;; (logior
   ;;  64
   ;;  (logand
   ;;   18446744073709551551
   ;;   (logior 32 (logand 18446744073709551583 b))))
   (set-dirty-bit (set-accessed-bit b)))
  :hints (("Goal" :in-theory (e/d
                              (ia32e-la-to-pa-page-table-entry-components-equal-p
                               set-dirty-bit
                               set-accessed-bit)
                              ()))))
;; ......................................................................
;; Rules about the three return values of ia32e-la-to-pa-page-table-entry:
;; ......................................................................

(defrule mv-nth-0-no-error-ia32e-la-to-pa-page-table
  (implies (ia32e-la-to-pa-page-table-entry-validp
            lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86)
           (equal (mv-nth
                   0
                   (ia32e-la-to-pa-page-table
                    lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86))
                  nil))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-table)
                  (not)))

(defrule mv-nth-0-no-error-ia32e-la-to-pa-page-table-with-disjoint-!memi
  (implies (and (ia32e-la-to-pa-page-table-entry-validp
                 lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86)
                (equal page-table-entry-addr
                       (page-table-entry-addr lin-addr page-table-base-addr))
                (disjoint-p (addr-range 1 addr)
                            (addr-range 8 page-table-entry-addr)))
           (equal (mv-nth
                   0
                   (ia32e-la-to-pa-page-table
                    lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl
                    (xw :mem addr val x86)))
                  nil))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-table)
                  (addr-range-1 not)))

(defrule mv-nth-0-no-error-ia32e-la-to-pa-page-table-with-disjoint-wm-low-64
  (implies (and (ia32e-la-to-pa-page-table-entry-validp
                 lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86)
                (equal page-table-entry-addr
                       (page-table-entry-addr lin-addr page-table-base-addr))
                (disjoint-p (addr-range 8 addr)
                            (addr-range 8 page-table-entry-addr))
                (integerp addr))
           (equal (mv-nth
                   0
                   (ia32e-la-to-pa-page-table
                    lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl
                    (wm-low-64 addr val x86)))
                  nil))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-table)
                  (not)))

(defrule mv-nth-1-no-error-ia32e-la-to-pa-page-table
  (implies (ia32e-la-to-pa-page-table-entry-validp
            lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86)
           (equal (mv-nth
                   1
                   (ia32e-la-to-pa-page-table
                    lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86))
                  ;; Physical address
                  (part-install
                   (part-select lin-addr :low 0 :high 11)
                   (ash (ia32e-pte-4K-page-slice
                         :pte-page
                         (rm-low-64 (page-table-entry-addr lin-addr page-table-base-addr)
                                    x86))
                        12)
                   :low 0 :high 11)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-table)
                  (not)))

(defruled mv-nth-1-no-error-ia32e-la-to-pa-page-table-different-components
  (implies (and (ia32e-la-to-pa-page-table-entry-validp
                 lin-addr page-table-base-addr u-s-acc-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
                (ia32e-la-to-pa-page-table-entry-validp
                 lin-addr page-table-base-addr u-s-acc-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))
           (equal (mv-nth
                   1
                   (ia32e-la-to-pa-page-table
                    lin-addr page-table-base-addr u-s-acc-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86))
                  (mv-nth
                   1
                   (ia32e-la-to-pa-page-table
                    lin-addr page-table-base-addr u-s-acc-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
  :do-not '(preprocess)
  :in-theory (e/d () (ia32e-la-to-pa-page-table-entry-validp not)))

(defrule mv-nth-1-no-error-ia32e-la-to-pa-page-table-with-disjoint-!memi
  (implies (and (ia32e-la-to-pa-page-table-entry-validp
                 lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86)
                (equal page-table-entry-addr
                       (page-table-entry-addr lin-addr page-table-base-addr))
                (disjoint-p (addr-range 1 addr)
                            (addr-range 8 page-table-entry-addr)))
           (equal (mv-nth
                   1
                   (ia32e-la-to-pa-page-table
                    lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl
                    (xw :mem addr val x86)))
                  (mv-nth
                   1
                   (ia32e-la-to-pa-page-table
                    lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl
                    x86))))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-table)
                  (addr-range-1 not)))

(defrule mv-nth-1-no-error-ia32e-la-to-pa-page-table-with-disjoint-wm-low-64
  (implies (and (ia32e-la-to-pa-page-table-entry-validp
                 lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86)
                (equal page-table-entry-addr
                       (page-table-entry-addr lin-addr page-table-base-addr))
                (disjoint-p (addr-range 8 addr)
                            (addr-range 8 page-table-entry-addr))
                (integerp addr))
           (equal (mv-nth
                   1
                   (ia32e-la-to-pa-page-table
                    lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl
                    (wm-low-64 addr val x86)))
                  (mv-nth
                   1
                   (ia32e-la-to-pa-page-table
                    lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl
                    x86))))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-table)
                  ()))

(defrule mv-nth-2-no-error-ia32e-la-to-pa-page-table
  (implies (and (ia32e-la-to-pa-page-table-entry-validp
                 lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86)

                (equal page-table-entry-addr
                       (page-table-entry-addr lin-addr page-table-base-addr))
                (equal page-table-entry (rm-low-64 page-table-entry-addr x86))

                (equal accessed (ia32e-page-tables-slice :a page-table-entry))
                (equal dirty (ia32e-page-tables-slice :d page-table-entry))

                (equal accessed-entry
                       (if (equal accessed 0)
                           (set-accessed-bit page-table-entry)
                         page-table-entry))
                (equal dirty-entry
                       (if (and (equal dirty 0)
                                (equal r-w-x :w))
                           (set-dirty-bit accessed-entry)
                         accessed-entry))
                (equal dirty-x86
                       (if (or (equal accessed 0)
                               (and (equal dirty 0)
                                    (equal r-w-x :w)))
                           (wm-low-64 page-table-entry-addr dirty-entry x86)
                         x86)))
           (equal (mv-nth
                   2
                   (ia32e-la-to-pa-page-table
                    lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86))
                  dirty-x86))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-table)
                  ()))

;; ......................................................................
;; Reading page-table-entry-addr again using rm-low-64:
;; ......................................................................

(defruled rm-low-64-and-page-table
  ;; Note that the conclusion of this theorem is very similar to
  ;; theorems about other page-table-entry accessor functions.  After all, all
  ;; paging data structures are modified in the same way.
  (implies (and (ia32e-la-to-pa-page-table-entry-validp
                 lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86)
                (equal page-table-entry-addr
                       (page-table-entry-addr lin-addr page-table-base-addr))
                (equal page-table-entry (rm-low-64 page-table-entry-addr x86))
                (physical-address-p page-table-base-addr)
                (canonical-address-p lin-addr)
                (equal (loghead 12 page-table-base-addr) 0)
                (x86p x86))
           (equal (rm-low-64 page-table-entry-addr
                             (mv-nth
                              2
                              (ia32e-la-to-pa-page-table
                               lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86)))
                  (cond
                   ( ;; Accessed and dirty bits are set.
                    (and (equal (ia32e-page-tables-slice :a page-table-entry) 1)
                         (equal (ia32e-page-tables-slice :d page-table-entry) 1))
                    (rm-low-64 page-table-entry-addr x86))

                   ( ;; Accessed bit is set and dirty bit is clear and
                    ;; memory write is being done.
                    (and (equal (ia32e-page-tables-slice :a page-table-entry) 1)
                         (equal (ia32e-page-tables-slice :d page-table-entry) 0)
                         (equal r-w-x :w))
                    (set-dirty-bit (rm-low-64 page-table-entry-addr x86)))

                   ( ;; Accessed bit is set and dirty bit is clear and
                    ;; memory write is not being done.
                    (and (equal (ia32e-page-tables-slice :a page-table-entry) 1)
                         (equal (ia32e-page-tables-slice :d page-table-entry) 0)
                         (not (equal r-w-x :w)))
                    (rm-low-64 page-table-entry-addr x86))

                   ( ;; Accessed and dirty bits are clear and memory
                    ;; write is being done.
                    (and (equal (ia32e-page-tables-slice :a page-table-entry) 0)
                         (equal (ia32e-page-tables-slice :d page-table-entry) 0)
                         (equal r-w-x :w))
                    (set-dirty-bit (set-accessed-bit (rm-low-64 page-table-entry-addr x86))))

                   ( ;; Accessed bit and dirty bits are clear and memory
                    ;; write is not being done.
                    (and (equal (ia32e-page-tables-slice :a page-table-entry) 0)
                         (equal (ia32e-page-tables-slice :d page-table-entry) 0)
                         (not (equal r-w-x :w)))
                    (set-accessed-bit (rm-low-64 page-table-entry-addr x86)))

                   (t
                    ;; This shouldn't be reached.
                    (rm-low-64 page-table-entry-addr
                               (mv-nth
                                2
                                (ia32e-la-to-pa-page-table
                                 lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86)))))))

  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-table)
                  (not
                   unsigned-byte-p
                   signed-byte-p)))

;; ......................................................................
;; !memi and state after data structure walk WoW theorem:
;; ......................................................................

(defrule disjoint-!memi-mv-nth-2-no-error-ia32e-la-to-pa-page-table
  (implies (and (ia32e-la-to-pa-page-table-entry-validp
                 lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86)
                (equal page-table-entry-addr
                       (page-table-entry-addr lin-addr page-table-base-addr))
                (disjoint-p (addr-range 1 addr)
                            (addr-range 8 page-table-entry-addr))
                (integerp addr))
           (equal
            (mv-nth 2 (ia32e-la-to-pa-page-table
                       lin-addr page-table-base-addr u-s-acc wp smep
                       nxe r-w-x cpl
                       (xw :mem addr val x86)))
            (xw :mem addr val
                (mv-nth 2 (ia32e-la-to-pa-page-table
                           lin-addr page-table-base-addr u-s-acc wp smep
                           nxe r-w-x cpl x86)))))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-table)
                  (not
                   addr-range-1)))

;; ......................................................................
;; Reading addresses disjoint from page-table-entry-addr after walking
;; the page table:
;; ......................................................................

(defrule disjoint-memi-mv-nth-2-no-error-ia32e-la-to-pa-page-table
  (implies (and (ia32e-la-to-pa-page-table-entry-validp
                 lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86)
                (equal page-table-entry-addr
                       (page-table-entry-addr lin-addr page-table-base-addr))
                (disjoint-p (addr-range 1 addr)
                            (addr-range 8 page-table-entry-addr)))
           (equal
            (xr :mem
                addr
                (mv-nth 2 (ia32e-la-to-pa-page-table
                           lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86)))
            (xr :mem addr x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-table)
                  (not
                   addr-range-1)))

(defrule disjoint-rm-low-64-mv-nth-2-no-error-ia32e-la-to-pa-page-table
  (implies (and (ia32e-la-to-pa-page-table-entry-validp
                 lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86)
                (equal page-table-entry-addr
                       (page-table-entry-addr lin-addr page-table-base-addr))
                (disjoint-p (addr-range 8 addr)
                            (addr-range 8 page-table-entry-addr))
                (integerp addr))
           (equal
            (rm-low-64
             addr
             (mv-nth 2 (ia32e-la-to-pa-page-table
                        lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86)))
            (rm-low-64 addr x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-table)
                  (not)))

(defrule disjoint-rm-low-32-mv-nth-2-no-error-ia32e-la-to-pa-page-table
  (implies (and (ia32e-la-to-pa-page-table-entry-validp
                 lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86)
                (equal page-table-entry-addr
                       (page-table-entry-addr lin-addr page-table-base-addr))
                (disjoint-p (addr-range 4 addr)
                            (addr-range 8 page-table-entry-addr))
                (integerp addr))
           (equal
            (rm-low-32
             addr
             (mv-nth 2 (ia32e-la-to-pa-page-table
                        lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86)))
            (rm-low-32 addr x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-table
                   wm-low-64)
                  (not)))

;; ......................................................................
;; Theorems that state that the validity of the page table entry is
;; preserved when writes are done to disjoint addresses or :a/:d are
;; set:
;; ......................................................................

(defrule page-table-entry-with-disjoint-!memi-still-valid-ia32e-la-to-pa-page-table
  (implies (and (ia32e-la-to-pa-page-table-entry-validp
                 lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86)
                (equal page-table-entry-addr
                       (page-table-entry-addr lin-addr page-table-base-addr))
                (disjoint-p
                 (addr-range 1 addr)
                 (addr-range 8 page-table-entry-addr)))
           (ia32e-la-to-pa-page-table-entry-validp
            lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl
            (xw :mem addr val x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-table)
                  (not addr-range-1
                       unsigned-byte-p
                       signed-byte-p)))

(defrule page-table-entry-with-disjoint-wm-low-64-still-valid-ia32e-la-to-pa-page-table
  (implies (and (ia32e-la-to-pa-page-table-entry-validp
                 lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86)
                (equal page-table-entry-addr
                       (page-table-entry-addr lin-addr page-table-base-addr))
                (disjoint-p
                 (addr-range 8 addr)
                 (addr-range 8 page-table-entry-addr))
                (integerp addr))
           (ia32e-la-to-pa-page-table-entry-validp
            lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl
            (wm-low-64 addr val x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-table)
                  (not
                   unsigned-byte-p
                   signed-byte-p)))

(defrule page-table-entry-with-accessed-bit-set-still-valid-ia32e-la-to-pa-page-table
  (implies (and (ia32e-la-to-pa-page-table-entry-validp
                 lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86)
                (equal page-table-entry-addr
                       (page-table-entry-addr lin-addr page-table-base-addr))
                (equal page-table-entry (rm-low-64 page-table-entry-addr x86))

                (physical-address-p page-table-base-addr)
                (canonical-address-p lin-addr)
                (x86p x86))

           (ia32e-la-to-pa-page-table-entry-validp
            lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl
            (wm-low-64
             page-table-entry-addr
             ;; (!ia32e-page-tables-slice :a 1 page-table-entry)
             ;; (logior 32 (logand 18446744073709551583 page-table-entry))
             (set-accessed-bit page-table-entry)
             x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-table
                   set-accessed-bit)
                  (not
                   unsigned-byte-p
                   signed-byte-p)))

(defrule page-table-entry-with-dirty-bit-set-still-valid-ia32e-la-to-pa-page-table
  (implies (and (ia32e-la-to-pa-page-table-entry-validp
                 lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86)
                (equal page-table-entry-addr
                       (page-table-entry-addr lin-addr page-table-base-addr))
                (equal page-table-entry (rm-low-64 page-table-entry-addr x86))

                (physical-address-p page-table-base-addr)
                (canonical-address-p lin-addr)
                (x86p x86))

           (ia32e-la-to-pa-page-table-entry-validp
            lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl
            (wm-low-64
             page-table-entry-addr
             ;; (!ia32e-page-tables-slice :d 1 page-table-entry)
             ;; (logior 64 (logand 18446744073709551551 page-table-entry))
             (set-dirty-bit page-table-entry)
             x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-table
                   set-dirty-bit)
                  (not
                   unsigned-byte-p
                   signed-byte-p)))

(defrule page-table-entry-with-accessed-and-dirty-bits-set-still-valid-ia32e-la-to-pa-page-table
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-table-entry-validp
                 lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86)
                (equal page-table-entry-addr
                       (page-table-entry-addr lin-addr page-table-base-addr))
                (equal page-table-entry (rm-low-64 page-table-entry-addr x86))

                (physical-address-p page-table-base-addr)
                (canonical-address-p lin-addr)
                (x86p x86))

           (ia32e-la-to-pa-page-table-entry-validp
            lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl
            (wm-low-64
             page-table-entry-addr
             ;; (!ia32e-page-tables-slice :d 1 (!ia32e-page-tables-slice :a 1 page-table-entry))
             ;; (logior
             ;;  64
             ;;  (logand
             ;;   18446744073709551551
             ;;   (logior 32 (logand 18446744073709551583 page-table-entry))))
             (set-dirty-bit (set-accessed-bit page-table-entry))
             x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-table
                   set-accessed-bit
                   set-dirty-bit)
                  (not
                   unsigned-byte-p
                   signed-byte-p)))

;; ......................................................................
;; Reading page table entry from x86 states where :a/:d are set:
;; ......................................................................

(defrule reading-entry-with-accessed-bit-set-ia32e-la-to-pa-page-table
  (implies
   (and (ia32e-la-to-pa-page-table-entry-validp
         lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86)
        (equal page-table-entry-addr
               (page-table-entry-addr lin-addr page-table-base-addr))
        (equal page-table-entry
               (rm-low-64 page-table-entry-addr x86))
        (physical-address-p page-table-base-addr)
        (canonical-address-p lin-addr)
        (x86p x86))
   (equal
    (mv-nth
     1
     (ia32e-la-to-pa-page-table
      lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl
      (wm-low-64
       page-table-entry-addr
       ;; (!ia32e-page-tables-slice :a 1 page-table-entry)
       ;; (logior 32 (logand 18446744073709551583 page-table-entry))
       (set-accessed-bit page-table-entry)
       x86)))
    (mv-nth
     1
     (ia32e-la-to-pa-page-table
      lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86))))
  :do-not '(preprocess)
  :in-theory (e/d (set-accessed-bit)
                  (not
                   mv-nth-2-no-error-ia32e-la-to-pa-page-table
                   unsigned-byte-p
                   signed-byte-p)))

(defrule reading-entry-with-dirty-bit-set-ia32e-la-to-pa-page-table
  (implies (and (ia32e-la-to-pa-page-table-entry-validp
                 lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86)
                (equal page-table-entry-addr
                       (page-table-entry-addr lin-addr page-table-base-addr))
                (equal page-table-entry (rm-low-64 page-table-entry-addr x86))
                (physical-address-p page-table-base-addr)
                (canonical-address-p lin-addr)
                (x86p x86))

           (equal
            (mv-nth
             1
             (ia32e-la-to-pa-page-table
              lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl
              (wm-low-64
               page-table-entry-addr
               ;; (!ia32e-page-tables-slice :d 1 page-table-entry)
               ;; (logior 64 (logand 18446744073709551551 page-table-entry))
               (set-dirty-bit page-table-entry)
               x86)))
            (mv-nth
             1
             (ia32e-la-to-pa-page-table
              lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86))))
  :do-not '(preprocess)
  :in-theory (e/d (set-dirty-bit)
                  (not
                   mv-nth-2-no-error-ia32e-la-to-pa-page-table
                   unsigned-byte-p
                   signed-byte-p)))

(defrule reading-entry-with-accessed-and-dirty-bits-set-ia32e-la-to-pa-page-table
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-table-entry-validp
                 lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86)
                (equal page-table-entry-addr
                       (page-table-entry-addr lin-addr page-table-base-addr))
                (equal page-table-entry (rm-low-64 page-table-entry-addr x86))
                (physical-address-p page-table-base-addr)
                (canonical-address-p lin-addr)
                (x86p x86))

           (equal
            (mv-nth
             1
             (ia32e-la-to-pa-page-table
              lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl
              (wm-low-64
               page-table-entry-addr
               ;; (!ia32e-page-tables-slice :d 1 (!ia32e-page-tables-slice :a 1 page-table-entry))
               ;; (logior
               ;;  64
               ;;  (logand
               ;;   18446744073709551551
               ;;   (logior 32 (logand 18446744073709551583 page-table-entry))))
               (set-dirty-bit (set-accessed-bit page-table-entry))
               x86)))
            (mv-nth
             1
             (ia32e-la-to-pa-page-table
              lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86))))
  :do-not '(preprocess)
  :in-theory (e/d (set-accessed-bit
                   set-dirty-bit)
                  (not
                   mv-nth-2-no-error-ia32e-la-to-pa-page-table
                   unsigned-byte-p
                   signed-byte-p)))

;; ......................................................................
;; More theorems about preservation of validity of page table entries:
;; ......................................................................

(defrule relating-validity-of-two-entries-in-two-x86-states-wrt-page-table-4K-pages
  (implies (and (ia32e-la-to-pa-page-table-entry-validp
                 lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86)
                (equal page-table-entry-addr
                       (page-table-entry-addr lin-addr page-table-base-addr))
                (equal page-table-entry-1 (rm-low-64 page-table-entry-addr x86))
                (equal page-table-entry-2 (rm-low-64 page-table-entry-addr x86-another))
                (ia32e-la-to-pa-page-table-entry-components-equal-p
                 page-table-entry-1 page-table-entry-2))

           (ia32e-la-to-pa-page-table-entry-validp
            lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl
            x86-another))
  :in-theory (e/d (ia32e-la-to-pa-page-table-entry-components-equal-p)
                  ()))

(defruled page-table-components-equal-rm-low-64-of-table-page-table-entry-addr-via-page-table-4K-pages
  (implies (and (ia32e-la-to-pa-page-table-entry-validp
                 lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86)
                (equal page-table-entry-addr
                       (page-table-entry-addr lin-addr page-table-base-addr))
                (equal page-table-entry (rm-low-64 page-table-entry-addr x86))
                (physical-address-p page-table-base-addr)
                (canonical-address-p lin-addr)
                (x86p x86))

           (ia32e-la-to-pa-page-table-entry-components-equal-p
            (rm-low-64 page-table-entry-addr x86)
            (rm-low-64
             page-table-entry-addr
             (mv-nth
              2
              (ia32e-la-to-pa-page-table
               lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86)))))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (e/d (rm-low-64-and-page-table
                            ia32e-la-to-pa-page-table-entry-components-equal-p)
                           (not
                            member-p-cons
                            disjoint-p-cons
                            ia32e-la-to-pa-page-table-entry-validp
                            unsigned-byte-p
                            signed-byte-p)))))

(defrule re-read-entry-still-valid-ia32e-la-to-pa-page-table
  (implies (and (ia32e-la-to-pa-page-table-entry-validp
                 lin-addr page-table-base-addr u-s-acc-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
                (ia32e-la-to-pa-page-table-entry-validp
                 lin-addr page-table-base-addr u-s-acc-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)
                (physical-address-p page-table-base-addr)
                (canonical-address-p lin-addr)
                (x86p x86))
           (ia32e-la-to-pa-page-table-entry-validp
            lin-addr page-table-base-addr u-s-acc-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
            (mv-nth
             2
             (ia32e-la-to-pa-page-table
              lin-addr page-table-base-addr u-s-acc-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
  :do-not '(preprocess)
  :in-theory (e/d (page-table-components-equal-rm-low-64-of-table-page-table-entry-addr-via-page-table-4K-pages)
                  (ia32e-la-to-pa-page-table-entry-validp
                   mv-nth-2-no-error-ia32e-la-to-pa-page-table
                   not
                   unsigned-byte-p
                   signed-byte-p)))

;; ......................................................................
;; Two page table walks
;; ......................................................................

(encapsulate
 ()

 (local
  (defthm open-addr-range
    (implies (natp x)
             (equal (addr-range 8 x)
                    (list x (+ 1 x) (+ 2 x) (+ 3 x)
                          (+ 4 x) (+ 5 x) (+ 6 x) (+ 7 x))))))

 (local
  (encapsulate
   ()

   (local (include-book "arithmetic-5/top" :dir :system))

   (defthm multiples-of-8-and-disjointness-of-physical-addresses-helper-1
     (implies (and (equal (loghead 3 x) 0)
                   (equal (loghead 3 y) 0)
                   (posp n)
                   (<= n 7)
                   (natp x)
                   (natp y))
              (not (equal (+ n x) y)))
     :hints (("Goal" :in-theory (e/d* (loghead)
                                      ()))))

   (defthm multiples-of-8-and-disjointness-of-physical-addresses-helper-2
     (implies (and (equal (loghead 3 x) 0)
                   (equal (loghead 3 y) 0)
                   (not (equal x y))
                   (posp n)
                   (<= n 7)
                   (posp m)
                   (<= m 7)
                   (natp x)
                   (natp y))
              (not (equal (+ n x) (+ m y))))
     :hints (("Goal" :in-theory (e/d* (loghead)
                                      ()))))))

 (defthm multiples-of-8-and-disjointness-of-physical-addresses
   (implies (and (equal (loghead 3 addr-1) 0)
                 (equal (loghead 3 addr-2) 0)
                 (not (equal addr-2 addr-1))
                 (natp addr-1)
                 (natp addr-2))
            (disjoint-p (addr-range 8 addr-2)
                        (addr-range 8 addr-1)))))

(defrule two-page-table-walks-ia32e-la-to-pa-page-table
  (implies (and (ia32e-la-to-pa-page-table-entry-validp
                 lin-addr-1 page-table-base-addr-1 u-s-acc-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
                (ia32e-la-to-pa-page-table-entry-validp
                 lin-addr-2 page-table-base-addr-2 u-s-acc-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)

                (equal page-table-entry-addr-1
                       (page-table-entry-addr lin-addr-1 page-table-base-addr-1))
                (equal page-table-entry-addr-2
                       (page-table-entry-addr lin-addr-2 page-table-base-addr-2))

                ;; Both page-table-entry-addr are multiples of 8. (see
                ;; PAGE-TABLE-ENTRY-ADDR-IS-A-MULTIPLE-OF-8) So, one
                ;; of the following can be true:
                ;; 1. (equal (addr-range 8 page-table-entry-addr-1)
                ;;           (addr-range 8 page-table-entry-addr-2))
                ;; 2. (disjoint-p (addr-range 8 page-table-entry-addr-1)
                ;;                (addr-range 8 page-table-entry-addr-2))
                (equal (loghead 12 page-table-base-addr-1) 0)
                (equal (loghead 12 page-table-base-addr-2) 0)

                (canonical-address-p lin-addr-1)
                (canonical-address-p lin-addr-2)
                (physical-address-p page-table-base-addr-1)
                (physical-address-p page-table-base-addr-2)
                (x86p x86))
           (equal
            (mv-nth
             1
             (ia32e-la-to-pa-page-table
              lin-addr-1 page-table-base-addr-1 u-s-acc-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
              (mv-nth
               2
               (ia32e-la-to-pa-page-table
                lin-addr-2 page-table-base-addr-2 u-s-acc-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
            (mv-nth
             1
             (ia32e-la-to-pa-page-table
              lin-addr-1 page-table-base-addr-1 u-s-acc-1 wp-1 smep-1 nxe-1 r-w-x-1
              cpl-1 x86))))
  :cases ((equal (page-table-entry-addr lin-addr-1 page-table-base-addr-1)
                 (page-table-entry-addr lin-addr-2 page-table-base-addr-2)))
  :in-theory (e/d ()
                  (ia32e-la-to-pa-page-table-entry-validp
                   mv-nth-1-no-error-ia32e-la-to-pa-page-table
                   unsigned-byte-p
                   signed-byte-p
                   member-p-cons
                   disjoint-p-cons))
  :do-not '(preprocess))

;; ......................................................................
;; Validity of a page table entry is preserved after a walk
;; ......................................................................

(defrule validity-preserved-same-x86-state-wrt-page-table
  (implies (and (ia32e-la-to-pa-page-table-entry-validp
                 lin-addr-1 page-table-base-addr-1 u-s-acc-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
                (ia32e-la-to-pa-page-table-entry-validp
                 lin-addr-2 page-table-base-addr-2 u-s-acc-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)

                (equal page-table-entry-addr-1
                       (page-table-entry-addr lin-addr-1 page-table-base-addr-1))
                (equal page-table-entry-addr-2
                       (page-table-entry-addr lin-addr-2 page-table-base-addr-2))

                ;; Both page-table-entry-addr are multiples of 8 (the
                ;; function page-table-entry-addr always returns
                ;; addresses that are a multiple of 8 if the base-addr
                ;; is 4K-aligned --- I could have the 4K-aligned
                ;; nature of page-table-base-addr in the hyps as an
                ;; alternative to the following two hyps.)

                ;; So, one of the following can be true:
                ;; 1. (equal (addr-range 8 page-table-entry-addr-1)
                ;;           (addr-range 8 page-table-entry-addr-2))
                ;; 2. (disjoint-p (addr-range 8 page-table-entry-addr-1)
                ;;                (addr-range 8 page-table-entry-addr-2))
                (equal (loghead 12 page-table-base-addr-1) 0)
                (equal (loghead 12 page-table-base-addr-2) 0)

                (canonical-address-p lin-addr-1)
                (canonical-address-p lin-addr-2)
                (physical-address-p page-table-base-addr-1)
                (physical-address-p page-table-base-addr-2)
                (x86p x86))
           (ia32e-la-to-pa-page-table-entry-validp
            lin-addr-1 page-table-base-addr-1 u-s-acc-1 wp-1 smep-1
            nxe-1 r-w-x-1 cpl-1
            (mv-nth 2
                    (ia32e-la-to-pa-page-table
                     lin-addr-2 page-table-base-addr-2 u-s-acc-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
  :cases ((equal (page-table-entry-addr lin-addr-1 page-table-base-addr-1)
                 (page-table-entry-addr lin-addr-2 page-table-base-addr-2)))
  :in-theory (e/d (mv-nth-2-no-error-ia32e-la-to-pa-page-table)
                  (addr-range-1
                   ia32e-la-to-pa-page-table-entry-validp
                   member-p-cons
                   disjoint-p-cons
                   not
                   unsigned-byte-p
                   signed-byte-p)))

;; ......................................................................
;; Translation-Governing-Addresses-For-Page-Table and
;; ia32e-la-to-pa-page-table-entry:
;; ......................................................................

(defrule translation-governing-addresses-for-page-table-and-ia32e-la-to-pa-page-table
  (equal
   (translation-governing-addresses-for-page-table
    lin-addr-1 page-table-base-addr-1
    (mv-nth 2
            (ia32e-la-to-pa-page-table
             lin-addr-2 page-table-base-addr-2 u-s-acc-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)))
   (translation-governing-addresses-for-page-table
    lin-addr-1 page-table-base-addr-1 x86))
  :in-theory (e/d ()
                  (ia32e-la-to-pa-page-table-entry-validp
                   addr-range-1
                   mv-nth-2-no-error-ia32e-la-to-pa-page-table
                   member-p-cons
                   disjoint-p-cons
                   not
                   unsigned-byte-p
                   signed-byte-p)))

(in-theory (e/d () (ia32e-la-to-pa-page-table-entry-validp)))

;; ======================================================================
