;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")

(include-book "x86-ia32e-paging" :dir :machine :ttags :all)

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))

(local (in-theory (e/d* () (signed-byte-p unsigned-byte-p))))

;; ======================================================================

;; In this book, we provide another interface to the paging
;; specification functions (in machine/x86-ia32e-paging.lisp). Unlike
;; the old specification functions, these functions do not take the
;; base-addr as input --- base-addr is computed from lin-addr and x86
;; state for every paging structure traversal function. We intend to
;; use these functions only for reasoning.

;; ======================================================================

;; Base addresses of paging structures:

(define pml4-table-base-addr (x86)

  (b* ((cr3 (ctri *cr3* x86))
       ;; PML4 Table:
       (pml4-base-addr (ash (cr3-slice :cr3-pdb cr3) 12)))
      (mv nil pml4-base-addr))

  ///

  (defthm-usb n52p-mv-nth-1-pml4-table-base-addr
    :hyp (x86p x86)
    :bound 52
    :concl (mv-nth 1 (pml4-table-base-addr x86))
    :gen-linear t
    :hints-l (("Goal" :in-theory (e/d* () (acl2::unsigned-byte-p-of-ash))))
    :hyp-t t
    :gen-type t)

  (defthm loghead-12-of-mv-nth-1-pml4-table-base-addr=0
    (implies (x86p x86)
             (equal (loghead 12 (mv-nth 1 (pml4-table-base-addr x86)))
                    0))))

(define page-dir-ptr-table-base-addr
  ((lin-addr :type (signed-byte #.*max-linear-address-size*))
   (x86))

  (b* ( ;; PML4 Table:
       ((mv & pml4-base-addr)
        (pml4-table-base-addr x86))
       (pml4-entry-addr
        (pml4-table-entry-addr lin-addr pml4-base-addr))
       (pml4-entry (rm-low-64 pml4-entry-addr x86))

       ;; Page-Dir-Ptr Directory Pointer Table:
       (ptr-table-base-addr
        (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12)))
      (mv nil ptr-table-base-addr))

  ///

  (defthm-usb n52p-mv-nth-1-page-dir-ptr-table-base-addr
    :hyp (and (canonical-address-p lin-addr)
              (x86p x86))
    :bound 52
    :concl (mv-nth 1 (page-dir-ptr-table-base-addr lin-addr x86))
    :gen-linear t
    :hints-l (("Goal" :in-theory (e/d* () (acl2::unsigned-byte-p-of-ash))))
    :hyp-t t
    :gen-type t)

  (defthm loghead-12-of-mv-nth-1-page-dir-ptr-table-base-addr=0
    (implies (and (canonical-address-p lin-addr)
                  (x86p x86))
             (equal (loghead 12 (mv-nth 1 (page-dir-ptr-table-base-addr lin-addr x86)))
                    0))))

(define page-directory-base-addr
  ((lin-addr :type (signed-byte #.*max-linear-address-size*))
   (x86))

  (b* ( ;; Page-Directory Directory Pointer Table:
       ((mv & ptr-table-base-addr)
        (page-dir-ptr-table-base-addr lin-addr x86))
       (ptr-table-entry-addr
        (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
       (ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))

       (pdpte-ps? (equal (ia32e-page-tables-slice :ps ptr-table-entry) 1))

       ;; 1G pages:
       ((when pdpte-ps?)
        (mv t 0))

       ;; Page Directory:
       (page-directory-base-addr
        (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12)))

      (mv nil page-directory-base-addr))

  ///

  (defthm-usb n52p-mv-nth-1-page-directory-base-addr
    :hyp (and (canonical-address-p lin-addr)
              (x86p x86))
    :bound 52
    :concl (mv-nth 1 (page-directory-base-addr lin-addr x86))
    :gen-linear t
    :hints-l (("Goal" :in-theory (e/d* () (acl2::unsigned-byte-p-of-ash))))
    :hyp-t t
    :gen-type t)

  (defthm loghead-12-of-mv-nth-1-page-directory-base-addr=0
    (implies (and (canonical-address-p lin-addr)
                  (x86p x86))
             (equal (loghead 12 (mv-nth 1 (page-directory-base-addr lin-addr x86)))
                    0))))

(define page-table-base-addr
  ((lin-addr :type (signed-byte #.*max-linear-address-size*))
   (x86))

  (b* ( ;; Page Directory:
       ((mv flg page-directory-base-addr)
        (page-directory-base-addr lin-addr x86))
       ((when flg)
        (mv flg 0))
       ;; 2M pages:
       (page-directory-entry-addr
        (page-directory-entry-addr lin-addr page-directory-base-addr))
       (page-directory-entry (rm-low-64 page-directory-entry-addr x86))

       (pde-ps? (equal (ia32e-page-tables-slice :ps page-directory-entry) 1))
       ((when pde-ps?)
        (mv t 0))

       ;; Page Table
       ;; 4K pages
       (page-table-base-addr
        (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12)))
      (mv nil page-table-base-addr))

  ///

  (defthm-usb n52p-mv-nth-1-page-table-base-addr
    :hyp (and (canonical-address-p lin-addr)
              (x86p x86))
    :bound 52
    :concl (mv-nth 1 (page-table-base-addr lin-addr x86))
    :gen-linear t
    :hints-l (("Goal" :in-theory (e/d* () (acl2::unsigned-byte-p-of-ash))))
    :hyp-t t
    :gen-type t)

  (defthm loghead-12-of-mv-nth-1-page-table-base-addr=0
    (implies (and (canonical-address-p lin-addr)
                  (x86p x86))
             (equal (loghead 12 (mv-nth 1 (page-table-base-addr lin-addr x86)))
                    0))))

;; ======================================================================

;; Alternate interfaces to paging structure traversal functions:

(define ia32e-la-to-pa-PT
  ((lin-addr  :type (signed-byte   #.*max-linear-address-size*))
   (u-s-acc   :type (unsigned-byte  1))
   (wp        :type (unsigned-byte  1))
   (smep      :type (unsigned-byte  1))
   (nxe       :type (unsigned-byte  1))
   (r-w-x     :type (member  :r :w :x))
   (cpl       :type (unsigned-byte  2))
   (x86))
  :enabled t
  (b* (((mv flg base-addr)
        (page-table-base-addr lin-addr x86))
       ((when flg)
        (mv flg 0 x86)))
      (ia32e-la-to-pa-page-table
       lin-addr base-addr u-s-acc wp smep nxe r-w-x cpl x86)))

(define ia32e-la-to-pa-PD
  ((lin-addr  :type (signed-byte   #.*max-linear-address-size*))
   (wp        :type (unsigned-byte  1))
   (smep      :type (unsigned-byte  1))
   (nxe       :type (unsigned-byte  1))
   (r-w-x     :type (member  :r :w :x))
   (cpl       :type (unsigned-byte  2))
   (x86))
  :enabled t
  (b* (((mv flg base-addr)
        (page-directory-base-addr lin-addr x86))
       ((when flg)
        (mv flg 0 x86)))
      (ia32e-la-to-pa-page-directory
       lin-addr base-addr wp smep nxe r-w-x cpl x86)))

(define ia32e-la-to-pa-PDPT
  ((lin-addr  :type (signed-byte   #.*max-linear-address-size*))
   (wp        :type (unsigned-byte  1))
   (smep      :type (unsigned-byte  1))
   (nxe       :type (unsigned-byte  1))
   (r-w-x     :type (member  :r :w :x))
   (cpl       :type (unsigned-byte  2))
   (x86))
  :enabled t
  (b* (((mv flg base-addr)
        (page-dir-ptr-table-base-addr lin-addr x86))
       ((when flg)
        (mv flg 0 x86)))
      (ia32e-la-to-pa-page-dir-ptr-table
       lin-addr base-addr wp smep nxe r-w-x cpl x86)))

(define ia32e-la-to-pa-PML4T
  ((lin-addr  :type (signed-byte   #.*max-linear-address-size*))
   (wp        :type (unsigned-byte  1))
   (smep      :type (unsigned-byte  1))
   (nxe       :type (unsigned-byte  1))
   (r-w-x     :type (member  :r :w :x))
   (cpl       :type (unsigned-byte  2))
   (x86))
  :enabled t
  (b* (((mv flg base-addr)
        (pml4-table-base-addr x86))
       ((when flg)
        (mv flg 0 x86)))
      (ia32e-la-to-pa-pml4-table
       lin-addr base-addr wp smep nxe r-w-x cpl x86)))

;; ======================================================================
