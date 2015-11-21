;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")

(include-book "gather-paging-structures" :ttags :all)

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))
(local (include-book "centaur/gl/gl" :dir :system))

;; ======================================================================

(local
 (def-gl-thm 4K-aligned-physical-address-helper
   :hyp (and (unsigned-byte-p 52 x)
             (equal (loghead 12 x) 0))
   :concl (equal (logand 18446744073709547520 x)
                 x)
   :g-bindings `((x (:g-number ,(gl-int 0 1 53))))))

(local (in-theory (e/d* () (signed-byte-p unsigned-byte-p))))

;; ======================================================================

;; In this book, we provide another interface to the paging
;; specification functions (in machine/x86-ia32e-paging.lisp). Unlike
;; the old specification functions, these functions do not take the
;; base-addr as input --- base-addr is computed from lin-addr and x86
;; state for every paging structure traversal function. We intend to
;; use these functions only for reasoning.

;; ======================================================================

;; Base address and conditions for finding an entry of a paging data
;; structure:

(define superior-entry-points-to-an-inferior-one-p
  ((superior-entry-addr :type (unsigned-byte #.*physical-address-size*))
   (x86))
  :guard (physical-address-p (+ 7 superior-entry-addr))
  :enabled t
  (let* ((superior-entry (rm-low-64 superior-entry-addr x86)))
    (and
     ;; Superior entry present.
     (equal (ia32e-page-tables-slice :p  superior-entry) 1)
     ;; Page Size = 0, i.e., next level of paging structure is required.
     (equal (ia32e-page-tables-slice :ps superior-entry) 0)
     ;; Next level of paging structure fits in the physical memory.
     (physical-address-p
      (+
       (ash 512 3)
       (ash (ia32e-page-tables-slice :reference-addr superior-entry)
            12))))))

(define pml4-table-base-addr (x86)
  (if (good-paging-structures-x86p x86)
      (b* ((cr3 (ctri *cr3* x86))
           ;; PML4 Table:
           (pml4-base-addr (ash (cr3-slice :cr3-pdb cr3) 12)))
          (mv nil pml4-base-addr))
    (mv t 0))

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
                    0)))

  (defthm pml4-table-base-addr-no-error
    (implies (good-paging-structures-x86p x86)
             (equal (mv-nth 0 (pml4-table-base-addr x86)) nil)))

  (defthm logand--4096-of-pml4-table-base-addr
    (equal (logand -4096 (mv-nth 1 (pml4-table-base-addr x86)))
           (mv-nth 1 (pml4-table-base-addr x86)))))

(define pml4-table-entry-addr-found-p (lin-addr x86)
  :non-executable t
  :enabled t
  (and (canonical-address-p lin-addr)
       (physical-address-p (+ (ash 512 3) (mv-nth 1 (pml4-table-base-addr x86))))
       (good-paging-structures-x86p x86)))

(define page-dir-ptr-table-base-addr
  ((lin-addr :type (signed-byte #.*max-linear-address-size*))
   (x86))

  (if (good-paging-structures-x86p x86)
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
    (mv t 0))

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
                    0)))

  (defthm logand--4096-of-page-dir-ptr-table-base-addr
    (equal (logand -4096 (mv-nth 1 (page-dir-ptr-table-base-addr lin-addr x86)))
           (mv-nth 1 (page-dir-ptr-table-base-addr lin-addr x86)))))

(define page-dir-ptr-table-entry-addr-found-p
  ((lin-addr :type (signed-byte #.*max-linear-address-size*))
   x86)
  :non-executable t
  :enabled t
  (and (pml4-table-entry-addr-found-p lin-addr x86)
       (superior-entry-points-to-an-inferior-one-p
        (pml4-table-entry-addr lin-addr (mv-nth 1 (pml4-table-base-addr x86)))
        x86)
       (x86p x86))
  ///
  (defthm page-dir-ptr-table-entry-addr-found-p-implies-pml4-table-entry-addr-found-p
    (implies (page-dir-ptr-table-entry-addr-found-p lin-addr x86)
             (pml4-table-entry-addr-found-p lin-addr x86)))

  (defthm page-dir-ptr-table-entry-addr-found-p-and-page-dir-ptr-table-base-addr-no-error
    (implies (page-dir-ptr-table-entry-addr-found-p lin-addr x86)
             (not (mv-nth 0 (page-dir-ptr-table-base-addr lin-addr x86))))
    :hints (("Goal" :in-theory (e/d* (page-dir-ptr-table-base-addr) ())))))

(define page-directory-base-addr
  ((lin-addr :type (signed-byte #.*max-linear-address-size*))
   (x86))

  (if (good-paging-structures-x86p x86)
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

    (mv t 0))

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
                    0)))

  (defthm logand--4096-of-page-directory-base-addr
    (equal (logand -4096 (mv-nth 1 (page-directory-base-addr lin-addr x86)))
           (mv-nth 1 (page-directory-base-addr lin-addr x86)))))

(define page-directory-entry-addr-found-p
  ((lin-addr :type (signed-byte #.*max-linear-address-size*))
   x86)
  :non-executable t
  :enabled t
  (and (page-dir-ptr-table-entry-addr-found-p lin-addr x86)
       (superior-entry-points-to-an-inferior-one-p
        (page-dir-ptr-table-entry-addr lin-addr (mv-nth 1 (page-dir-ptr-table-base-addr lin-addr x86)))
        x86))
  ///
  (defthm page-directory-entry-addr-found-p-implies-page-dir-ptr-table-entry-addr-found-p
    (implies (page-directory-entry-addr-found-p lin-addr x86)
             (page-dir-ptr-table-entry-addr-found-p lin-addr x86)))

  (defthm page-directory-entry-addr-found-p-and-page-directory-base-addr-no-error
    (implies (page-directory-entry-addr-found-p lin-addr x86)
             (not (mv-nth 0 (page-directory-base-addr lin-addr x86))))
    :hints (("Goal" :in-theory (e/d* (page-directory-base-addr) ())))))

(define page-table-base-addr
  ((lin-addr :type (signed-byte #.*max-linear-address-size*))
   (x86))

  (if (good-paging-structures-x86p x86)
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
    (mv t 0))

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
                    0)))

  (defthm logand--4096-of-page-table-base-addr
    (equal (logand -4096 (mv-nth 1 (page-table-base-addr lin-addr x86)))
           (mv-nth 1 (page-table-base-addr lin-addr x86)))))

(define page-table-entry-addr-found-p
  ((lin-addr :type (signed-byte #.*max-linear-address-size*))
   x86)
  :non-executable t
  :enabled t
  (and (page-directory-entry-addr-found-p lin-addr x86)
       (superior-entry-points-to-an-inferior-one-p
        (page-directory-entry-addr lin-addr (mv-nth 1 (page-directory-base-addr lin-addr x86)))
        x86))
  ///
  (defthm page-table-entry-addr-found-p-implies-page-directory-entry-addr-found-p
    (implies (page-table-entry-addr-found-p lin-addr x86)
             (page-directory-entry-addr-found-p lin-addr x86)))

  (defthm page-table-entry-addr-found-p-and-page-table-base-addr-no-error
    (implies (page-table-entry-addr-found-p lin-addr x86)
             (not (mv-nth 0 (page-table-base-addr lin-addr x86))))
    :hints (("Goal" :in-theory (e/d* (page-table-base-addr)
                                     ())))))

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
  :non-executable t
  :enabled t

  (if (page-table-entry-addr-found-p lin-addr x86)
      (b* (((mv & base-addr)
            (page-table-base-addr lin-addr x86)))
          (ia32e-la-to-pa-page-table
           lin-addr base-addr u-s-acc wp smep nxe r-w-x cpl x86))
    (mv t 0 x86)))

(defrule mv-nth-0-no-error-ia32e-la-to-pa-page-table
  (implies (ia32e-la-to-pa-page-table-entry-validp
            lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86)
           (equal (mv-nth
                   0
                   (ia32e-la-to-pa-page-table
                    lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86))
                  nil))
  :in-theory (e/d (ia32e-la-to-pa-page-table)
                  (bitops::logand-with-negated-bitmask)))

(define ia32e-la-to-pa-PD
  ((lin-addr  :type (signed-byte   #.*max-linear-address-size*))
   (wp        :type (unsigned-byte  1))
   (smep      :type (unsigned-byte  1))
   (nxe       :type (unsigned-byte  1))
   (r-w-x     :type (member  :r :w :x))
   (cpl       :type (unsigned-byte  2))
   (x86))
  :non-executable t
  :enabled t
  (if (page-directory-entry-addr-found-p lin-addr x86)
      (b* (((mv & base-addr)
            (page-directory-base-addr lin-addr x86)))
          (ia32e-la-to-pa-page-directory
           lin-addr base-addr wp smep nxe r-w-x cpl x86))
    (mv t 0 x86)))

(defrule mv-nth-0-no-error-ia32e-la-to-pa-page-directory
  (implies (ia32e-la-to-pa-page-directory-entry-validp
            lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)
           (equal (mv-nth
                   0
                   (ia32e-la-to-pa-page-directory
                    lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86))
                  nil))
  :in-theory (e/d (ia32e-la-to-pa-page-directory)
                  (bitops::logand-with-negated-bitmask)))

(defthm ia32e-la-to-pa-PD-and-ia32e-la-to-pa-page-table
  (implies (and (page-table-entry-addr-found-p lin-addr x86)
                (not (mv-nth 0 (ia32e-la-to-pa-page-directory
                                lin-addr
                                (mv-nth 1 (page-directory-base-addr lin-addr x86))
                                wp smep nxe r-w-x cpl x86)))
                (equal
                 u-s-acc
                 (ia32e-page-tables-slice
                  :u/s (rm-low-64 (page-directory-entry-addr
                                   lin-addr
                                   (mv-nth 1 (page-directory-base-addr lin-addr x86)))
                                  x86))))
           (equal (mv-nth 1 (ia32e-la-to-pa-PD lin-addr wp smep nxe r-w-x cpl x86))
                  (mv-nth 1 (ia32e-la-to-pa-page-table
                             lin-addr
                             (mv-nth 1 (page-table-base-addr lin-addr x86))
                             u-s-acc wp smep nxe r-w-x cpl x86))))
  :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa-page-directory
                                    page-table-base-addr)
                                   (bitops::logand-with-negated-bitmask)))))


(define ia32e-la-to-pa-PDPT
  ((lin-addr  :type (signed-byte   #.*max-linear-address-size*))
   (wp        :type (unsigned-byte  1))
   (smep      :type (unsigned-byte  1))
   (nxe       :type (unsigned-byte  1))
   (r-w-x     :type (member  :r :w :x))
   (cpl       :type (unsigned-byte  2))
   (x86))
  :non-executable t
  :enabled t
  (if (page-dir-ptr-table-entry-addr-found-p lin-addr x86)
      (b* (((mv & base-addr)
            (page-dir-ptr-table-base-addr lin-addr x86)))
          (ia32e-la-to-pa-page-dir-ptr-table
           lin-addr base-addr wp smep nxe r-w-x cpl x86))
    (mv t 0 x86)))

(defrule mv-nth-0-no-error-ia32e-la-to-pa-page-dir-ptr-table
  (implies (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
            lin-addr page-dir-ptr-table-base-addr wp smep nxe r-w-x cpl x86)
           (equal (mv-nth
                   0
                   (ia32e-la-to-pa-page-dir-ptr-table
                    lin-addr page-dir-ptr-table-base-addr wp smep nxe r-w-x cpl x86))
                  nil))
  :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table)
                  (bitops::logand-with-negated-bitmask)))

(defthm ia32e-la-to-pa-PDPT-and-ia32e-la-to-pa-page-directory
  (implies (and (page-directory-entry-addr-found-p lin-addr x86)
                (not (mv-nth 0 (ia32e-la-to-pa-page-dir-ptr-table
                                lin-addr
                                (mv-nth 1 (page-dir-ptr-table-base-addr lin-addr x86))
                                wp smep nxe r-w-x cpl x86))))
           (equal (mv-nth 1 (ia32e-la-to-pa-PDPT lin-addr wp smep nxe r-w-x cpl x86))
                  (mv-nth 1 (ia32e-la-to-pa-page-directory
                             lin-addr
                             (mv-nth 1 (page-directory-base-addr lin-addr x86))
                             wp smep nxe r-w-x cpl x86))))
  :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa-page-dir-ptr-table
                                    page-directory-base-addr)
                                   (bitops::logand-with-negated-bitmask)))))

(define ia32e-la-to-pa-PML4T
  ((lin-addr  :type (signed-byte   #.*max-linear-address-size*))
   (wp        :type (unsigned-byte  1))
   (smep      :type (unsigned-byte  1))
   (nxe       :type (unsigned-byte  1))
   (r-w-x     :type (member  :r :w :x))
   (cpl       :type (unsigned-byte  2))
   (x86))
  :non-executable t
  :enabled t
  (if (pml4-table-entry-addr-found-p lin-addr x86)
      (b* (((mv & base-addr)
            (pml4-table-base-addr x86)))
          (ia32e-la-to-pa-pml4-table
           lin-addr base-addr wp smep nxe r-w-x cpl x86))
    (mv t 0 x86)))

(defrule mv-nth-0-no-error-ia32e-la-to-pa-pml4-table
  (implies (ia32e-la-to-pa-pml4-table-entry-validp
            lin-addr pml4-table-base-addr wp smep nxe r-w-x cpl x86)
           (equal (mv-nth
                   0
                   (ia32e-la-to-pa-pml4-table
                    lin-addr pml4-table-base-addr wp smep nxe r-w-x cpl x86))
                  nil))
  :in-theory (e/d (ia32e-la-to-pa-pml4-table)
                  (bitops::logand-with-negated-bitmask)))

(defthm ia32e-la-to-pa-PML4T-and-ia32e-la-to-pa-page-dir-ptr-table
  (implies (and (page-dir-ptr-table-entry-addr-found-p lin-addr x86)
                (not (mv-nth 0 (ia32e-la-to-pa-pml4-table
                                lin-addr
                                (mv-nth 1 (pml4-table-base-addr x86))
                                wp smep nxe r-w-x cpl x86))))
           (equal (mv-nth 1 (ia32e-la-to-pa-PML4T lin-addr wp smep nxe r-w-x cpl x86))
                  (mv-nth 1 (ia32e-la-to-pa-page-dir-ptr-table
                             lin-addr
                             (mv-nth 1 (page-dir-ptr-table-base-addr lin-addr x86))
                             wp smep nxe r-w-x cpl x86))))
  :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa-pml4-table
                                    page-dir-ptr-table-base-addr)
                                   (bitops::logand-with-negated-bitmask)))))

;; ======================================================================
