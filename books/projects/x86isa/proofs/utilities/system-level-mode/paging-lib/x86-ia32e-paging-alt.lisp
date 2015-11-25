;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")

(include-book "gather-paging-structures" :ttags :all)
(include-book "clause-processors/find-subterms" :dir :system)

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))
(local (include-book "centaur/gl/gl" :dir :system))

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

;; Base addresses:

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
            12)))))

  ///

  (defthm superior-entry-points-to-an-inferior-one-p-xw
    (implies (not (equal fld :mem))
             (equal (superior-entry-points-to-an-inferior-one-p addr (xw fld index val x86))
                    (superior-entry-points-to-an-inferior-one-p addr x86)))))

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
           (mv-nth 1 (pml4-table-base-addr x86))))

  (defthm logand-positive-of-pml4-table-base-addr
    (equal (logand 18446744073709547520
                   (loghead 52 (mv-nth 1 (pml4-table-base-addr x86))))
           (mv-nth 1 (pml4-table-base-addr x86))))

  (defthm pml4-table-base-addr-and-xw
    (implies (and (not (equal fld :mem))
                  (not (equal fld :ctr))
                  (x86p x86)
                  (x86p (xw fld index val x86)))
             (equal (mv-nth 1 (pml4-table-base-addr (xw fld index val x86)))
                    (mv-nth 1 (pml4-table-base-addr x86))))))

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
           (mv-nth 1 (page-dir-ptr-table-base-addr lin-addr x86))))

  (defthm logand-positive-of-page-dir-ptr-table-base-addr
    (equal (logand 18446744073709547520
                   (loghead 52 (mv-nth 1 (page-dir-ptr-table-base-addr lin-addr x86))))
           (mv-nth 1 (page-dir-ptr-table-base-addr lin-addr x86)))))

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
           (mv-nth 1 (page-directory-base-addr lin-addr x86))))

  (defthm logand-positive-of-page-directory-base-addr
    (equal (logand 18446744073709547520
                   (loghead 52 (mv-nth 1 (page-directory-base-addr lin-addr x86))))
           (mv-nth 1 (page-directory-base-addr lin-addr x86)))))

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
           (mv-nth 1 (page-table-base-addr lin-addr x86))))

  (defthm logand-positive-of-page-table-base-addr
    (equal (logand 18446744073709547520
                   (loghead 52 (mv-nth 1 (page-table-base-addr lin-addr x86))))
           (mv-nth 1 (page-table-base-addr lin-addr x86)))))

;; ======================================================================

;;  Conditions for finding an entry of a paging data structure:

(define pml4-table-entry-addr-found-p (lin-addr x86)
  :non-executable t
  :enabled t
  (and (canonical-address-p lin-addr)
       (physical-address-p (+ (ash 512 3) (mv-nth 1 (pml4-table-base-addr x86))))
       (good-paging-structures-x86p x86)))

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

(defun find-binding-from-entry-found-p-aux (var calls)
  (if (endp calls)
      nil
    (b* ((call (car calls))
         (var-val (if (equal var 'lin-addr)
                      (second call)
                    (if (equal var 'x86)
                        (third call)
                      nil))))
        (append `((,var . ,var-val))
                (find-binding-from-entry-found-p-aux var (cdr calls))))))

(defun find-binding-from-entry-found-p (var mfc state)
  (declare (xargs :stobjs (state) :mode :program)
           (ignorable state))
  (b* ((calls (acl2::find-calls-of-fns-lst
               '(page-table-entry-addr-found-p
                 page-directory-entry-addr-found-p
                 page-dir-ptr-table-entry-addr-found-p
                 pml4-table-entry-addr-found-p)
               (acl2::mfc-clause mfc))))
      (find-binding-from-entry-found-p-aux var calls)))

(defthmd entry-found-p-and-lin-addr
  (implies (and (bind-free (find-binding-from-entry-found-p 'x86 mfc state) (x86))
                (or (page-table-entry-addr-found-p lin-addr x86)
                    (page-directory-entry-addr-found-p lin-addr x86)
                    (page-dir-ptr-table-entry-addr-found-p lin-addr x86)
                    (pml4-table-entry-addr-found-p lin-addr x86)))
           (equal (logext 48 lin-addr) lin-addr))
  :hints (("Goal" :in-theory (e/d* (page-table-entry-addr-found-p
                                    page-directory-entry-addr-found-p
                                    page-dir-ptr-table-entry-addr-found-p
                                    pml4-table-entry-addr-found-p)
                                   ()))))

(defthmd entry-found-p-and-good-paging-structures-x86p
  (implies (and (bind-free (find-binding-from-entry-found-p 'lin-addr mfc state) (lin-addr))
                (or (page-table-entry-addr-found-p lin-addr x86)
                    (page-directory-entry-addr-found-p lin-addr x86)
                    (page-dir-ptr-table-entry-addr-found-p lin-addr x86)
                    (pml4-table-entry-addr-found-p lin-addr x86)))
           (good-paging-structures-x86p x86))
  :hints (("Goal" :in-theory (e/d* (page-table-entry-addr-found-p
                                    page-directory-entry-addr-found-p
                                    page-dir-ptr-table-entry-addr-found-p
                                    pml4-table-entry-addr-found-p)
                                   ()))))

(local (in-theory (e/d (entry-found-p-and-lin-addr
                        entry-found-p-and-good-paging-structures-x86p)
                       ())))

;; ======================================================================

;; Alternate interfaces to paging structure traversal functions:

;; (i-am-here)

;; page-table-base-addr and xw
;; page-table-entry-addr-found-p and xw

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
    (mv t 0 x86))

  ///

  (defthmd ia32e-la-to-pa-PT-and-ia32e-la-to-pa-page-table
    ;; Sanity check for ia32e-la-to-pa-PT.
    (implies (and (page-table-entry-addr-found-p lin-addr x86)
                  (equal base-addr (mv-nth 1 (page-table-base-addr lin-addr x86))))
             (equal (ia32e-la-to-pa-PT lin-addr u-s-acc wp smep nxe r-w-x cpl x86)
                    (ia32e-la-to-pa-page-table lin-addr base-addr u-s-acc wp smep nxe r-w-x cpl x86))))

  (local (in-theory (e/d () (page-table-entry-addr-found-p))))

  (defthm-usb n52p-mv-nth-1-ia32e-la-to-pa-PT
    :hyp t
    :bound *physical-address-size*
    :concl (mv-nth 1
                   (ia32e-la-to-pa-PT
                    lin-addr u-s-acc wp smep nxe r-w-x cpl
                    x86))
    :gen-linear t
    :gen-type t)

  (defthm x86p-mv-nth-2-ia32e-la-to-pa-PT
    (implies (x86p x86)
             (x86p
              (mv-nth 2
                      (ia32e-la-to-pa-PT
                       lin-addr u-s-acc wp smep nxe r-w-x cpl
                       x86)))))

  (defthm xr-ia32e-la-to-pa-PT
    (implies (and (not (equal fld :mem))
                  (not (equal fld :fault)))
             (equal (xr fld index
                        (mv-nth 2
                                (ia32e-la-to-pa-PT
                                 lin-addr u-s-acc wp smep nxe r-w-x cpl
                                 x86)))
                    (xr fld index x86))))

  ;; (defthm ia32e-la-to-pa-PT-xw-values
  ;;   (implies (and (not (equal fld :mem))
  ;;                 (not (equal fld :fault)))
  ;;            (and (equal (mv-nth 0
  ;;                                (ia32e-la-to-pa-PT
  ;;                                 lin-addr u-s-acc wp smep nxe r-w-x cpl
  ;;                                 (xw fld index value x86)))
  ;;                        (mv-nth 0
  ;;                                (ia32e-la-to-pa-PT
  ;;                                 lin-addr u-s-acc wp smep nxe r-w-x cpl
  ;;                                 x86)))
  ;;                 (equal (mv-nth 1
  ;;                                (ia32e-la-to-pa-PT
  ;;                                 lin-addr u-s-acc wp smep nxe r-w-x cpl
  ;;                                 (xw fld index value x86)))
  ;;                        (mv-nth 1
  ;;                                (ia32e-la-to-pa-PT
  ;;                                 lin-addr u-s-acc wp smep nxe r-w-x cpl
  ;;                                 x86))))))

  ;; (defthm ia32e-la-to-pa-PT-xw-state
  ;;   (implies (and (not (equal fld :mem))
  ;;                 (not (equal fld :fault)))
  ;;            (equal (mv-nth 2
  ;;                           (ia32e-la-to-pa-PT
  ;;                            lin-addr u-s-acc wp smep nxe r-w-x cpl
  ;;                            (xw fld index value x86)))
  ;;                   (xw fld index value
  ;;                       (mv-nth 2
  ;;                               (ia32e-la-to-pa-PT
  ;;                                lin-addr u-s-acc wp smep nxe r-w-x cpl
  ;;                                x86))))))
  )

;; ----------------------------------------------------------------------

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
  :guard-hints (("Goal" :in-theory (e/d* () (acl2::member-of-cons member-equal))))
  (if (page-directory-entry-addr-found-p lin-addr x86)

      (b* (((mv & base-addr)
            (page-directory-base-addr lin-addr x86))
           (p-entry-addr
            (page-directory-entry-addr lin-addr base-addr))
           (entry (rm-low-64 p-entry-addr x86)))

          (if (equal (ia32e-page-tables-slice :ps entry) 1)
              ;; 2MB page
              (ia32e-la-to-pa-page-directory
               lin-addr base-addr wp smep nxe r-w-x cpl x86)
            ;; 4K page
            (b* (((mv fault-flg val x86)
                  (paging-entry-no-page-fault-p lin-addr entry wp smep nxe r-w-x cpl x86))
                 ((when fault-flg)
                  (mv 'Page-Fault val x86))
                 ;; No errors at this level.
                 ((mv flg address x86)
                  (ia32e-la-to-pa-PT
                   lin-addr (ia32e-page-tables-slice :u/s entry)
                   wp smep nxe r-w-x cpl x86))
                 ((when flg)
                  ;; Error, so do not update accessed bit.
                  (mv flg 0 x86))

                 ;; Get accessed bit.  Dirty bit is ignored when PDE
                 ;; references the PT.
                 (accessed        (ia32e-page-tables-slice :a entry))
                 ;; Update accessed bit, if needed.
                 (entry (if (equal accessed 0)
                            (set-accessed-bit entry)
                          entry))
                 ;; Update x86, if needed.
                 (x86 (if (equal accessed 0)
                          (wm-low-64 p-entry-addr entry x86)
                        x86)))
                (mv nil address x86))))

    (mv t 0 x86))

  ///

  (defthmd ia32e-la-to-pa-PD-and-ia32e-la-to-pa-page-directory-only-2M-pages
    ;; Sanity check for ia32e-la-to-pa-PD.
    (implies (and (page-directory-entry-addr-found-p lin-addr x86)
                  (equal base-addr (mv-nth 1 (page-directory-base-addr lin-addr x86)))
                  (equal entry (rm-low-64 (page-directory-entry-addr lin-addr base-addr) x86))
                  (equal (ia32e-page-tables-slice :ps entry) 1))
             (equal (ia32e-la-to-pa-PD
                     lin-addr wp smep nxe r-w-x cpl x86)
                    (ia32e-la-to-pa-page-directory
                     lin-addr base-addr wp smep nxe r-w-x cpl x86))))

  (defthmd ia32e-la-to-pa-PD-and-ia32e-la-to-pa-page-directory-2M-and-4K-pages
    ;; Sanity check for ia32e-la-to-pa-PD.
    (implies (and (page-table-entry-addr-found-p lin-addr x86)
                  (equal page-directory-base-addr
                         (mv-nth 1 (page-directory-base-addr lin-addr x86))))
             (equal (ia32e-la-to-pa-PD lin-addr wp smep nxe r-w-x cpl x86)
                    (ia32e-la-to-pa-page-directory
                     lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)))
    :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa-page-directory
                                      page-table-base-addr
                                      ia32e-la-to-pa-PT)
                                     (page-directory-entry-addr-found-p
                                      page-table-entry-addr-found-p
                                      ia32e-la-to-pa-page-table
                                      bitops::logand-with-negated-bitmask))))))

;; ----------------------------------------------------------------------

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
  :guard-hints (("Goal" :in-theory (e/d* () (acl2::member-of-cons member-equal))))
  (if (page-dir-ptr-table-entry-addr-found-p lin-addr x86)

      (b* (((mv & base-addr)
            (page-dir-ptr-table-base-addr lin-addr x86))
           (p-entry-addr
            (page-dir-ptr-table-entry-addr lin-addr base-addr))
           (entry (rm-low-64 p-entry-addr x86)))
          (if (equal (ia32e-page-tables-slice :ps entry) 1)
              ;; 1GB page
              (ia32e-la-to-pa-page-dir-ptr-table
               lin-addr base-addr wp smep nxe r-w-x cpl x86)
            ;; 2M or 4K page
            (b* (((mv fault-flg val x86)
                  (paging-entry-no-page-fault-p lin-addr entry wp smep nxe r-w-x cpl x86))
                 ((when fault-flg)
                  (mv 'Page-Fault val x86))
                 ;; No errors at this level.
                 ((mv flg address x86)
                  (ia32e-la-to-pa-PD lin-addr wp smep nxe r-w-x cpl x86))
                 ((when flg)
                  ;; Error, so do not update accessed bit.
                  (mv flg 0 x86))

                 ;; Get accessed bit.  Dirty bit is ignored when PDE
                 ;; references the PT.
                 (accessed        (ia32e-page-tables-slice :a entry))
                 ;; Update accessed bit, if needed.
                 (entry (if (equal accessed 0)
                            (set-accessed-bit entry)
                          entry))
                 ;; Update x86, if needed.
                 (x86 (if (equal accessed 0)
                          (wm-low-64 p-entry-addr entry x86)
                        x86)))
                (mv nil address x86))))


    (mv t 0 x86))

  ///

  (defthmd ia32e-la-to-pa-PDPT-and-ia32e-la-to-pa-page-dir-ptr-table-only-1G-pages
    ;; Sanity check for ia32e-la-to-pa-PDPT.
    (implies (and (page-dir-ptr-table-entry-addr-found-p lin-addr x86)
                  (equal base-addr (mv-nth 1 (page-dir-ptr-table-base-addr lin-addr x86)))
                  (equal entry (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr) x86))
                  (equal (ia32e-page-tables-slice :ps entry) 1))
             (equal (ia32e-la-to-pa-PDPT
                     lin-addr wp smep nxe r-w-x cpl x86)
                    (ia32e-la-to-pa-page-dir-ptr-table
                     lin-addr base-addr wp smep nxe r-w-x cpl x86))))

  (defthmd ia32e-la-to-pa-PDPT-and-ia32e-la-to-pa-page-dir-ptr-table-2M-pages
    ;; Sanity check for ia32e-la-to-pa-PDPT.
    (implies (and (page-directory-entry-addr-found-p lin-addr x86)
                  (equal page-dir-ptr-table-base-addr
                         (mv-nth 1 (page-dir-ptr-table-base-addr lin-addr x86)))
                  (equal page-directory-base-addr
                         (mv-nth 1 (page-directory-base-addr lin-addr x86)))
                  (equal page-directory-entry
                         (rm-low-64
                          (page-directory-entry-addr lin-addr page-directory-base-addr)
                          x86))
                  (equal (ia32e-page-tables-slice :ps page-directory-entry) 1))
             (equal (ia32e-la-to-pa-PDPT lin-addr wp smep nxe r-w-x cpl x86)
                    (ia32e-la-to-pa-page-dir-ptr-table
                     lin-addr page-dir-ptr-table-base-addr wp smep nxe r-w-x cpl x86)))
    :hints (("Goal"
             :use ((:instance ia32e-la-to-pa-PD-and-ia32e-la-to-pa-page-directory-only-2M-pages
                              (base-addr
                               (mv-nth 1 (page-directory-base-addr lin-addr x86)))
                              (entry (rm-low-64 (page-directory-entry-addr
                                                 lin-addr
                                                 (mv-nth 1 (page-directory-base-addr lin-addr x86))) x86))))
             :in-theory (e/d* (ia32e-la-to-pa-page-dir-ptr-table
                               page-directory-base-addr)
                              (ia32e-la-to-pa-PT
                               ia32e-la-to-pa-PD
                               page-dir-ptr-table-entry-addr-found-p
                               page-directory-entry-addr-found-p
                               page-table-entry-addr-found-p
                               bitops::logand-with-negated-bitmask)))))

  (defthmd ia32e-la-to-pa-PDPT-and-ia32e-la-to-pa-page-dir-ptr-table-4K-pages
    ;; Sanity check for ia32e-la-to-pa-PDPT.
    (implies (and (page-table-entry-addr-found-p lin-addr x86)
                  (equal page-dir-ptr-table-base-addr
                         (mv-nth 1 (page-dir-ptr-table-base-addr lin-addr x86))))
             (equal (ia32e-la-to-pa-PDPT lin-addr wp smep nxe r-w-x cpl x86)
                    (ia32e-la-to-pa-page-dir-ptr-table
                     lin-addr page-dir-ptr-table-base-addr wp smep nxe r-w-x cpl x86)))
    :hints (("Goal"
             :use ((:instance ia32e-la-to-pa-PD-and-ia32e-la-to-pa-page-directory-2M-and-4K-pages
                              (page-directory-base-addr
                               (mv-nth 1 (page-directory-base-addr lin-addr x86)))))
             :in-theory (e/d* (ia32e-la-to-pa-page-dir-ptr-table
                               page-directory-base-addr)
                              (ia32e-la-to-pa-PT
                               ia32e-la-to-pa-PD
                               page-dir-ptr-table-entry-addr-found-p
                               page-directory-entry-addr-found-p
                               page-table-entry-addr-found-p
                               bitops::logand-with-negated-bitmask))))))

;; ----------------------------------------------------------------------

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
  :guard-hints (("Goal" :in-theory (e/d* () (acl2::member-of-cons member-equal))))

  (if (pml4-table-entry-addr-found-p lin-addr x86)

      (b* (((mv & base-addr)
            (pml4-table-base-addr x86))
           (p-entry-addr
            (pml4-table-entry-addr lin-addr base-addr))
           (entry (rm-low-64 p-entry-addr x86))
           ((mv fault-flg val x86)
            (paging-entry-no-page-fault-p lin-addr entry wp smep nxe r-w-x cpl x86))
           ((when fault-flg)
            (mv 'Page-Fault val x86))
           ((mv flag address x86)
            (ia32e-la-to-pa-PDPT lin-addr wp smep nxe r-w-x cpl x86))
           ((when flag)
            (mv flag 0 x86))

           (accessed (ia32e-page-tables-slice :a entry))
           (entry (if (equal accessed 0)
                      (set-accessed-bit entry)
                    entry))
           ;; Update x86, if needed.
           (x86 (if (equal accessed 0)
                    (wm-low-64 p-entry-addr entry x86)
                  x86)))
          (mv nil address x86))

    (mv t 0 x86))

  ///

  (defthmd ia32e-la-to-pa-PML4T-and-ia32e-la-to-pa-pml4-table-1G-pages
    ;; Sanity check for ia32e-la-to-pa-PML4T.
    (implies (and (page-dir-ptr-table-entry-addr-found-p lin-addr x86)
                  (equal pml4-table-base-addr (mv-nth 1 (pml4-table-base-addr x86)))
                  (equal page-dir-ptr-table-base-addr
                         (mv-nth 1 (page-dir-ptr-table-base-addr lin-addr x86)))
                  (equal
                   page-dir-ptr-table-entry
                   (rm-low-64
                    (page-dir-ptr-table-entry-addr lin-addr page-dir-ptr-table-base-addr)
                    x86))
                  (equal (ia32e-page-tables-slice :ps page-dir-ptr-table-entry) 1))
             (equal (ia32e-la-to-pa-PML4T lin-addr wp smep nxe r-w-x cpl x86)
                    (ia32e-la-to-pa-pml4-table
                     lin-addr pml4-table-base-addr wp smep nxe r-w-x cpl x86)))
    :hints (("Goal"
             :use ((:instance ia32e-la-to-pa-PDPT-and-ia32e-la-to-pa-page-dir-ptr-table-only-1G-pages
                              (base-addr (mv-nth 1 (page-dir-ptr-table-base-addr lin-addr x86)))
                              (entry (rm-low-64 (page-dir-ptr-table-entry-addr
                                                 lin-addr
                                                 (mv-nth 1 (page-dir-ptr-table-base-addr lin-addr x86)))
                                                x86))))
             :in-theory (e/d* (ia32e-la-to-pa-pml4-table
                               page-dir-ptr-table-base-addr)
                              (ia32e-la-to-pa-PT
                               ia32e-la-to-pa-PD
                               ia32e-la-to-pa-PDPT
                               pml4-table-entry-addr-found-p
                               page-dir-ptr-table-entry-addr-found-p
                               page-directory-entry-addr-found-p
                               page-table-entry-addr-found-p
                               bitops::logand-with-negated-bitmask)))))

  (defthmd ia32e-la-to-pa-PML4T-and-ia32e-la-to-pa-pml4-table-2M-pages
    ;; Sanity check for ia32e-la-to-pa-PML4T.
    (implies (and (page-directory-entry-addr-found-p lin-addr x86)
                  (equal pml4-table-base-addr (mv-nth 1 (pml4-table-base-addr x86)))
                  (equal page-dir-ptr-table-base-addr
                         (mv-nth 1 (page-dir-ptr-table-base-addr lin-addr x86)))
                  (equal page-directory-base-addr
                         (mv-nth 1 (page-directory-base-addr lin-addr x86)))
                  (equal page-directory-entry
                         (rm-low-64
                          (page-directory-entry-addr lin-addr page-directory-base-addr)
                          x86))
                  (equal (ia32e-page-tables-slice :ps page-directory-entry) 1))
             (equal (ia32e-la-to-pa-PML4T lin-addr wp smep nxe r-w-x cpl x86)
                    (ia32e-la-to-pa-pml4-table
                     lin-addr pml4-table-base-addr wp smep nxe r-w-x cpl x86)))
    :hints (("Goal"
             :use ((:instance ia32e-la-to-pa-PDPT-and-ia32e-la-to-pa-page-dir-ptr-table-2M-pages))
             :in-theory (e/d* (ia32e-la-to-pa-pml4-table
                               page-dir-ptr-table-base-addr)
                              (ia32e-la-to-pa-PT
                               ia32e-la-to-pa-PD
                               ia32e-la-to-pa-PDPT
                               pml4-table-entry-addr-found-p
                               page-dir-ptr-table-entry-addr-found-p
                               page-directory-entry-addr-found-p
                               page-table-entry-addr-found-p
                               bitops::logand-with-negated-bitmask)))))

  (defthmd ia32e-la-to-pa-PML4T-and-ia32e-la-to-pa-pml4-table-4K-pages
    ;; Sanity check for ia32e-la-to-pa-PML4T.
    (implies (and (page-table-entry-addr-found-p lin-addr x86)
                  (equal pml4-table-base-addr
                         (mv-nth 1 (pml4-table-base-addr x86))))
             (equal (ia32e-la-to-pa-PML4T lin-addr wp smep nxe r-w-x cpl x86)
                    (ia32e-la-to-pa-pml4-table
                     lin-addr pml4-table-base-addr wp smep nxe r-w-x cpl x86)))
    :hints (("Goal"
             :use ((:instance ia32e-la-to-pa-PDPT-and-ia32e-la-to-pa-page-dir-ptr-table-4K-pages
                              (page-dir-ptr-table-base-addr
                               (mv-nth 1 (page-dir-ptr-table-base-addr lin-addr x86)))))
             :in-theory (e/d* (ia32e-la-to-pa-pml4-table
                               page-dir-ptr-table-base-addr)
                              (ia32e-la-to-pa-PT
                               ia32e-la-to-pa-PD
                               ia32e-la-to-pa-PDPT
                               pml4-table-entry-addr-found-p
                               page-dir-ptr-table-entry-addr-found-p
                               page-directory-entry-addr-found-p
                               page-table-entry-addr-found-p
                               bitops::logand-with-negated-bitmask))))))

;; ======================================================================
