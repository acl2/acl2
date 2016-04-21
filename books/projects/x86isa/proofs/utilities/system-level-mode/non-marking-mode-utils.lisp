;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")
(include-book "physical-memory-utils")
(include-book "gl-lemmas")
(include-book "clause-processors/find-subterms" :dir :system)

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))
(local (include-book "centaur/gl/gl" :dir :system))

(local (in-theory (e/d* () (signed-byte-p unsigned-byte-p))))

;; ======================================================================

(defsection system-level-memory-utils
  :parents (proof-utilities)

  :short "Reasoning about paging data structures"

  :long "<p>WORK IN PROGRESS...</p>

<p>This doc topic will be updated in later commits...</p>"
  )

(local (xdoc::set-default-parents system-level-memory-utils))

;; ----------------------------------------------------------------------
;; Debugging:
;; ----------------------------------------------------------------------

;; If you think some rules from this book should fire when you are
;; unwinding your (x86-run ... x86) expression, monitoring the
;; following rules (maybe using Jared Davis's why macro) can tell you
;; (maybe) what's going on.

;; (acl2::why x86-run-opener-not-ms-not-zp-n)
;; (acl2::why x86-fetch-decode-execute-opener)
;; (acl2::why get-prefixes-opener-lemma-no-prefix-byte)
;; (acl2::why ia32e-la-to-pa-values-and-mv-nth-1-wb)
;; (acl2::why rb-in-terms-of-nth-and-pos-in-system-level-non-marking-mode)
;; (acl2::why combine-bytes-rb-in-terms-of-rb-subset-p-in-system-level-non-marking-mode)
;; (acl2::why program-at-wb-disjoint-in-system-level-non-marking-mode)
;; (acl2::why rb-wb-disjoint-in-system-level-non-marking-mode)
;; (acl2::why disjointness-of-translation-governing-addresses-from-all-translation-governing-addresses)
;; (acl2::why la-to-pas-values-and-mv-nth-1-wb-disjoint-from-xlation-gov-addrs)

;; ======================================================================

;; Some misc. lemmas and utils:

(defthm combine-bytes-of-list-combine-bytes
  (equal (combine-bytes (list (combine-bytes xs)))
         (combine-bytes xs))
  :hints (("Goal" :in-theory (e/d* (combine-bytes) (force (force))))))

(defun get-subterm-from-list-of-terms (n x)
  (declare (xargs :guard (and (natp n) (pseudo-term-listp x))))
  ;; E.g.:
  ;; (get-subterm-from-list-of-terms 1 '((las-to-pas l-addrs-1 r-w-x cpl x86)
  ;;                                     (las-to-pas l-addrs-2 r-w-x cpl x86)
  ;;                                     (las-to-pas l-addrs-2 r-w-x cpl x86)
  ;;                                     (foo x)))
  (if (atom x)
      nil
    (cons (nth n (acl2::list-fix (car x)))
          (get-subterm-from-list-of-terms n (cdr x)))))

(define make-bind-free-alist-lists (var values)
  (if (atom values)
      nil
    (cons (acons var (car values) nil)
          (make-bind-free-alist-lists var (cdr values)))))

;; ======================================================================

;; Normalizing memory reads:

(local
 (defthm dumb-integerp-of-mem-rewrite
   (implies (x86p x86)
            (integerp (xr :mem index x86)))))

(defthm mv-nth-2-rb-in-system-level-non-marking-mode
  (implies (and (not (page-structure-marking-mode x86))
                (not (mv-nth 0 (rb l-addrs r-w-x x86))))
           (equal (mv-nth 2 (rb l-addrs r-w-x x86))
                  x86))
  :hints (("Goal" :in-theory (e/d* (rb) (force (force))))))

(defthm rm08-to-rb
  (implies (and (x86p x86)
                (force (canonical-address-p lin-addr)))
           (equal (rm08 lin-addr r-w-x x86)
                  (b* (((mv flg bytes x86)
                        (rb (create-canonical-address-list 1 lin-addr) r-w-x x86))
                       (result (combine-bytes bytes)))
                    (mv flg result x86))))
  :hints (("Goal"
           :use ((:instance rb-and-rm08-in-programmer-level-mode (addr lin-addr)))
           :in-theory (e/d* (rm08 rb ifix)
                            (rb-1 signed-byte-p
                                  unsigned-byte-p
                                  force (force))))))

(defthm rm16-to-rb
  ;; Why don't we need (x86p x86) here?
  (implies (and (force (canonical-address-p lin-addr))
                (force (canonical-address-p (+ 1 lin-addr))))
           (equal (rm16 lin-addr r-w-x x86)
                  (b* (((mv flg bytes x86)
                        (rb (create-canonical-address-list 2 lin-addr) r-w-x x86))
                       (result (combine-bytes bytes)))
                    (mv flg result x86))))
  :hints (("Goal"
           :in-theory (e/d* (rm16 rm08 ifix)
                            (cons-equal
                             signed-byte-p
                             unsigned-byte-p
                             bitops::logior-equal-0
                             (:meta acl2::mv-nth-cons-meta)
                             force (force))))))

(defthm rm32-to-rb
  (implies (and (force (canonical-address-p lin-addr))
                (force (canonical-address-p (+ 3 lin-addr)))
                (x86p x86))
           (equal (rm32 lin-addr r-w-x x86)
                  (b* (((mv flg bytes x86)
                        (rb (create-canonical-address-list 4 lin-addr) r-w-x x86))
                       (result (combine-bytes bytes)))
                    (mv flg result x86))))
  :hints (("Goal"
           :in-theory (e/d* (rm32 rm08)
                            (signed-byte-p
                             unsigned-byte-p
                             bitops::logior-equal-0
                             force (force))))))

(defthm rm64-to-rb
  (implies (and (force (canonical-address-p lin-addr))
                (force (canonical-address-p (+ 7 lin-addr)))
                (force (x86p x86)))
           (equal (rm64 lin-addr r-w-x x86)
                  (b* (((mv flg bytes x86)
                        (rb (create-canonical-address-list 8 lin-addr) r-w-x x86))
                       (result (combine-bytes bytes)))
                    (mv flg result x86))))
  :hints (("Goal"
           :expand ((create-canonical-address-list 8 lin-addr)
                    (create-canonical-address-list 7 (+ 1 lin-addr))
                    (create-canonical-address-list 6 (+ 2 lin-addr))
                    (create-canonical-address-list 5 (+ 3 lin-addr)))
           :in-theory (e/d* (rm64)
                            ((:linear bitops::logior-<-0-linear-2)
                             (:linear ash-monotone-2)
                             (:rewrite bitops::ash-<-0)
                             (:rewrite acl2::natp-when-integerp)
                             cons-equal
                             signed-byte-p
                             unsigned-byte-p
                             bitops::logior-equal-0
                             (:meta acl2::mv-nth-cons-meta)
                             force (force))))))

(defthm mv-nth-0-rb-and-mv-nth-0-las-to-pas-in-system-level-mode
  (implies (not (xr :programmer-level-mode 0 x86))
           (equal (mv-nth 0 (rb l-addrs r-w-x x86))
                  (mv-nth 0 (las-to-pas l-addrs r-w-x (cpl x86) x86))))
  :hints (("Goal" :in-theory (e/d* (rb) (force (force))))))

;; ======================================================================

;; Normalizing memory writes:

(defthm xr-mem-write-to-physical-memory-disjoint
  (implies (not (member-p index p-addrs))
           (equal (xr :mem index (write-to-physical-memory p-addrs bytes x86))
                  (xr :mem index x86)))
  :hints (("Goal" :in-theory (e/d* (member-p) (force (force))))))

(defthm wm08-to-wb
  (implies (and (force (canonical-address-p lin-addr))
                (force (unsigned-byte-p 8 byte)))
           (equal (wm08 lin-addr byte x86)
                  (wb (create-addr-bytes-alist
                       (create-canonical-address-list 1 lin-addr)
                       (list byte))
                      x86)))
  :hints (("Goal" :in-theory (e/d* (wm08 wvm08 wb)
                                   (signed-byte-p
                                    unsigned-byte-p
                                    force (force))))))

(defthm wm16-to-wb
  (implies (and (force (canonical-address-p lin-addr))
                (force (canonical-address-p (1+ lin-addr))))
           (equal (wm16 lin-addr word x86)
                  (wb (create-addr-bytes-alist
                       (create-canonical-address-list 2 lin-addr)
                       (byte-ify 2 word))
                      x86)))
  :hints (("Goal" :in-theory (e/d* (wm16 wb byte-ify)
                                   (signed-byte-p
                                    unsigned-byte-p
                                    force (force))))))

(defthm wm32-to-wb
  (implies (and (force (canonical-address-p lin-addr))
                (force (canonical-address-p (+ 3 lin-addr))))
           (equal (wm32 lin-addr dword x86)
                  (wb (create-addr-bytes-alist
                       (create-canonical-address-list 4 lin-addr)
                       (byte-ify 4 dword))
                      x86)))
  :hints (("Goal" :in-theory (e/d* (wm32 wb byte-ify)
                                   (signed-byte-p
                                    unsigned-byte-p
                                    force (force))))))

(defthm wm64-to-wb
  (implies (and (force (canonical-address-p lin-addr))
                (force (canonical-address-p (+ 7 lin-addr))))
           (equal (wm64 lin-addr qword x86)
                  (wb (create-addr-bytes-alist
                       (create-canonical-address-list 8 lin-addr)
                       (byte-ify 8 qword))
                      x86)))
  :hints (("Goal"
           :expand ((create-canonical-address-list 8 lin-addr)
                    (create-canonical-address-list 7 (+ 1 lin-addr))
                    (create-canonical-address-list 6 (+ 2 lin-addr))
                    (create-canonical-address-list 5 (+ 3 lin-addr)))
           :in-theory (e/d* (wm64 wb byte-ify)
                            (signed-byte-p
                             unsigned-byte-p
                             force (force))))))

(defthm mv-nth-0-wb-and-mv-nth-0-las-to-pas-in-system-level-mode
  (implies (not (xr :programmer-level-mode 0 x86))
           (equal (mv-nth 0 (wb addr-lst x86))
                  (mv-nth 0 (las-to-pas (strip-cars addr-lst) :w (cpl x86) x86))))
  :hints (("Goal" :in-theory (e/d* (wb) (force (force))))))

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

  (b* ((cr3       (ctri *cr3* x86))
       ;; PML4 Table:
       (pml4-base-addr (ash (cr3-slice :cr3-pdb cr3) 12)))

    (translation-governing-addresses-for-pml4-table
     lin-addr pml4-base-addr x86))

  ///

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
             :in-theory (e/d* (disjoint-p disjoint-p-commutative) (translation-governing-addresses)))))

  (defthm translation-governing-addresses-and-mv-nth-1-wb-disjoint-p
    (implies (and (disjoint-p
                   (translation-governing-addresses lin-addr x86)
                   (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w (cpl x86) x86)))
                  (not (mv-nth 0 (las-to-pas (strip-cars addr-lst) :w (cpl x86) x86)))
                  (not (programmer-level-mode x86))
                  (not (page-structure-marking-mode x86))
                  (x86p x86))
             (equal (translation-governing-addresses lin-addr (mv-nth 1 (wb addr-lst x86)))
                    (translation-governing-addresses lin-addr x86)))
    :hints (("Goal" :in-theory (e/d* (disjoint-p wb) (translation-governing-addresses))))))

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
    :hints (("Goal" :in-theory (e/d* () (translation-governing-addresses force (force))))))

  (defthm all-translation-governing-addresses-and-mv-nth-1-wb-disjoint
    (implies (and (disjoint-p
                   (all-translation-governing-addresses l-addrs x86)
                   (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w (cpl x86) x86)))
                  (not (mv-nth 0 (las-to-pas (strip-cars addr-lst) :w (cpl x86) x86)))
                  (not (programmer-level-mode x86))
                  (not (page-structure-marking-mode x86))
                  (x86p x86))
             (equal (all-translation-governing-addresses l-addrs (mv-nth 1 (wb addr-lst x86)))
                    (all-translation-governing-addresses l-addrs x86)))
    :hints (("Goal"
             :in-theory (e/d* (all-translation-governing-addresses) (translation-governing-addresses))
             :induct (all-translation-governing-addresses l-addrs x86)))))

(defun find-l-addrs-from-fn
  (fn l-addrs-var mfc state)
  (declare (xargs :stobjs (state) :mode :program)
           (ignorable state))
  (b* ((calls (acl2::find-calls-lst fn (acl2::mfc-clause mfc)))
       ((when (not calls))
        ;; fn term not encountered.
        nil)
       (l-addrs (get-subterm-from-list-of-terms 1 calls))
       (alst-lst (make-bind-free-alist-lists l-addrs-var l-addrs)))
    alst-lst))

(defthm disjointness-of-translation-governing-addresses-from-all-translation-governing-addresses
  (implies (and (bind-free
                 (find-l-addrs-from-fn 'all-translation-governing-addresses 'l-addrs mfc state)
                 (l-addrs))
                (disjoint-p (all-translation-governing-addresses l-addrs x86) other-p-addrs)
                (member-p lin-addr l-addrs))
           (disjoint-p (translation-governing-addresses lin-addr x86) other-p-addrs))
  :hints (("Goal" :in-theory (e/d* (member-p) ()))))

(defthm disjointness-of-all-translation-governing-addresses-from-all-translation-governing-addresses-subset-p
  (implies (and (bind-free
                 (find-l-addrs-from-fn 'all-translation-governing-addresses 'l-addrs mfc state)
                 (l-addrs))
                (syntaxp (not (eq l-addrs-subset l-addrs)))
                (disjoint-p (all-translation-governing-addresses l-addrs x86) other-p-addrs)
                (subset-p l-addrs-subset l-addrs))
           (disjoint-p (all-translation-governing-addresses l-addrs-subset x86) other-p-addrs))
  :hints (("Goal" :in-theory (e/d* (subset-p member-p) (translation-governing-addresses)))))

;; ======================================================================

;; Lemmas about paging structure walkers:

(defthmd open-mv-nth-0-las-to-pas
  (implies (and (canonical-address-p lin-addr)
                (not (zp n))
                (not (page-structure-marking-mode x86)))
           (equal (mv-nth 0 (las-to-pas (create-canonical-address-list n lin-addr) r-w-x cpl x86))
                  (if (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x cpl x86))
                      (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x cpl x86))
                    (mv-nth 0 (las-to-pas (create-canonical-address-list (+ -1 n) (+ 1 lin-addr))
                                          r-w-x cpl x86))))))

(defthmd open-mv-nth-1-las-to-pas
  (implies (and (canonical-address-p lin-addr)
                (not (zp n))
                (not (mv-nth 0 (las-to-pas (create-canonical-address-list n lin-addr) r-w-x cpl x86)))
                (not (page-structure-marking-mode x86)))
           (equal (mv-nth 1 (las-to-pas (create-canonical-address-list n lin-addr) r-w-x cpl x86))
                  (cons (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x cpl x86))
                        (mv-nth 1 (las-to-pas (create-canonical-address-list (+ -1 n) (+ 1 lin-addr))
                                              r-w-x cpl x86))))))

(defthm mv-nth-1-ia32e-la-to-pa-system-level-non-marking-mode-when-error
  (implies (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x cpl x86))
           (equal (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x cpl x86)) 0))
  :hints (("Goal" :in-theory (e/d (ia32e-la-to-pa
                                   ia32e-la-to-pa-pml4-table)
                                  (force (force))))))

(defthm mv-nth-1-las-to-pas-system-level-non-marking-mode-when-error
  (implies (and (not (page-structure-marking-mode x86))
                (not (programmer-level-mode x86))
                (mv-nth 0 (las-to-pas l-addrs r-w-x cpl x86)))
           (equal (mv-nth 1 (las-to-pas l-addrs r-w-x cpl x86)) nil))
  :hints (("Goal" :in-theory (e/d (las-to-pas) (force (force))))))

(defun find-l-addrs-from-las-to-pas
  (l-addrs-var mfc state)
  (declare (xargs :stobjs (state) :mode :program)
           (ignorable state))
  (b* ((calls (acl2::find-calls-lst 'las-to-pas (acl2::mfc-clause mfc)))
       ((when (not calls))
        ;; las-to-pas term not encountered.
        nil)
       (l-addrs (get-subterm-from-list-of-terms 1 calls))
       (alst-lst (make-bind-free-alist-lists l-addrs-var l-addrs)))
    alst-lst))

(defthm mv-nth-0-ia32e-la-to-pa-member-of-mv-nth-1-las-to-pas-if-lin-addr-member-p
  (implies (and (bind-free (find-l-addrs-from-las-to-pas 'l-addrs mfc state) (l-addrs))
                (member-p lin-addr l-addrs)
                (not (mv-nth 0 (las-to-pas l-addrs r-w-x cpl x86)))
                (not (page-structure-marking-mode x86)))
           (equal (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x cpl x86)) nil))
  :hints (("Goal" :in-theory (e/d* (member-p) ()))))

(defthm mv-nth-1-ia32e-la-to-pa-member-of-mv-nth-1-las-to-pas-if-lin-addr-member-p
  (implies (and (member-p lin-addr l-addrs)
                (not (mv-nth 0 (las-to-pas     l-addrs r-w-x cpl x86)))
                (not (page-structure-marking-mode x86)))
           (member-p (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x cpl x86))
                     (mv-nth 1 (las-to-pas     l-addrs r-w-x cpl x86))))
  :hints (("Goal" :in-theory (e/d* (member-p) ()))))

(defthm las-to-pas-values-and-xw-mem-not-member
  (implies (and (not (member-p index (all-translation-governing-addresses l-addrs x86)))
                (physical-address-p index)
                (canonical-address-listp l-addrs)
                (not (page-structure-marking-mode x86)))
           (and (equal (mv-nth 0 (las-to-pas l-addrs r-w-x cpl (xw :mem index byte x86)))
                       (mv-nth 0 (las-to-pas l-addrs r-w-x cpl x86)))
                (equal (mv-nth 1 (las-to-pas l-addrs r-w-x cpl (xw :mem index byte x86)))
                       (mv-nth 1 (las-to-pas l-addrs r-w-x cpl x86)))))
  :hints (("Goal" :induct (las-to-pas l-addrs r-w-x cpl x86)
           :in-theory (e/d* (disjoint-p) (translation-governing-addresses)))))

(defthmd r-w-x-is-irrelevant-for-mv-nth-1-ia32e-la-to-pa-page-table-when-no-errors
  (implies (and (not (mv-nth 0
                             (ia32e-la-to-pa-page-table
                              lin-addr base-addr u/s-acc r/w-acc x/d-acc
                              wp smep smap ac nxe r-w-x-1 cpl x86)))
                (syntaxp (not (eq r-w-x-2 r-w-x-1)))
                (not (mv-nth 0
                             (ia32e-la-to-pa-page-table
                              lin-addr base-addr u/s-acc r/w-acc x/d-acc
                              wp smep smap ac nxe r-w-x-2 cpl x86))))
           (equal (mv-nth 1
                          (ia32e-la-to-pa-page-table
                           lin-addr base-addr u/s-acc r/w-acc x/d-acc
                           wp smep smap ac nxe r-w-x-2 cpl x86))
                  (mv-nth 1
                          (ia32e-la-to-pa-page-table
                           lin-addr base-addr u/s-acc r/w-acc x/d-acc
                           wp smep smap ac nxe r-w-x-1 cpl x86))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (disjoint-p
                             member-p
                             ia32e-la-to-pa-page-table)
                            (bitops::logand-with-negated-bitmask
                             (:meta acl2::mv-nth-cons-meta)
                             force (force))))))

(defthmd r-w-x-is-irrelevant-for-mv-nth-1-ia32e-la-to-pa-page-directory-when-no-errors
  (implies (and (not (mv-nth 0
                             (ia32e-la-to-pa-page-directory
                              lin-addr base-addr u/s-acc r/w-acc x/d-acc
                              wp smep smap ac nxe r-w-x-1 cpl x86)))
                (syntaxp (not (eq r-w-x-2 r-w-x-1)))
                (not (mv-nth 0
                             (ia32e-la-to-pa-page-directory
                              lin-addr base-addr u/s-acc r/w-acc x/d-acc
                              wp smep smap ac nxe r-w-x-2 cpl x86))))
           (equal (mv-nth 1
                          (ia32e-la-to-pa-page-directory
                           lin-addr base-addr u/s-acc r/w-acc x/d-acc
                           wp smep smap ac nxe r-w-x-2 cpl x86))
                  (mv-nth 1
                          (ia32e-la-to-pa-page-directory
                           lin-addr base-addr u/s-acc r/w-acc x/d-acc
                           wp smep smap ac nxe r-w-x-1 cpl x86))))
  :hints (("Goal"
           :use ((:instance r-w-x-is-irrelevant-for-mv-nth-1-ia32e-la-to-pa-page-table-when-no-errors
                            (lin-addr (logext 48 lin-addr))
                            (base-addr (ash
                                        (loghead
                                         40
                                         (logtail
                                          12
                                          (rm-low-64 (page-directory-entry-addr (logext 48 lin-addr)
                                                                                (logand 18446744073709547520
                                                                                        (loghead 52 base-addr)))
                                                     x86)))
                                        12))
                            (u/s-acc (logand
                                      u/s-acc
                                      (page-user-supervisor
                                       (rm-low-64 (page-directory-entry-addr (logext 48 lin-addr)
                                                                             (logand 18446744073709547520
                                                                                     (loghead 52 base-addr)))
                                                  x86))))
                            (r/w-acc (logand
                                      r/w-acc
                                      (page-read-write
                                       (rm-low-64 (page-directory-entry-addr (logext 48 lin-addr)
                                                                             (logand 18446744073709547520
                                                                                     (loghead 52 base-addr)))
                                                  x86))))
                            (x/d-acc
                             (logand
                              x/d-acc
                              (page-execute-disable
                               (rm-low-64 (page-directory-entry-addr (logext 48 lin-addr)
                                                                     (logand 18446744073709547520
                                                                             (loghead 52 base-addr)))
                                          x86))))))
           :do-not-induct t
           :in-theory (e/d* (disjoint-p
                             member-p
                             ia32e-la-to-pa-page-directory)
                            (bitops::logand-with-negated-bitmask
                             (:meta acl2::mv-nth-cons-meta)
                             force (force))))))

(defthmd r-w-x-is-irrelevant-for-mv-nth-1-ia32e-la-to-pa-page-dir-ptr-table-when-no-errors
  (implies (and (not (mv-nth 0
                             (ia32e-la-to-pa-page-dir-ptr-table
                              lin-addr base-addr u/s-acc r/w-acc x/d-acc
                              wp smep smap ac nxe r-w-x-1 cpl x86)))
                (syntaxp (not (eq r-w-x-2 r-w-x-1)))
                (not (mv-nth 0
                             (ia32e-la-to-pa-page-dir-ptr-table
                              lin-addr base-addr u/s-acc r/w-acc x/d-acc
                              wp smep smap ac nxe r-w-x-2 cpl x86))))
           (equal (mv-nth 1
                          (ia32e-la-to-pa-page-dir-ptr-table
                           lin-addr base-addr u/s-acc r/w-acc x/d-acc
                           wp smep smap ac nxe r-w-x-2 cpl x86))
                  (mv-nth 1
                          (ia32e-la-to-pa-page-dir-ptr-table
                           lin-addr base-addr u/s-acc r/w-acc x/d-acc
                           wp smep smap ac nxe r-w-x-1 cpl x86))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance r-w-x-is-irrelevant-for-mv-nth-1-ia32e-la-to-pa-page-directory-when-no-errors
                            (lin-addr (logext 48 lin-addr))
                            (base-addr (ash
                                        (loghead
                                         40
                                         (logtail
                                          12
                                          (rm-low-64 (page-dir-ptr-table-entry-addr (logext 48 lin-addr)
                                                                                    (logand 18446744073709547520
                                                                                            (loghead 52 base-addr)))
                                                     x86)))
                                        12))
                            (u/s-acc (logand
                                      u/s-acc
                                      (page-user-supervisor
                                       (rm-low-64 (page-dir-ptr-table-entry-addr (logext 48 lin-addr)
                                                                                 (logand 18446744073709547520
                                                                                         (loghead 52 base-addr)))
                                                  x86))))
                            (r/w-acc (logand
                                      r/w-acc
                                      (page-read-write
                                       (rm-low-64 (page-dir-ptr-table-entry-addr (logext 48 lin-addr)
                                                                                 (logand 18446744073709547520
                                                                                         (loghead 52 base-addr)))
                                                  x86))))
                            (x/d-acc
                             (logand
                              x/d-acc
                              (page-execute-disable
                               (rm-low-64 (page-dir-ptr-table-entry-addr (logext 48 lin-addr)
                                                                         (logand 18446744073709547520
                                                                                 (loghead 52 base-addr)))
                                          x86))))))
           :in-theory (e/d* (disjoint-p
                             member-p
                             ia32e-la-to-pa-page-dir-ptr-table)
                            (r-w-x-is-irrelevant-for-mv-nth-1-ia32e-la-to-pa-page-table-when-no-errors
                             bitops::logand-with-negated-bitmask
                             (:meta acl2::mv-nth-cons-meta)
                             force (force))))))

(defthmd r-w-x-is-irrelevant-for-mv-nth-1-ia32e-la-to-pa-pml4-table-when-no-errors
  (implies (and (not (mv-nth 0
                             (ia32e-la-to-pa-pml4-table
                              lin-addr base-addr wp smep smap ac nxe r-w-x-1 cpl x86)))
                (syntaxp (not (eq r-w-x-2 r-w-x-1)))
                (not (mv-nth 0
                             (ia32e-la-to-pa-pml4-table
                              lin-addr base-addr wp smep smap ac nxe r-w-x-2 cpl x86))))
           (equal (mv-nth 1
                          (ia32e-la-to-pa-pml4-table
                           lin-addr base-addr wp smep smap ac nxe r-w-x-2 cpl x86))
                  (mv-nth 1
                          (ia32e-la-to-pa-pml4-table
                           lin-addr base-addr wp smep smap ac nxe r-w-x-1 cpl x86))))
  :hints (("Goal"
           :use ((:instance r-w-x-is-irrelevant-for-mv-nth-1-ia32e-la-to-pa-page-dir-ptr-table-when-no-errors
                            (lin-addr (logext 48 lin-addr))
                            (base-addr (ash
                                        (loghead
                                         40
                                         (logtail
                                          12
                                          (rm-low-64 (pml4-table-entry-addr (logext 48 lin-addr)
                                                                            (logand 18446744073709547520
                                                                                    (loghead 52 base-addr)))
                                                     x86)))
                                        12))
                            (u/s-acc (page-user-supervisor
                                      (rm-low-64 (pml4-table-entry-addr (logext 48 lin-addr)
                                                                        (logand 18446744073709547520
                                                                                (loghead 52 base-addr)))
                                                 x86)))
                            (r/w-acc (page-read-write
                                      (rm-low-64 (pml4-table-entry-addr (logext 48 lin-addr)
                                                                        (logand 18446744073709547520
                                                                                (loghead 52 base-addr)))
                                                 x86)))
                            (x/d-acc
                             (page-execute-disable
                              (rm-low-64 (pml4-table-entry-addr (logext 48 lin-addr)
                                                                (logand 18446744073709547520
                                                                        (loghead 52 base-addr)))
                                         x86)))))
           :do-not-induct t
           :in-theory (e/d* (disjoint-p
                             member-p
                             ia32e-la-to-pa-pml4-table)
                            (bitops::logand-with-negated-bitmask
                             (:meta acl2::mv-nth-cons-meta)
                             force (force))))))

(defun find-almost-matching-ia32e-la-to-pas-aux (free-r-w-x-var new-arg-lists original-arg-list)
  (if (endp new-arg-lists)
      nil
    (b* ((new-arg-list (car new-arg-lists))
         (matching? (and (equal (first new-arg-list)  (first original-arg-list)) ;; lin-addr
                         (not (equal (second new-arg-list) (second original-arg-list))) ;; r-w-x
                         (equal (third new-arg-list)  (third original-arg-list)) ;; cpl
                         (equal (fourth new-arg-list) (fourth original-arg-list))))) ;; x86
      (if matching?
          (cons (acons free-r-w-x-var ;; original r-w-x
                       (second new-arg-list)
                       nil)
                (find-almost-matching-ia32e-la-to-pas-aux free-r-w-x-var (cdr new-arg-lists) original-arg-list))
        (find-almost-matching-ia32e-la-to-pas-aux free-r-w-x-var (cdr new-arg-lists) original-arg-list)))))

(defun find-almost-matching-ia32e-la-to-pas
  (fn-name free-r-w-x-var original-arg-list mfc state)
  (declare (xargs :stobjs (state) :mode :program)
           (ignorable state))
  (b* ((calls (acl2::find-calls-lst fn-name (acl2::mfc-clause mfc)))
       ((when (not calls))
        ;; ia32e-la-to-pa term not encountered.
        nil)
       (new-arg-lists (strip-cdrs calls)))
    (find-almost-matching-ia32e-la-to-pas-aux free-r-w-x-var new-arg-lists original-arg-list)))

(defthm r-w-x-is-irrelevant-for-mv-nth-1-ia32e-la-to-pa-when-no-errors
  (implies (and (bind-free (find-almost-matching-ia32e-la-to-pas
                            'ia32e-la-to-pa 'r-w-x-1
                            (list lin-addr r-w-x-2 cpl x86) mfc state)
                           (r-w-x-1))
                (syntaxp (and
                          ;; The bind-free ensures that r-w-x-2 and
                          ;; r-w-x-1 are unequal, but I'll still leave
                          ;; this thing in.
                          (not (eq r-w-x-2 r-w-x-1))
                          ;; r-w-x-2 must be smaller than r-w-x-1.
                          (term-order r-w-x-2 r-w-x-1)))
                (not (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x-1 cpl x86)))
                (not (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x-2 cpl x86))))
           (equal (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x-2 cpl x86))
                  (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x-1 cpl x86))))
  :hints (("Goal"
           :use ((:instance r-w-x-is-irrelevant-for-mv-nth-1-ia32e-la-to-pa-pml4-table-when-no-errors
                            (lin-addr (logext 48 lin-addr))
                            (base-addr (ash (loghead 40 (logtail 12 (xr :ctr *cr3* x86))) 12))
                            (wp (bool->bit (logbitp 16 (xr :ctr *cr0* x86))))
                            (smep (loghead 1 (bool->bit (logbitp 20 (xr :ctr *cr4* x86)))))
                            (smap 0)
                            (ac (bool->bit (logbitp 18 (xr :rflags 0 x86))))
                            (nxe (loghead 1 (bool->bit (logbitp 11 (xr :msr *ia32_efer-idx* x86)))))))
           :in-theory (e/d* (ia32e-la-to-pa) ()))))

(defthm r-w-x-is-irrelevant-for-mv-nth-1-las-to-pas-when-no-errors
  (implies (and (bind-free (find-almost-matching-ia32e-la-to-pas
                            'las-to-pas 'r-w-x-1 (list l-addrs r-w-x-2 cpl x86) mfc state)
                           (r-w-x-1))
                (syntaxp (and
                          ;; The bind-free ensures that r-w-x-2 and
                          ;; r-w-x-1 are unequal, but I'll still leave
                          ;; this thing in.
                          (not (eq r-w-x-2 r-w-x-1))
                          ;; r-w-x-2 must be smaller than r-w-x-1.
                          (term-order r-w-x-2 r-w-x-1)))
                (not (mv-nth 0 (las-to-pas l-addrs r-w-x-1 cpl x86)))
                (not (mv-nth 0 (las-to-pas l-addrs r-w-x-2 cpl x86)))
                (not (page-structure-marking-mode x86)))
           (equal (mv-nth 1 (las-to-pas l-addrs r-w-x-2 cpl x86))
                  (mv-nth 1 (las-to-pas l-addrs r-w-x-1 cpl x86))))
  :hints (("Goal" :in-theory (e/d* (r-w-x-is-irrelevant-for-mv-nth-1-ia32e-la-to-pa-when-no-errors)
                                   ()))))

(defthmd las-to-pas-subset-p
  ;; This is a pretty expensive rule --- a more general version of
  ;; las-to-pas-subset-p-with-l-addrs-from-bind-free.
  (implies (and (bind-free
                 (find-l-addrs-from-fn 'las-to-pas 'l-addrs mfc state)
                 (l-addrs))
                (syntaxp (not (eq l-addrs-subset l-addrs)))
                (subset-p l-addrs-subset l-addrs)
                (not (mv-nth 0 (las-to-pas l-addrs r-w-x cpl x86)))
                (not (page-structure-marking-mode x86)))
           (equal (mv-nth 0 (las-to-pas l-addrs-subset r-w-x cpl x86))
                  nil))
  :hints (("Goal" :in-theory (e/d* (subset-p) ()))))

(defthm las-to-pas-subset-p-with-l-addrs-from-bind-free
  ;; This rule will help in fetching instructions.
  (implies (and (bind-free
                 (find-l-addrs-from-fn 'program-at 'l-addrs mfc state)
                 (l-addrs))
                (syntaxp (not (eq l-addrs-subset l-addrs)))
                (not (mv-nth 0 (las-to-pas l-addrs r-w-x cpl x86)))
                (subset-p l-addrs-subset l-addrs)
                (not (page-structure-marking-mode x86)))
           (equal (mv-nth 0 (las-to-pas l-addrs-subset r-w-x cpl x86))
                  nil))
  :hints (("Goal" :in-theory (e/d* (subset-p) ()))))

;; ======================================================================

;; Lemmas about memory reads:

(defthm read-from-physical-memory-and-mv-nth-2-ia32e-la-to-pa
  (implies (not (page-structure-marking-mode x86))
           (equal (read-from-physical-memory p-addrs (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x cpl x86)))
                  (read-from-physical-memory p-addrs x86)))
  :hints (("Goal" :in-theory (e/d* () (force (force))))))

(defthmd rm08-in-terms-of-nth-pos-and-rb-in-system-level-non-marking-mode
  (implies (and (not (mv-nth 0 (las-to-pas l-addrs r-w-x (cpl x86) x86)))
                (member-p addr l-addrs)
                (canonical-address-listp l-addrs)
                (equal bytes (mv-nth 1 (rb l-addrs r-w-x x86)))
                (not (mv-nth 0 (rm08 addr r-w-x x86)))
                (not (programmer-level-mode x86))
                (not (page-structure-marking-mode x86))
                (x86p x86))
           (equal (mv-nth 1 (rm08 addr r-w-x x86))
                  (nth (pos addr l-addrs) bytes)))
  :hints (("Goal" :in-theory (e/d (pos rm08 member-p)
                                  (signed-byte-p
                                   (:meta acl2::mv-nth-cons-meta))))))

(local
 (defthmd rb-in-terms-of-nth-and-pos-in-system-level-non-marking-mode-helper
   (implies
    (and (signed-byte-p 48 lin-addr)
         (not (mv-nth 0 (rb (list lin-addr) :x x86)))
         (not (xr :programmer-level-mode 0 x86))
         (not (xr :page-structure-marking-mode 0 x86))
         (x86p x86))
    (equal (car (mv-nth 1 (rb (list lin-addr) :x x86)))
           (combine-bytes (mv-nth 1 (rb (list lin-addr) :x x86)))))
   :hints (("Goal" :in-theory (e/d* () ((:meta acl2::mv-nth-cons-meta)))))))

(defun find-info-from-program-at-term (thm mfc state)
  (declare (xargs :stobjs (state) :mode :program)
           (ignorable thm state))
  (b* ((call (acl2::find-call-lst 'program-at (acl2::mfc-clause mfc)))
       ((when (not call))
        ;; (cw "~%~p0: Program-At term not encountered.~%" thm)
        nil)
       (addresses (cadr call))
       ((when (not (equal (car addresses)
                          'create-canonical-address-list)))
        ;; (cw "~%~p0: Program-At without Create-Canonical-Address-List encountered.~%" thm)
        nil)
       (n (cadr addresses))
       (prog-addr (caddr addresses))
       (bytes (caddr call)))
    `((n . ,n)
      (prog-addr . ,prog-addr)
      (bytes . ,bytes))))

(defthm rb-in-terms-of-nth-and-pos-in-system-level-non-marking-mode
  (implies (and (bind-free
                 (find-info-from-program-at-term
                  'rb-in-terms-of-nth-and-pos-in-system-level-non-marking-mode
                  mfc state)
                 (n prog-addr bytes))
                (program-at (create-canonical-address-list n prog-addr) bytes x86)
                (member-p lin-addr (create-canonical-address-list n prog-addr))
                (syntaxp (quotep n))
                (not (mv-nth 0 (ia32e-la-to-pa lin-addr :x (cpl x86) x86)))
                ;; (not (mv-nth 0 (rb (list lin-addr) :x x86)))
                (not (programmer-level-mode x86))
                (not (page-structure-marking-mode x86))
                (x86p x86))
           (equal (car (mv-nth 1 (rb (list lin-addr) :x x86)))
                  (nth (pos lin-addr (create-canonical-address-list n prog-addr)) bytes)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (program-at
                            rb-in-terms-of-nth-and-pos-in-system-level-non-marking-mode-helper)
                           (acl2::mv-nth-cons-meta
                            rm08-to-rb
                            member-p-canonical-address-p-canonical-address-listp))
           :use ((:instance rm08-to-rb
                            (r-w-x :x))
                 (:instance member-p-canonical-address-p-canonical-address-listp
                            (e lin-addr))
                 (:instance rm08-in-terms-of-nth-pos-and-rb-in-system-level-non-marking-mode
                            (addr lin-addr)
                            (r-w-x :x)
                            (l-addrs (create-canonical-address-list n prog-addr)))))))

(defthmd rb-unwinding-thm-in-system-level-non-marking-mode
  (implies (and (consp l-addrs)
                (not (mv-nth 0 (rb l-addrs r-w-x x86)))
                (not (page-structure-marking-mode x86)))
           (equal (mv-nth 1 (rb l-addrs r-w-x x86))
                  (cons (car (mv-nth 1 (rb (list (car l-addrs)) r-w-x x86)))
                        (mv-nth 1 (rb (cdr l-addrs) r-w-x x86)))))
  :hints (("Goal" :in-theory (e/d (rb append) (acl2::mv-nth-cons-meta force (force))))))

(defthmd rb-unwinding-thm-in-system-level-non-marking-mode-for-errors
  (implies (and (subset-p l-addrs-subset l-addrs)
                (consp l-addrs)
                (not (mv-nth 0 (rb l-addrs r-w-x x86)))
                (not (page-structure-marking-mode x86)))
           (equal (mv-nth 0 (rb l-addrs-subset r-w-x x86))
                  nil))
  :hints (("Goal" :in-theory (e/d (subset-p) (acl2::mv-nth-cons-meta force (force))))))

(defthm rb-in-terms-of-rb-subset-p-in-system-level-non-marking-mode
  (implies
   (and (bind-free
         (find-info-from-program-at-term
          'rb-in-terms-of-rb-subset-p-in-system-level-non-marking-mode
          mfc state)
         (n prog-addr bytes))
        (program-at (create-canonical-address-list n prog-addr) bytes x86)
        (subset-p l-addrs (create-canonical-address-list n prog-addr))
        (syntaxp (quotep n))
        (consp l-addrs)
        ;; (not (mv-nth 0 (rb l-addrs :x x86)))
        (not (mv-nth 0 (las-to-pas l-addrs :x (cpl x86) x86)))
        (not (programmer-level-mode x86))
        (not (page-structure-marking-mode x86))
        (x86p x86))
   (equal (mv-nth 1 (rb l-addrs :x x86))
          (append (list (nth (pos
                              (car l-addrs)
                              (create-canonical-address-list n prog-addr))
                             bytes))
                  (mv-nth 1 (rb (cdr l-addrs) :x x86)))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (subset-p
                            member-p)
                           (rb
                            canonical-address-p
                            acl2::mv-nth-cons-meta
                            rb-in-terms-of-nth-and-pos-in-system-level-non-marking-mode))
           :use ((:instance rb-in-terms-of-nth-and-pos-in-system-level-non-marking-mode
                            (lin-addr (car l-addrs)))
                 (:instance rb-unwinding-thm-in-system-level-non-marking-mode
                            (r-w-x :x))
                 (:instance rb-unwinding-thm-in-system-level-non-marking-mode-for-errors
                            (r-w-x :x)
                            (l-addrs-subset (list (car l-addrs))))))))

(defthm combine-bytes-rb-in-terms-of-rb-subset-p-in-system-level-non-marking-mode
  (implies
   (and (bind-free
         (find-info-from-program-at-term
          'combine-bytes-rb-in-terms-of-rb-subset-p-in-system-level-non-marking-mode
          mfc state)
         (n prog-addr bytes))
        (program-at (create-canonical-address-list n prog-addr) bytes x86)
        (subset-p l-addrs (create-canonical-address-list n prog-addr))
        (syntaxp (quotep n))
        (consp l-addrs)
        ;; (not (mv-nth 0 (rb l-addrs :x x86)))
        (not (mv-nth 0 (las-to-pas l-addrs :x (cpl x86) x86)))
        (not (programmer-level-mode x86))
        (not (page-structure-marking-mode x86))
        (x86p x86))
   (equal (combine-bytes (mv-nth 1 (rb l-addrs :x x86)))
          (combine-bytes
           (append (list (nth (pos
                               (car l-addrs)
                               (create-canonical-address-list n prog-addr))
                              bytes))
                   (mv-nth 1 (rb (cdr l-addrs) :x x86))))))
  :hints (("Goal" :in-theory (union-theories
                              '()
                              (theory 'minimal-theory))
           :use ((:instance rb-in-terms-of-rb-subset-p-in-system-level-non-marking-mode)))))

(defthm unsigned-byte-p-of-combine-bytes-and-rb-in-system-level-mode
  (implies (and (syntaxp (quotep m))
                (syntaxp (quotep n))
                (equal m (ash n 3))
                (natp n)
                (not (mv-nth 0 (las-to-pas (create-canonical-address-list n lin-addr) r-w-x (cpl x86) x86)))
                (canonical-address-p (+ -1 n lin-addr))
                (canonical-address-p lin-addr)
                (not (xr :programmer-level-mode 0 x86))
                (x86p x86))
           (unsigned-byte-p
            m
            (combine-bytes (mv-nth 1 (rb (create-canonical-address-list n lin-addr) r-w-x x86)))))
  :hints (("Goal" :in-theory (e/d* () (rb)))))

;; ======================================================================

;; Lemmas about memory writes:

(defthm xr-mem-wb-in-system-level-mode
  (implies (and (not (mv-nth 0 (las-to-pas (strip-cars addr-lst) :w (cpl x86) x86)))
                (disjoint-p (list index)
                            (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w (cpl x86) x86)))
                (not (page-structure-marking-mode x86))
                (not (programmer-level-mode x86)))
           (equal (xr :mem index (mv-nth 1 (wb addr-lst x86)))
                  (xr :mem index x86)))
  :hints (("Goal" :in-theory (e/d* (wb disjoint-p member-p)
                                   (write-to-physical-memory
                                    (:meta acl2::mv-nth-cons-meta)
                                    force (force))))))

(defun-nx wb-duplicate-writes-induct (addr-list x86)
  (if (endp addr-list)
      nil
    (if (member-p (car (car addr-list)) (strip-cars (cdr addr-list)))
        (wb-duplicate-writes-induct (cdr addr-list) x86)
      (wb-duplicate-writes-induct
       (cdr addr-list)
       (mv-nth 1 (wb (list (car addr-list)) x86))))))

(local
 (defthm strip-cars-of-remove-duplicate-keys-is-remove-duplicates-equal-of-strip-cars
   (implies (alistp alst)
            (equal (strip-cars (remove-duplicate-keys alst))
                   (remove-duplicates-equal (strip-cars alst))))))

(defthm remove-duplicate-keys-mv-nth-0-las-to-pas
  (implies (and (canonical-address-listp l-addrs)
                (not (mv-nth 0 (las-to-pas l-addrs r-w-x cpl x86)))
                (not (page-structure-marking-mode x86)))
           (equal (mv-nth 0 (las-to-pas (remove-duplicates-equal l-addrs) r-w-x cpl x86))
                  (mv-nth 0 (las-to-pas l-addrs r-w-x cpl x86))))
  :hints (("Goal" :induct (las-to-pas (remove-duplicates-equal l-addrs) r-w-x cpl x86))))

(local
 (defthmd write-to-physical-memory-xw-mem-member-p-helper
   (implies (equal (write-to-physical-memory (cdr p-addrs)
                                             (cdr bytes)
                                             (xw :mem index byte
                                                 (xw :mem (car p-addrs)
                                                     (car bytes)
                                                     x86)))
                   (write-to-physical-memory (cdr p-addrs)
                                             (cdr bytes)
                                             (xw :mem (car p-addrs)
                                                 (car bytes)
                                                 x86)))
            (equal (write-to-physical-memory (cdr p-addrs)
                                             (cdr bytes)
                                             (xw :mem (car p-addrs)
                                                 (car bytes)
                                                 (xw :mem index byte x86)))
                   (write-to-physical-memory (cdr p-addrs)
                                             (cdr bytes)
                                             (xw :mem (car p-addrs)
                                                 (car bytes)
                                                 x86))))
   :hints (("Goal" :cases ((equal index (car p-addrs)))))))

(defthm write-to-physical-memory-xw-mem-member-p
  (implies (member-p index p-addrs)
           (equal (write-to-physical-memory p-addrs bytes (xw :mem index byte x86))
                  (write-to-physical-memory p-addrs bytes x86)))
  :hints (("Goal" :in-theory (e/d* (member-p write-to-physical-memory-xw-mem-member-p-helper) ()))))

(defthm member-p-and-remove-duplicates-equal
  (equal (member-p e (remove-duplicates-equal x))
         (member-p e x))
  :hints (("Goal" :in-theory (e/d* (member-p) ()))))

(defthm canonical-address-listp-and-remove-duplicates-equal
  (implies (canonical-address-listp x)
           (canonical-address-listp (remove-duplicates-equal x))))

(defthm all-translation-governing-addresses-remove-duplicates-equal-and-subset-p
  (subset-p (all-translation-governing-addresses (remove-duplicates-equal l-addrs) x86)
            (all-translation-governing-addresses l-addrs x86))
  :hints (("Goal" :in-theory (e/d* (subset-p) (translation-governing-addresses)))))

(defthm member-p-of-all-translation-governing-addresses-and-remove-duplicates-equal
  (implies (not (member-p addr (all-translation-governing-addresses l-addrs x86)))
           (not (member-p addr (all-translation-governing-addresses (remove-duplicates-equal l-addrs) x86)))))

(defthm wb-remove-duplicate-writes-in-system-level-non-marking-mode
  (implies (and (syntaxp (not (and (consp addr-lst)
                                   (eq (car addr-lst) 'remove-duplicate-keys))))
                (disjoint-p
                 ;; Physical addresses corresponding to (strip-cars
                 ;; addr-lst) are disjoint from the
                 ;; translation-governing addresses.
                 (all-translation-governing-addresses (strip-cars addr-lst)  x86)
                 (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w (cpl x86) x86)))
                (addr-byte-alistp addr-lst)
                ;; (not (mv-nth 0 (wb addr-lst x86)))
                (not (mv-nth 0 (las-to-pas (strip-cars addr-lst) :w (cpl x86) x86)))
                (not (programmer-level-mode x86))
                (not (page-structure-marking-mode x86)))
           (equal (wb addr-lst x86)
                  ;; TO-DO: I need to replace remove-duplicate-keys
                  ;; with remove-duplicate-phy-addresses or something
                  ;; like that.
                  (wb (remove-duplicate-keys addr-lst) x86)))
  :hints (("Goal" :do-not '(generalize)
           :in-theory (e/d (disjoint-p member-p subset-p)
                           (acl2::mv-nth-cons-meta
                            translation-governing-addresses))
           :induct (wb-duplicate-writes-induct addr-lst x86))))

;; ======================================================================

;; Lemmas about interaction of writes and paging walkers:

(defthm rm-low-32-wb-in-system-level-mode-disjoint
  (implies (and (not (mv-nth 0 (las-to-pas (strip-cars addr-lst) :w (cpl x86) x86)))
                (disjoint-p (addr-range 4 index)
                            (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w (cpl x86) x86)))
                (not (page-structure-marking-mode x86)))
           (equal (rm-low-32 index (mv-nth 1 (wb addr-lst x86)))
                  (rm-low-32 index x86)))
  :hints (("Goal" :in-theory (e/d* (rm-low-32 disjoint-p member-p)
                                   (write-to-physical-memory
                                    (:meta acl2::mv-nth-cons-meta)
                                    force (force))))))

(local
 (defthmd open-addr-range-8
   (implies (integerp x)
            (equal (addr-range 8 x)
                   (list x (+ 1 x) (+ 2 x) (+ 3 x)
                         (+ 4 x) (+ 5 x) (+ 6 x) (+ 7 x))))))

(defthm rm-low-64-wb-in-system-level-mode-disjoint
  (implies (and (not (mv-nth 0 (las-to-pas (strip-cars addr-lst) :w (cpl x86) x86)))
                (disjoint-p (addr-range 8 index)
                            (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w (cpl x86) x86)))
                (not (page-structure-marking-mode x86))
                (integerp index))
           (equal (rm-low-64 index (mv-nth 1 (wb addr-lst x86)))
                  (rm-low-64 index x86)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (rm-low-64
                             disjoint-p
                             open-addr-range-8)
                            (wb
                             (:meta acl2::mv-nth-cons-meta)
                             force (force))))))

(defthm rm-low-64-and-write-to-physical-memory-disjoint
  (implies (disjoint-p (addr-range 8 p-addr-1) p-addrs-2)
           (equal (rm-low-64 p-addr-1 (write-to-physical-memory p-addrs-2 bytes x86))
                  (rm-low-64 p-addr-1 x86)))
  :hints (("Goal" :in-theory (e/d* (rm-low-64 rm-low-32 disjoint-p)
                                   (force (force))))))

(defthm xr-mem-write-to-physical-memory-member
  (implies (and (member-p index p-addrs)
                (no-duplicates-p p-addrs))
           (equal (xr :mem index (write-to-physical-memory p-addrs bytes x86))
                  (nth (pos index p-addrs) bytes)))
  :hints (("Goal" :in-theory (e/d* (member-p pos) (force (force))))))

(local
 (defthm nth-0-xs
   (equal (nth 0 xs) (car xs))))

(local
 (defthmd rm-low-64-and-write-to-physical-memory-equal-helper-1
   (implies (and (byte-listp bytes)
                 (equal (len bytes) 8))
            (equal (combine-bytes (cdddr (cddddr bytes)))
                   (car (cdddr (cddddr bytes)))))))

(def-gl-export rm-low-64-and-write-to-physical-memory-equal-helper-2
  :hyp (and (n08p a) (n08p b) (n08p c) (n08p d)
            (n08p e) (n08p f) (n08p g) (n08p h))
  :concl (equal
          (logior (ash b 8)
                  (ash (logior (ash d 8)
                               c)
                       16)
                  (ash (logior (ash f 8)
                               (ash (logior (ash h 8)
                                            g)
                                    16)
                               e)
                       32)
                  a)
          (logior
           a
           (ash
            (logior
             b
             (ash
              (logior
               c
               (ash
                (logior
                 d
                 (ash
                  (logior e
                          (ash (logior f
                                       (ash (logior g
                                                    (ash h 8))
                                            8))
                               8))
                  8))
                8))
              8))
            8)))
  :g-bindings
  (gl::auto-bindings
   (:mix (:nat a 8) (:nat b 8) (:nat c 8) (:nat d 8)
         (:nat e 8) (:nat f 8) (:nat g 8) (:nat h 8))))

(in-theory (e/d () (rm-low-64-and-write-to-physical-memory-equal-helper-2)))

(defthm rm-low-64-and-write-to-physical-memory-equal
  (implies (and (equal p-addrs-2 (addr-range 8 p-addr-1))
                (equal (len bytes) (len p-addrs-2))
                (byte-listp bytes)
                (not (programmer-level-mode x86)))
           (equal (rm-low-64 p-addr-1 (write-to-physical-memory p-addrs-2 bytes x86))
                  (combine-bytes bytes)))
  :hints (("Goal"
           :do-not '(preprocess)
           :do-not-induct t
           :use ((:instance rm-low-64-and-write-to-physical-memory-equal-helper-1))
           :in-theory (e/d* (rm-low-64
                             rm-low-32 member-p
                             rm-low-64-and-write-to-physical-memory-equal-helper-2)
                            (write-to-physical-memory
                             nth
                             force
                             (force)
                             rm32-rb-system-level-mode-proof-helper
                             member-p-cons
                             acl2::commutativity-of-logior
                             acl2::cdr-of-repeat-increment
                             mv-nth-2-rcl-spec-16
                             write-to-physical-memory-xw-mem-member-p
                             (:linear bitops::logior-<-0-linear-2)
                             (:type-prescription bitops::logior-natp-type)
                             (:linear ash-monotone-2)
                             x86isa::combining-logior-of-loghead-and-ash-logtail
                             (:rewrite acl2::zip-open))))))

(defthm ia32e-la-to-pa-values-and-write-to-physical-memory-disjoint
  (implies (and (disjoint-p p-addrs (translation-governing-addresses lin-addr x86))
                (physical-address-listp p-addrs)
                (canonical-address-p lin-addr))
           (and (equal (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x cpl (write-to-physical-memory p-addrs bytes x86)))
                       (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x cpl x86)))
                (equal (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x cpl (write-to-physical-memory p-addrs bytes x86)))
                       (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x cpl x86)))))
  :hints (("Goal"
           :induct (write-to-physical-memory p-addrs bytes x86)
           :in-theory (e/d* (disjoint-p) (translation-governing-addresses)))))

(defthm las-to-pas-values-and-write-to-physical-memory-disjoint
  (implies (and (disjoint-p (all-translation-governing-addresses l-addrs x86) p-addrs)
                (physical-address-listp p-addrs)
                (canonical-address-listp l-addrs)
                (not (page-structure-marking-mode x86)))
           (and (equal (mv-nth 0 (las-to-pas l-addrs r-w-x cpl (write-to-physical-memory p-addrs bytes x86)))
                       (mv-nth 0 (las-to-pas l-addrs r-w-x cpl x86)))
                (equal (mv-nth 1 (las-to-pas l-addrs r-w-x cpl (write-to-physical-memory p-addrs bytes x86)))
                       (mv-nth 1 (las-to-pas l-addrs r-w-x cpl x86)))))
  :hints (("Goal" :induct (las-to-pas l-addrs r-w-x cpl x86)
           :in-theory (e/d* (disjoint-p disjoint-p-commutative) (translation-governing-addresses)))))

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

(defthm ia32e-la-to-pa-page-table-values-and-write-to-translation-governing-address
  ;; Similar lemmas can be found in proofs/zero-copy/zero-copy.lisp.
  (b* ((p-addrs (translation-governing-addresses-for-page-table lin-addr base-addr x86))
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
                             translation-governing-addresses-for-page-table)
                            (wb
                             bitops::logand-with-negated-bitmask
                             (:meta acl2::mv-nth-cons-meta)
                             force (force))))))

(defthm mv-nth-0-paging-entry-no-page-fault-p-and-mv-nth-1-wb
  (equal (mv-nth 0
                 (paging-entry-no-page-fault-p
                  structure-type lin-addr
                  entry u/s-acc r/w-acc x/d-acc wp
                  smep smap ac nxe r-w-x cpl
                  (mv-nth 1 (wb addr-lst x86))
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

(defthm ia32e-la-to-pa-page-table-values-and-mv-nth-1-wb-disjoint-from-xlation-gov-addrs
  (implies (and (equal cpl (cpl x86))
                (not (mv-nth 0 (las-to-pas (strip-cars addr-lst) :w cpl x86)))
                (disjoint-p
                 (translation-governing-addresses-for-page-table lin-addr base-addr x86)
                 (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w cpl x86)))
                (not (page-structure-marking-mode x86))
                (canonical-address-p lin-addr)
                (physical-address-p base-addr)
                (equal (loghead 12 base-addr) 0))
           (and
            (equal (mv-nth 0
                           (ia32e-la-to-pa-page-table
                            lin-addr base-addr u/s-acc r/w-acc x/d-acc
                            wp smep smap ac nxe r-w-x cpl (mv-nth 1 (wb addr-lst x86))))
                   (mv-nth 0
                           (ia32e-la-to-pa-page-table
                            lin-addr base-addr u/s-acc r/w-acc x/d-acc
                            wp smep smap ac nxe r-w-x cpl x86)))
            (equal (mv-nth 1
                           (ia32e-la-to-pa-page-table
                            lin-addr base-addr u/s-acc r/w-acc x/d-acc
                            wp smep smap ac nxe r-w-x cpl (mv-nth 1 (wb addr-lst x86))))
                   (mv-nth 1
                           (ia32e-la-to-pa-page-table
                            lin-addr base-addr u/s-acc r/w-acc x/d-acc
                            wp smep smap ac nxe r-w-x cpl x86)))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (disjoint-p
                             member-p
                             ia32e-la-to-pa-page-table
                             translation-governing-addresses-for-page-table)
                            (wb
                             bitops::logand-with-negated-bitmask
                             (:meta acl2::mv-nth-cons-meta)
                             force (force))))))

(defthm ia32e-la-to-pa-page-directory-values-and-mv-nth-1-wb-disjoint-from-xlation-gov-addrs
  (implies (and (equal cpl (cpl x86))
                (not (mv-nth 0 (las-to-pas (strip-cars addr-lst) :w cpl x86)))
                (disjoint-p
                 (translation-governing-addresses-for-page-directory lin-addr base-addr x86)
                 (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w cpl x86)))
                (not (page-structure-marking-mode x86))
                (canonical-address-p lin-addr)
                (physical-address-p base-addr)
                (equal (loghead 12 base-addr) 0))
           (and
            (equal (mv-nth 0
                           (ia32e-la-to-pa-page-directory
                            lin-addr base-addr u/s-acc r/w-acc x/d-acc
                            wp smep smap ac nxe r-w-x cpl (mv-nth 1 (wb addr-lst x86))))
                   (mv-nth 0
                           (ia32e-la-to-pa-page-directory
                            lin-addr base-addr u/s-acc r/w-acc x/d-acc
                            wp smep smap ac nxe r-w-x cpl x86)))
            (equal (mv-nth 1
                           (ia32e-la-to-pa-page-directory
                            lin-addr base-addr u/s-acc r/w-acc x/d-acc
                            wp smep smap ac nxe r-w-x cpl (mv-nth 1 (wb addr-lst x86))))
                   (mv-nth 1
                           (ia32e-la-to-pa-page-directory
                            lin-addr base-addr u/s-acc r/w-acc x/d-acc
                            wp smep smap ac nxe r-w-x cpl x86)))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (disjoint-p
                             member-p
                             ia32e-la-to-pa-page-directory
                             translation-governing-addresses-for-page-directory)
                            (wb
                             translation-governing-addresses-for-page-table
                             bitops::logand-with-negated-bitmask
                             (:meta acl2::mv-nth-cons-meta)
                             force (force))))))

(defthm ia32e-la-to-pa-page-dir-ptr-table-values-and-mv-nth-1-wb-disjoint-from-xlation-gov-addrs
  (implies (and (equal cpl (cpl x86))
                (not (mv-nth 0 (las-to-pas (strip-cars addr-lst) :w cpl x86)))
                (disjoint-p
                 (translation-governing-addresses-for-page-dir-ptr-table lin-addr base-addr x86)
                 (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w cpl x86)))
                (not (page-structure-marking-mode x86))
                (canonical-address-p lin-addr)
                (physical-address-p base-addr)
                (equal (loghead 12 base-addr) 0))
           (and
            (equal (mv-nth 0
                           (ia32e-la-to-pa-page-dir-ptr-table
                            lin-addr base-addr u/s-acc r/w-acc x/d-acc
                            wp smep smap ac nxe r-w-x cpl (mv-nth 1 (wb addr-lst x86))))
                   (mv-nth 0
                           (ia32e-la-to-pa-page-dir-ptr-table
                            lin-addr base-addr u/s-acc r/w-acc x/d-acc
                            wp smep smap ac nxe r-w-x cpl x86)))
            (equal (mv-nth 1
                           (ia32e-la-to-pa-page-dir-ptr-table
                            lin-addr base-addr u/s-acc r/w-acc x/d-acc
                            wp smep smap ac nxe r-w-x cpl (mv-nth 1 (wb addr-lst x86))))
                   (mv-nth 1
                           (ia32e-la-to-pa-page-dir-ptr-table
                            lin-addr base-addr u/s-acc r/w-acc x/d-acc
                            wp smep smap ac nxe r-w-x cpl x86)))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (disjoint-p
                             member-p
                             ia32e-la-to-pa-page-dir-ptr-table
                             translation-governing-addresses-for-page-dir-ptr-table)
                            (wb
                             translation-governing-addresses-for-page-directory
                             bitops::logand-with-negated-bitmask
                             (:meta acl2::mv-nth-cons-meta)
                             force (force))))))

(defthm ia32e-la-to-pa-pml4-table-values-and-mv-nth-1-wb-disjoint-from-xlation-gov-addrs
  (implies (and (equal cpl (cpl x86))
                (not (mv-nth 0 (las-to-pas (strip-cars addr-lst) :w cpl x86)))
                (disjoint-p
                 (translation-governing-addresses-for-pml4-table lin-addr base-addr x86)
                 (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w cpl x86)))
                (not (page-structure-marking-mode x86))
                (canonical-address-p lin-addr)
                (physical-address-p base-addr)
                (equal (loghead 12 base-addr) 0))
           (and
            (equal (mv-nth 0
                           (ia32e-la-to-pa-pml4-table
                            lin-addr base-addr wp smep smap ac nxe r-w-x cpl
                            (mv-nth 1 (wb addr-lst x86))))
                   (mv-nth 0
                           (ia32e-la-to-pa-pml4-table
                            lin-addr base-addr wp smep smap ac nxe r-w-x cpl x86)))
            (equal (mv-nth 1
                           (ia32e-la-to-pa-pml4-table
                            lin-addr base-addr wp smep smap ac nxe r-w-x cpl
                            (mv-nth 1 (wb addr-lst x86))))
                   (mv-nth 1
                           (ia32e-la-to-pa-pml4-table
                            lin-addr base-addr wp smep smap ac nxe r-w-x cpl x86)))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (disjoint-p
                             member-p
                             ia32e-la-to-pa-pml4-table
                             translation-governing-addresses-for-pml4-table)
                            (wb
                             translation-governing-addresses-for-page-dir-ptr-table
                             bitops::logand-with-negated-bitmask
                             (:meta acl2::mv-nth-cons-meta)
                             force (force))))))

(defthm ia32e-la-to-pa-values-and-mv-nth-1-wb-disjoint-from-xlation-gov-addrs
  (implies (and (equal cpl (cpl x86))
                (not (mv-nth 0 (las-to-pas (strip-cars addr-lst) :w cpl x86)))
                (disjoint-p (translation-governing-addresses lin-addr x86)
                            (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w cpl x86)))
                (not (page-structure-marking-mode x86))
                (canonical-address-p lin-addr))
           (and
            (equal (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x cpl (mv-nth 1 (wb addr-lst x86))))
                   (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x cpl x86)))
            (equal (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x cpl (mv-nth 1 (wb addr-lst x86))))
                   (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x cpl x86)))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (disjoint-p
                             member-p
                             ia32e-la-to-pa
                             translation-governing-addresses)
                            (wb
                             translation-governing-addresses-for-pml4-table
                             (:meta acl2::mv-nth-cons-meta)
                             force (force))))))

(defthm la-to-pas-values-and-mv-nth-1-wb-disjoint-from-xlation-gov-addrs
  (implies (and (equal cpl (cpl x86))
                (not (mv-nth 0 (las-to-pas (strip-cars addr-lst) :w cpl x86)))
                (disjoint-p (all-translation-governing-addresses l-addrs x86)
                            (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w cpl x86)))
                (not (page-structure-marking-mode x86))
                (canonical-address-listp l-addrs))
           (and
            (equal (mv-nth 0 (las-to-pas l-addrs r-w-x cpl (mv-nth 1 (wb addr-lst x86))))
                   (mv-nth 0 (las-to-pas l-addrs r-w-x cpl x86)))
            (equal (mv-nth 1 (las-to-pas l-addrs r-w-x cpl (mv-nth 1 (wb addr-lst x86))))
                   (mv-nth 1 (las-to-pas l-addrs r-w-x cpl x86)))))
  :hints (("Goal"
           :induct (all-translation-governing-addresses l-addrs x86)
           :in-theory (e/d* ()
                            (wb
                             translation-governing-addresses
                             (:meta acl2::mv-nth-cons-meta)
                             force (force))))))

;; ======================================================================

;; Lemmas about interaction of memory reads and writes:

(defthm read-from-physical-memory-and-write-to-physical-memory-disjoint
  (implies (disjoint-p p-addrs-1 p-addrs-2)
           (equal (read-from-physical-memory
                   p-addrs-1
                   (write-to-physical-memory p-addrs-2 bytes x86))
                  (read-from-physical-memory p-addrs-1 x86)))
  :hints (("Goal" :in-theory (e/d* (disjoint-p) ()))))

(defthm rb-wb-disjoint-in-system-level-non-marking-mode
  (implies (and (disjoint-p
                 (mv-nth 1 (las-to-pas l-addrs r-w-x (cpl x86) x86))
                 (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w (cpl x86) x86)))
                (disjoint-p
                 (all-translation-governing-addresses l-addrs x86)
                 (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w (cpl x86) x86)))
                (not (programmer-level-mode x86))
                (not (page-structure-marking-mode x86))
                (canonical-address-listp l-addrs)
                ;; I should try to eliminate the following hyp too...
                ;; (not (mv-nth 0 (wb addr-lst x86)))
                (not (mv-nth 0 (las-to-pas (strip-cars addr-lst) :w (cpl x86) x86))))
           (and
            (equal (mv-nth 0 (rb l-addrs r-w-x (mv-nth 1 (wb addr-lst x86))))
                   (mv-nth 0 (rb l-addrs r-w-x x86)))
            (equal (mv-nth 1 (rb l-addrs r-w-x (mv-nth 1 (wb addr-lst x86))))
                   (mv-nth 1 (rb l-addrs r-w-x x86)))))
  :hints (("Goal" :do-not-induct t)))

(defthm read-from-physical-memory-and-mv-nth-1-wb-disjoint
  ;; Similar to rb-wb-disjoint-in-system-level-non-marking-mode
  (implies (and (disjoint-p
                 p-addrs
                 (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w (cpl x86) x86)))
                ;; I should try to eliminate the following hyp too...
                (not (mv-nth 0 (las-to-pas (strip-cars addr-lst) :w (cpl x86) x86)))
                (not (programmer-level-mode x86))
                (not (page-structure-marking-mode x86))
                (x86p x86))
           (equal (read-from-physical-memory p-addrs (mv-nth 1 (wb addr-lst x86)))
                  (read-from-physical-memory p-addrs x86)))
  :hints (("Goal" :in-theory (e/d* (wb) ()))))

(defthm assoc-list-and-create-phy-addr-bytes-alist
  (implies (and (true-listp y)
                (equal (len x) (len y))
                (no-duplicates-p x))
           (equal (assoc-list x (create-phy-addr-bytes-alist x y))
                  y)))

(defthm assoc-list-of-rev-of-create-phy-addr-bytes-alist
  (implies (and (true-listp y)
                (equal (len x) (len y))
                (no-duplicates-p x))
           (equal (assoc-list x (acl2::rev (create-phy-addr-bytes-alist x y)))
                  y)))

(defthm read-from-physical-memory-and-write-to-physical-memory-equal
  (implies (and (no-duplicates-p p-addrs)
                (physical-address-listp p-addrs)
                (equal (len p-addrs) (len bytes)))
           (equal (read-from-physical-memory p-addrs (write-to-physical-memory p-addrs bytes x86))
                  (assoc-list p-addrs (reverse (create-phy-addr-bytes-alist p-addrs bytes)))))
  :hints (("Goal"
           :induct (read-from-physical-memory p-addrs (write-to-physical-memory p-addrs bytes x86))
           :in-theory (e/d* (member-p) ()))))

(defthmd rb-wb-equal-in-system-level-non-marking-mode
  (implies (and (equal
                 (mv-nth 1 (las-to-pas l-addrs r-w-x (cpl x86) x86))
                 (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w (cpl x86) x86)))
                (disjoint-p
                 (all-translation-governing-addresses l-addrs x86)
                 (mv-nth 1 (las-to-pas l-addrs r-w-x (cpl x86) x86)))
                (no-duplicates-p
                 (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w (cpl x86) x86)))
                (not (programmer-level-mode x86))
                (not (page-structure-marking-mode x86))
                (canonical-address-listp l-addrs)
                (addr-byte-alistp addr-lst)
                ;; (not (mv-nth 0 (rb l-addrs r-w-x x86)))
                (not (mv-nth 0 (las-to-pas l-addrs r-w-x (cpl x86) x86)))
                ;; (not (mv-nth 0 (wb addr-lst x86)))
                (not (mv-nth 0 (las-to-pas (strip-cars addr-lst) :w (cpl x86) x86))))
           (equal (mv-nth 1 (rb l-addrs r-w-x (mv-nth 1 (wb addr-lst x86))))
                  (strip-cdrs addr-lst)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d* () (force (force))))))

;; ======================================================================

;; Lemmas about program-at:

(defthm program-at-wb-disjoint-in-system-level-non-marking-mode
  (implies (and (disjoint-p
                 (mv-nth 1 (las-to-pas l-addrs :x (cpl x86) x86))
                 (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w (cpl x86) x86)))
                (disjoint-p
                 (all-translation-governing-addresses l-addrs x86)
                 (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w (cpl x86) x86)))
                (not (programmer-level-mode x86))
                (not (page-structure-marking-mode x86))
                (canonical-address-listp l-addrs)
                ;; I should try to eliminate the following hyp too...
                ;; (not (mv-nth 0 (wb addr-lst x86)))
                (not (mv-nth 0 (las-to-pas (strip-cars addr-lst) :w (cpl x86) x86))))
           (equal (program-at l-addrs bytes (mv-nth 1 (wb addr-lst x86)))
                  (program-at l-addrs bytes x86)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (program-at) (rb wb)))))

(defthm program-at-pop-x86-oracle-in-system-level-mode
  (implies (not (programmer-level-mode x86))
           (equal (program-at addresses r-w-x (mv-nth 1 (pop-x86-oracle x86)))
                  (program-at addresses r-w-x x86)))
  :hints (("Goal" :in-theory (e/d (program-at pop-x86-oracle pop-x86-oracle-logic)
                                  (rb)))))

(defthm program-at-xw-in-system-level-mode
  (implies (and (not (programmer-level-mode x86))
                (not (equal fld :mem))
                (not (equal fld :rflags))
                (not (equal fld :ctr))
                (not (equal fld :seg-visible))
                (not (equal fld :msr))
                (not (equal fld :fault))
                (not (equal fld :programmer-level-mode))
                (not (equal fld :page-structure-marking-mode)))
           (equal (program-at l-addrs bytes (xw fld index value x86))
                  (program-at l-addrs bytes x86)))
  :hints (("Goal" :in-theory (e/d* (program-at) (rb)))))

(defthm program-at-xw-rflags-not-ac-values-in-system-level-mode
  (implies (and (not (programmer-level-mode x86))
                (equal (rflags-slice :ac value)
                       (rflags-slice :ac (rflags x86))))
           (equal (program-at l-addrs bytes (xw :rflags 0 value x86))
                  (program-at l-addrs bytes x86)))
  :hints (("Goal" :in-theory (e/d* (program-at) (rb)))))

(defthm program-at-values-and-!flgi
  (implies (and (not (equal index *ac*))
                (not (page-structure-marking-mode x86))
                (not (programmer-level-mode x86))
                (x86p x86))
           (equal (program-at l-addrs bytes (!flgi index value x86))
                  (program-at l-addrs bytes x86)))
  :hints (("Goal" :in-theory (e/d* (program-at) (rb)))))

(defthm program-at-values-and-!flgi-undefined
  (implies (and (not (equal index *ac*))
                (not (page-structure-marking-mode x86))
                (not (programmer-level-mode x86))
                (x86p x86))
           (equal (program-at l-addrs bytes (!flgi-undefined index x86))
                  (program-at l-addrs bytes x86)))
  :hints (("Goal" :in-theory (e/d* (program-at) (rb)))))


;; ======================================================================

(globally-disable '(rb wb canonical-address-p program-at
                       unsigned-byte-p signed-byte-p
                       las-to-pas all-translation-governing-addresses))

;; ======================================================================
