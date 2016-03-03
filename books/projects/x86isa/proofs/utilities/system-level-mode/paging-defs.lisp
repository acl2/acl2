;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")
(include-book "physical-memory-utils")
(include-book "gl-lemmas")
(include-book "clause-processors/find-subterms" :dir :system)

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))

(local (in-theory (e/d* () (signed-byte-p unsigned-byte-p))))

;; ======================================================================

(defsection reasoning-about-page-tables
  :parents (proof-utilities)

  :short "Reasoning about paging data structures"

  :long "<p>WORK IN PROGRESS...</p>

<p>This doc topic will be updated in later commits...</p>"
  )

(defsection paging-defs
  :parents (reasoning-about-page-tables)

  :long "<p>WORK IN PROGRESS...</p>

<p>This doc topic will be updated in later commits...</p>"
  )

(local (xdoc::set-default-parents paging-defs))

;; ======================================================================

;; Some misc. lemmas:

(defthm combine-bytes-of-list-combine-bytes
  (equal (combine-bytes (list (combine-bytes xs)))
         (combine-bytes xs))
  :hints (("Goal" :in-theory (e/d* (combine-bytes) (force (force))))))

;; ======================================================================

;; Normalizing memory reads:

(local
 (defthm dumb-integerp-of-mem
   (implies (x86p x86)
            (integerp (xr :mem index x86)))))

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

;; ======================================================================

;; Lemmas to aid in symbolic simulation:

(defthmd rm08-in-terms-of-nth-pos-and-rb-in-system-level-non-marking-mode
  (implies (and (not (mv-nth 0 (las-to-pas l-addrs r-w-x (loghead 2 (xr :seg-visible 1 x86)) x86)))
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
                (not (mv-nth 0 (rb (list lin-addr) :x x86)))
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

;; ======================================================================

;; translation-governing-addresses:

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
  :enabled t
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
  :enabled t

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
  :enabled t

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
  :enabled t

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
              (integerp index)
              ;; (not (member-p index (addr-range 8 (pml4-table-entry-addr lin-addr base-addr))))
              ;; (not (member-p index (addr-range 8 (page-dir-ptr-table-entry-addr
              ;;                                     lin-addr
              ;;                                     (ash
              ;;                                      (loghead 40
              ;;                                               (logtail 12
              ;;                                                        (rm-low-64 (pml4-table-entry-addr lin-addr base-addr)
              ;;                                                                   x86)))
              ;;                                      12)))))
              ;; (not (member-p index (addr-range 8 (page-directory-entry-addr
              ;;                                     lin-addr
              ;;                                     (ash (loghead 40
              ;;                                                   (logtail 12
              ;;                                                            (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr (ash
              ;;                                                                                                                (loghead 40
              ;;                                                                                                                         (logtail 12
              ;;                                                                                                                                  (rm-low-64 (pml4-table-entry-addr lin-addr base-addr)
              ;;                                                                                                                                             x86)))
              ;;                                                                                                                12)) x86)))
              ;;                                          12)))))
              )
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

  :enabled t

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
    :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa) (translation-governing-addresses-for-pml4-table))))))

(define all-translation-governing-addresses
  ((l-addrs canonical-address-listp)
   x86)
  :guard (not (xr :programmer-level-mode 0 x86))
  :non-executable t
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
    :hints (("Goal" :in-theory (e/d* () (translation-governing-addresses))))))

(defthm ia32e-la-to-pa-values-and-write-to-physical-memory
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

(defthm las-to-pas-values-and-write-to-physical-memory
  (implies (and (disjoint-p p-addrs (all-translation-governing-addresses l-addrs x86))
                (physical-address-listp p-addrs)
                (canonical-address-listp l-addrs)
                (not (page-structure-marking-mode x86)))
           (and (equal (mv-nth 0 (las-to-pas l-addrs r-w-x cpl (write-to-physical-memory p-addrs bytes x86)))
                       (mv-nth 0 (las-to-pas l-addrs r-w-x cpl x86)))
                (equal (mv-nth 1 (las-to-pas l-addrs r-w-x cpl (write-to-physical-memory p-addrs bytes x86)))
                       (mv-nth 1 (las-to-pas l-addrs r-w-x cpl x86)))))
  :hints (("Goal" :induct (las-to-pas l-addrs r-w-x cpl x86)
           :in-theory (e/d* (disjoint-p) (translation-governing-addresses)))))

;; (acl2::why |(rm-low-64 addr2 (xw :mem addr1 val x86)) --- disjoint addr|)
;; (acl2::why mv-nth-2-las-to-pas-system-level-non-marking-mode)
;; (acl2::why mv-nth-2-ia32e-la-to-pa-system-level-non-marking-mode)
;; (acl2::why las-to-pas-values-and-write-to-physical-memory)

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

(defthm read-from-physical-memory-and-write-to-physical-memory-disjoint
  (implies (disjoint-p p-addrs-1 p-addrs-2)
           (equal (read-from-physical-memory
                   p-addrs-1
                   (write-to-physical-memory p-addrs-2 bytes x86))
                  (read-from-physical-memory p-addrs-1 x86)))
  :hints (("Goal" :in-theory (e/d* (disjoint-p) ()))))

(defthm rb-wb-disjoint-in-system-level-non-marking-mode
  (implies (and (disjoint-p
                 (mv-nth 1 (las-to-pas l-addrs r-w-x (loghead 2 (xr :seg-visible 1 x86)) x86))
                 (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w (loghead 2 (xr :seg-visible 1 x86)) x86)))
                (disjoint-p (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w (loghead 2 (xr :seg-visible 1 x86)) x86))
                            (all-translation-governing-addresses l-addrs x86))
                (not (programmer-level-mode x86))
                (not (page-structure-marking-mode x86))
                (canonical-address-listp l-addrs)
                ;; I should try to eliminate the following hyp too...
                (not (mv-nth 0 (wb addr-lst x86))))
           (equal (mv-nth 1 (rb l-addrs r-w-x (mv-nth 1 (wb addr-lst x86))))
                  (mv-nth 1 (rb l-addrs r-w-x x86))))
  :hints (("Goal" :do-not-induct t)))

#||

(i-am-here)

(defthm two-ia32e-la-to-pa-if-the-inner-returns-an-error
  ;; Bah, of course there are too many case splits here that can be
  ;; avoided easily...
  (implies (not (page-structure-marking-mode x86))
           (and
            (equal (mv-nth 0 (ia32e-la-to-pa lin-addr-1 r-w-x-1 cpl-1
                                             (mv-nth 2 (ia32e-la-to-pa lin-addr-2 r-w-x-2 cpl-2 x86))))
                   (mv-nth 0 (ia32e-la-to-pa lin-addr-1 r-w-x-1 cpl-1 x86)))
            (equal (mv-nth 1 (ia32e-la-to-pa lin-addr-1 r-w-x-1 cpl-1
                                             (mv-nth 2 (ia32e-la-to-pa lin-addr-2 r-w-x-2 cpl-2 x86))))
                   (mv-nth 1 (ia32e-la-to-pa lin-addr-1 r-w-x-1 cpl-1 x86)))))
  :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa
                                    ia32e-la-to-pa-pml4-table
                                    ia32e-la-to-pa-page-dir-ptr-table
                                    ia32e-la-to-pa-page-directory
                                    ia32e-la-to-pa-page-table
                                    page-size
                                    paging-entry-no-page-fault-p
                                    page-fault-exception)
                                   (not)))))

(defthm two-las-to-pas-if-the-inner-returns-an-error
  ;; Bah, of course there are too many case splits here that can be
  ;; avoided easily...
  (implies (not (page-structure-marking-mode x86))
           (and
            (equal (mv-nth 0 (las-to-pas l-addrs-1 r-w-x-1 cpl-1
                                         (mv-nth 2 (las-to-pas l-addrs-2 r-w-x-2 cpl-2 x86))))
                   (mv-nth 0 (las-to-pas l-addrs-1 r-w-x-1 cpl-1 x86)))
            (equal (mv-nth 1 (las-to-pas l-addrs-1 r-w-x-1 cpl-1
                                         (mv-nth 2 (las-to-pas l-addrs-2 r-w-x-2 cpl-2 x86))))
                   (mv-nth 1 (las-to-pas l-addrs-1 r-w-x-1 cpl-1 x86)))))
  :hints (("Goal" :in-theory (e/d* (las-to-pas) (not)))))

(defthm xr-mem-mv-nth-2-ia32e-la-to-pa-page-table
  (implies (not (member-p index (addr-range 8 (page-table-entry-addr lin-addr base-addr))))
           (equal (xr :mem index (mv-nth 2 (ia32e-la-to-pa-page-table
                                            lin-addr
                                            base-addr u/s-acc r/w-acc x/d-acc
                                            wp smep smap ac nxe r-w-x cpl x86)))
                  (xr :mem index x86)))
  :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa-page-table
                                    paging-entry-no-page-fault-p)
                                   ()))))

(defthm xr-mem-mv-nth-2-ia32e-la-to-pa
  (implies t
           (equal (xr :mem index (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x cpl x86)))
                  (xr :mem index x86)))
  :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa
                                    ia32e-la-to-pa-pml4-table
                                    paging-entry-no-page-fault-p)
                                   ()))))

(defthm read-from-physical-memory-and-mv-nth-2-ia32e-la-to-pa
  (implies t
           (equal (read-from-physical-memory p-addrs (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x cpl x86)))
                  (read-from-physical-memory p-addrs x86)))
  :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa
                                    ia32e-la-to-pa-pml4-table
                                    paging-entry-no-page-fault-p)
                                   ()))))

||#





;; (define create-phy-addr-bytes-alist
;;   ((addr-list (physical-address-listp addr-list))
;;    (byte-list (byte-listp byte-list)))
;;   :guard (equal (len addr-list) (len byte-list))
;;   :enabled t
;;   (if (mbt (equal (len addr-list) (len byte-list)))
;;       (if (endp addr-list)
;;           nil
;;         (acons (car addr-list) (car byte-list)
;;                (create-phy-addr-bytes-alist (cdr addr-list)
;;                                             (cdr byte-list))))
;;     nil))

;; (defthm read-from-physical-memory-and-write-to-physical-memory-subset-p
;;   (implies (subset-p p-addrs-1 p-addrs-2)
;;            (equal (read-from-physical-memory
;;                    p-addrs-1
;;                    (write-to-physical-memory p-addrs-2 bytes x86))
;;                   (assoc-list p-addrs-1 (reverse (create-phy-addr-bytes-alist p-addrs-2 bytes)))))
;;   :hints (("Goal" :in-theory (e/d* (subset-p) ()))))



#||

(defthmd rb-wb-equal
  (implies (and (equal addresses (strip-cars (remove-duplicate-keys addr-lst)))
                (programmer-level-mode x86)
                (addr-byte-alistp addr-lst))
           (equal (mv-nth 1 (rb addresses r-w-x (mv-nth 1 (wb addr-lst x86))))
                  (assoc-list addresses (reverse addr-lst))))
  :hints (("Goal" :in-theory (e/d (wm08 rm08) ()))))

(defthm rb-wb-subset
  (implies (and (subset-p addresses (strip-cars addr-lst))
                (programmer-level-mode x86)
                ;; [Shilpi]: Ugh, this hyp. below is so annoying. I
                ;; could remove it if I proved something like
                ;; subset-p-strip-cars-of-remove-duplicate-keys,
                ;; commented out below.
                (canonical-address-listp addresses)
                (addr-byte-alistp addr-lst))
           (equal (mv-nth 1 (rb addresses r-w-x (mv-nth 1 (wb addr-lst x86))))
                  (assoc-list addresses (reverse addr-lst))))
  :hints (("Goal" :induct (assoc-list addresses (reverse addr-lst)))))

(defthmd rb-rb-subset
  ;; [Shilpi]: This theorem can be generalized so that the conclusion mentions
  ;; addr1, where addr1 <= addr.  Also, this is an expensive rule. Keep it
  ;; disabled generally.
  (implies (and (equal (mv-nth 1 (rb (create-canonical-address-list i addr) r-w-x x86))
                       bytes)
                (canonical-address-p (+ -1 i addr))
                (canonical-address-p addr)
                (xr :programmer-level-mode 0 x86)
                (posp i)
                (< j i))
           (equal (mv-nth 1 (rb (create-canonical-address-list j addr) r-w-x x86))
                  (take j bytes)))
  :hints (("Goal" :in-theory (e/d* (rb canonical-address-p signed-byte-p) ()))))

(defthm rb-rb-split-reads
  (implies (and (canonical-address-p addr)
                (xr :programmer-level-mode 0 x86)
                (natp j)
                (natp k))
           (equal (mv-nth 1 (rb (create-canonical-address-list (+ k j) addr) r-w-x x86))
                  (append (mv-nth 1 (rb (create-canonical-address-list k addr) r-w-x x86))
                          (mv-nth 1 (rb (create-canonical-address-list j (+ k addr)) r-w-x x86)))))
  :hints (("Goal" :in-theory (e/d* (rb canonical-address-p signed-byte-p)
                                   ((:meta acl2::mv-nth-cons-meta))))))

(defthm program-at-wb-disjoint
  (implies (and (programmer-level-mode x86)
                (canonical-address-listp addresses)
                (disjoint-p addresses (strip-cars addr-lst)))
           (equal (program-at addresses r-w-x (mv-nth 1 (wb addr-lst x86)))
                  (program-at addresses r-w-x x86)))
  :hints (("Goal" :in-theory (e/d (program-at) (rb)))))

(defthm program-at-pop-x86-oracle
  (implies (programmer-level-mode x86)
           (equal (program-at addresses r-w-x (mv-nth 1 (pop-x86-oracle x86)))
                  (program-at addresses r-w-x x86)))
  :hints (("Goal" :in-theory (e/d (program-at pop-x86-oracle pop-x86-oracle-logic)
                                  (rb)))))

(defthm program-at-write-user-rflags
  (implies (programmer-level-mode x86)
           (equal (program-at addresses r-w-x (write-user-rflags flags mask x86))
                  (program-at addresses r-w-x x86)))
  :hints (("Goal" :in-theory (e/d (write-user-rflags)
                                  (force (force))))))


(defthm wb-and-wb-combine-wbs
  (implies (and (addr-byte-alistp addr-list1)
                (addr-byte-alistp addr-list2)
                (programmer-level-mode x86))
           (equal (mv-nth 1 (wb addr-list2 (mv-nth 1 (wb addr-list1 x86))))
                  (mv-nth 1 (wb (append addr-list1 addr-list2) x86))))
  :hints (("Goal" :do-not '(generalize)
           :in-theory (e/d (wb-and-wm08) (append acl2::mv-nth-cons-meta)))))

(defthmd wb-remove-duplicate-writes
  (implies (and (syntaxp
                 (not
                  (and (consp addr-list)
                       (eq (car addr-list) 'remove-duplicate-keys))))
                (addr-byte-alistp addr-list)
                (programmer-level-mode x86))
           (equal (wb addr-list x86)
                  (wb (remove-duplicate-keys addr-list) x86)))
  :hints (("Goal" :do-not '(generalize)
           :in-theory (e/d (wm08)
                           (acl2::mv-nth-cons-meta))
           :induct (wb-duplicate-writes-induct addr-list x86))))

(defthm rb-in-terms-of-rb-subset-p
  (implies
   (and (bind-free (find-info-from-program-at-term
                    'rb-in-terms-of-rb-subset-p
                    mfc state)
                   (n prog-addr bytes))
        (program-at (create-canonical-address-list n prog-addr) bytes x86)
        (subset-p addresses (create-canonical-address-list n prog-addr))
        (consp addresses)
        (syntaxp (quotep n))
        (programmer-level-mode x86))
   (equal (mv-nth 1 (rb addresses :x x86))
          (append (list (nth (pos
                              (car addresses)
                              (create-canonical-address-list n prog-addr))
                             bytes))
                  (mv-nth 1 (rb (cdr addresses) :x x86)))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (subset-p)
                           (canonical-address-p
                            acl2::mv-nth-cons-meta
                            rb-in-terms-of-nth-and-pos))
           :use ((:instance rb-unwinding-thm
                            (r-w-x :x))
                 (:instance rb-in-terms-of-nth-and-pos
                            (addr (car addresses)))))))

(defthm combine-bytes-rb-in-terms-of-rb-subset-p
  (implies
   (and (bind-free (find-info-from-program-at-term
                    'combine-bytes-rb-in-terms-of-rb-subset-p
                    mfc state)
                   (n prog-addr bytes))
        (program-at (create-canonical-address-list n prog-addr) bytes x86)
        (subset-p addresses (create-canonical-address-list n prog-addr))
        (consp addresses)
        (syntaxp (quotep n))
        (programmer-level-mode x86))
   (equal
    (combine-bytes (mv-nth 1 (rb addresses :x x86)))
    (combine-bytes
     (append (list (nth (pos (car addresses)
                             (create-canonical-address-list n prog-addr))
                        bytes))
             (mv-nth 1 (rb (cdr addresses) :x x86))))))
  :hints (("Goal" :in-theory (union-theories
                              '()
                              (theory 'minimal-theory))
           :use ((:instance rb-in-terms-of-rb-subset-p)))))

(globally-disable '(rb wb canonical-address-p program-at
                       unsigned-byte-p signed-byte-p))

||#
