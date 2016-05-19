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

(defsection common-system-level-utils
  :parents (proof-utilities)

  :short "Reasoning in the system-level mode"

  :long "<p>WORK IN PROGRESS...</p>

<p>This book contains lemmas that come in useful in both the marking
  and non-marking sub-modes of the system-level mode.</p>"
  )

(local (xdoc::set-default-parents common-system-level-utils))

;; ======================================================================

;; Some misc. lemmas and utils:

(defthm combine-bytes-of-list-combine-bytes
  (equal (combine-bytes (list (combine-bytes xs)))
         (combine-bytes xs))
  :hints (("Goal" :in-theory (e/d* (combine-bytes) (force (force))))))

(defthmd open-addr-range-4
  (implies (integerp x)
           (equal (addr-range 4 x)
                  (list x (+ 1 x) (+ 2 x) (+ 3 x)))))

(defthmd open-addr-range-8
  (implies (integerp x)
           (equal (addr-range 8 x)
                  (list x (+ 1 x) (+ 2 x) (+ 3 x)
                        (+ 4 x) (+ 5 x) (+ 6 x) (+ 7 x)))))

(defthmd disjoint-p-and-addr-range-first-part
  (implies (and (disjoint-p (addr-range n index) xs)
                (natp n)
                (< m n))
           (disjoint-p (addr-range m index) xs))
  :hints (("Goal" :in-theory (e/d* (disjoint-p) ()))))

(defthmd disjoint-p-and-addr-range-second-part-n=8
  ;; TO-DO: Speed this up!
  (implies (and (disjoint-p (addr-range 8 index) xs)
                (integerp index))
           (disjoint-p (addr-range 4 (+ 4 index)) xs))
  :hints (("Goal"
           :use ((:instance open-addr-range-4 (x index))
                 (:instance open-addr-range-8 (x index)))
           :in-theory (e/d* (disjoint-p member-p) ()))))

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

(defthm mv-nth-2-rb-in-system-level-marking-mode
  (implies (and (not (programmer-level-mode x86))
                (page-structure-marking-mode x86)
                (not (mv-nth 0 (rb l-addrs r-w-x x86))))
           (equal (mv-nth 2 (rb l-addrs r-w-x x86))
                  (mv-nth 2 (las-to-pas l-addrs r-w-x (cpl x86) (double-rewrite x86)))))
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
                  (mv-nth 0 (las-to-pas (strip-cars addr-lst) :w (cpl x86) (double-rewrite x86)))))
  :hints (("Goal" :in-theory (e/d* (wb) (force (force))))))

;; ======================================================================

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

(defthm program-at-pop-x86-oracle-in-system-level-mode
  (implies (not (programmer-level-mode x86))
           (equal (program-at addresses r-w-x (mv-nth 1 (pop-x86-oracle x86)))
                  (program-at addresses r-w-x x86)))
  :hints (("Goal" :in-theory (e/d (program-at pop-x86-oracle pop-x86-oracle-logic)
                                  (rb)))))

;; (defthm program-at-xw-in-system-level-mode
;;   (implies (and (not (programmer-level-mode x86))
;;                 (not (equal fld :mem))
;;                 (not (equal fld :rflags))
;;                 (not (equal fld :ctr))
;;                 (not (equal fld :seg-visible))
;;                 (not (equal fld :msr))
;;                 (not (equal fld :fault))
;;                 (not (equal fld :programmer-level-mode))
;;                 (not (equal fld :page-structure-marking-mode)))
;;            (equal (program-at l-addrs bytes (xw fld index value x86))
;;                   (program-at l-addrs bytes x86)))
;;   :hints (("Goal" :in-theory (e/d* (program-at) (rb)))))

;; The following make-event generates a bunch of rules that together
;; say the same thing as program-at-xw-in-system-level-mode but these
;; rules are more efficient than program-at-xw-in-system-level-mode as
;; they match less frequently.

(make-event
 (generate-read-fn-over-xw-thms
  (remove-elements-from-list
   '(:mem :rflags :ctr :seg-visible :msr :fault :programmer-level-mode :page-structure-marking-mode)
   *x86-field-names-as-keywords*)
  'program-at
  (acl2::formals 'program-at (w state))
  :hyps '(not (programmer-level-mode x86))
  :prepwork '((local (in-theory (e/d (program-at) (rb)))))))

(defthm program-at-xw-rflags-not-ac-values-in-system-level-mode
  (implies (and (not (programmer-level-mode x86))
                (equal (rflags-slice :ac value)
                       (rflags-slice :ac (rflags x86))))
           (equal (program-at l-addrs bytes (xw :rflags 0 value x86))
                  (program-at l-addrs bytes x86)))
  :hints (("Goal" :in-theory (e/d* (program-at) (rb)))))

(defthm program-at-values-and-!flgi
  (implies (and (not (equal index *ac*))
                (not (programmer-level-mode x86))
                (x86p x86))
           (equal (program-at l-addrs bytes (!flgi index value x86))
                  (program-at l-addrs bytes x86)))
  :hints (("Goal" :in-theory (e/d* (program-at) (rb)))))

(defthm program-at-values-and-!flgi-undefined
  (implies (and (not (equal index *ac*))
                (not (programmer-level-mode x86))
                (x86p x86))
           (equal (program-at l-addrs bytes (!flgi-undefined index x86))
                  (program-at l-addrs bytes x86)))
  :hints (("Goal" :in-theory (e/d* (program-at) (rb)))))

;; ======================================================================

(defthm mv-nth-1-ia32e-la-to-pa-when-error
  (implies (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x cpl x86))
           (equal (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x cpl x86)) 0))
  :hints (("Goal" :in-theory (e/d (ia32e-la-to-pa
                                   ia32e-la-to-pa-pml4-table)
                                  (force (force))))))

(defthm mv-nth-1-las-to-pas-when-error
  (implies (mv-nth 0 (las-to-pas l-addrs r-w-x cpl x86))
           (equal (mv-nth 1 (las-to-pas l-addrs r-w-x cpl x86)) nil))
  :hints (("Goal" :in-theory (e/d (las-to-pas) (force (force))))))

;; ======================================================================

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

;; ----------------------------------------------------------------------

(defthmd r/x-is-irrelevant-for-mv-nth-2-ia32e-la-to-pa-page-table-when-no-errors
  (implies (and (not (mv-nth 0
                             (ia32e-la-to-pa-page-table
                              lin-addr base-addr u/s-acc r/w-acc x/d-acc
                              wp smep smap ac nxe r-w-x-1 cpl x86)))
                (syntaxp (not (eq r-w-x-2 r-w-x-1)))
                (not (equal r-w-x-1 :w))
                (not (equal r-w-x-2 :w))
                (not (mv-nth 0
                             (ia32e-la-to-pa-page-table
                              lin-addr base-addr u/s-acc r/w-acc x/d-acc
                              wp smep smap ac nxe r-w-x-2 cpl x86))))
           (equal (mv-nth 2
                          (ia32e-la-to-pa-page-table
                           lin-addr base-addr u/s-acc r/w-acc x/d-acc
                           wp smep smap ac nxe r-w-x-2 cpl x86))
                  (mv-nth 2
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

(defthmd r/x-is-irrelevant-for-mv-nth-2-ia32e-la-to-pa-page-directory-when-no-errors
  (implies (and (not (mv-nth 0
                             (ia32e-la-to-pa-page-directory
                              lin-addr base-addr u/s-acc r/w-acc x/d-acc
                              wp smep smap ac nxe r-w-x-1 cpl x86)))
                (syntaxp (not (eq r-w-x-2 r-w-x-1)))
                (not (equal r-w-x-1 :w))
                (not (equal r-w-x-2 :w))
                (not (mv-nth 0
                             (ia32e-la-to-pa-page-directory
                              lin-addr base-addr u/s-acc r/w-acc x/d-acc
                              wp smep smap ac nxe r-w-x-2 cpl x86))))
           (equal (mv-nth 2
                          (ia32e-la-to-pa-page-directory
                           lin-addr base-addr u/s-acc r/w-acc x/d-acc
                           wp smep smap ac nxe r-w-x-2 cpl x86))
                  (mv-nth 2
                          (ia32e-la-to-pa-page-directory
                           lin-addr base-addr u/s-acc r/w-acc x/d-acc
                           wp smep smap ac nxe r-w-x-1 cpl x86))))
  :hints (("Goal"
           :use ((:instance r/x-is-irrelevant-for-mv-nth-2-ia32e-la-to-pa-page-table-when-no-errors
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

(defthmd r/x-is-irrelevant-for-mv-nth-2-ia32e-la-to-pa-page-dir-ptr-table-when-no-errors
  (implies (and (not (mv-nth 0
                             (ia32e-la-to-pa-page-dir-ptr-table
                              lin-addr base-addr u/s-acc r/w-acc x/d-acc
                              wp smep smap ac nxe r-w-x-1 cpl x86)))
                (syntaxp (not (eq r-w-x-2 r-w-x-1)))
                (not (equal r-w-x-1 :w))
                (not (equal r-w-x-2 :w))
                (not (mv-nth 0
                             (ia32e-la-to-pa-page-dir-ptr-table
                              lin-addr base-addr u/s-acc r/w-acc x/d-acc
                              wp smep smap ac nxe r-w-x-2 cpl x86))))
           (equal (mv-nth 2
                          (ia32e-la-to-pa-page-dir-ptr-table
                           lin-addr base-addr u/s-acc r/w-acc x/d-acc
                           wp smep smap ac nxe r-w-x-2 cpl x86))
                  (mv-nth 2
                          (ia32e-la-to-pa-page-dir-ptr-table
                           lin-addr base-addr u/s-acc r/w-acc x/d-acc
                           wp smep smap ac nxe r-w-x-1 cpl x86))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance r/x-is-irrelevant-for-mv-nth-2-ia32e-la-to-pa-page-directory-when-no-errors
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

(defthmd r/x-is-irrelevant-for-mv-nth-2-ia32e-la-to-pa-pml4-table-when-no-errors
  (implies (and (not (mv-nth 0
                             (ia32e-la-to-pa-pml4-table
                              lin-addr base-addr wp smep smap ac nxe r-w-x-1 cpl x86)))
                (syntaxp (not (eq r-w-x-2 r-w-x-1)))
                (not (equal r-w-x-1 :w))
                (not (equal r-w-x-2 :w))
                (not (mv-nth 0
                             (ia32e-la-to-pa-pml4-table
                              lin-addr base-addr wp smep smap ac nxe r-w-x-2 cpl x86))))
           (equal (mv-nth 2
                          (ia32e-la-to-pa-pml4-table
                           lin-addr base-addr wp smep smap ac nxe r-w-x-2 cpl x86))
                  (mv-nth 2
                          (ia32e-la-to-pa-pml4-table
                           lin-addr base-addr wp smep smap ac nxe r-w-x-1 cpl x86))))
  :hints (("Goal"
           :use ((:instance r/x-is-irrelevant-for-mv-nth-2-ia32e-la-to-pa-page-dir-ptr-table-when-no-errors
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

(defthm r/x-is-irrelevant-for-mv-nth-2-ia32e-la-to-pa-when-no-errors
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
                (not (equal r-w-x-1 :w))
                (not (equal r-w-x-2 :w))
                (not (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x-1 cpl x86)))
                (not (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x-2 cpl x86))))
           (equal (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x-2 cpl x86))
                  (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x-1 cpl x86))))
  :hints (("Goal"
           :use ((:instance r/x-is-irrelevant-for-mv-nth-2-ia32e-la-to-pa-pml4-table-when-no-errors
                            (lin-addr (logext 48 lin-addr))
                            (base-addr (ash (loghead 40 (logtail 12 (xr :ctr *cr3* x86))) 12))
                            (wp (bool->bit (logbitp 16 (xr :ctr *cr0* x86))))
                            (smep (loghead 1 (bool->bit (logbitp 20 (xr :ctr *cr4* x86)))))
                            (smap 0)
                            (ac (bool->bit (logbitp 18 (xr :rflags 0 x86))))
                            (nxe (loghead 1 (bool->bit (logbitp 11 (xr :msr *ia32_efer-idx* x86)))))))
           :in-theory (e/d* (ia32e-la-to-pa) ()))))

;; ======================================================================
