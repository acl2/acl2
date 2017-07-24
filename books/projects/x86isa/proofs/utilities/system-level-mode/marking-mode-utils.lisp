;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")
(include-book "common-system-level-utils")
(include-book "paging/top")
(include-book "clause-processors/find-subterms" :dir :system)

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))

(local (in-theory (e/d* () (signed-byte-p unsigned-byte-p))))

;; ======================================================================

(local (xdoc::set-default-parents system-level-marking-mode-proof-utilities))

;; ======================================================================

;; Combining nests of (mv-nth 2 (las-to-pas ...)) when linear
;; addresses are in sequence:

(local
 (define r-w-x-irrelevant-ind-scheme (n lin-addr r-w-x-1 r-w-x-2 x86-1 x86-2)
   :verify-guards nil
   :non-executable t
   :enabled t
   (if (or (zp n) (not (xlate-equiv-memory x86-1 x86-2)))
       (mv nil nil x86-1 x86-2)
     (b* (((unless (canonical-address-p lin-addr))
           (mv t nil x86-1 x86-2))
          ((mv flg-1 p-addr-1 x86-1)
           (ia32e-la-to-pa lin-addr r-w-x-1 x86-1))
          ((mv flg-2 p-addr-2 x86-2)
           (ia32e-la-to-pa lin-addr r-w-x-2 x86-2))
          ((unless (and (equal flg-1 flg-2)
                        (equal p-addr-1 p-addr-2)
                        (xlate-equiv-memory x86-1 x86-2)))
           (mv t nil x86-1 x86-2))
          ((when flg-1) (mv flg-1 nil x86-1 x86-2))
          ((mv flgs p-addrs x86-1 x86-2)
           (r-w-x-irrelevant-ind-scheme
            (1- n) (1+ lin-addr) r-w-x-1 r-w-x-2 x86-1 x86-2)))
       (mv flgs (if flgs nil (cons p-addr-1 p-addrs)) x86-1 x86-2)))))

(defthm r-w-x-is-irrelevant-for-mv-nth-1-las-to-pas-when-no-errors
  (implies (and (bind-free (find-almost-matching-las-to-pas
                            'r-w-x-1 n lin-addr mfc state)
                           (r-w-x-1))
                (syntaxp (and (not (eq r-w-x-2 r-w-x-1))
                              ;; r-w-x-2 must be smaller than r-w-x-1.
                              (term-order r-w-x-2 r-w-x-1)))
                (not (mv-nth 0 (las-to-pas n lin-addr r-w-x-1 x86)))
                (not (mv-nth 0 (las-to-pas n lin-addr r-w-x-2 x86))))
           (equal (mv-nth 1 (las-to-pas n lin-addr r-w-x-2 x86))
                  (mv-nth 1 (las-to-pas n lin-addr r-w-x-1 x86))))
  :hints (("Goal"
           :in-theory (e/d* (las-to-pas) ())
           :induct (r-w-x-irrelevant-ind-scheme n lin-addr r-w-x-1 r-w-x-2 x86 x86))
          (if (equal (car id) '(0 1))
              '(:expand ((las-to-pas n lin-addr r-w-x-1 x86)
                         (las-to-pas n lin-addr r-w-x-2 x86)))
            nil)))

(defthm r-w-x-is-irrelevant-for-mv-nth-2-las-to-pas-when-no-errors
  (implies (and (bind-free (find-almost-matching-las-to-pas
                            'r-w-x-1 n lin-addr mfc state)
                           (r-w-x-1))
                (syntaxp (and (not (eq r-w-x-2 r-w-x-1))
                              ;; r-w-x-2 must be smaller than r-w-x-1.
                              (term-order r-w-x-2 r-w-x-1)))
                (not (equal r-w-x-1 :w))
                (not (equal r-w-x-2 :w))
                (not (mv-nth 0 (las-to-pas n lin-addr r-w-x-1 x86)))
                (not (mv-nth 0 (las-to-pas n lin-addr r-w-x-2 x86))))
           (equal (mv-nth 2 (las-to-pas n lin-addr r-w-x-2 x86))
                  (mv-nth 2 (las-to-pas n lin-addr r-w-x-1 x86))))
  :hints (("Goal"
           :in-theory (e/d* (las-to-pas) ())
           :induct (r-w-x-irrelevant-ind-scheme n lin-addr r-w-x-1 r-w-x-2 x86 x86))
          (if (equal (car id) '(0 1))
              '(:expand ((las-to-pas n lin-addr r-w-x-1 x86)
                         (las-to-pas n lin-addr r-w-x-2 x86)))
            nil)))

(defthm combine-mv-nth-2-las-to-pas-same-r-w-x
  (implies (and (equal lin-addr-2 (+ n-1 lin-addr-1))
                (not (mv-nth 0 (las-to-pas n-1 lin-addr-1 r-w-x (double-rewrite x86))))
                (posp n-1) (posp n-2))
           (equal (mv-nth 2 (las-to-pas n-2 lin-addr-2 r-w-x
                                        (mv-nth 2 (las-to-pas n-1 lin-addr-1 r-w-x x86))))
                  (mv-nth 2 (las-to-pas (+ n-1 n-2) lin-addr-1 r-w-x x86)))
           ;; TODO: Do I need the following instead?
           ;; (equal (mv-nth 2 (las-to-pas n-1 lin-addr-1 r-w-x
           ;;                              (mv-nth 2 (las-to-pas n-2 lin-addr-2 r-w-x x86))))
           ;;        (mv-nth 2 (las-to-pas (+ n-1 n-2) lin-addr-1 r-w-x x86)))
           )
  :hints (("Goal" :in-theory (e/d* (las-to-pas zp) ()))))

;; ======================================================================

;; Lemmas about interaction of memory writes and paging walkers:

(defthm xr-mem-wb-in-system-level-mode
  (implies
   (and (disjoint-p
         (list index)
         (mv-nth 1 (las-to-pas n-w write-addr :w (double-rewrite x86))))
        (disjoint-p
         (list index)
         (all-xlation-governing-entries-paddrs n-w write-addr (double-rewrite x86)))
        (not (programmer-level-mode x86)))
   (equal (xr :mem index (mv-nth 1 (wb n-w write-addr w value x86)))
          (xr :mem index x86)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (wb disjoint-p member-p)
                            (write-to-physical-memory
                             (:meta acl2::mv-nth-cons-meta)
                             force (force))))))

(defthm rm-low-32-wb-in-system-level-mode-disjoint
  (implies (and
            (disjoint-p
             (addr-range 4 index)
             (mv-nth 1 (las-to-pas n-w write-addr :w (double-rewrite x86))))
            (disjoint-p
             (addr-range 4 index)
             (all-xlation-governing-entries-paddrs n-w write-addr (double-rewrite x86))))
           (equal (rm-low-32 index (mv-nth 1 (wb n-w write-addr w value x86)))
                  (rm-low-32 index x86)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (rm-low-32 disjoint-p member-p)
                            (wb
                             (:meta acl2::mv-nth-cons-meta)
                             force (force))))))

(defthm rm-low-64-wb-in-system-level-mode-disjoint
  (implies (and
            (disjoint-p
             (addr-range 8 index)
             (mv-nth 1 (las-to-pas n-w write-addr :w (double-rewrite x86))))
            (disjoint-p
             (addr-range 8 index)
             (all-xlation-governing-entries-paddrs n-w write-addr (double-rewrite x86)))
            (integerp index))
           (equal (rm-low-64 index (mv-nth 1 (wb n-w write-addr w value x86)))
                  (rm-low-64 index x86)))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance rm-low-32-wb-in-system-level-mode-disjoint
                            (index index))
                 (:instance rm-low-32-wb-in-system-level-mode-disjoint
                            (index (+ 4 index))))
           :in-theory (e/d* (rm-low-64)
                            (rm-low-32-wb-in-system-level-mode-disjoint
                             wb (:meta acl2::mv-nth-cons-meta)
                             force (force))))))

(defthm las-to-pas-values-and-write-to-physical-memory-disjoint
  ;; Generalization of
  ;; ia32e-la-to-pa-values-and-write-to-physical-memory-disjoint.
  (implies
   (and (disjoint-p
         p-addrs
         (all-xlation-governing-entries-paddrs n lin-addr (double-rewrite x86)))
        (physical-address-listp p-addrs)
        (x86p x86))
   (and
    (equal (mv-nth 0 (las-to-pas n lin-addr r-w-x
                                 (write-to-physical-memory p-addrs value x86)))
           (mv-nth 0 (las-to-pas n lin-addr r-w-x x86)))
    (equal (mv-nth 1 (las-to-pas n lin-addr r-w-x
                                 (write-to-physical-memory p-addrs value x86)))
           (mv-nth 1 (las-to-pas n lin-addr r-w-x x86)))))
  :hints (("Goal" :induct (las-to-pas n lin-addr r-w-x
                                      (write-to-physical-memory p-addrs value x86))
           :in-theory (e/d* (disjoint-p
                             disjoint-p-commutative
                             signed-byte-p
                             all-xlation-governing-entries-paddrs)
                            (xlation-governing-entries-paddrs)))))

(defthm ia32e-la-to-pa-page-table-values-and-mv-nth-1-wb-disjoint-from-xlation-gov-addrs
  (implies
   (and (disjoint-p
         (mv-nth 1 (las-to-pas n-w write-addr :w (double-rewrite x86)))
         (xlation-governing-entries-paddrs-for-page-table
          lin-addr base-addr (double-rewrite x86)))
        (canonical-address-p lin-addr)
        (physical-address-p base-addr)
        (equal (loghead 12 base-addr) 0))
   (and
    (equal (mv-nth 0
                   (ia32e-la-to-pa-page-table
                    lin-addr base-addr u/s-acc r/w-acc x/d-acc
                    wp smep smap ac nxe r-w-x cpl (mv-nth 1 (wb n-w write-addr w value x86))))
           (mv-nth 0
                   (ia32e-la-to-pa-page-table
                    lin-addr base-addr u/s-acc r/w-acc x/d-acc
                    wp smep smap ac nxe r-w-x cpl x86)))
    (equal (mv-nth 1
                   (ia32e-la-to-pa-page-table
                    lin-addr base-addr u/s-acc r/w-acc x/d-acc
                    wp smep smap ac nxe r-w-x cpl (mv-nth 1 (wb n-w write-addr w value x86))))
           (mv-nth 1
                   (ia32e-la-to-pa-page-table
                    lin-addr base-addr u/s-acc r/w-acc x/d-acc
                    wp smep smap ac nxe r-w-x cpl x86)))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (disjoint-p
                             disjoint-p-commutative
                             member-p
                             ia32e-la-to-pa-page-table
                             xlation-governing-entries-paddrs-for-page-table
                             wb)
                            (bitops::logand-with-negated-bitmask
                             (:meta acl2::mv-nth-cons-meta)
                             force (force))))))

(defthm rm-low-64-page-directory-entry-addr-and-mv-nth-1-wb
  ;; Different from RM-LOW-64-WB-IN-SYSTEM-LEVEL-MODE-DISJOINT, which
  ;; hangs on equal instead of xlate-equiv-entries.
  (implies
   (and (disjoint-p
         (mv-nth 1 (las-to-pas n-w write-addr :w (double-rewrite x86)))
         (xlation-governing-entries-paddrs-for-page-directory
          lin-addr base-addr (double-rewrite x86))))
   (xlate-equiv-entries
    (rm-low-64 (page-directory-entry-addr lin-addr base-addr)
               (mv-nth 1 (wb n-w write-addr w value x86)))
    (rm-low-64 (page-directory-entry-addr lin-addr base-addr)
               x86)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (xlation-governing-entries-paddrs-for-page-directory
                             disjoint-p-commutative)
                            ()))))

(defthm ia32e-la-to-pa-page-directory-values-and-mv-nth-1-wb-disjoint-from-xlation-gov-addrs
  (implies (and (disjoint-p
                 (mv-nth 1 (las-to-pas n-w write-addr :w (double-rewrite x86)))
                 (xlation-governing-entries-paddrs-for-page-directory
                  lin-addr base-addr (double-rewrite x86)))
                (canonical-address-p lin-addr)
                (physical-address-p base-addr)
                (equal (loghead 12 base-addr) 0))
           (and
            (equal (mv-nth 0
                           (ia32e-la-to-pa-page-directory
                            lin-addr base-addr u/s-acc r/w-acc x/d-acc
                            wp smep smap ac nxe r-w-x cpl
                            (mv-nth 1 (wb n-w write-addr w value x86))))
                   (mv-nth 0
                           (ia32e-la-to-pa-page-directory
                            lin-addr base-addr u/s-acc r/w-acc x/d-acc
                            wp smep smap ac nxe r-w-x cpl x86)))
            (equal (mv-nth 1
                           (ia32e-la-to-pa-page-directory
                            lin-addr base-addr u/s-acc r/w-acc x/d-acc
                            wp smep smap ac nxe r-w-x cpl
                            (mv-nth 1 (wb n-w write-addr w value x86))))
                   (mv-nth 1
                           (ia32e-la-to-pa-page-directory
                            lin-addr base-addr u/s-acc r/w-acc x/d-acc
                            wp smep smap ac nxe r-w-x cpl x86)))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance xlate-equiv-entries-and-page-size
                            (e-1 (rm-low-64 (page-directory-entry-addr lin-addr base-addr)
                                            x86))
                            (e-2 (rm-low-64 (page-directory-entry-addr lin-addr base-addr)
                                            (mv-nth 1 (wb n-w write-addr w value x86)))))
                 (:instance xlate-equiv-entries-and-page-execute-disable
                            (e-1 (rm-low-64 (page-directory-entry-addr lin-addr base-addr)
                                            x86))
                            (e-2 (rm-low-64 (page-directory-entry-addr lin-addr base-addr)
                                            (mv-nth 1 (wb n-w write-addr w value x86)))))
                 (:instance xlate-equiv-entries-and-logtail
                            (n 12)
                            (e-1 (rm-low-64 (page-directory-entry-addr lin-addr base-addr)
                                            x86))
                            (e-2 (rm-low-64 (page-directory-entry-addr lin-addr base-addr)
                                            (mv-nth 1 (wb n-w write-addr w value x86)))))
                 (:instance xlate-equiv-entries-and-logtail
                            (n 21)
                            (e-1 (rm-low-64 (page-directory-entry-addr lin-addr base-addr)
                                            x86))
                            (e-2 (rm-low-64 (page-directory-entry-addr lin-addr base-addr)
                                            (mv-nth 1 (wb n-w write-addr w value x86))))))
           :in-theory (e/d* (disjoint-p
                             disjoint-p-commutative
                             member-p
                             ia32e-la-to-pa-page-directory
                             xlation-governing-entries-paddrs-for-page-directory)
                            (wb
                             bitops::logand-with-negated-bitmask
                             (:meta acl2::mv-nth-cons-meta)
                             force (force))))))

(defthm rm-low-64-page-dir-ptr-table-entry-addr-and-mv-nth-1-wb
  ;; Different from RM-LOW-64-WB-IN-SYSTEM-LEVEL-MODE-DISJOINT, which
  ;; hangs on equal instead of xlate-equiv-entries.
  (implies
   (and (disjoint-p
         (mv-nth 1 (las-to-pas n-w write-addr :w (double-rewrite x86)))
         (xlation-governing-entries-paddrs-for-page-dir-ptr-table
          lin-addr base-addr (double-rewrite x86))))
   (xlate-equiv-entries
    (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr)
               (mv-nth 1 (wb n-w write-addr w value x86)))
    (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr)
               x86)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (xlation-governing-entries-paddrs-for-page-dir-ptr-table
                             disjoint-p-commutative)
                            ()))))

(defthm ia32e-la-to-pa-page-dir-ptr-table-values-and-mv-nth-1-wb-disjoint-from-xlation-gov-addrs
  (implies (and
            (disjoint-p
             (mv-nth 1 (las-to-pas n-w write-addr :w (double-rewrite x86)))
             (xlation-governing-entries-paddrs-for-page-dir-ptr-table
              lin-addr base-addr (double-rewrite x86)))
            (canonical-address-p lin-addr)
            (physical-address-p base-addr)
            (equal (loghead 12 base-addr) 0))
           (and
            (equal (mv-nth 0
                           (ia32e-la-to-pa-page-dir-ptr-table
                            lin-addr base-addr u/s-acc r/w-acc x/d-acc
                            wp smep smap ac nxe r-w-x cpl
                            (mv-nth 1 (wb n-w write-addr w value x86))))
                   (mv-nth 0
                           (ia32e-la-to-pa-page-dir-ptr-table
                            lin-addr base-addr u/s-acc r/w-acc x/d-acc
                            wp smep smap ac nxe r-w-x cpl x86)))
            (equal (mv-nth 1
                           (ia32e-la-to-pa-page-dir-ptr-table
                            lin-addr base-addr u/s-acc r/w-acc x/d-acc
                            wp smep smap ac nxe r-w-x cpl
                            (mv-nth 1 (wb n-w write-addr w value x86))))
                   (mv-nth 1
                           (ia32e-la-to-pa-page-dir-ptr-table
                            lin-addr base-addr u/s-acc r/w-acc x/d-acc
                            wp smep smap ac nxe r-w-x cpl x86)))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance xlate-equiv-entries-and-page-size
                            (e-1 (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr)
                                            x86))
                            (e-2 (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr)
                                            (mv-nth 1 (wb n-w write-addr w value x86)))))
                 (:instance xlate-equiv-entries-and-page-execute-disable
                            (e-1 (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr)
                                            x86))
                            (e-2 (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr)
                                            (mv-nth 1 (wb n-w write-addr w value x86)))))
                 (:instance xlate-equiv-entries-and-logtail
                            (n 12)
                            (e-1 (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr)
                                            x86))
                            (e-2 (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr)
                                            (mv-nth 1 (wb n-w write-addr w value x86)))))
                 (:instance xlate-equiv-entries-and-logtail
                            (n 30)
                            (e-1 (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr)
                                            x86))
                            (e-2 (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr)
                                            (mv-nth 1 (wb n-w write-addr w value x86))))))

           :in-theory (e/d* (disjoint-p
                             disjoint-p-commutative
                             member-p
                             ia32e-la-to-pa-page-dir-ptr-table
                             xlation-governing-entries-paddrs-for-page-dir-ptr-table)
                            (wb
                             bitops::logand-with-negated-bitmask
                             (:meta acl2::mv-nth-cons-meta)
                             force (force))))))

(defthm rm-low-64-pml4-table-entry-addr-and-mv-nth-1-wb
  ;; Different from RM-LOW-64-WB-IN-SYSTEM-LEVEL-MODE-DISJOINT, which
  ;; hangs on equal instead of xlate-equiv-entries.
  (implies
   (and (disjoint-p
         (mv-nth 1 (las-to-pas n-w write-addr :w (double-rewrite x86)))
         (xlation-governing-entries-paddrs-for-pml4-table
          lin-addr base-addr (double-rewrite x86))))
   (xlate-equiv-entries
    (rm-low-64 (pml4-table-entry-addr lin-addr base-addr)
               (mv-nth 1 (wb n-w write-addr w value x86)))
    (rm-low-64 (pml4-table-entry-addr lin-addr base-addr)
               x86)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (xlation-governing-entries-paddrs-for-pml4-table
                             disjoint-p-commutative)
                            (force (force))))))

(defthm ia32e-la-to-pa-pml4-table-values-and-mv-nth-1-wb-disjoint-from-xlation-gov-addrs
  (implies (and
            (disjoint-p
             (mv-nth 1 (las-to-pas n-w write-addr :w (double-rewrite x86)))
             (xlation-governing-entries-paddrs-for-pml4-table
              lin-addr base-addr (double-rewrite x86)))
            (canonical-address-p lin-addr)
            (physical-address-p base-addr)
            (equal (loghead 12 base-addr) 0))
           (and
            (equal (mv-nth 0
                           (ia32e-la-to-pa-pml4-table
                            lin-addr base-addr wp smep smap ac nxe r-w-x cpl
                            (mv-nth 1 (wb n-w write-addr w value x86))))
                   (mv-nth 0
                           (ia32e-la-to-pa-pml4-table
                            lin-addr base-addr wp smep smap ac nxe r-w-x cpl x86)))
            (equal (mv-nth 1
                           (ia32e-la-to-pa-pml4-table
                            lin-addr base-addr wp smep smap ac nxe r-w-x cpl
                            (mv-nth 1 (wb n-w write-addr w value x86))))
                   (mv-nth 1
                           (ia32e-la-to-pa-pml4-table
                            lin-addr base-addr wp smep smap ac nxe r-w-x cpl x86)))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance xlate-equiv-entries-and-page-execute-disable
                            (e-1 (rm-low-64 (pml4-table-entry-addr lin-addr base-addr)
                                            x86))
                            (e-2 (rm-low-64 (pml4-table-entry-addr lin-addr base-addr)
                                            (mv-nth 1 (wb n-w write-addr w value x86)))))
                 (:instance xlate-equiv-entries-and-logtail
                            (n 12)
                            (e-1 (rm-low-64 (pml4-table-entry-addr lin-addr base-addr)
                                            x86))
                            (e-2 (rm-low-64 (pml4-table-entry-addr lin-addr base-addr)
                                            (mv-nth 1 (wb n-w write-addr w value x86))))))
           :in-theory (e/d* (disjoint-p
                             disjoint-p-commutative
                             member-p
                             ia32e-la-to-pa-pml4-table
                             xlation-governing-entries-paddrs-for-pml4-table)
                            (wb
                             bitops::logand-with-negated-bitmask
                             (:meta acl2::mv-nth-cons-meta)
                             force (force))))))

(defthm ia32e-la-to-pa-values-and-mv-nth-1-wb-disjoint-from-xlation-gov-addrs
  (implies (and (disjoint-p
                 (mv-nth 1 (las-to-pas n-w write-addr :w (double-rewrite x86)))
                 (xlation-governing-entries-paddrs lin-addr (double-rewrite x86)))
                (canonical-address-p lin-addr))
           (and
            (equal (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x
                                             (mv-nth 1 (wb n-w write-addr w value x86))))
                   (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x x86)))
            (equal (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x
                                             (mv-nth 1 (wb n-w write-addr w value x86))))
                   (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x x86)))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (disjoint-p
                             disjoint-p-commutative
                             member-p
                             ia32e-la-to-pa
                             xlation-governing-entries-paddrs)
                            (wb
                             bitops::logand-with-negated-bitmask
                             (:meta acl2::mv-nth-cons-meta)
                             force (force))))))

(defthm la-to-pas-values-and-mv-nth-1-wb-disjoint-from-xlation-gov-addrs
  ;; This is a theorem that, at first glance, seems suspicious;
  ;; there's just one hypothesis --- the disjointness of the write's
  ;; physical addresses from the translation-governing addresses of
  ;; the linear region <n,lin-addr>.  All this says is: if the write
  ;; does not affect the translation-governing entries of
  ;; <n,lin-addr>, it can't change the address mapping of
  ;; <n,lin-addr>.

  ;; This is *different* from saying that after the write, a read from
  ;; <n, lin-addr> will return the same value --- for that to happen,
  ;; we need (at least) to know that the physical addresses
  ;; corresponding to <n,lin-addr> and <n-w,write-addr> are disjoint
  ;; too.
  (implies (disjoint-p
            (mv-nth 1 (las-to-pas n-w write-addr :w (double-rewrite x86)))
            (all-xlation-governing-entries-paddrs n lin-addr (double-rewrite x86)))
           (and
            (equal (mv-nth 0 (las-to-pas n lin-addr r-w-x
                                         (mv-nth 1 (wb n-w write-addr w value x86))))
                   (mv-nth 0 (las-to-pas n lin-addr r-w-x (double-rewrite x86))))
            (equal (mv-nth 1 (las-to-pas n lin-addr r-w-x
                                         (mv-nth 1 (wb n-w write-addr w value x86))))
                   (mv-nth 1 (las-to-pas n lin-addr r-w-x (double-rewrite x86))))))
  :hints (("Goal"
           :induct (las-to-pas n lin-addr r-w-x
                               (mv-nth 1 (wb n-w write-addr w value x86)))
           :in-theory (e/d* ()
                            (disjointness-of-all-xlation-governing-entries-paddrs-from-all-xlation-governing-entries-paddrs-subset-p
                             wb
                             xlation-governing-entries-paddrs
                             (:meta acl2::mv-nth-cons-meta)
                             force (force))))
          (if (equal (car id) '(0 1))
              '(:expand ((las-to-pas n lin-addr r-w-x x86)))
            nil)))

;; ======================================================================

;; Lemmas about interaction of top-level memory reads and writes:

(defthm read-from-physical-memory-and-mv-nth-1-wb-disjoint
  ;; Similar to rb-wb-disjoint-in-system-level-mode
  (implies (and (disjoint-p
                 p-addrs
                 (mv-nth 1 (las-to-pas n-w write-addr :w (double-rewrite x86))))
                (disjoint-p
                 p-addrs
                 (all-xlation-governing-entries-paddrs
                  n-w write-addr (double-rewrite x86)))
                (not (programmer-level-mode x86)))
           (equal (read-from-physical-memory p-addrs
                                             (mv-nth 1 (wb n-w write-addr w value x86)))
                  (read-from-physical-memory p-addrs x86)))
  :hints (("Goal" :in-theory (e/d* (wb) ()))))

(defthm rb-wb-disjoint-in-system-level-mode
  (implies (and
            (disjoint-p
             ;; The physical addresses pertaining to the read
             ;; operation are disjoint from those pertaining to the
             ;; write operation.
             (mv-nth 1 (las-to-pas n-w write-addr :w (double-rewrite x86)))
             (mv-nth 1 (las-to-pas n lin-addr r-w-x (double-rewrite x86))))
            (disjoint-p
             ;; The physical addresses corresponding to the read are
             ;; disjoint from the xlation-governing-entries-paddrs
             ;; pertaining to the write.
             (mv-nth 1 (las-to-pas n lin-addr r-w-x (double-rewrite x86)))
             (all-xlation-governing-entries-paddrs n-w write-addr (double-rewrite x86)))
            (disjoint-p
             ;; The physical addresses pertaining to the read are
             ;; disjoint from the xlation-governing-entries-paddrs
             ;; pertaining to the read.
             (mv-nth 1 (las-to-pas n lin-addr r-w-x (double-rewrite x86)))
             (all-xlation-governing-entries-paddrs n lin-addr (double-rewrite x86)))
            (disjoint-p
             ;; The physical addresses pertaining to the write are
             ;; disjoint from the xlation-governing-entries-paddrs
             ;; pertaining to the read.
             (mv-nth 1 (las-to-pas n-w write-addr :w (double-rewrite x86)))
             (all-xlation-governing-entries-paddrs n lin-addr (double-rewrite x86)))
            (not (programmer-level-mode x86)))
           (and
            (equal (mv-nth 0 (rb n lin-addr r-w-x
                                 (mv-nth 1 (wb n-w write-addr w value x86))))
                   (mv-nth 0 (rb n lin-addr r-w-x x86)))
            (equal (mv-nth 1 (rb n lin-addr r-w-x
                                 (mv-nth 1 (wb n-w write-addr w value x86))))
                   (mv-nth 1 (rb n lin-addr r-w-x x86)))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance xlate-equiv-memory-and-las-to-pas
                            (x86-1 (mv-nth 2 (las-to-pas n-w write-addr :w x86)))
                            (x86-2 x86)))
           :in-theory (e/d* (disjoint-p-commutative)
                            (wb
                             disjointness-of-all-xlation-governing-entries-paddrs-from-all-xlation-governing-entries-paddrs-subset-p)))))

(defthmd rb-wb-equal-in-system-level-mode
  (implies (and (equal
                 ;; The physical addresses pertaining to the read
                 ;; operation are equal to those pertaining to the
                 ;; write operation.
                 (mv-nth 1 (las-to-pas n lin-addr r-w-x (double-rewrite x86)))
                 (mv-nth 1 (las-to-pas n-w write-addr :w (double-rewrite x86))))
                (disjoint-p
                 ;; The physical addresses pertaining to the write are
                 ;; disjoint from the xlation-governing-entries-paddrs
                 ;; pertaining to the read.
                 (mv-nth 1 (las-to-pas n-w write-addr :w (double-rewrite x86)))
                 (all-xlation-governing-entries-paddrs n lin-addr (double-rewrite x86)))

                (no-duplicates-p
                 (mv-nth 1 (las-to-pas n-w write-addr :w x86)))
                (not (mv-nth 0 (las-to-pas n lin-addr r-w-x x86)))
                (not (mv-nth 0 (las-to-pas n-w write-addr :w x86)))
                (unsigned-byte-p (ash n-w 3) value)
                (natp n-w)
                (x86p x86))
           (equal (mv-nth 1 (rb n lin-addr r-w-x
                                (mv-nth 1 (wb n-w write-addr w value x86))))
                  value))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d* (disjoint-p-commutative) (force (force)))
           :use ((:instance xlate-equiv-memory-and-las-to-pas
                            (x86-1 (mv-nth 2 (las-to-pas n-w write-addr :w x86)))
                            (x86-2 x86))))))

;; ======================================================================

(globally-disable '(rb
                    wb
                    canonical-address-p
                    prog-at
                    las-to-pas
                    all-xlation-governing-entries-paddrs
                    unsigned-byte-p
                    signed-byte-p))

(in-theory (e/d*
            ;; We enable all these functions so that reasoning about
            ;; memory can be done in terms of rb and wb.
            (rim-size
             rm-size
             wim-size
             wm-size
             rm08 rim08 wm08 wim08
             rm16 rim16 wm16 wim16
             rm32 rim32 wm32 wim32
             rm64 rim64 wm64 wim64)
            ()))

;; ======================================================================

(defthm xlate-equiv-memory-is-equal-in-programmer-level-mode
  ;; TODO: Move to paging/gather-paging-structures.lisp?
  (implies (programmer-level-mode x86-1)
           (iff (xlate-equiv-memory x86-1 x86-2)
                (equal x86-1 x86-2)))
  :hints (("Goal" :in-theory (e/d* (xlate-equiv-memory) ()))))

(defsection xlate-equiv-memory-and-rm08
  :parents (system-level-marking-mode-proof-utilities)

  (defthmd xlate-equiv-memory-and-rvm08
    (implies (and (xr :programmer-level-mode 0 x86-1)
                  (xlate-equiv-memory x86-1 x86-2))
             (and (equal (mv-nth 0 (rvm08 lin-addr x86-1))
                         (mv-nth 0 (rvm08 lin-addr x86-2)))
                  (equal (mv-nth 1 (rvm08 lin-addr x86-1))
                         (mv-nth 1 (rvm08 lin-addr x86-2)))))
    :hints (("Goal" :in-theory (e/d* (xlate-equiv-memory)
                                     (force (force))))))


  (defthm xlate-equiv-memory-and-mv-nth-0-rm08-cong
    (implies (xlate-equiv-memory x86-1 x86-2)
             (equal (mv-nth 0 (rm08 lin-addr r-w-x x86-1))
                    (mv-nth 0 (rm08 lin-addr r-w-x x86-2))))
    :hints
    (("Goal" :cases ((xr :programmer-level-mode 0 x86-1))
      :in-theory (e/d* (rm08 disjoint-p member-p)
                       (force (force)))
      :use ((:instance xlate-equiv-memory-and-rvm08))))
    :rule-classes :congruence)

  (defthmd xlate-equiv-memory-and-xr-mem-from-rest-of-memory
    (implies
     (and (bind-free
           (find-an-xlate-equiv-x86
            'xlate-equiv-memory-and-xr-mem-from-rest-of-memory
            x86-1 'x86-2 mfc state)
           (x86-2))
          (syntaxp (not (equal x86-1 x86-2)))
          (xlate-equiv-memory (double-rewrite x86-1) x86-2)
          (disjoint-p (list j)
                      (open-qword-paddr-list
                       (gather-all-paging-structure-qword-addresses (double-rewrite x86-1))))
          (natp j)
          (< j *mem-size-in-bytes*))
     (equal (xr :mem j x86-1) (xr :mem j x86-2)))
    :hints (("Goal" :in-theory (e/d* (xlate-equiv-memory disjoint-p) ()))))

  (defthm xlate-equiv-memory-and-mv-nth-1-rm08
    (implies
     (and (bind-free
           (find-an-xlate-equiv-x86
            'xlate-equiv-memory-and-mv-nth-1-rm08
            x86-1 'x86-2 mfc state)
           (x86-2))
          (syntaxp (not (equal x86-1 x86-2)))
          (xlate-equiv-memory (double-rewrite x86-1) x86-2)
          (disjoint-p
           (list (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x x86-1)))
           (open-qword-paddr-list
            (gather-all-paging-structure-qword-addresses (double-rewrite x86-1)))))
     (equal (mv-nth 1 (rm08 lin-addr r-w-x x86-1))
            (mv-nth 1 (rm08 lin-addr r-w-x x86-2))))
    :hints (("Goal"
             :cases ((xr :programmer-level-mode 0 x86-1))
             :in-theory (e/d* (rm08
                               rb
                               disjoint-p
                               member-p
                               las-to-pas)
                              (force (force)))
             :use ((:instance xlate-equiv-memory-and-xr-mem-from-rest-of-memory
                              (j (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x x86-1)))
                              (x86-1 (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x x86-1)))
                              (x86-2 (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x x86-2))))
                   (:instance xlate-equiv-memory-and-rvm08)))))

  (defthm xlate-equiv-memory-and-two-mv-nth-2-rm08-cong
    (implies (xlate-equiv-memory x86-1 x86-2)
             (xlate-equiv-memory (mv-nth 2 (rm08 lin-addr r-w-x x86-1))
                                 (mv-nth 2 (rm08 lin-addr r-w-x x86-2))))
    :hints (("Goal" :in-theory (e/d* (rm08 rb) (force (force)))))
    :rule-classes :congruence)

  (defthm xlate-equiv-memory-and-mv-nth-2-rm08
    (xlate-equiv-memory (mv-nth 2 (rm08 lin-addr r-w-x x86)) x86)
    :hints (("Goal" :in-theory (e/d* (rm08 rb) (force (force)))))))

;; ======================================================================

;; Get-prefixes in system-level marking mode:

(defsection get-prefixes-in-system-level-marking-mode
  :parents (system-level-marking-mode-proof-utilities)

  (local (in-theory (e/d* () ((tau-system) not))))

  (defthmd xr-not-mem-and-get-prefixes
    ;; I don't need this lemma in the programmer-level mode because
    ;; (mv-nth 2 (get-prefixes ... x86)) == x86 there.
    (implies (and (not (equal fld :mem))
                  (not (equal fld :fault)))
             (equal (xr fld index (mv-nth 2 (get-prefixes start-rip prefixes cnt x86)))
                    (xr fld index x86)))
    :hints (("Goal"
             :induct (get-prefixes start-rip prefixes cnt x86)
             :in-theory (e/d* (get-prefixes rm08 rb las-to-pas)
                              (negative-logand-to-positive-logand-with-integerp-x
                               unsigned-byte-p-of-logior
                               acl2::loghead-identity
                               not force (force))))))

  ;; The following make-events generate a bunch of rules that together
  ;; say the same thing as xr-not-mem-and-get-prefixes, but these
  ;; rules are more efficient than xr-not-mem-and-get-prefixes as they
  ;; match less frequently.
  (make-event
   (generate-xr-over-write-thms
    (remove-elements-from-list
     '(:mem :fault)
     *x86-field-names-as-keywords*)
    'get-prefixes
    (acl2::formals 'get-prefixes (w state))
    :output-index 2
    :prepwork '((local (in-theory (e/d (xr-not-mem-and-get-prefixes) ()))))))

  (defthm xr-fault-and-get-prefixes
    (implies (not (mv-nth 0 (las-to-pas cnt start-rip :x x86)))
             (equal (xr :fault index (mv-nth 2 (get-prefixes start-rip prefixes cnt x86)))
                    (xr :fault index x86)))
    :hints (("Goal"
             :induct (get-prefixes start-rip prefixes cnt x86)
             :in-theory (e/d* (get-prefixes rb las-to-pas)
                              (mv-nth-0-ia32e-la-to-pa-member-of-mv-nth-1-las-to-pas-if-lin-addr-member-p
                               negative-logand-to-positive-logand-with-integerp-x
                               unsigned-byte-p-of-logior
                               subset-p
                               not force (force))))))

  (defthmd get-prefixes-xw-values-in-system-level-mode
    (implies (and (not (programmer-level-mode x86))
                  (not (equal fld :mem))
                  (not (equal fld :rflags))
                  (not (equal fld :ctr))
                  (not (equal fld :seg-visible))
                  (not (equal fld :msr))
                  (not (equal fld :fault))
                  (not (equal fld :programmer-level-mode))
                  (not (equal fld :page-structure-marking-mode)))
             (and (equal (mv-nth 0 (get-prefixes start-rip prefixes cnt (xw fld index value x86)))
                         (mv-nth 0 (get-prefixes start-rip prefixes cnt x86)))
                  (equal (mv-nth 1 (get-prefixes start-rip prefixes cnt (xw fld index value x86)))
                         (mv-nth 1 (get-prefixes start-rip prefixes cnt x86)))))
    :hints (("Goal"
             :induct (get-prefixes start-rip prefixes cnt x86)
             :expand (get-prefixes start-rip prefixes cnt (xw fld index value x86))
             :in-theory (e/d* (get-prefixes
                               rb
                               las-to-pas)
                              (rm08
                               negative-logand-to-positive-logand-with-integerp-x
                               unsigned-byte-p-of-logior
                               acl2::ash-0
                               acl2::zip-open
                               acl2::ifix-when-not-integerp
                               acl2::loghead-identity
                               (:t bitops::logior-natp-type)
                               (:t natp-get-prefixes)
                               (:t n08p-mv-nth-1-rm08)
                               force (force))))))

  (defthmd get-prefixes-xw-state-in-system-level-mode
    (implies (and (not (programmer-level-mode x86))
                  (not (equal fld :mem))
                  (not (equal fld :rflags))
                  (not (equal fld :ctr))
                  (not (equal fld :seg-visible))
                  (not (equal fld :msr))
                  (not (equal fld :fault))
                  (not (equal fld :programmer-level-mode))
                  (not (equal fld :page-structure-marking-mode)))
             (equal (mv-nth 2 (get-prefixes start-rip prefixes cnt (xw fld index value x86)))
                    (xw fld index value (mv-nth 2 (get-prefixes start-rip prefixes cnt x86)))))
    :hints (("Goal"
             :induct (get-prefixes start-rip prefixes cnt x86)
             :expand (get-prefixes start-rip prefixes cnt (xw fld index value x86))
             :in-theory (e/d* (get-prefixes
                               las-to-pas
                               rb)
                              (rm08
                               negative-logand-to-positive-logand-with-integerp-x
                               unsigned-byte-p-of-logior
                               acl2::ash-0
                               acl2::zip-open
                               acl2::ifix-when-not-integerp
                               acl2::loghead-identity
                               (:t bitops::logior-natp-type)
                               (:t natp-get-prefixes)
                               (:t n08p-mv-nth-1-rm08)
                               force (force))))))

  (make-event
   (generate-read-fn-over-xw-thms
    (remove-elements-from-list
     '(:mem :rflags :ctr :seg-visible :msr :fault :programmer-level-mode :page-structure-marking-mode)
     *x86-field-names-as-keywords*)
    'get-prefixes
    (acl2::formals 'get-prefixes (w state))
    :output-index 0
    :prepwork '((local (in-theory (e/d (get-prefixes-xw-values-in-system-level-mode
                                        get-prefixes-xw-state-in-system-level-mode)
                                       ()))))
    :hyps '(not (programmer-level-mode x86))))

  (make-event
   (generate-read-fn-over-xw-thms
    (remove-elements-from-list
     '(:mem :rflags :ctr :seg-visible :msr :fault :programmer-level-mode :page-structure-marking-mode)
     *x86-field-names-as-keywords*)
    'get-prefixes
    (acl2::formals 'get-prefixes (w state))
    :output-index 1
    :prepwork '((local (in-theory (e/d (get-prefixes-xw-values-in-system-level-mode
                                        get-prefixes-xw-state-in-system-level-mode)
                                       ()))))
    :hyps '(not (programmer-level-mode x86))))

  (make-event
   (generate-write-fn-over-xw-thms
    (remove-elements-from-list
     '(:mem :rflags :ctr :seg-visible :msr :fault :programmer-level-mode :page-structure-marking-mode)
     *x86-field-names-as-keywords*)
    'get-prefixes
    (acl2::formals 'get-prefixes (w state))
    :output-index 2
    :prepwork '((local (in-theory (e/d (get-prefixes-xw-values-in-system-level-mode
                                        get-prefixes-xw-state-in-system-level-mode)
                                       ()))))
    :hyps '(not (programmer-level-mode x86))))

  (defthm get-prefixes-xw-rflags-not-ac-state-in-system-level-mode
    (implies (and (not (programmer-level-mode x86))
                  (equal (rflags-slice :ac value)
                         (rflags-slice :ac (rflags x86))))
             (equal (mv-nth 2 (get-prefixes start-rip prefixes cnt (xw :rflags 0 value x86)))
                    (xw :rflags 0 value (mv-nth 2 (get-prefixes start-rip prefixes cnt x86)))))
    :hints (("Goal"
             :induct (get-prefixes start-rip prefixes cnt x86)
             :expand (get-prefixes start-rip prefixes cnt (xw :rflags 0 value x86))
             :in-theory (e/d* (get-prefixes)
                              (negative-logand-to-positive-logand-with-integerp-x
                               unsigned-byte-p-of-logior
                               acl2::ash-0
                               acl2::zip-open
                               acl2::ifix-when-not-integerp
                               acl2::loghead-identity
                               (:t bitops::logior-natp-type)
                               (:t natp-get-prefixes)
                               (:t n08p-mv-nth-1-rm08)
                               force (force))))))

  (defthm get-prefixes-and-!flgi-state-in-system-level-mode
    (implies (and (not (equal index *ac*))
                  (not (programmer-level-mode x86))
                  (x86p x86))
             (equal (mv-nth 2 (get-prefixes start-rip prefixes cnt (!flgi index value x86)))
                    (!flgi index value (mv-nth 2 (get-prefixes start-rip prefixes cnt x86)))))
    :hints (("Goal"
             :do-not-induct t
             :cases ((equal index *iopl*))
             :use ((:instance rflags-slice-ac-simplify
                              (index index)
                              (rflags (xr :rflags 0 x86)))
                   (:instance get-prefixes-xw-rflags-not-ac-state-in-system-level-mode
                              (value (logior (loghead 32 (ash (loghead 1 value) (nfix index)))
                                             (logand (xr :rflags 0 x86)
                                                     (loghead 32 (lognot (expt 2 (nfix index))))))))
                   (:instance get-prefixes-xw-rflags-not-ac-state-in-system-level-mode
                              (value (logior (ash (loghead 2 value) 12)
                                             (logand 4294955007 (xr :rflags 0 x86))))))
             :in-theory (e/d* (!flgi-open-to-xw-rflags
                               !flgi)
                              (force (force))))))

  (defthm get-prefixes-xw-rflags-not-ac-values-in-system-level-mode
    (implies (and (not (programmer-level-mode x86))
                  (equal (rflags-slice :ac value)
                         (rflags-slice :ac (rflags x86))))
             (and
              (equal (mv-nth 0 (get-prefixes start-rip prefixes cnt (xw :rflags 0 value x86)))
                     (mv-nth 0 (get-prefixes start-rip prefixes cnt x86)))
              (equal (mv-nth 1 (get-prefixes start-rip prefixes cnt (xw :rflags 0 value x86)))
                     (mv-nth 1 (get-prefixes start-rip prefixes cnt x86)))))
    :hints (("Goal"
             :induct (get-prefixes start-rip prefixes cnt x86)
             :expand (get-prefixes start-rip prefixes cnt (xw :rflags 0 value x86))
             :in-theory (e/d* (get-prefixes)
                              (rm08 force (force))))))

  (defthm get-prefixes-values-and-!flgi-in-system-level-mode
    (implies (and (not (equal index *ac*))
                  (not (programmer-level-mode x86))
                  (x86p x86))
             (and (equal (mv-nth 0 (get-prefixes start-rip prefixes cnt (!flgi index value x86)))
                         (mv-nth 0 (get-prefixes start-rip prefixes cnt x86)))
                  (equal (mv-nth 1 (get-prefixes start-rip prefixes cnt (!flgi index value x86)))
                         (mv-nth 1 (get-prefixes start-rip prefixes cnt x86)))))
    :hints (("Goal"
             :do-not-induct t
             :cases ((equal index *iopl*))
             :use ((:instance rflags-slice-ac-simplify
                              (index index)
                              (rflags (xr :rflags 0 x86)))
                   (:instance get-prefixes-xw-rflags-not-ac-values-in-system-level-mode
                              (value (logior (loghead 32 (ash (loghead 1 value) (nfix index)))
                                             (logand (xr :rflags 0 x86)
                                                     (loghead 32 (lognot (expt 2 (nfix index))))))))
                   (:instance get-prefixes-xw-rflags-not-ac-values-in-system-level-mode
                              (value (logior (ash (loghead 2 value) 12)
                                             (logand 4294955007 (xr :rflags 0 x86))))))
             :in-theory (e/d* (!flgi-open-to-xw-rflags
                               !flgi)
                              (rm08
                               get-prefixes-xw-rflags-not-ac-values-in-system-level-mode
                               force (force))))))

  ;; Opener lemmas:

  (defthm get-prefixes-opener-lemma-group-1-prefix-in-marking-mode
    (implies
     (and
      (canonical-address-p (1+ start-rip))
      (not (zp cnt))
      (equal (prefixes-slice :group-1-prefix prefixes) 0)
      (let*
          ((flg (mv-nth 0 (rm08 start-rip :x x86)))
           (prefix-byte-group-code
            (get-one-byte-prefix-array-code (mv-nth 1 (rm08 start-rip :x x86)))))
        (and (not flg)
             (equal prefix-byte-group-code 1))))
     (equal (get-prefixes start-rip prefixes cnt x86)
            (get-prefixes (+ 1 start-rip)
                          (!prefixes-slice :group-1-prefix
                                           (mv-nth 1 (rm08 start-rip :x x86))
                                           prefixes)
                          (+ -1 cnt)
                          (mv-nth 2 (rm08 start-rip :x x86)))))
    :hints (("Goal"
             :induct (get-prefixes start-rip prefixes cnt x86)
             :in-theory (e/d* (get-prefixes
                               las-to-pas)
                              (acl2::ash-0
                               acl2::zip-open
                               byte-listp
                               unsigned-byte-p-of-logior
                               negative-logand-to-positive-logand-with-integerp-x
                               force (force))))))

  (defthm get-prefixes-opener-lemma-group-2-prefix-in-marking-mode
    (implies (and
              (canonical-address-p (1+ start-rip))
              (not (zp cnt))
              (equal (prefixes-slice :group-2-prefix prefixes) 0)
              (let*
                  ((flg (mv-nth 0 (rm08 start-rip :x x86)))
                   (prefix-byte-group-code
                    (get-one-byte-prefix-array-code (mv-nth 1 (rm08 start-rip :x x86)))))
                (and (not flg)
                     (equal prefix-byte-group-code 2))))
             (equal (get-prefixes start-rip prefixes cnt x86)
                    (get-prefixes (1+ start-rip)
                                  (!prefixes-slice :group-2-prefix
                                                   (mv-nth 1 (rm08 start-rip :x x86))
                                                   prefixes)
                                  (1- cnt)
                                  (mv-nth 2 (rm08 start-rip :x x86)))))
    :hints (("Goal"
             :induct (get-prefixes start-rip prefixes cnt x86)
             :in-theory (e/d* (get-prefixes
                               las-to-pas)
                              (acl2::ash-0
                               acl2::zip-open
                               byte-listp
                               unsigned-byte-p-of-logior
                               negative-logand-to-positive-logand-with-integerp-x
                               force (force))))))

  (defthm get-prefixes-opener-lemma-group-3-prefix-in-marking-mode
    (implies (and
              (canonical-address-p (1+ start-rip))
              (not (zp cnt))
              (equal (prefixes-slice :group-3-prefix prefixes) 0)
              (let*
                  ((flg (mv-nth 0 (rm08 start-rip :x x86)))
                   (prefix-byte-group-code
                    (get-one-byte-prefix-array-code (mv-nth 1 (rm08 start-rip :x x86)))))
                (and (not flg)
                     (equal prefix-byte-group-code 3))))
             (equal (get-prefixes start-rip prefixes cnt x86)
                    (get-prefixes (1+ start-rip)
                                  (!prefixes-slice :group-3-prefix
                                                   (mv-nth 1 (rm08 start-rip :x x86))
                                                   prefixes)
                                  (1- cnt)
                                  (mv-nth 2 (rm08 start-rip :x x86)))))
    :hints (("Goal"
             :induct (get-prefixes start-rip prefixes cnt x86)
             :in-theory (e/d* (get-prefixes
                               las-to-pas)
                              (acl2::ash-0
                               acl2::zip-open
                               byte-listp
                               unsigned-byte-p-of-logior
                               negative-logand-to-positive-logand-with-integerp-x
                               force (force))))))

  (defthm get-prefixes-opener-lemma-group-4-prefix-in-marking-mode
    (implies (and
              (canonical-address-p (1+ start-rip))
              (not (zp cnt))
              (equal (prefixes-slice :group-4-prefix prefixes) 0)
              (let*
                  ((flg (mv-nth 0 (rm08 start-rip :x x86)))
                   (prefix-byte-group-code
                    (get-one-byte-prefix-array-code (mv-nth 1 (rm08 start-rip :x x86)))))
                (and (not flg)
                     (equal prefix-byte-group-code 4))))
             (equal (get-prefixes start-rip prefixes cnt x86)
                    (get-prefixes (1+ start-rip)
                                  (!prefixes-slice :group-4-prefix
                                                   (mv-nth 1 (rm08 start-rip :x x86))
                                                   prefixes)
                                  (1- cnt)
                                  (mv-nth 2 (rm08 start-rip :x x86)))))
    :hints (("Goal"
             :induct (get-prefixes start-rip prefixes cnt x86)
             :in-theory (e/d* (get-prefixes
                               las-to-pas)
                              (acl2::ash-0
                               acl2::zip-open
                               byte-listp
                               unsigned-byte-p-of-logior
                               negative-logand-to-positive-logand-with-integerp-x
                               force (force))))))

  ;; Get-prefixes and xlate-equiv-memory:

  (defun-nx get-prefixes-two-x86-induct-hint
    (start-rip prefixes cnt x86-1 x86-2)
    (declare (xargs :measure (nfix cnt)))
    (if (zp cnt)
        ;; Error, too many prefix bytes
        (mv nil prefixes x86-1 x86-2)

      (b* ((ctx 'get-prefixes-two-x86-induct-hint)
           ((mv flg-1 byte-1 x86-1)
            (rm08 start-rip :x x86-1))
           ((mv flg-2 byte-2 x86-2)
            (rm08 start-rip :x x86-2))
           ((when flg-1)
            (mv (cons ctx flg-1) byte-1 x86-1))
           ((when flg-2)
            (mv (cons ctx flg-2) byte-2 x86-2))
           ;; Quit if byte-1 and byte-2 aren't equal...
           ((when (not (equal byte-1 byte-2)))
            (mv nil prefixes x86-1 x86-2))
           (byte byte-1)

           (prefix-byte-group-code
            (get-one-byte-prefix-array-code byte)))

        (if (zp prefix-byte-group-code)
            (let ((prefixes
                   (!prefixes-slice :next-byte byte prefixes)))
              (mv nil (!prefixes-slice :num-prefixes (- 5 cnt) prefixes) x86-1 x86-2))

          (case prefix-byte-group-code
            (1 (let ((prefix-1?
                      (prefixes-slice :group-1-prefix prefixes)))
                 (if (or (eql 0 (the (unsigned-byte 8) prefix-1?))
                         ;; Redundant Prefix Okay
                         (eql byte prefix-1?))
                     (let ((next-rip (the (signed-byte
                                           #.*max-linear-address-size+1*)
                                          (1+ start-rip))))
                       (if (mbe :logic (canonical-address-p next-rip)
                                :exec
                                (< (the (signed-byte
                                         #.*max-linear-address-size+1*)
                                        next-rip)
                                   #.*2^47*))
                           ;; Storing the group 1 prefix and going on...
                           (get-prefixes-two-x86-induct-hint
                            next-rip
                            (the (unsigned-byte 43)
                                 (!prefixes-slice :group-1-prefix
                                                  byte
                                                  prefixes))
                            (the (integer 0 5) (1- cnt))
                            x86-1
                            x86-2)
                         (mv (cons 'non-canonical-address next-rip) prefixes x86-1 x86-2)))
                   ;; We do not tolerate more than one prefix from a prefix group.
                   (mv t prefixes x86-1 x86-2))))

            (2 (let ((prefix-2?
                      (prefixes-slice :group-2-prefix prefixes)))
                 (if (or (eql 0 (the (unsigned-byte 8) prefix-2?))
                         ;; Redundant Prefixes Okay
                         (eql byte (the (unsigned-byte 8) prefix-2?)))
                     (let ((next-rip (the (signed-byte
                                           #.*max-linear-address-size+1*)
                                          (1+ start-rip))))
                       (if (mbe :logic (canonical-address-p next-rip)
                                :exec
                                (< (the (signed-byte
                                         #.*max-linear-address-size+1*)
                                        next-rip)
                                   #.*2^47*))
                           ;; Storing the group 2 prefix and going on...
                           (get-prefixes-two-x86-induct-hint
                            next-rip
                            (!prefixes-slice :group-2-prefix
                                             byte
                                             prefixes)
                            (the (integer 0 5) (1- cnt))
                            x86-1 x86-2)
                         (mv (cons 'non-canonical-address next-rip)
                             prefixes x86-1 x86-2)))
                   ;; We do not tolerate more than one prefix from a prefix group.
                   (mv t prefixes x86-1 x86-2))))

            (3 (let ((prefix-3?
                      (prefixes-slice :group-3-prefix prefixes)))
                 (if (or (eql 0 (the (unsigned-byte 8) prefix-3?))
                         ;; Redundant Prefix Okay
                         (eql byte (the (unsigned-byte 8) prefix-3?)))

                     (let ((next-rip (the (signed-byte
                                           #.*max-linear-address-size+1*)
                                          (1+ start-rip))))
                       (if (mbe :logic (canonical-address-p next-rip)
                                :exec
                                (< (the (signed-byte
                                         #.*max-linear-address-size+1*)
                                        next-rip)
                                   #.*2^47*))
                           ;; Storing the group 3 prefix and going on...
                           (get-prefixes-two-x86-induct-hint
                            next-rip
                            (!prefixes-slice :group-3-prefix
                                             byte
                                             prefixes)
                            (the (integer 0 5) (1- cnt)) x86-1 x86-2)
                         (mv (cons 'non-canonical-address next-rip)
                             prefixes x86-1 x86-2)))
                   ;; We do not tolerate more than one prefix from a prefix group.
                   (mv t prefixes x86-1 x86-2))))

            (4 (let ((prefix-4?
                      (prefixes-slice :group-4-prefix prefixes)))
                 (if (or (eql 0 (the (unsigned-byte 8) prefix-4?))
                         ;; Redundant Prefix Okay
                         (eql byte (the (unsigned-byte 8) prefix-4?)))
                     (let ((next-rip (the (signed-byte
                                           #.*max-linear-address-size+1*)
                                          (1+ start-rip))))
                       (if (mbe :logic (canonical-address-p next-rip)
                                :exec
                                (< (the (signed-byte
                                         #.*max-linear-address-size+1*)
                                        next-rip)
                                   #.*2^47*))
                           ;; Storing the group 4 prefix and going on...
                           (get-prefixes-two-x86-induct-hint
                            next-rip
                            (!prefixes-slice :group-4-prefix
                                             byte
                                             prefixes)
                            (the (integer 0 5) (1- cnt))
                            x86-1 x86-2)
                         (mv (cons 'non-canonical-address next-rip)
                             prefixes x86-1 x86-2)))
                   ;; We do not tolerate more than one prefix from a prefix group.
                   (mv t prefixes x86-1 x86-2))))

            (otherwise
             (mv t prefixes x86-1 x86-2)))))))

  (defthm xlate-equiv-memory-and-two-get-prefixes-values
    (implies
     (and
      (bind-free
       (find-an-xlate-equiv-x86
        'xlate-equiv-memory-and-two-get-prefixes-values
        x86-1 'x86-2 mfc state)
       (x86-2))
      (syntaxp (not (equal x86-1 x86-2)))
      (xlate-equiv-memory (double-rewrite x86-1) x86-2)
      (canonical-address-p start-rip)
      (not (mv-nth 0 (las-to-pas cnt start-rip :x x86-1)))
      (disjoint-p
       (mv-nth 1 (las-to-pas cnt start-rip :x x86-1))
       (open-qword-paddr-list
        (gather-all-paging-structure-qword-addresses (double-rewrite x86-1)))))
     (and (equal (mv-nth 0 (get-prefixes start-rip prefixes cnt x86-1))
                 (mv-nth 0 (get-prefixes start-rip prefixes cnt x86-2)))
          (equal (mv-nth 1 (get-prefixes start-rip prefixes cnt x86-1))
                 (mv-nth 1 (get-prefixes start-rip prefixes cnt x86-2)))))
    :hints (("Goal"
             :induct (get-prefixes-two-x86-induct-hint start-rip prefixes cnt x86-1 x86-2)
             :in-theory (e/d* (get-prefixes disjoint-p
                                            member-p las-to-pas
                                            mv-nth-0-las-to-pas-subset-p)
                              ()))
            (if
                ;; Apply to all subgoals under a top-level induction.
                (and (consp (car id))
                     (< 1 (len (car id))))
                '(:expand ((las-to-pas cnt start-rip :x x86-1)
                           (get-prefixes start-rip prefixes cnt x86-1)
                           (get-prefixes start-rip prefixes cnt x86-2))
                          :use
                          ((:instance xlate-equiv-memory-and-mv-nth-0-rm08-cong
                                      (lin-addr start-rip)
                                      (r-w-x :x))
                           (:instance xlate-equiv-memory-and-mv-nth-1-rm08
                                      (lin-addr start-rip)
                                      (r-w-x :x)))
                          :in-theory
                          (e/d* (disjoint-p
                                 member-p
                                 get-prefixes
                                 las-to-pas
                                 mv-nth-0-las-to-pas-subset-p)
                                (rm08
                                 xlate-equiv-memory-and-mv-nth-0-rm08-cong
                                 xlate-equiv-memory-and-mv-nth-1-rm08
                                 (:rewrite mv-nth-0-ia32e-la-to-pa-member-of-mv-nth-1-las-to-pas-if-lin-addr-member-p))))
              nil)))

  (defthm xlate-equiv-memory-and-mv-nth-2-get-prefixes
    (implies (and (not (programmer-level-mode (double-rewrite x86)))
                  (page-structure-marking-mode (double-rewrite x86))
                  (canonical-address-p start-rip)
                  (not (mv-nth 0 (las-to-pas cnt start-rip :x (double-rewrite x86)))))
             (xlate-equiv-memory (mv-nth 2 (get-prefixes start-rip prefixes cnt x86))
                                 (double-rewrite x86)))
    :hints (("Goal"
             :induct (get-prefixes start-rip prefixes cnt x86)
             :in-theory (e/d* (get-prefixes  mv-nth-0-las-to-pas-subset-p subset-p)
                              (rm08
                               acl2::ash-0
                               acl2::zip-open
                               cdr-create-canonical-address-list
                               force (force))))
            (if
                ;; Apply to all subgoals under a top-level induction.
                (and (consp (car id))
                     (< 1 (len (car id))))
                '(:in-theory (e/d* (subset-p get-prefixes mv-nth-0-las-to-pas-subset-p)
                                   (rm08
                                    acl2::ash-0
                                    acl2::zip-open
                                    force (force)))
                             :expand ((las-to-pas cnt start-rip :x x86))
                             :use ((:instance xlate-equiv-memory-and-las-to-pas
                                              (n (+ -1 cnt))
                                              (lin-addr (+ 1 start-rip))
                                              (r-w-x :x)
                                              (x86-1
                                               (mv-nth 2
                                                       (las-to-pas 1 start-rip :x x86)))
                                              (x86-2 x86))))
              nil)))

  (defthmd xlate-equiv-memory-and-two-mv-nth-2-get-prefixes
    (implies (and (xlate-equiv-memory x86-1 x86-2)
                  (not (programmer-level-mode x86-2))
                  (page-structure-marking-mode (double-rewrite x86-2))
                  (canonical-address-p start-rip)
                  (not (mv-nth 0 (las-to-pas cnt start-rip :x (double-rewrite x86-2)))))
             (xlate-equiv-memory (mv-nth 2 (get-prefixes start-rip prefixes cnt x86-1))
                                 (mv-nth 2 (get-prefixes start-rip prefixes cnt x86-2))))
    :hints (("Goal"
             :use ((:instance xlate-equiv-memory-and-mv-nth-2-get-prefixes (x86 x86-1))
                   (:instance xlate-equiv-memory-and-mv-nth-2-get-prefixes (x86 x86-2)))
             :in-theory (e/d* ()
                              (xlate-equiv-memory-and-mv-nth-2-get-prefixes
                               acl2::ash-0
                               acl2::zip-open
                               cdr-create-canonical-address-list))))))

;; ======================================================================

;; rb in system-level marking mode:

(defsection rb-in-system-level-marking-mode
  :parents (system-level-marking-mode-proof-utilities)

  (defthm xr-fault-rb-state-in-system-level-mode
    (implies (not (mv-nth 0 (las-to-pas n lin-addr r-w-x (double-rewrite x86))))
             (equal (xr :fault index (mv-nth 2 (rb n lin-addr r-w-x x86)))
                    (xr :fault index x86)))
    :hints (("Goal" :in-theory (e/d* (las-to-pas rb) (force (force))))))

  (defthm rb-and-!flgi-state-in-system-level-mode
    (implies (and (not (equal index *ac*))
                  (x86p x86))
             (equal (mv-nth 2 (rb n lin-addr r-w-x (!flgi index value x86)))
                    (!flgi index value (mv-nth 2 (rb n lin-addr r-w-x x86)))))
    :hints (("Goal"
             :do-not-induct t
             :cases ((equal index *iopl*))
             :use ((:instance rflags-slice-ac-simplify
                              (index index)
                              (rflags (xr :rflags 0 x86)))
                   (:instance rb-xw-rflags-not-ac-state-in-system-level-mode
                              (r-x r-w-x)
                              (addr lin-addr)
                              (value (logior (loghead 32 (ash (loghead 1 value) (nfix index)))
                                             (logand (xr :rflags 0 x86)
                                                     (loghead 32 (lognot (expt 2 (nfix index))))))))
                   (:instance rb-xw-rflags-not-ac-state-in-system-level-mode
                              (r-x r-w-x)
                              (addr lin-addr)
                              (value (logior (ash (loghead 2 value) 12)
                                             (logand 4294955007 (xr :rflags 0 x86))))))
             :in-theory (e/d* (!flgi-open-to-xw-rflags)
                              (force (force))))))

  (defthm mv-nth-0-rb-and-xlate-equiv-memory-cong
    (implies (xlate-equiv-memory x86-1 x86-2)
             (equal (mv-nth 0 (rb n lin-addr r-w-x x86-1))
                    (mv-nth 0 (rb n lin-addr r-w-x x86-2))))
    :hints (("Goal" :in-theory (e/d* (rb) (force (force)))))
    :rule-classes :congruence)

  (defthm read-from-physical-memory-and-xlate-equiv-memory-disjoint-from-paging-structures
    (implies
     (and (bind-free
           (find-an-xlate-equiv-x86
            'read-from-physical-memory-and-xlate-equiv-memory
            x86-1 'x86-2 mfc state)
           (x86-2))
          (syntaxp (and (not (eq x86-2 x86-1))
                        ;; x86-2 must be "smaller" than x86-1.
                        (term-order x86-2 x86-1)))
          (xlate-equiv-memory (double-rewrite x86-1) x86-2)
          (disjoint-p
           (mv-nth 1 (las-to-pas n lin-addr r-w-x (double-rewrite x86-1)))
           (open-qword-paddr-list
            (gather-all-paging-structure-qword-addresses (double-rewrite x86-1)))))
     (equal (read-from-physical-memory (mv-nth 1 (las-to-pas n lin-addr r-w-x x86-1)) x86-1)
            (read-from-physical-memory (mv-nth 1 (las-to-pas n lin-addr r-w-x x86-1)) x86-2)))
    :hints (("Goal"
             :induct (cons (las-to-pas n lin-addr r-w-x x86-1)
                           (las-to-pas n lin-addr r-w-x x86-2))
             :in-theory (e/d* (las-to-pas disjoint-p)
                              (disjointness-of-all-xlation-governing-entries-paddrs-from-all-xlation-governing-entries-paddrs-subset-p force (force))))
            (if
                ;; Apply to all subgoals under a top-level induction.
                (and (consp (car id))
                     (< 1 (len (car id))))
                '(:in-theory
                  (e/d* (las-to-pas disjoint-p)
                        (disjointness-of-all-xlation-governing-entries-paddrs-from-all-xlation-governing-entries-paddrs-subset-p force (force)))
                  :use ((:instance xlate-equiv-memory-and-xr-mem-from-rest-of-memory
                                   (j (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x x86-1)))
                                   (x86-1 x86-1)
                                   (x86-2 x86-2))))
              nil)))

  (defthm mv-nth-1-rb-and-xlate-equiv-memory-disjoint-from-paging-structures
    (implies
     (and (bind-free
           (find-an-xlate-equiv-x86
            'mv-nth-1-rb-and-xlate-equiv-memory-disjoint-from-paging-structures
            x86-1 'x86-2 mfc state)
           (x86-2))
          (syntaxp (and
                    (not (eq x86-2 x86-1))
                    ;; x86-2 must be "smaller" than x86-1.
                    (term-order x86-2 x86-1)))
          (xlate-equiv-memory (double-rewrite x86-1) x86-2)
          (disjoint-p
           (mv-nth 1 (las-to-pas n lin-addr r-w-x (double-rewrite x86-1)))
           (open-qword-paddr-list
            (gather-all-paging-structure-qword-addresses (double-rewrite x86-1)))))
     (equal (mv-nth 1 (rb n lin-addr r-w-x x86-1))
            (mv-nth 1 (rb n lin-addr r-w-x x86-2))))
    :hints (("Goal"
             :do-not-induct t
             :use
             ((:instance read-from-physical-memory-and-xlate-equiv-memory-disjoint-from-paging-structures)
              (:instance read-from-physical-memory-and-xlate-equiv-memory-disjoint-from-paging-structures
                         (x86-1 (mv-nth 2 (las-to-pas n lin-addr r-w-x x86-1)))
                         (x86-2 (mv-nth 2 (las-to-pas n lin-addr r-w-x x86-2)))))
             :in-theory (e/d* (rb)
                              (read-from-physical-memory-and-xlate-equiv-memory-disjoint-from-paging-structures
                               force (force))))))

  (defthm mv-nth-2-rb-and-xlate-equiv-memory
    (implies (and (page-structure-marking-mode (double-rewrite x86))
                  (not (mv-nth 0 (las-to-pas n lin-addr r-w-x (double-rewrite x86))))
                  (not (programmer-level-mode (double-rewrite x86))))
             (xlate-equiv-memory (mv-nth 2 (rb n lin-addr r-w-x x86))
                                 (double-rewrite x86)))
    :hints (("Goal" :in-theory (e/d* () (force (force))))))

  (defthmd xlate-equiv-memory-and-two-mv-nth-2-rb
    (implies (and (xlate-equiv-memory x86-1 x86-2)
                  (page-structure-marking-mode x86-1)
                  (not (mv-nth 0 (las-to-pas n lin-addr r-w-x (double-rewrite x86-1)))))
             (xlate-equiv-memory (mv-nth 2 (rb n lin-addr r-w-x x86-1))
                                 (mv-nth 2 (rb n lin-addr r-w-x x86-2))))
    :hints (("Goal" :in-theory (e/d* () (mv-nth-2-rb-and-xlate-equiv-memory))
             :use ((:instance mv-nth-2-rb-and-xlate-equiv-memory (x86 x86-1))
                   (:instance mv-nth-2-rb-and-xlate-equiv-memory (x86 x86-2))))))

  (defthm mv-nth-1-rb-after-mv-nth-2-rb
    ;; This rule will come in useful when rb isn't rewritten to
    ;; rb-alt, i.e., for reads from the paging structures.  Hence,
    ;; I'll use disjoint-p$ in the hyps here instead of disjoint-p.
    (implies
     (and
      (disjoint-p$
       (mv-nth 1 (las-to-pas n-1 lin-addr-1 r-w-x-1 (double-rewrite x86)))
       (all-xlation-governing-entries-paddrs n-2 lin-addr-2 (double-rewrite x86)))
      (disjoint-p$
       (mv-nth 1 (las-to-pas n-1 lin-addr-1 r-w-x-1 (double-rewrite x86)))
       (all-xlation-governing-entries-paddrs n-1 lin-addr-1 (double-rewrite x86))))
     (equal (mv-nth 1 (rb n-1 lin-addr-1 r-w-x-1
                          (mv-nth 2 (rb n-2 lin-addr-2 r-w-x-2 x86))))
            (mv-nth 1 (rb n-1 lin-addr-1 r-w-x-1 x86))))
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d* (rb disjoint-p$) (force (force))))))

  (defthm mv-nth-1-rb-after-mv-nth-2-las-to-pas
    (implies
     (and
      (disjoint-p
       (mv-nth 1 (las-to-pas n-1 lin-addr-1 r-w-x-1 (double-rewrite x86)))
       (all-xlation-governing-entries-paddrs n-2 lin-addr-2 (double-rewrite x86)))
      (disjoint-p
       (mv-nth 1 (las-to-pas n-1 lin-addr-1 r-w-x-1 (double-rewrite x86)))
       (all-xlation-governing-entries-paddrs n-1 lin-addr-1 (double-rewrite x86)))
      (not (programmer-level-mode x86)))
     (equal (mv-nth 1 (rb n-1 lin-addr-1 r-w-x-1 (mv-nth 2 (las-to-pas n-2 lin-addr-2 r-w-x-2 x86))))
            (mv-nth 1 (rb n-1 lin-addr-1 r-w-x-1 (double-rewrite x86)))))
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d* (rb) (force (force)))))))

;; ======================================================================

;; Lemmas about gather-all-paging-structure-qword-addresses:

(defthm gather-all-paging-structure-qword-addresses-and-write-to-physical-memory-disjoint
  (implies
   (and (disjoint-p
         p-addrs
         (open-qword-paddr-list
          (gather-all-paging-structure-qword-addresses (double-rewrite x86))))
        (physical-address-listp p-addrs))
   (equal
    (gather-all-paging-structure-qword-addresses
     (write-to-physical-memory p-addrs value x86))
    (gather-all-paging-structure-qword-addresses (double-rewrite x86))))
  :hints (("Goal" :in-theory (e/d* (write-to-physical-memory
                                    byte-listp
                                    n08p
                                    len
                                    disjoint-p
                                    gather-all-paging-structure-qword-addresses-xw-fld=mem-disjoint)
                                   ()))))

(defthm gather-all-paging-structure-qword-addresses-and-wb-disjoint
  (implies
   (and
    ;; We need disjoint-p$ here instead of disjoint-p because this
    ;; first hyp should be present in the top-level hyps of the
    ;; effects theorems of programs.
    (disjoint-p$
     (mv-nth 1 (las-to-pas n-w write-addr :w (double-rewrite x86)))
     (open-qword-paddr-list
      (gather-all-paging-structure-qword-addresses (double-rewrite x86))))
    (not (programmer-level-mode x86)))
   (equal
    (gather-all-paging-structure-qword-addresses (mv-nth 1 (wb n-w write-addr w value x86)))
    (gather-all-paging-structure-qword-addresses (double-rewrite x86))))
  :hints (("Goal" :in-theory (e/d* (wb disjoint-p$)
                                   (force (force) (:meta acl2::mv-nth-cons-meta))))))

;; ======================================================================

;; Lemmas about prog-at:

(local (in-theory (e/d* (rb
                         wb
                         canonical-address-p
                         prog-at
                         las-to-pas
                         all-xlation-governing-entries-paddrs
                         unsigned-byte-p
                         signed-byte-p)
                        ())))

;; Lemmas to read a byte of an instruction when symbolically
;; simulating a program:

(defthmd rb-unwinding-thm-in-system-level-mode
  (implies
   (and
    (not (mv-nth 0 (rb n lin-addr r-w-x x86)))
    (disjoint-p
     (mv-nth 1 (las-to-pas n lin-addr r-w-x (double-rewrite x86)))
     (all-xlation-governing-entries-paddrs n lin-addr (double-rewrite x86)))
    (posp n))
   (equal (mv-nth 1 (rb n lin-addr r-w-x x86))
          (logior (mv-nth 1 (rb 1 lin-addr r-w-x x86))
                  (ash (mv-nth 1 (rb (1- n) (1+ lin-addr) r-w-x x86)) 8))))
  :hints (("Goal" :in-theory (e/d (rb disjoint-p)
                                  (acl2::mv-nth-cons-meta force (force))))))

(local
 (defthmd rm08-in-terms-of-nth-pos-and-rb-helper
   (implies (and (disjoint-p (mv-nth 1 (las-to-pas n lin-addr r-w-x x86))
                             (all-xlation-governing-entries-paddrs n lin-addr x86))
                 (not (mv-nth 0 (las-to-pas n lin-addr r-w-x x86)))
                 (<= lin-addr addr)
                 (< addr (+ n lin-addr))
                 (posp n) (integerp lin-addr) (integerp addr))
            (equal (member-p
                    (mv-nth 1 (ia32e-la-to-pa addr r-w-x x86))
                    (xlation-governing-entries-paddrs addr x86))
                   nil))
   :hints (("Goal"
            :do-not-induct t
            :use ((:instance not-member-p-when-disjoint-p
                             (e (mv-nth 1 (ia32e-la-to-pa addr r-w-x x86)))
                             (x (mv-nth 1 (las-to-pas n lin-addr r-w-x x86)))
                             (y (xlation-governing-entries-paddrs addr x86))))
            :in-theory (e/d* (all-xlation-governing-entries-paddrs
                              member-p
                              disjoint-p
                              subset-p
                              disjoint-p-commutative)
                             (not-member-p-when-disjoint-p))))))


(local
 (defthmd rb-one-byte-of-program-in-marking-mode-helper
   ;; TODO: Ugh, I'm embarassed about putting this here when
   ;; prog-at-nil-when-translation-error should suffice.  Remove
   ;; soon...
   (implies
    (and (prog-at (+ 1 prog-addr)
                  (cdr bytes)
                  (mv-nth 2 (ia32e-la-to-pa prog-addr :x x86)))
         (not (xr :programmer-level-mode 0 x86)))
    (equal (mv-nth 0
                   (las-to-pas (len (cdr bytes))
                               (+ 1 prog-addr)
                               :x x86))
           nil))
   :hints (("Goal" :in-theory (e/d* () (prog-at-nil-when-translation-error))
            :use ((:instance prog-at-nil-when-translation-error
                             (prog-addr (+ 1 prog-addr))
                             (bytes (cdr bytes))
                             (x86 (mv-nth 2 (ia32e-la-to-pa prog-addr :x x86)))))))))

(defthm rb-one-byte-of-program-in-marking-mode
  (implies (and
            (bind-free (find-prog-at-info 'prog-addr 'bytes mfc state)
                       (prog-addr bytes))
            (prog-at prog-addr bytes x86)
            (disjoint-p
             (mv-nth 1 (las-to-pas (len bytes) prog-addr :x (double-rewrite x86)))
             (all-xlation-governing-entries-paddrs
              (len bytes) prog-addr (double-rewrite x86)))
            (not (mv-nth 0 (las-to-pas
                            (len bytes) prog-addr :x (double-rewrite x86))))
            (<= prog-addr lin-addr)
            (< lin-addr (+ (len bytes) prog-addr))
            (canonical-address-p lin-addr)
            (not (programmer-level-mode x86)))
           (equal (mv-nth 1 (rb 1 lin-addr :x x86))
                  (nth (- lin-addr prog-addr) bytes)))
  :hints (("Goal"
           ;; TODO: This ind-hint is fine, but the proof takes ~10s
           ;; longer with the hint than without it.  Why?
           :induct (list (len bytes) lin-addr (prog-at prog-addr bytes x86))
           :in-theory (e/d (prog-at
                            all-xlation-governing-entries-paddrs
                            disjoint-p
                            rb
                            las-to-pas
                            rb-one-byte-of-program-in-marking-mode-helper
                            rm08-in-terms-of-nth-pos-and-rb-helper)
                           (not acl2::mv-nth-cons-meta (force) force)))))

(local
 (defthmd rb-in-terms-of-rb-subset-p-helper
   (implies (and
             ;; <n-2,lin-addr-2> is a subset of <n-1,lin-addr-1>.
             (<= lin-addr-1 lin-addr-2)
             (< (+ n-2 lin-addr-2) (+ n-1 lin-addr-1))
             (disjoint-p (mv-nth 1 (las-to-pas n-1 lin-addr-1 r-w-x x86))
                         (all-xlation-governing-entries-paddrs n-1 lin-addr-1 x86))
             (not (mv-nth 0 (las-to-pas n-1 lin-addr-1 r-w-x x86)))
             (posp n-1) (posp n-2)
             (integerp lin-addr-1)
             (integerp lin-addr-2))
            (disjoint-p (mv-nth 1 (las-to-pas n-2 lin-addr-2 r-w-x x86))
                        (all-xlation-governing-entries-paddrs n-2 lin-addr-2 x86)))))

(defthm rb-in-terms-of-rb-subset-p-in-marking-mode
  (implies
   (and
    (bind-free (find-prog-at-info 'prog-addr 'bytes mfc state)
               (prog-addr bytes))
    (syntaxp (quotep n))
    (prog-at prog-addr bytes x86)
    (<= prog-addr lin-addr)
    (< (+ n lin-addr) (+ (len bytes) prog-addr))
    (disjoint-p
     (mv-nth 1 (las-to-pas (len bytes) prog-addr :x (double-rewrite x86)))
     (all-xlation-governing-entries-paddrs
      (len bytes) prog-addr (double-rewrite x86)))
    (not (mv-nth 0 (las-to-pas (len bytes) prog-addr :x (double-rewrite x86))))
    (not (mv-nth 0 (las-to-pas n lin-addr :x x86)))
    (posp n)
    (integerp prog-addr)
    (canonical-address-p lin-addr)
    (not (programmer-level-mode x86)))
   (equal (mv-nth 1 (rb n lin-addr :x x86))
          (logior (nth (- lin-addr prog-addr) bytes)
                  (ash (mv-nth 1 (rb (1- n) (1+ lin-addr) :x x86)) 8))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (subset-p
                            member-p
                            disjoint-p
                            disjoint-p-commutative)
                           (rb
                            canonical-address-p
                            acl2::mv-nth-cons-meta
                            all-xlation-governing-entries-paddrs
                            las-to-pas))
           :use ((:instance rb-in-terms-of-rb-subset-p-helper
                            (r-w-x :x)
                            (n-1 (len bytes))
                            (lin-addr-1 prog-addr)
                            (n-2 n)
                            (lin-addr-2 lin-addr))
                 (:instance rb-one-byte-of-program-in-marking-mode)
                 (:instance rb-unwinding-thm-in-system-level-mode
                            (r-w-x :x))))))

(defthmd prog-at-and-xlate-equiv-memory
  (implies
   (and (bind-free
         (find-an-xlate-equiv-x86
          'prog-at-and-xlate-equiv-memory
          x86-1 'x86-2 mfc state)
         (x86-2))
        (syntaxp (and (not (eq x86-2 x86-1))
                      ;; x86-2 must be smaller than x86-1.
                      (term-order x86-2 x86-1)))
        (xlate-equiv-memory x86-1 x86-2)
        (disjoint-p
         (mv-nth 1 (las-to-pas (len bytes) prog-addr :x x86-1))
         (open-qword-paddr-list
          (gather-all-paging-structure-qword-addresses x86-1))))
   (equal (prog-at prog-addr bytes x86-1)
          (prog-at prog-addr bytes x86-2)))
  :hints (("Goal" :in-theory (e/d* (prog-at) ()))
          (if
              ;; Apply to all subgoals under a top-level induction.
              (and (consp (car id))
                   (< 1 (len (car id))))
              '(:in-theory
                (e/d* (rb-one-byte-of-program-in-marking-mode-helper
                       disjoint-p)
                      ())
                :use ((:instance xlate-equiv-memory-and-xr-mem-from-rest-of-memory
                                 (j (mv-nth 1 (ia32e-la-to-pa prog-addr :x x86-1)))
                                 (x86-1 (mv-nth 2
                                                (ia32e-la-to-pa prog-addr :x x86-1)))
                                 (x86-2 (mv-nth 2
                                                (ia32e-la-to-pa prog-addr :x x86-2))))))
            nil)))

(i-am-here)

(define program-at (prog-addr bytes x86)

  :parents (x86-top-level-memory)
  :non-executable t

  :short "Predicate that makes a statement about a program's location
  in the memory"
  :guard (and (canonical-address-p prog-addr)
              (canonical-address-p (+ -1 (len bytes) prog-addr))
              (byte-listp bytes))

  (b* (((mv flg bytes-read ?x86)
        (rb (len bytes) prog-addr :x x86)))
    (and
     (equal flg        nil)
     (equal bytes-read (combine-bytes bytes)))))


(defthm program-at-wb-disjoint-in-system-level-mode
  (implies
   (and

    (not (mv-nth 0 (las-to-pas (len bytes) prog-addr :x (double-rewrite x86))))

    (disjoint-p
     ;; The physical addresses pertaining to the write
     ;; operation are disjoint from those pertaining to the
     ;; read operation.
     (mv-nth 1 (las-to-pas n-w write-addr :w (double-rewrite x86)))
     (mv-nth 1 (las-to-pas (len bytes) prog-addr :x (double-rewrite x86))))
    (disjoint-p
     ;; The physical addresses corresponding to the read are
     ;; disjoint from the xlation-governing-entries-paddrs
     ;; pertaining to the write.
     (mv-nth 1 (las-to-pas (len bytes) prog-addr :x (double-rewrite x86)))
     (all-xlation-governing-entries-paddrs n-w write-addr (double-rewrite x86)))
    (disjoint-p
     ;; The physical addresses pertaining to the read are
     ;; disjoint from the xlation-governing-entries-paddrs
     ;; pertaining to the read.
     (mv-nth 1 (las-to-pas (len bytes) prog-addr :x (double-rewrite x86)))
     (all-xlation-governing-entries-paddrs
      (len bytes) prog-addr (double-rewrite x86)))
    (disjoint-p
     ;; The physical addresses pertaining to the write are
     ;; disjoint from the xlation-governing-entries-paddrs
     ;; pertaining to the read.
     (mv-nth 1 (las-to-pas n-w write-addr :w (double-rewrite x86)))
     (all-xlation-governing-entries-paddrs
      (len bytes) prog-addr (double-rewrite x86)))
    (natp n-w)
    (not (programmer-level-mode x86))
    (x86p x86))
   (equal (program-at prog-addr bytes (mv-nth 1 (wb n-w write-addr w value x86)))
          (program-at prog-addr bytes x86)))
  :hints (("Goal"
           :in-theory (e/d (program-at
                            disjoint-p)
                           (rb wb
                               disjointness-of-all-xlation-governing-entries-paddrs-from-all-xlation-governing-entries-paddrs-subset-p)))))

(local
 (defthm non-zero-len-of-consp
   ;; Ugh, why do I need this?
   (implies (consp x)
            (equal (equal (len x) 0) nil))))

(local
 (defthm prog-at-wb-disjoint-helper-1
   (implies
    (and
     (bind-free '((bytes . bytes)))
     (consp bytes)
     (signed-byte-p 48 prog-addr)
     ;; (disjoint-p
     ;;  (mv-nth 1 (las-to-pas n-w write-addr :w x86))
     ;;  (xlation-governing-entries-paddrs prog-addr x86))
     (disjoint-p
      (mv-nth 1 (las-to-pas n-w write-addr :w x86))
      (all-xlation-governing-entries-paddrs (len bytes) prog-addr x86)))
    (and
     (equal (mv-nth 0 (ia32e-la-to-pa prog-addr :x
                                      (mv-nth 1 (wb n-w write-addr w value x86))))
            (mv-nth 0 (ia32e-la-to-pa prog-addr :x x86)))
     (equal (mv-nth 1 (ia32e-la-to-pa prog-addr :x
                                      (mv-nth 1 (wb n-w write-addr w value x86))))
            (mv-nth 1 (ia32e-la-to-pa prog-addr :x x86)))))
   :hints (("Goal" :do-not-induct t
            :expand ((all-xlation-governing-entries-paddrs (len bytes) prog-addr x86))
            :in-theory (e/d (disjoint-p disjoint-p-commutative prog-at) (rb wb))))))

(local
 (defthm prog-at-wb-disjoint-in-non-marking-mode-helper-2
   (implies
    (and
     (bind-free '((bytes . bytes)))
     (signed-byte-p 48 prog-addr)
     (not (mv-nth 0 (las-to-pas (len bytes) prog-addr :x (double-rewrite x86))))
     (disjoint-p (mv-nth 1 (las-to-pas (len bytes) prog-addr :x x86))
                 (mv-nth 1 (las-to-pas n-w write-addr :w x86)))
     ;; (disjoint-p
     ;;  (mv-nth 1 (las-to-pas bytes prog-addr :x x86))
     ;;  (mv-nth 1 (las-to-pas n-w write-addr :w x86)))
     (not (member-p (mv-nth 1 (ia32e-la-to-pa prog-addr :x (double-rewrite x86)))
                    (all-xlation-governing-entries-paddrs
                     n-w write-addr (double-rewrite x86))))
     ;; (disjoint-p
     ;;  (mv-nth 1 (las-to-pas bytes prog-addr :x x86))
     ;;  (all-xlation-governing-entries-paddrs n-w write-addr (double-rewrite x86)))
     (not
      (member-p (mv-nth 1 (ia32e-la-to-pa prog-addr :x (double-rewrite x86)))
                (xlation-governing-entries-paddrs prog-addr (double-rewrite x86))))
     ;; (disjoint-p (mv-nth 1 (las-to-pas (len bytes) prog-addr :x (double-rewrite x86)))
     ;;             (all-xlation-governing-entries-paddrs (len bytes) prog-addr x86))
     (disjoint-p (mv-nth 1 (las-to-pas n-w write-addr :w x86))
                 (xlation-governing-entries-paddrs prog-addr x86))
     (not (xr :programmer-level-mode 0 x86))
     (consp bytes))
    (equal (mv-nth 1 (rb 1 prog-addr :x (mv-nth 1 (wb n-w write-addr w value x86))))
           (mv-nth 1 (rb 1 prog-addr :x x86))))
   :hints (("Goal" :do-not-induct t
            ;; :expand ((all-xlation-governing-entries-paddrs (len bytes) prog-addr x86)
            ;;          (all-xlation-governing-entries-paddrs n-w write-addr x86)
            ;;          (las-to-pas (len bytes) prog-addr :x x86))
            :expand ((las-to-pas (len bytes) prog-addr :x x86))
            :in-theory (e/d (disjoint-p disjoint-p-commutative prog-at)
                            (rb wb))))))

(local
 (defthm prog-at-wb-disjoint-in-non-marking-mode-helper-3
   (implies
    (and

     (disjoint-p
      (mv-nth 1 (las-to-pas (len bytes) prog-addr :x x86))
      (open-qword-paddr-list
       (gather-all-paging-structure-qword-addresses x86)))

     (disjoint-p
      (mv-nth 1 (las-to-pas (len bytes) prog-addr :x (double-rewrite x86)))
      (all-xlation-governing-entries-paddrs
       (len bytes) prog-addr (double-rewrite x86)))
     (disjoint-p
      (mv-nth 1 (las-to-pas (len bytes) prog-addr :x (double-rewrite x86)))
      (all-xlation-governing-entries-paddrs n lin-addr (double-rewrite x86)))
     (natp n) (integerp lin-addr))
    (equal (prog-at prog-addr bytes
                    (mv-nth 2 (rb n lin-addr r-w-x x86)))
           (prog-at prog-addr bytes x86)))
   :hints (("Goal"
            :in-theory (e/d (rb disjoint-p prog-at las-to-pas)
                            (disjoint-p-append-2)))

           (if
               ;; Apply to all subgoals under a top-level induction.
               (and (consp (car id))
                    (< 1 (len (car id))))
               '(:in-theory
                 (e/d* (disjoint-p)
                       (disjoint-p-append-2))
                 :use ((:instance prog-at-and-xlate-equiv-memory
                                  (prog-addr (+ 1 prog-addr))
                                  (bytes (cdr bytes))
                                  (x86-1 (mv-nth 2
                                                 (ia32e-la-to-pa prog-addr
                                                                 :x (mv-nth 2 (las-to-pas n lin-addr r-w-x x86)))))
                                  (x86-2 (mv-nth 2 (ia32e-la-to-pa prog-addr :x x86))))
                       (:instance xlate-equiv-memory-and-xr-mem-from-rest-of-memory
                                  (j (mv-nth 1 (ia32e-la-to-pa prog-addr :x x86)))
                                  (x86-1 (mv-nth 2
                                                 (ia32e-la-to-pa prog-addr :x x86)))
                                  (x86-2 x86))
                       (:instance xlate-equiv-memory-and-xr-mem-from-rest-of-memory
                                  (j (mv-nth 1 (ia32e-la-to-pa prog-addr :x x86)))
                                  (x86-1 (mv-nth
                                          2
                                          (ia32e-la-to-pa prog-addr
                                                          :x (mv-nth 2
                                                                     (las-to-pas n lin-addr r-w-x x86)))))
                                  (x86-2 (mv-nth 2
                                                 (ia32e-la-to-pa prog-addr :x x86))))))
             nil))))

(local
 (in-theory (e/d* ()
                  (infer-disjointness-with-all-xlation-governing-entries-paddrs-from-gather-all-paging-structure-qword-addresses-with-both-disjoint-p-and-disjoint-p$-and-subset-p
                   infer-disjointness-with-all-xlation-governing-entries-paddrs-from-gather-all-paging-structure-qword-addresses-with-disjoint-p$
                   two-mv-nth-1-las-to-pas-subset-p-disjoint-from-las-to-pas
                   infer-disjointness-with-all-xlation-governing-entries-paddrs-from-gather-all-paging-structure-qword-addresses
                   disjoint-p-all-xlation-governing-entries-paddrs-subset-p
                   mv-nth-1-las-to-pas-subset-p-disjoint-from-other-p-addrs))))

(thm
 (IMPLIES
  (AND
   (CONSP BYTES)
   (INTEGERP PROG-ADDR)
   (<= -140737488355328 PROG-ADDR)
   (< PROG-ADDR 140737488355328)
   (NOT (MV-NTH 0 (IA32E-LA-TO-PA PROG-ADDR :X X86)))
   (NOT (EQUAL (CAR BYTES)
               (MV-NTH 1
                       (RB 1 PROG-ADDR
                           :X (MV-NTH 1 (WB N-W WRITE-ADDR W VALUE X86))))))
   (DISJOINT-P (MV-NTH 1 (LAS-TO-PAS N-W WRITE-ADDR :W X86))
               (MV-NTH 1
                       (LAS-TO-PAS (LEN BYTES)
                                   PROG-ADDR
                                   :X X86)))
   (not (member-p (mv-nth '1
                          (ia32e-la-to-pa prog-addr ':x x86))
                  (mv-nth '1
                          (las-to-pas n-w write-addr ':w x86))))
   (not
    (member-p (mv-nth '1
                      (ia32e-la-to-pa prog-addr ':x x86))
              (all-xlation-governing-entries-paddrs n-w write-addr x86)))
   (not (member-p (mv-nth '1
                          (ia32e-la-to-pa prog-addr ':x x86))
                  (xlation-governing-entries-paddrs prog-addr x86)))
   (disjoint-p (mv-nth '1
                       (las-to-pas n-w write-addr ':w x86))
               (xlation-governing-entries-paddrs prog-addr x86))
   (DISJOINT-P (MV-NTH 1
                       (LAS-TO-PAS (LEN BYTES)
                                   PROG-ADDR
                                   :X X86))
               (ALL-XLATION-GOVERNING-ENTRIES-PADDRS N-W WRITE-ADDR X86))
   (DISJOINT-P (MV-NTH 1
                       (LAS-TO-PAS (LEN BYTES)
                                   PROG-ADDR
                                   :X X86))
               (ALL-XLATION-GOVERNING-ENTRIES-PADDRS (LEN BYTES)
                                                     PROG-ADDR X86))
   (DISJOINT-P (MV-NTH 1 (LAS-TO-PAS N-W WRITE-ADDR :W X86))
               (ALL-XLATION-GOVERNING-ENTRIES-PADDRS (LEN BYTES)
                                                     PROG-ADDR X86))
   (NATP N-W)
   (NOT (XR :PROGRAMMER-LEVEL-MODE 0 X86))
   (X86P X86))
  (NOT (PROG-AT PROG-ADDR BYTES X86)))
 :hints (("Goal"
          :in-theory (e/d (prog-at
                           disjoint-p
                           rb-one-byte-of-program-in-marking-mode-helper
                           las-to-pas)
                          (disjointness-of-all-xlation-governing-entries-paddrs-from-all-xlation-governing-entries-paddrs-subset-p
                           rb wb)))))

(defthm prog-at-wb-disjoint-in-system-level-mode
  (implies
   (and

    ;; (disjoint-p
    ;;  (mv-nth 1 (las-to-pas (len bytes) prog-addr :x x86))
    ;;  (open-qword-paddr-list
    ;;   (gather-all-paging-structure-qword-addresses x86)))
    (not (mv-nth 0 (las-to-pas (len bytes) prog-addr :x (double-rewrite x86))))

    (disjoint-p
     ;; The physical addresses pertaining to the write
     ;; operation are disjoint from those pertaining to the
     ;; read operation.
     (mv-nth 1 (las-to-pas n-w write-addr :w (double-rewrite x86)))
     (mv-nth 1 (las-to-pas (len bytes) prog-addr :x (double-rewrite x86))))
    (disjoint-p
     ;; The physical addresses corresponding to the read are
     ;; disjoint from the xlation-governing-entries-paddrs
     ;; pertaining to the write.
     (mv-nth 1 (las-to-pas (len bytes) prog-addr :x (double-rewrite x86)))
     (all-xlation-governing-entries-paddrs n-w write-addr (double-rewrite x86)))
    (disjoint-p
     ;; The physical addresses pertaining to the read are
     ;; disjoint from the xlation-governing-entries-paddrs
     ;; pertaining to the read.
     (mv-nth 1 (las-to-pas (len bytes) prog-addr :x (double-rewrite x86)))
     (all-xlation-governing-entries-paddrs
      (len bytes) prog-addr (double-rewrite x86)))
    (disjoint-p
     ;; The physical addresses pertaining to the write are
     ;; disjoint from the xlation-governing-entries-paddrs
     ;; pertaining to the read.
     (mv-nth 1 (las-to-pas n-w write-addr :w (double-rewrite x86)))
     (all-xlation-governing-entries-paddrs
      (len bytes) prog-addr (double-rewrite x86)))
    (natp n-w)
    (not (programmer-level-mode x86))
    (x86p x86))
   (equal (prog-at prog-addr bytes (mv-nth 1 (wb n-w write-addr w value x86)))
          (prog-at prog-addr bytes x86)))
  :hints (("Goal"
           :induct (list (len bytes) (las-to-pas n-w write-addr w x86) (prog-at prog-addr bytes x86))
           :in-theory (e/d (prog-at
                            disjoint-p
                            rb)
                           (wb
                            disjointness-of-all-xlation-governing-entries-paddrs-from-all-xlation-governing-entries-paddrs-subset-p)))))

;; ======================================================================



(defthm rb-wb-disjoint-in-system-level-mode
  (implies (and
            (disjoint-p
             ;; The physical addresses pertaining to the read
             ;; operation are disjoint from those pertaining to the
             ;; write operation.
             (mv-nth 1 (las-to-pas n-w write-addr :w (double-rewrite x86)))
             (mv-nth 1 (las-to-pas n lin-addr r-w-x (double-rewrite x86))))
            (disjoint-p
             ;; The physical addresses corresponding to the read are
             ;; disjoint from the xlation-governing-entries-paddrs
             ;; pertaining to the write.
             (mv-nth 1 (las-to-pas n lin-addr r-w-x (double-rewrite x86)))
             (all-xlation-governing-entries-paddrs n-w write-addr (double-rewrite x86)))
            (disjoint-p
             ;; The physical addresses pertaining to the read are
             ;; disjoint from the xlation-governing-entries-paddrs
             ;; pertaining to the read.
             (mv-nth 1 (las-to-pas n lin-addr r-w-x (double-rewrite x86)))
             (all-xlation-governing-entries-paddrs n lin-addr (double-rewrite x86)))
            (disjoint-p
             ;; The physical addresses pertaining to the write are
             ;; disjoint from the xlation-governing-entries-paddrs
             ;; pertaining to the read.
             (mv-nth 1 (las-to-pas n-w write-addr :w (double-rewrite x86)))
             (all-xlation-governing-entries-paddrs n lin-addr (double-rewrite x86)))
            (not (programmer-level-mode x86)))
           (and
            (equal (mv-nth 0 (rb n lin-addr r-w-x
                                 (mv-nth 1 (wb n-w write-addr w value x86))))
                   (mv-nth 0 (rb n lin-addr r-w-x x86)))
            (equal (mv-nth 1 (rb n lin-addr r-w-x
                                 (mv-nth 1 (wb n-w write-addr w value x86))))
                   (mv-nth 1 (rb n lin-addr r-w-x x86)))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance xlate-equiv-memory-and-las-to-pas
                            (x86-1 (mv-nth 2 (las-to-pas n-w write-addr :w x86)))
                            (x86-2 x86)))
           :in-theory (e/d* (disjoint-p-commutative)
                            (wb
                             disjointness-of-all-xlation-governing-entries-paddrs-from-all-xlation-governing-entries-paddrs-subset-p)))))
