;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")
(include-book "common-system-level-utils")
(include-book "paging-lib/common-paging-lemmas")
(include-book "gl-lemmas")
(include-book "clause-processors/find-subterms" :dir :system)

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))
(local (include-book "centaur/gl/gl" :dir :system))

(local (in-theory (e/d* () (signed-byte-p unsigned-byte-p))))

;; ======================================================================

(defsection non-marking-mode-utils
  :parents (proof-utilities)

  :short "Reasoning in the system-level non-marking mode"

  :long "<p>WORK IN PROGRESS...</p>

<p>This doc topic will be updated in later commits...</p>"
  )

(local (xdoc::set-default-parents non-marking-mode-utils))

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
;; (acl2::why la-to-pas-values-and-mv-nth-1-wb-disjoint-from-xlation-gov-addrs-in-non-marking-mode)

;; ======================================================================

;; Lemmas about memory reads:

(defthm read-from-physical-memory-and-mv-nth-2-ia32e-la-to-pa-in-non-marking-mode
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

;; ======================================================================

;; Lemmas about memory writes:

(defthm xr-mem-wb-in-system-level-non-marking-mode
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



(defthm mv-nth-0-ia32e-la-to-pa-member-of-mv-nth-1-las-to-pas-if-lin-addr-member-p-in-non-marking-mode
  (implies (and (bind-free (find-l-addrs-from-las-to-pas 'l-addrs mfc state)
                           (l-addrs))
                (member-p lin-addr l-addrs)
                (not (mv-nth 0 (las-to-pas l-addrs r-w-x cpl x86)))
                (not (page-structure-marking-mode x86)))
           (equal (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x cpl x86)) nil))
  :hints (("Goal" :in-theory (e/d* (member-p) ()))))

(defthm mv-nth-1-ia32e-la-to-pa-member-of-mv-nth-1-las-to-pas-if-lin-addr-member-p-in-non-marking-mode
  (implies (and (member-p lin-addr l-addrs)
                (not (mv-nth 0 (las-to-pas l-addrs r-w-x cpl x86)))
                (not (page-structure-marking-mode x86)))
           (member-p (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x cpl x86))
                     (mv-nth 1 (las-to-pas     l-addrs r-w-x cpl x86))))
  :hints (("Goal" :in-theory (e/d* (member-p) ()))))

(defthm las-to-pas-values-and-xw-mem-not-member-in-non-marking-mode
  (implies (and (not (member-p index (all-translation-governing-addresses l-addrs x86)))
                (physical-address-p index)
                (canonical-address-listp l-addrs)
                (unsigned-byte-p 8 byte)
                (not (page-structure-marking-mode x86)))
           (and (equal (mv-nth 0 (las-to-pas l-addrs r-w-x cpl (xw :mem index byte x86)))
                       (mv-nth 0 (las-to-pas l-addrs r-w-x cpl x86)))
                (equal (mv-nth 1 (las-to-pas l-addrs r-w-x cpl (xw :mem index byte x86)))
                       (mv-nth 1 (las-to-pas l-addrs r-w-x cpl x86)))))
  :hints (("Goal"
           :in-theory (e/d* (disjoint-p
                             member-p)
                            (translation-governing-addresses)))))

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

(defthm member-p-and-remove-duplicates-equal
  (equal (member-p e (remove-duplicates-equal x))
         (member-p e x))
  :hints (("Goal" :in-theory (e/d* (member-p) ()))))

(defthm canonical-address-listp-and-remove-duplicates-equal
  (implies (canonical-address-listp x)
           (canonical-address-listp (remove-duplicates-equal x))))

(defthmd all-translation-governing-addresses-remove-duplicates-equal-and-subset-p
  (subset-p (all-translation-governing-addresses (remove-duplicates-equal l-addrs) x86)
            (all-translation-governing-addresses l-addrs x86))
  :hints (("Goal" :in-theory (e/d* (subset-p) (translation-governing-addresses)))))

(defthmd member-p-of-all-translation-governing-addresses-and-remove-duplicates-equal
  (implies (not (member-p addr (all-translation-governing-addresses l-addrs x86)))
           (not (member-p addr (all-translation-governing-addresses (remove-duplicates-equal l-addrs) x86)))))

(defthmd wb-remove-duplicate-writes-in-system-level-non-marking-mode
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
                (not (page-structure-marking-mode x86))
                (x86p x86))
           (equal (wb addr-lst x86)
                  ;; TO-DO: I need to replace remove-duplicate-keys
                  ;; with remove-duplicate-phy-addresses or something
                  ;; like that.
                  (wb (remove-duplicate-keys addr-lst) x86)))
  :hints (("Goal" :do-not '(generalize)
           :in-theory (e/d (disjoint-p
                            member-p
                            subset-p
                            member-p-of-all-translation-governing-addresses-and-remove-duplicates-equal
                            all-translation-governing-addresses-remove-duplicates-equal-and-subset-p)
                           (acl2::mv-nth-cons-meta
                            disjoint-p-subset-p
                            member-p-and-remove-duplicates-equal
                            disjointness-of-all-translation-governing-addresses-from-all-translation-governing-addresses-subset-p
                            translation-governing-addresses))
           :induct (wb-duplicate-writes-induct addr-lst x86))))

;; ======================================================================

;; Lemmas about interaction of writes and paging walkers:

(defthm rm-low-32-wb-in-system-level-non-marking-mode-disjoint
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

(defthm rm-low-64-wb-in-system-level-non-marking-mode-disjoint
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

(defthm las-to-pas-values-in-non-marking-mode-and-write-to-physical-memory-disjoint
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

(defthm ia32e-la-to-pa-page-table-values-and-mv-nth-1-wb-disjoint-from-xlation-gov-addrs-in-non-marking-mode
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

(defthm ia32e-la-to-pa-page-directory-values-and-mv-nth-1-wb-disjoint-from-xlation-gov-addrs-in-non-marking-mode
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

(defthm ia32e-la-to-pa-page-dir-ptr-table-values-and-mv-nth-1-wb-disjoint-from-xlation-gov-addrs-in-non-marking-mode
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

(defthm ia32e-la-to-pa-pml4-table-values-and-mv-nth-1-wb-disjoint-from-xlation-gov-addrs-in-non-marking-mode
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

(defthm ia32e-la-to-pa-values-and-mv-nth-1-wb-disjoint-from-xlation-gov-addrs-in-non-marking-mode
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

(defthm la-to-pas-values-and-mv-nth-1-wb-disjoint-from-xlation-gov-addrs-in-non-marking-mode
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

(defthm read-from-physical-memory-and-mv-nth-1-wb-disjoint-in-non-marking-mode
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

(defthmd las-to-pas-subset-p-in-non-marking-mode
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

(defthm las-to-pas-subset-p-with-l-addrs-from-bind-free-in-non-marking-mode
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

;; ======================================================================

(defthm r-w-x-is-irrelevant-for-mv-nth-1-las-to-pas-when-no-errors-in-non-marking-mode
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

(local
 (defthm translation-governing-addresses-and-write-to-physical-memory
   ;; TO-DO: This already exists in paging-lib/paging-top.
   (implies (and (disjoint-p p-addrs (all-translation-governing-addresses l-addrs x86))
                 (physical-address-listp p-addrs))
            (equal
             (all-translation-governing-addresses l-addrs (write-to-physical-memory p-addrs bytes x86))
             (all-translation-governing-addresses l-addrs x86)))
   :hints (("Goal" :in-theory (e/d* (disjoint-p-commutative) ())))))

(defthm translation-governing-addresses-and-mv-nth-1-wb-disjoint-p-in-non-marking-mode
  (implies (and (not (mv-nth 0 (las-to-pas (strip-cars addr-lst) :w (cpl x86) x86)))
                (disjoint-p (translation-governing-addresses lin-addr x86)
                            (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w (cpl x86) x86)))
                (not (programmer-level-mode x86))
                (not (page-structure-marking-mode x86))
                (x86p x86))
           (equal (translation-governing-addresses lin-addr (mv-nth 1 (wb addr-lst x86)))
                  (translation-governing-addresses lin-addr x86)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (disjoint-p wb) ()))))

(defthm all-translation-governing-addresses-and-mv-nth-1-wb-disjoint-in-non-marking-mode
  (implies (and
            (not (mv-nth 0 (las-to-pas (strip-cars addr-lst) :w (cpl x86) x86)))
            (disjoint-p (all-translation-governing-addresses l-addrs x86)
                        (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w (cpl x86) x86)))
            (not (programmer-level-mode x86))
            (not (page-structure-marking-mode x86))
            (x86p x86))
           (equal (all-translation-governing-addresses l-addrs (mv-nth 1 (wb addr-lst x86)))
                  (all-translation-governing-addresses l-addrs x86)))
  :hints (("Goal"
           :in-theory (e/d* (all-translation-governing-addresses)
                            (translation-governing-addresses
                             wb))
           :induct (all-translation-governing-addresses l-addrs x86))))

;; ======================================================================

(globally-disable '(rb wb canonical-address-p program-at
                       unsigned-byte-p signed-byte-p
                       las-to-pas all-translation-governing-addresses))

;; ======================================================================
