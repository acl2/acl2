;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")
(include-book "paging-lib/paging-top")

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "centaur/gl/gl" :dir :system))

;; ======================================================================

(defsection system-level-memory-utils
  :parents (proof-utilities)

  :short "Helper lemmas for reasoning about memory in the system-level
  mode"
  )

(local (xdoc::set-default-parents system-level-memory-utils))

(local (in-theory (e/d* (entry-found-p-and-good-paging-structures-x86p
                         entry-found-p-and-lin-addr)
                        (signed-byte-p
                         unsigned-byte-p))))

;; ======================================================================

(local
 (defthm open-create-canonical-address-list
   (implies (and (canonical-address-p lin-addr)
                 (posp n)
                 (canonical-address-p (+ -1 n lin-addr)))
            (equal (create-canonical-address-list n lin-addr)
                   (cons lin-addr
                         (create-canonical-address-list (+ -1 n) (+ 1 lin-addr)))))
   :hints (("Goal" :in-theory (e/d* () (signed-byte-p))))))

(defthmd create-canonical-address-list-end-addr-is-canonical
  (implies (and (equal (len (create-canonical-address-list count addr)) count)
                (posp count)
                (equal end-addr (+ -1 addr count)))
           (canonical-address-p end-addr)))

(define all-paging-entries-found-p (l-addrs x86)
  :enabled t
  :guard (canonical-address-listp l-addrs)
  (if (atom l-addrs)
      (eql l-addrs nil)
    (and (paging-entries-found-p (car l-addrs) x86)
         (all-paging-entries-found-p (cdr l-addrs) x86)))
  ///
  (defthm canonical-address-listp-first-input-to-all-paging-entries-found-p
    (implies (all-paging-entries-found-p l-addrs x86)
             (canonical-address-listp l-addrs))
    :hints (("Goal" :in-theory (e/d* () (signed-byte-p))))
    :rule-classes (:rewrite :forward-chaining))

  (defthm all-paging-entries-found-p-after-a-walk
    (implies (and (paging-entries-found-p lin-addr x86)
                  (all-paging-entries-found-p l-addrs x86))
             (all-paging-entries-found-p
              l-addrs
              (mv-nth 2 (ia32e-entries-found-la-to-pa lin-addr r-w-x-1 cpl-1 x86)))))

  (defthm all-paging-entries-found-p-and-xw-mem-disjoint-from-all-paging-structures
    (implies (and (all-paging-entries-found-p l-addrs x86)
                  (pairwise-disjoint-p-aux
                   (list index)
                   (open-qword-paddr-list-list
                    (gather-all-paging-structure-qword-addresses x86)))
                  (physical-address-p index)
                  (unsigned-byte-p 8 val))
             (all-paging-entries-found-p l-addrs (xw :mem index val x86))))

  (defthm all-paging-entries-found-p-subset-p
    (implies (and (all-paging-entries-found-p l-addrs x86)
                  (subset-p l-addrs-subset l-addrs))
             (all-paging-entries-found-p l-addrs-subset x86))
    :hints (("Goal" :in-theory (e/d* (subset-p) ()))))

  (defthm all-paging-entries-found-p-member-p
    (implies (and (all-paging-entries-found-p l-addrs x86)
                  (member-p lin-addr l-addrs))
             (paging-entries-found-p lin-addr x86)))

  (defthm paging-entries-found-p-after-rm08
    (implies (and (paging-entries-found-p lin-addr-1 x86)
                  (paging-entries-found-p lin-addr-2 x86))
             (paging-entries-found-p lin-addr-1 (mv-nth 2 (rm08 lin-addr-2 r-w-x x86))))
    :hints (("Goal" :in-theory (e/d* (rm08
                                      ia32e-la-to-pa-and-ia32e-entries-found-la-to-pa)
                                     ()))))

  (defthm all-paging-entries-found-p-after-rm08
    (implies (and (all-paging-entries-found-p l-addrs x86)
                  (paging-entries-found-p lin-addr-2 x86))
             (all-paging-entries-found-p l-addrs (mv-nth 2 (rm08 lin-addr-2 r-w-x x86))))
    :hints (("Goal" :in-theory (e/d* (rm08
                                      ia32e-la-to-pa-and-ia32e-entries-found-la-to-pa)
                                     ()))))

  (local
   (defthm all-paging-entries-found-p-after-rb-1
     (implies (and (all-paging-entries-found-p l-addrs-1 x86)
                   (all-paging-entries-found-p l-addrs-2 x86))
              (all-paging-entries-found-p l-addrs-1 (mv-nth 2 (rb-1 l-addrs-2 r-w-x x86 acc))))
     :hints (("Goal"
              :induct (rb-1 l-addrs-2 r-w-x x86 acc)
              :in-theory (e/d* (ia32e-la-to-pa-and-ia32e-entries-found-la-to-pa)
                               ())))))

  (defthm all-paging-entries-found-p-after-rb
    (implies (and (all-paging-entries-found-p l-addrs-1 x86)
                  (all-paging-entries-found-p l-addrs-2 x86))
             (all-paging-entries-found-p l-addrs-1 (mv-nth 2 (rb l-addrs-2 r-w-x x86))))
    :hints (("Goal" :in-theory (e/d* () (rb-1)))))

  (defthm paging-entries-found-p-after-wm08
    (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
                  (paging-entries-found-p lin-addr-1 x86)
                  (paging-entries-found-p lin-addr-2 x86)
                  (pairwise-disjoint-p-aux
                   (list (mv-nth 1 (ia32e-entries-found-la-to-pa lin-addr-2 :w cpl x86)))
                   (open-qword-paddr-list-list (gather-all-paging-structure-qword-addresses x86)))
                  (not (programmer-level-mode x86)))
             (paging-entries-found-p lin-addr-1 (mv-nth 1 (wm08 lin-addr-2 val x86))))
    :hints (("Goal" :in-theory (e/d* (wm08
                                      ia32e-la-to-pa-and-ia32e-entries-found-la-to-pa)
                                     ())))))

(define no-page-faults-during-translation-p
  (l-addrs
   (r-w-x :type (member :r :w :x))
   (cpl   :type (unsigned-byte 2))
   x86)
  :non-executable t
  :enabled t
  :guard (canonical-address-listp l-addrs)
  (if (atom l-addrs)
      (eql l-addrs nil)
    (and (not (mv-nth 0 (ia32e-entries-found-la-to-pa (car l-addrs) r-w-x cpl x86)))
         (no-page-faults-during-translation-p (cdr l-addrs) r-w-x cpl x86)))
  ///
  (defthm no-page-faults-during-translation-p-after-a-walk
    (implies (and (paging-entries-found-p lin-addr x86)
                  (all-paging-entries-found-p l-addrs x86)
                  (no-page-faults-during-translation-p l-addrs r-w-x cpl x86))
             (no-page-faults-during-translation-p
              l-addrs r-w-x cpl
              (mv-nth 2 (ia32e-entries-found-la-to-pa lin-addr r-w-x-1 cpl-1 x86)))))

  (defthm no-page-faults-during-translation-p-and-xw-mem-disjoint-from-all-paging-structures
    (implies (and (all-paging-entries-found-p l-addrs x86)
                  (no-page-faults-during-translation-p l-addrs r-w-x cpl x86)
                  (pairwise-disjoint-p-aux
                   (list index)
                   (open-qword-paddr-list-list
                    (gather-all-paging-structure-qword-addresses x86)))
                  (physical-address-p index)
                  (unsigned-byte-p 8 val))
             (no-page-faults-during-translation-p l-addrs r-w-x cpl (xw :mem index val x86))))

  (defthm no-page-faults-during-translation-p-subset-p
    (implies (and (no-page-faults-during-translation-p l-addrs r-w-x cpl x86)
                  (subset-p l-addrs-subset l-addrs))
             (no-page-faults-during-translation-p
              l-addrs-subset r-w-x cpl x86))
    :hints (("Goal" :in-theory (e/d* (subset-p) ()))))

  (defthm no-page-faults-during-translation-p-member-p
    (implies (and (no-page-faults-during-translation-p l-addrs r-w-x cpl x86)
                  (member-p lin-addr l-addrs))
             (not (mv-nth 0 (ia32e-entries-found-la-to-pa lin-addr r-w-x cpl x86)))))

  (defthm no-page-faults-during-translation-p-after-rm08
    (implies (and (no-page-faults-during-translation-p l-addrs r-w-x-1 cpl x86)
                  (paging-entries-found-p lin-addr x86))
             (no-page-faults-during-translation-p l-addrs r-w-x-1 cpl (mv-nth 2 (rm08 lin-addr r-w-x-2 x86))))
    :hints (("Goal" :in-theory (e/d* (rm08
                                      ia32e-la-to-pa-and-ia32e-entries-found-la-to-pa)
                                     ()))))

  (defthm no-page-faults-during-translation-p-after-rb-1
    (implies (and (no-page-faults-during-translation-p l-addrs-1 r-w-x-1 cpl x86)
                  (all-paging-entries-found-p l-addrs-1 x86)
                  (all-paging-entries-found-p l-addrs-2 x86))
             (no-page-faults-during-translation-p l-addrs-1 r-w-x-1 cpl
                                                  (mv-nth 2 (rb-1 l-addrs-2 r-w-x-2 x86 acc))))
    :hints (("Goal" :induct (rb-1 l-addrs-2 r-w-x-2 x86 acc)
             :in-theory (e/d* (rm08
                               ia32e-la-to-pa-and-ia32e-entries-found-la-to-pa)
                              (force (force))))))

  (defthm no-page-faults-during-translation-p-after-rb
    (implies (and (no-page-faults-during-translation-p l-addrs-1 r-w-x-1 cpl x86)
                  (all-paging-entries-found-p l-addrs-1 x86)
                  (all-paging-entries-found-p l-addrs-2 x86))
             (no-page-faults-during-translation-p l-addrs-1 r-w-x-1 cpl (mv-nth 2 (rb l-addrs-2 r-w-x-2 x86))))
    :hints (("Goal" :in-theory (e/d* () (rb-1))))))

(define mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
  (l-addrs
   (r-w-x :type (member :r :w :x))
   (cpl   :type (unsigned-byte 2))
   x86)
  :prepwork
  ((defthm open-qword-paddr-list-list-and-true-list-listp
     (true-list-listp (open-qword-paddr-list-list xs))))
  :enabled t
  :guard (canonical-address-listp l-addrs)
  (if (atom l-addrs)
      (eql l-addrs nil)
    (and (pairwise-disjoint-p-aux
          (list (mv-nth 1 (ia32e-entries-found-la-to-pa (car l-addrs) r-w-x cpl x86)))
          (open-qword-paddr-list-list (gather-all-paging-structure-qword-addresses x86)))
         (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p (cdr l-addrs) r-w-x cpl x86)))
  ///
  (defthm mapped-lin-addrs-disjoint-from-paging-structure-addrs-p-after-a-walk
    (implies (good-paging-structures-x86p x86)
             (equal
              (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
               l-addrs r-w-x cpl
               (mv-nth 2 (ia32e-entries-found-la-to-pa lin-addr r-w-x-1 cpl-1 x86)))
              (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
               l-addrs r-w-x cpl x86))))

  (defthm mapped-lin-addrs-disjoint-from-paging-structure-addrs-p-and-xw-mem-disjoint-from-all-paging-structures
    (implies (and (all-paging-entries-found-p l-addrs x86)
                  (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p l-addrs r-w-x cpl x86)
                  (pairwise-disjoint-p-aux
                   (list index)
                   (open-qword-paddr-list-list
                    (gather-all-paging-structure-qword-addresses x86)))
                  (physical-address-p index)
                  (unsigned-byte-p 8 val))
             (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p l-addrs r-w-x cpl (xw :mem index val x86)))
    :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa-and-ia32e-entries-found-la-to-pa)
                                     ()))))

  (defthm mapped-lin-addrs-disjoint-from-paging-structure-addrs-p-subset-p
    (implies (and (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                   l-addrs r-w-x cpl x86)
                  (subset-p l-addrs-subset l-addrs))
             (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p l-addrs-subset r-w-x cpl x86))
    :hints (("Goal" :in-theory (e/d* (subset-p) ()))))

  (defthm mapped-lin-addrs-disjoint-from-paging-structure-addrs-p-member-p
    (implies (and (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                   l-addrs r-w-x cpl x86)
                  (member-p lin-addr l-addrs))
             (pairwise-disjoint-p-aux
              (list (mv-nth 1 (ia32e-entries-found-la-to-pa lin-addr r-w-x cpl x86)))
              (open-qword-paddr-list-list (gather-all-paging-structure-qword-addresses x86))))
    :hints (("Goal" :in-theory (e/d* (member-p) ()))))

  (defthm mapped-lin-addrs-disjoint-from-paging-structure-addrs-p-after-rm08
    (implies (and (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                   l-addrs r-w-x-1 cpl x86)
                  (paging-entries-found-p lin-addr x86))
             (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
              l-addrs r-w-x-1 cpl (mv-nth 2 (rm08 lin-addr r-w-x-2 x86))))
    :hints (("Goal" :in-theory (e/d* (rm08
                                      ia32e-la-to-pa-and-ia32e-entries-found-la-to-pa)
                                     ()))))

  (defthm mapped-lin-addrs-disjoint-from-paging-structure-addrs-p-after-rb-1
    (implies (and (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                   l-addrs-1 r-w-x-1 cpl x86)
                  (all-paging-entries-found-p l-addrs-2 x86))
             (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
              l-addrs-1 r-w-x-1 cpl (mv-nth 2 (rb-1 l-addrs-2 r-w-x-2 x86 acc))))
    :hints (("Goal" :induct (rb-1 l-addrs-2 r-w-x-2 x86 acc)
             :in-theory (e/d* (rm08
                               ia32e-la-to-pa-and-ia32e-entries-found-la-to-pa)
                              (force (force))))))

  (defthm mapped-lin-addrs-disjoint-from-paging-structure-addrs-p-after-rb
    (implies (and (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
                   l-addrs-1 r-w-x-1 cpl x86)
                  (all-paging-entries-found-p l-addrs-2 x86))
             (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
              l-addrs-1 r-w-x-1 cpl (mv-nth 2 (rb l-addrs-2 r-w-x-2 x86))))
    :hints (("Goal" :in-theory (e/d* () (rb-1))))))

;; ======================================================================

(defthm rm08-wm08-disjoint-in-system-level-mode
  (implies (and (not (programmer-level-mode x86))
                (paging-entries-found-p addr-1 x86)
                (paging-entries-found-p addr-2 x86)
                (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
                (not
                 ;; The physical addresses corresponding to addr-1 and
                 ;; addr-2 are different.
                 (equal (mv-nth 1 (ia32e-entries-found-la-to-pa addr-1 r-x cpl x86))
                        (mv-nth 1 (ia32e-entries-found-la-to-pa addr-2 :w cpl x86))))
                (pairwise-disjoint-p-aux
                 ;; The read isn't being done from the page tables.
                 (list (mv-nth 1 (ia32e-entries-found-la-to-pa addr-1 r-x cpl x86)))
                 (open-qword-paddr-list-list (gather-all-paging-structure-qword-addresses x86)))
                (pairwise-disjoint-p-aux
                 ;; The write isn't being done to the page tables ---
                 ;; this means that the translation-governing entries
                 ;; for addr-1 cannot be affected by the write.
                 (list (mv-nth 1 (ia32e-entries-found-la-to-pa addr-2 :w cpl x86)))
                 (open-qword-paddr-list-list
                  (gather-all-paging-structure-qword-addresses x86)))
                (unsigned-byte-p 8 val))
           (equal (mv-nth 1 (rm08 addr-1 r-x (mv-nth 1 (wm08 addr-2 val x86))))
                  (mv-nth 1 (rm08 addr-1 r-x x86))))
  :hints (("Goal"
           :use ((:instance gather-all-paging-structure-qword-addresses-xw-fld=mem-disjoint
                            (addrs (gather-all-paging-structure-qword-addresses x86))
                            (index (mv-nth 1 (ia32e-entries-found-la-to-pa addr-2 :w cpl x86)))
                            (val val)
                            (x86 x86)))
           :in-theory (e/d* (ia32e-la-to-pa-and-ia32e-entries-found-la-to-pa
                             rm08
                             wm08)
                            (signed-byte-p
                             unsigned-byte-p
                             gather-all-paging-structure-qword-addresses-xw-fld=mem-disjoint)))))

;; ======================================================================

;; Lemmas about rb in system-level mode:

(defthm rm08-returns-no-error-in-system-level-mode
  (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
                (paging-entries-found-p lin-addr x86)
                (not (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x cpl x86))))
           (equal (mv-nth 0 (rm08 lin-addr r-w-x x86)) nil))
  :hints (("Goal"
           :in-theory (e/d* (rm08
                             ia32e-la-to-pa-and-ia32e-entries-found-la-to-pa)
                            ()))))

(local
 (defthm rb-1-returns-no-error-in-system-level-mode
   (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
                 (all-paging-entries-found-p l-addrs x86)
                 (no-page-faults-during-translation-p l-addrs r-w-x cpl x86)
                 (subset-p l-addrs-subset l-addrs))
            (equal (mv-nth 0 (rb-1 l-addrs-subset r-w-x x86 acc)) nil))
   :hints (("Goal"
            :induct (rb-1 l-addrs-subset r-w-x x86 acc)
            :in-theory (e/d* (ia32e-la-to-pa-and-ia32e-entries-found-la-to-pa
                              rm08 subset-p)
                             (force (force)))))))

(defthm rb-returns-no-error-in-system-level-mode
  (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
                (all-paging-entries-found-p l-addrs x86)
                (no-page-faults-during-translation-p l-addrs r-w-x cpl x86)
                (subset-p l-addrs-subset l-addrs))
           (equal (mv-nth 0 (rb l-addrs-subset r-w-x x86)) nil))
  :hints (("Goal" :in-theory (e/d* () (rb-1 force (force))))))

(local
 (defthm len-of-rb-1-in-system-level-mode
   (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
                 (all-paging-entries-found-p l-addrs x86)
                 (no-page-faults-during-translation-p l-addrs r-w-x cpl x86))
            (equal (len (mv-nth 1 (rb-1 l-addrs r-w-x x86 acc)))
                   (+ (len acc) (len l-addrs))))
   :hints (("Goal"
            :in-theory (e/d* (ia32e-la-to-pa-and-ia32e-entries-found-la-to-pa
                              rm08)
                             (force (force)))
            :induct (rb-1 l-addrs r-w-x x86 acc)))))

(defthm len-of-rb-in-system-level-mode
  (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
                (all-paging-entries-found-p l-addrs x86)
                (no-page-faults-during-translation-p l-addrs r-w-x cpl x86))
           (equal (len (mv-nth 1 (rb l-addrs r-w-x x86))) (len l-addrs)))
  :hints (("Goal" :in-theory (e/d* () (rb-1 force (force))))))

;; Lemmas about wb in system-level mode:

(defthm wm08-returns-no-error-in-system-level-mode
  (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
                (paging-entries-found-p lin-addr x86)
                (not (mv-nth 0 (ia32e-la-to-pa lin-addr :w cpl x86))))
           (equal (mv-nth 0 (wm08 lin-addr val x86)) nil))
  :hints (("Goal"
           :in-theory (e/d* (wm08
                             ia32e-la-to-pa-and-ia32e-entries-found-la-to-pa)
                            ()))))

(defthm wm08-xw-mem-returns-no-error-in-system-level-mode
  (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
                (paging-entries-found-p lin-addr x86)
                (not (mv-nth 0 (ia32e-la-to-pa lin-addr :w cpl x86)))
                (pairwise-disjoint-p-aux
                 (list index)
                 (open-qword-paddr-list-list
                  (gather-all-paging-structure-qword-addresses x86)))
                (physical-address-p index)
                (unsigned-byte-p 8 val))
           (equal (mv-nth 0 (wm08 lin-addr val (xw :mem index val x86)))
                  nil))
  :hints (("Goal"
           :in-theory (e/d* (wm08
                             ia32e-la-to-pa-and-ia32e-entries-found-la-to-pa)
                            ()))))

;; (i-am-here)

;; (local (include-book "std/lists/nthcdr" :dir :system))

;; (defthm wb-returns-no-error-in-system-level-mode
;;   (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
;;                 (all-paging-entries-found-p l-addrs x86)
;;                 (no-page-faults-during-translation-p l-addrs :w cpl x86)
;;                 (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p l-addrs :w cpl x86)
;;                 (byte-listp bytes)
;;                 (not (xr :programmer-level-mode 0 x86)))
;;            (equal (mv-nth 0 (wb (create-addr-bytes-alist l-addrs bytes) x86))
;;                   nil))
;;   :hints (("Goal"
;;            :in-theory (e/d* (ia32e-la-to-pa-and-ia32e-entries-found-la-to-pa
;;                              wm08)
;;                             (ia32e-entries-found-la-to-pa-xw-mem-disjoint-from-paging-structures-state)))))

;; ======================================================================

;; Relating top-level memory accessors and updaters with rb and wb in
;; system-level mode:

(defthm rb-and-rm08-in-the-system-level-mode
  (implies (and (not (programmer-level-mode x86))
                (paging-entries-found-p lin-addr x86))
           (equal (rm08 lin-addr r-x x86)
                  (b* (((mv flg bytes x86)
                        (rb (create-canonical-address-list 1 lin-addr) r-x x86))
                       (result (combine-bytes bytes)))
                    (mv flg result x86))))
  :hints (("Goal"
           :in-theory (e/d* (ia32e-la-to-pa-and-ia32e-entries-found-la-to-pa
                             rm08
                             rb)
                            (signed-byte-p
                             unsigned-byte-p)))))

(defthm wb-and-wm08-in-the-system-level-mode
  (implies (and (not (programmer-level-mode x86))
                (paging-entries-found-p lin-addr x86)
                (unsigned-byte-p 8 byte))
           (equal (wm08 lin-addr byte x86)
                  (wb (create-addr-bytes-alist
                       (create-canonical-address-list 1 lin-addr)
                       (list byte))
                      x86)))
  :hints (("Goal"
           :in-theory (e/d* (ia32e-la-to-pa-and-ia32e-entries-found-la-to-pa
                             wm08
                             wb)
                            (signed-byte-p
                             unsigned-byte-p)))))

;; ======================================================================

(defthm rb-and-rm16-in-system-level-mode
  (implies
   (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
        (equal l-addrs (create-canonical-address-list 2 lin-addr))
        (equal (len l-addrs) 2)
        (all-paging-entries-found-p l-addrs x86)
        (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p l-addrs r-w-x cpl x86)
        (no-page-faults-during-translation-p l-addrs r-w-x cpl x86))
   (equal (rm16 lin-addr r-w-x x86)
          (b* (((mv flg bytes x86)
                (rb l-addrs r-w-x x86))
               (result (combine-bytes bytes)))
            (mv flg result x86))))
  :hints (("Goal"
           :in-theory (e/d* (ia32e-la-to-pa-and-ia32e-entries-found-la-to-pa
                             rm16
                             rm08)
                            (cons-equal
                             signed-byte-p
                             unsigned-byte-p
                             bitops::logior-equal-0
                             rb-and-rm08-in-the-system-level-mode
                             (:meta acl2::mv-nth-cons-meta)
                             force (force))))))

(defthm wb-and-wm16-in-system-level-mode
  (implies
   (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
        (equal l-addrs (create-canonical-address-list 2 lin-addr))
        (equal (len l-addrs) 2)
        (all-paging-entries-found-p l-addrs x86)
        (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p l-addrs :w cpl x86)
        (no-page-faults-during-translation-p l-addrs :w cpl x86))
   (equal (wm16 lin-addr word x86)
          (b* (((mv flg x86)
                (wb (create-addr-bytes-alist l-addrs (byte-ify 2 word)) x86)))
            (mv flg x86))))
  :hints (("Goal"
           :in-theory (e/d* (ia32e-la-to-pa-and-ia32e-entries-found-la-to-pa
                             wm16
                             wm08
                             byte-ify)
                            (signed-byte-p
                             unsigned-byte-p
                             bitops::logior-equal-0
                             wb-and-wm08-in-the-system-level-mode
                             (:meta acl2::mv-nth-cons-meta))))))


(local
 (def-gl-thm rm32-rb-system-level-mode-proof-helper
   :hyp (and (n08p a)
             (n08p b)
             (n08p c)
             (n08p d))
   :concl (equal (logior a (ash b 8) (ash (logior c (ash d 8)) 16))
                 (logior a (ash (logior b (ash (logior c (ash d 8)) 8)) 8)))
   :g-bindings
   (gl::auto-bindings
    (:mix (:nat a 8) (:nat b 8) (:nat c 8) (:nat d 8)))
   :rule-classes :linear))

(local (in-theory (e/d () (rm32-rb-system-level-mode-proof-helper))))

(defthm rb-and-rm32-in-system-level-mode
  (implies
   (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
        (equal l-addrs (create-canonical-address-list 4 lin-addr))
        (equal (len l-addrs) 4)
        (all-paging-entries-found-p l-addrs x86)
        (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p l-addrs r-w-x cpl x86)
        (no-page-faults-during-translation-p l-addrs r-w-x cpl x86))
   (equal (rm32 lin-addr r-w-x x86)
          (b* (((mv flg bytes x86)
                (rb l-addrs r-w-x x86))
               (result (combine-bytes bytes)))
            (mv flg result x86))))
  :hints (("Goal"
           :use ((:instance create-canonical-address-list-end-addr-is-canonical
                            (addr lin-addr)
                            (count 4)
                            (end-addr (+ 3 lin-addr))))
           :in-theory (e/d* (ia32e-la-to-pa-and-ia32e-entries-found-la-to-pa
                             rm32
                             rm08
                             rm32-rb-system-level-mode-proof-helper)
                            (signed-byte-p
                             unsigned-byte-p
                             bitops::logior-equal-0
                             rb-and-rm08-in-the-system-level-mode
                             (:meta acl2::mv-nth-cons-meta)
                             force (force))))))

(defthm wb-and-wm32-in-system-level-mode
  (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
                (equal l-addrs (create-canonical-address-list 4 lin-addr))
                (equal (len l-addrs) 4)
                (all-paging-entries-found-p l-addrs x86)
                (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p l-addrs :w cpl x86)
                (no-page-faults-during-translation-p l-addrs :w cpl x86))
           (equal (wm32 lin-addr dword x86)
                  (b* (((mv flg x86)
                        (wb (create-addr-bytes-alist l-addrs (byte-ify 4 dword))
                            x86)))
                    (mv flg x86))))
  :hints (("Goal"
           :use ((:instance create-canonical-address-list-end-addr-is-canonical
                            (addr lin-addr)
                            (count 4)
                            (end-addr (+ 3 lin-addr))))
           :in-theory (e/d* (ia32e-la-to-pa-and-ia32e-entries-found-la-to-pa
                             wm32
                             wm08
                             byte-ify
                             rm32-rb-system-level-mode-proof-helper)
                            (signed-byte-p
                             unsigned-byte-p
                             bitops::logior-equal-0
                             wb-and-wm08-in-the-system-level-mode
                             cons-equal
                             (:meta acl2::mv-nth-cons-meta)
                             force (force))))))


(local
 (def-gl-thm rb-and-rm64-in-system-level-mode-helper
   :hyp (and (n08p a) (n08p b) (n08p c) (n08p d)
             (n08p e) (n08p f) (n08p g) (n08p h))
   :concl (equal
           (logior a
                   (ash (logior b (ash (logior c (ash d 8)) 8)) 8)
                   (ash (logior e (ash (logior f (ash (logior g (ash h 8)) 8)) 8)) 32))
           (logior
            a
            (ash (logior
                  b
                  (ash (logior
                        c
                        (ash (logior d
                                     (ash
                                      (logior e
                                              (ash
                                               (logior f
                                                       (ash (logior g (ash h 8)) 8)) 8)) 8)) 8)) 8)) 8)))
   :g-bindings
   (gl::auto-bindings
    (:mix (:nat a 8) (:nat b 8) (:nat c 8) (:nat d 8)
          (:nat e 8) (:nat f 8) (:nat g 8) (:nat h 8)))
   :rule-classes :linear))

(local (in-theory (e/d () (rb-and-rm64-in-system-level-mode-helper))))

(defthmd rb-and-rm64-in-system-level-mode
  ;; Relies on open-create-canonical-address-list.
  (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
                (equal l-addrs (create-canonical-address-list 8 lin-addr))
                (equal (len l-addrs) 8)
                (all-paging-entries-found-p l-addrs x86)
                (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p l-addrs r-w-x cpl x86)
                (no-page-faults-during-translation-p l-addrs r-w-x cpl x86))
           (equal (rm64 lin-addr r-w-x x86)
                  (b* (((mv flg bytes x86)
                        (rb l-addrs r-w-x x86))
                       (result (combine-bytes bytes)))
                    (mv flg result x86))))
  :hints (("Goal"
           :use ((:instance create-canonical-address-list-end-addr-is-canonical
                            (addr lin-addr)
                            (count 8)
                            (end-addr (+ 7 lin-addr))))
           :in-theory (e/d* (ia32e-la-to-pa-and-ia32e-entries-found-la-to-pa
                             rb-and-rm64-in-system-level-mode-helper
                             rm64
                             rm08)
                            (signed-byte-p
                             unsigned-byte-p
                             bitops::logior-equal-0
                             rb-and-rm08-in-the-system-level-mode
                             (:meta acl2::mv-nth-cons-meta)
                             force (force))))))

;; ======================================================================

;; (i-am-here)

(local (in-theory (e/d () (rb-and-rm08-in-the-system-level-mode))))

(local
 (defthm rm08-returns-no-error-in-system-level-mode-after-rm08
   (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
                 (paging-entries-found-p lin-addr-1 x86)
                 (paging-entries-found-p lin-addr-2 x86)
                 (not (mv-nth 0 (ia32e-la-to-pa lin-addr-1 r-w-x-1 cpl x86))))
            (equal (mv-nth 0 (rm08 lin-addr-1 r-w-x-1 (mv-nth 2 (rm08 lin-addr-2 r-w-x-2 x86))))
                   nil))
   :hints (("Goal"
            :in-theory (e/d* (rm08
                              ia32e-la-to-pa-and-ia32e-entries-found-la-to-pa)
                             ())))))

(local
 (defthm rm08-returns-no-error-in-system-level-mode-after-rb-1
   (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
                 (paging-entries-found-p lin-addr-1 x86)
                 (all-paging-entries-found-p l-addrs-2 x86)
                 (not (mv-nth 0 (ia32e-la-to-pa lin-addr-1 r-w-x-1 cpl x86))))
            (equal (mv-nth 0 (rm08 lin-addr-1 r-w-x-1 (mv-nth 2 (rb-1 l-addrs-2 r-w-x-2 x86 acc-2))))
                   nil))
   :hints (("Goal"
            :induct (rb-1 l-addrs-2 r-w-x-2 x86 acc-2)
            :in-theory (e/d* (ia32e-la-to-pa-and-ia32e-entries-found-la-to-pa
                              rm08)
                             (force
                              (force)
                              all-paging-entries-found-p
                              no-page-faults-during-translation-p
                              mapped-lin-addrs-disjoint-from-paging-structure-addrs-p))))))

(local
 (defthm rb-1-returns-no-error-in-system-level-mode-after-rb-1
   (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
                 (all-paging-entries-found-p l-addrs-1 x86)
                 (all-paging-entries-found-p l-addrs-2 x86)
                 (no-page-faults-during-translation-p l-addrs-1 r-w-x-1 cpl x86)
                 ;; If I proved rb-1 and ia32e-la-to-pa theorem, I
                 ;; wouldn't need the following hyp. Look at the hyps
                 ;; of
                 ;; rm08-returns-no-error-in-system-level-mode-after-rb-1
                 ;; to see why.
                 (no-page-faults-during-translation-p l-addrs-2 r-w-x-2 cpl x86))
            (equal (mv-nth 0 (rb-1 l-addrs-1 r-w-x-1 (mv-nth 2 (rb-1 l-addrs-2 r-w-x-2 x86 acc-2)) acc-1))
                   nil))
   :hints (("Goal" :induct (rb-1 l-addrs-2 r-w-x-2 x86 acc-2)
            :in-theory (e/d* (ia32e-la-to-pa-and-ia32e-entries-found-la-to-pa
                              rm08)
                             (force
                              (force)
                              all-paging-entries-found-p
                              no-page-faults-during-translation-p
                              mapped-lin-addrs-disjoint-from-paging-structure-addrs-p))))))

(defthm rb-returns-no-error-in-system-level-mode-after-rb
  (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
                (all-paging-entries-found-p l-addrs-1 x86)
                (all-paging-entries-found-p l-addrs-2 x86)
                (no-page-faults-during-translation-p l-addrs-1 r-w-x-1 cpl x86)
                (no-page-faults-during-translation-p l-addrs-2 r-w-x-2 cpl x86))
           (equal (mv-nth 0 (rb l-addrs-1 r-w-x-1 (mv-nth 2 (rb l-addrs-2 r-w-x-2 x86))))
                  nil))
  :hints (("Goal"
           :in-theory (e/d* (ia32e-la-to-pa-and-ia32e-entries-found-la-to-pa)
                            (rb-1 force (force)
                                  all-paging-entries-found-p
                                  no-page-faults-during-translation-p
                                  mapped-lin-addrs-disjoint-from-paging-structure-addrs-p)))))

;; ----------------------------------------------------------------------

;; Page Traversal WoW Theorems:

;; (defthm rm08-rm08-WoW-in-the-system-level-mode
;;   ;; Need similar WoW thms for paging traversal functions...
;;   (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
;;                 ;; A hyp about physical addresses corresponding to
;;                 ;; lin-addr-1 and lin-addr-2 being unequal...
;;                 ...
;;                 (paging-entries-found-p lin-addr-1 x86)
;;                 (paging-entries-found-p lin-addr-2 x86)
;;                 (not (mv-nth 0 (ia32e-la-to-pa lin-addr-1 r-w-x-1 cpl x86))))
;;            (equal (mv-nth 2 (rm08 lin-addr-1 r-w-x-1 (mv-nth 2 (rm08 lin-addr-2 r-w-x-2 x86))))
;;                   (mv-nth 2 (rm08 lin-addr-2 r-w-x-2 (mv-nth 2 (rm08 lin-addr-1 r-w-x-1 x86))))))
;;   :hints (("Goal"
;;            :in-theory (e/d* (rm08
;;                              ia32e-la-to-pa-and-ia32e-entries-found-la-to-pa)
;;                             ()))))

;; ----------------------------------------------------------------------

(defthm rm08-value-in-system-level-mode-after-rm08
  ;; Need an rb version of this...
  (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
                (paging-entries-found-p lin-addr-1 x86)
                (paging-entries-found-p lin-addr-2 x86)
                (pairwise-disjoint-p-aux
                 (list (mv-nth 1 (ia32e-entries-found-la-to-pa lin-addr-1 r-w-x-1 cpl x86)))
                 (open-qword-paddr-list-list (gather-all-paging-structure-qword-addresses x86))))
           (equal (mv-nth 1 (rm08 lin-addr-1 r-w-x-1 (mv-nth 2 (rm08 lin-addr-2 r-w-x-2 x86))))
                  (mv-nth 1 (rm08 lin-addr-1 r-w-x-1 x86))))
  :hints (("Goal"
           :in-theory (e/d* (rm08
                             ia32e-la-to-pa-and-ia32e-entries-found-la-to-pa)
                            ()))))

(local
 (defthm cpl-unaffected-by-rm08
   (equal (xr :seg-visible 1 (mv-nth 2 (rm08 lin-addr r-w-x x86)))
          (xr :seg-visible 1 x86))
   :hints (("Goal" :in-theory (e/d* (rm08) (force (force)))))))

(local
 (defthm pairwise-disjoint-p-aux-after-rm08-lemma
   (implies (and (paging-entries-found-p lin-addr-1 x86)
                 (paging-entries-found-p lin-addr-2 x86)
                 (pairwise-disjoint-p-aux
                  (list (mv-nth 1 (ia32e-entries-found-la-to-pa
                                   lin-addr-1 r-w-x-1 (loghead 2 (xr :seg-visible 1 x86)) x86)))
                  (open-qword-paddr-list-list
                   (gather-all-paging-structure-qword-addresses x86))))
            (pairwise-disjoint-p-aux
             (list (mv-nth 1
                           (ia32e-entries-found-la-to-pa
                            lin-addr-1 r-w-x-1
                            (loghead 2 (xr :seg-visible 1 x86))
                            (mv-nth 2 (rm08 lin-addr-2 r-w-x-2 x86)))))
             (open-qword-paddr-list-list
              (gather-all-paging-structure-qword-addresses
               (mv-nth 2 (rm08 lin-addr-2 r-w-x-2 x86))))))
   :hints (("Goal" :in-theory (e/d* (rm08 ia32e-la-to-pa-and-ia32e-entries-found-la-to-pa)
                                    ())))))

(local
 (defthm ia32e-entries-found-la-to-pa-error-after-rm08
   (implies
    (and (paging-entries-found-p lin-addr-1 x86)
         (paging-entries-found-p lin-addr-2 x86)
         (not (mv-nth 0 (ia32e-entries-found-la-to-pa
                         lin-addr-1 r-w-x-1
                         (loghead 2 (xr :seg-visible 1 x86))
                         x86))))
    (not (mv-nth 0 (ia32e-entries-found-la-to-pa
                    lin-addr-1 r-w-x-1
                    (loghead 2 (xr :seg-visible 1 x86))
                    (mv-nth 2 (rm08 lin-addr-2 r-w-x-2 x86))))))
   :hints
   (("Goal"
     :in-theory (e/d* (rm08 ia32e-la-to-pa-and-ia32e-entries-found-la-to-pa)
                      ())))))

(local
 (defthm rm08-value-in-system-level-mode-after-rb-1
   (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
                 (paging-entries-found-p lin-addr-1 x86)
                 (all-paging-entries-found-p l-addrs-2 x86)
                 (pairwise-disjoint-p-aux
                  (list (mv-nth 1 (ia32e-entries-found-la-to-pa lin-addr-1 r-w-x-1 cpl x86)))
                  (open-qword-paddr-list-list
                   (gather-all-paging-structure-qword-addresses x86))))
            (equal (mv-nth 1 (rm08 lin-addr-1 r-w-x-1 (mv-nth 2 (rb-1 l-addrs-2 r-w-x-2 x86 acc-2))))
                   (mv-nth 1 (rm08 lin-addr-1 r-w-x-1 x86))))
   :hints (("Goal"
            :induct (rb-1 l-addrs-2 r-w-x-2 x86 acc-2)
            :in-theory (e/d* (ia32e-la-to-pa-and-ia32e-entries-found-la-to-pa)
                             (force
                              (force)
                              all-paging-entries-found-p
                              no-page-faults-during-translation-p
                              mapped-lin-addrs-disjoint-from-paging-structure-addrs-p))))))

;; (i-am-here)

;; (thm
;;  (IMPLIES
;;   (AND
;;    (CONSP L-ADDRS-1)
;;    (NOT (MV-NTH 0 (RM08 (CAR L-ADDRS-1) R-W-X-1 X86)))
;;    (EQUAL
;;     (MV-NTH
;;      1
;;      (RB-1 (CDR L-ADDRS-1)
;;            R-W-X-1
;;            (mv-nth 2 (rm08 (car l-addrs-1) r-w-x-1
;;                            (mv-nth 2
;;                                    (rb-1 l-addrs-2 r-w-x-2
;;                                          x86
;;                                          acc-2))))
;;            (APPEND ACC-1
;;                    (LIST (MV-NTH 1
;;                                  (RM08 (CAR L-ADDRS-1) R-W-X-1 X86))))))
;;     (MV-NTH
;;      1
;;      (RB-1 (CDR L-ADDRS-1)
;;            R-W-X-1
;;            (MV-NTH 2 (RM08 (CAR L-ADDRS-1) R-W-X-1 X86))
;;            (APPEND ACC-1
;;                    (LIST (MV-NTH 1
;;                                  (RM08 (CAR L-ADDRS-1) R-W-X-1 X86)))))))
;;    (ALL-PAGING-ENTRIES-FOUND-P L-ADDRS-1 X86)
;;    (ALL-PAGING-ENTRIES-FOUND-P L-ADDRS-2 X86)
;;    (NO-PAGE-FAULTS-DURING-TRANSLATION-P L-ADDRS-1 R-W-X-1
;;                                         (LOGHEAD 2 (XR :SEG-VISIBLE 1 X86))
;;                                         X86)
;;    (NO-PAGE-FAULTS-DURING-TRANSLATION-P L-ADDRS-2 R-W-X-2
;;                                         (LOGHEAD 2 (XR :SEG-VISIBLE 1 X86))
;;                                         X86)
;;    (MAPPED-LIN-ADDRS-DISJOINT-FROM-PAGING-STRUCTURE-ADDRS-P
;;     L-ADDRS-1 R-W-X-1
;;     (LOGHEAD 2 (XR :SEG-VISIBLE 1 X86))
;;     X86))
;;   (EQUAL (MV-NTH 1
;;                  (RB-1 L-ADDRS-1 R-W-X-1
;;                        (MV-NTH 2 (RB-1 L-ADDRS-2 R-W-X-2 X86 ACC-2))
;;                        ACC-1))
;;          (MV-NTH 1
;;                  (RB-1 (CDR L-ADDRS-1)
;;                        R-W-X-1
;;                        (MV-NTH 2 (RM08 (CAR L-ADDRS-1) R-W-X-1 X86))
;;                        (APPEND ACC-1
;;                                (LIST (MV-NTH 1
;;                                              (RM08 (CAR L-ADDRS-1)
;;                                                    R-W-X-1 X86))))))))
;;  :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa-and-ia32e-entries-found-la-to-pa) ())
;;           :expand (RB-1 L-ADDRS-1 R-W-X-1
;;                         (MV-NTH 2 (RB-1 L-ADDRS-2 R-W-X-2 X86 ACC-2))
;;                         ACC-1))))


;; (local
;;  (defthm rb-1-value-in-system-level-mode-after-rb-1
;;    (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
;;                  (all-paging-entries-found-p l-addrs-1 x86)
;;                  (all-paging-entries-found-p l-addrs-2 x86)
;;                  (no-page-faults-during-translation-p l-addrs-1 r-w-x-1 cpl x86)
;;                  (no-page-faults-during-translation-p l-addrs-2 r-w-x-2 cpl x86)
;;                  (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
;;                   l-addrs-1 r-w-x-1 cpl x86))
;;             (equal (mv-nth 1 (rb-1 l-addrs-1 r-w-x-1 (mv-nth 2 (rb-1 l-addrs-2 r-w-x-2 x86 acc-2)) acc-1))
;;                    (mv-nth 1 (rb-1 l-addrs-1 r-w-x-1 x86 acc-1))))
;;    :hints (("Goal" :induct (rb-1 l-addrs-1 r-w-x-1 x86 acc-1)
;;             :in-theory (e/d* (ia32e-la-to-pa-and-ia32e-entries-found-la-to-pa)
;;                              (force
;;                               (force)
;;                               all-paging-entries-found-p
;;                               no-page-faults-during-translation-p
;;                               mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
;;                               rb-1-accumulator-thm))))))

;; (defthm rb-value-in-system-level-mode-after-rb
;;   (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
;;                 (all-paging-entries-found-p l-addrs-1 x86)
;;                 (all-paging-entries-found-p l-addrs-2 x86)
;;                 (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
;;                  l-addrs-1 r-w-x-1 cpl x86))
;;            (equal (mv-nth 1 (rb l-addrs-1 r-w-x-1 (mv-nth 2 (rb l-addrs-2 r-w-x-2 x86))))
;;                   (mv-nth 1 (rb l-addrs-1 r-w-x-1 x86))))
;;   :hints (("Goal"
;;            :in-theory (e/d* (ia32e-la-to-pa-and-ia32e-entries-found-la-to-pa)
;;                             (rb-1 force (force)
;;                                   all-paging-entries-found-p
;;                                   no-page-faults-during-translation-p
;;                                   mapped-lin-addrs-disjoint-from-paging-structure-addrs-p)))))

;; (defthm rm08-after-ia32e-entries-found-la-to-pa
;;   (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
;;                 (paging-entries-found-p lin-addr-1 x86)
;;                 (paging-entries-found-p lin-addr-2 x86)
;;                 (not (programmer-level-mode x86))
;;                 (pairwise-disjoint-p-aux
;;                  (list
;;                   (mv-nth 1 (ia32e-entries-found-la-to-pa lin-addr-2 r-w-x-2 cpl x86)))
;;                  (open-qword-paddr-list-list
;;                   (gather-all-paging-structure-qword-addresses x86))))
;;            (equal
;;             (mv-nth
;;              1
;;              (rm08
;;               lin-addr-2 r-w-x-2
;;               (mv-nth 2 (ia32e-entries-found-la-to-pa lin-addr-1 r-w-x-1 cpl x86))))
;;             (mv-nth 1 (rm08 lin-addr-2 r-w-x-2 x86))))
;;   :hints
;;   (("Goal" :in-theory (e/d* (ia32e-la-to-pa-and-ia32e-entries-found-la-to-pa
;;                              rm08)
;;                             (force (force))))))

;; (thm
;;  ;; rb-1-after-ia32e-entries-found-la-to-pa needs WoW of
;;  ;; ia32e-entries-found-la-to-pa...  This is a checkpoint in the proof
;;  ;; of rb-1-after-ia32e-entries-found-la-to-pa.
;;  (IMPLIES
;;   (AND
;;    (CONSP L-ADDRS-2)
;;    (NOT (MV-NTH 0 (RM08 (CAR L-ADDRS-2) R-W-X-2 X86)))
;;    (PAGING-ENTRIES-FOUND-P LIN-ADDR-1 X86)
;;    (PAGING-ENTRIES-FOUND-P (CAR L-ADDRS-2)
;;                            X86)
;;    (ALL-PAGING-ENTRIES-FOUND-P (CDR L-ADDRS-2)
;;                                X86)
;;    (NOT (XR :PROGRAMMER-LEVEL-MODE 0 X86))
;;    (PAIRWISE-DISJOINT-P-AUX
;;     (LIST
;;      (MV-NTH 1
;;              (IA32E-ENTRIES-FOUND-LA-TO-PA (CAR L-ADDRS-2)
;;                                            R-W-X-2
;;                                            (LOGHEAD 2 (XR :SEG-VISIBLE 1 X86))
;;                                            X86)))
;;     (OPEN-QWORD-PADDR-LIST-LIST
;;      (GATHER-ALL-PAGING-STRUCTURE-QWORD-ADDRESSES X86)))
;;    (MAPPED-LIN-ADDRS-DISJOINT-FROM-PAGING-STRUCTURE-ADDRS-P
;;     (CDR L-ADDRS-2)
;;     R-W-X-2
;;     (LOGHEAD 2 (XR :SEG-VISIBLE 1 X86))
;;     X86)
;;    (EQUAL
;;     (MV-NTH
;;      1
;;      (RB-1 (CDR L-ADDRS-2)
;;            R-W-X-2
;;            (MV-NTH 2
;;                    (IA32E-ENTRIES-FOUND-LA-TO-PA
;;                     LIN-ADDR-1 R-W-X-1
;;                     (LOGHEAD 2 (XR :SEG-VISIBLE 1 X86))
;;                     (MV-NTH 2 (RM08 (CAR L-ADDRS-2) R-W-X-2 X86))))
;;            (APPEND ACC-2
;;                    (LIST (MV-NTH 1
;;                                  (RM08 (CAR L-ADDRS-2) R-W-X-2 X86))))))
;;     (MV-NTH
;;      1
;;      (RB-1 (CDR L-ADDRS-2)
;;            R-W-X-2
;;            (MV-NTH 2 (RM08 (CAR L-ADDRS-2) R-W-X-2 X86))
;;            (APPEND ACC-2
;;                    (LIST (MV-NTH 1
;;                                  (RM08 (CAR L-ADDRS-2) R-W-X-2 X86))))))))
;;   (EQUAL
;;    (MV-NTH
;;     1
;;     (RB-1
;;      L-ADDRS-2 R-W-X-2
;;      (MV-NTH 2
;;              (IA32E-ENTRIES-FOUND-LA-TO-PA LIN-ADDR-1 R-W-X-1
;;                                            (LOGHEAD 2 (XR :SEG-VISIBLE 1 X86))
;;                                            X86))
;;      ACC-2))
;;    (MV-NTH 1
;;            (RB-1 (CDR L-ADDRS-2)
;;                  R-W-X-2
;;                  (MV-NTH 2 (RM08 (CAR L-ADDRS-2) R-W-X-2 X86))
;;                  (APPEND ACC-2
;;                          (LIST (MV-NTH 1
;;                                        (RM08 (CAR L-ADDRS-2)
;;                                              R-W-X-2 X86))))))))
;;  :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa-and-ia32e-entries-found-la-to-pa
;;                                    rm08)
;;                                   ())
;;           :expand (RB-1
;;                    L-ADDRS-2 R-W-X-2
;;                    (MV-NTH 2
;;                            (IA32E-ENTRIES-FOUND-LA-TO-PA LIN-ADDR-1 R-W-X-1
;;                                                          (LOGHEAD 2 (XR :SEG-VISIBLE 1 X86))
;;                                                          X86))
;;                    ACC-2))))

;; (skip-proofs
;;  (defthm rb-1-after-ia32e-entries-found-la-to-pa
;;    (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
;;                  (paging-entries-found-p lin-addr-1 x86)
;;                  (all-paging-entries-found-p l-addrs-2 x86)
;;                  (not (programmer-level-mode x86))
;;                  (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
;;                   l-addrs-2 r-w-x-2 cpl x86))
;;             (equal (mv-nth 1
;;                            (rb-1
;;                             l-addrs-2 r-w-x-2
;;                             (mv-nth 2 (ia32e-entries-found-la-to-pa lin-addr-1 r-w-x-1 cpl x86))
;;                             acc-2))
;;                    (mv-nth 1 (rb-1 l-addrs-2 r-w-x-2 x86 acc-2))))
;;    :hints
;;    (("Goal"
;;      :induct (rb-1 l-addrs-2 r-w-x-2 x86 acc-2)
;;      :in-theory (e/d* (ia32e-la-to-pa-and-ia32e-entries-found-la-to-pa)
;;                       (force
;;                        rb-1-accumulator-thm
;;                        (force)))))))

;; (defthm rb-rb-split-reads-in-system-level-mode
;;   (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
;;                 (canonical-address-listp l-addrs-1)
;;                 (canonical-address-listp l-addrs-2)
;;                 (equal l-addrs (append l-addrs-1 l-addrs-2))
;;                 (not (programmer-level-mode x86))
;;                 (all-paging-entries-found-p l-addrs x86)
;;                 (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p l-addrs r-w-x cpl x86)
;;                 (no-page-faults-during-translation-p l-addrs r-w-x cpl x86))
;;            (equal (mv-nth 1 (rb l-addrs r-w-x x86))
;;                   (append (mv-nth 1 (rb l-addrs-1 r-w-x x86))
;;                           (mv-nth 1 (rb l-addrs-2 r-w-x x86)))))
;;   :hints (("Goal" :in-theory (e/d* (rm08
;;                                     ia32e-la-to-pa-and-ia32e-entries-found-la-to-pa)
;;                                    ((:meta acl2::mv-nth-cons-meta))))))

;; (defthm rb-and-rm64-in-system-level-mode-new
;;   ;; Shouldn't rely on open-create-canonical-address-list.
;;   (implies (and (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
;;                 (equal l-addrs (create-canonical-address-list 8 lin-addr))
;;                 (equal (len l-addrs) 8)
;;                 (all-paging-entries-found-p l-addrs x86)
;;                 (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p l-addrs r-w-x cpl x86)
;;                 (no-page-faults-during-translation-p l-addrs r-w-x cpl x86))
;;            (equal (rm64 lin-addr r-w-x x86)
;;                   (b* (((mv flag dword0-list x86)
;;                         (rb (create-canonical-address-list 4 lin-addr) r-w-x x86))
;;                        ((when flag) (mv flag nil x86))
;;                        ((mv flag dword1-list x86)
;;                         (rb (create-canonical-address-list 4 (+ 4 lin-addr)) r-w-x x86))
;;                        ((when flag) (mv flag nil x86))
;;                        (qword (combine-bytes (append dword0-list dword1-list))))
;;                     (mv nil qword x86))))
;;   :hints (("Goal"
;;            :do-not-induct t
;;            :use ((:instance create-canonical-address-list-end-addr-is-canonical
;;                             (addr lin-addr)
;;                             (count 8)
;;                             (end-addr (+ 7 lin-addr))))
;;            :in-theory (e/d* (ia32e-la-to-pa-and-ia32e-entries-found-la-to-pa
;;                              rb-and-rm64-in-system-level-mode-helper
;;                              ;; COMBINE-BYTES-OF-APPEND-OF-BYTE-LISTS
;;                              rm64)
;;                             (rb
;;                              signed-byte-p
;;                              unsigned-byte-p
;;                              bitops::logior-equal-0
;;                              rb-and-rm08-in-the-system-level-mode
;;                              (:meta acl2::mv-nth-cons-meta)
;;                              force (force)
;;                              all-paging-entries-found-p
;;                              mapped-lin-addrs-disjoint-from-paging-structure-addrs-p
;;                              no-page-faults-during-translation-p
;;                              open-create-canonical-address-list))))
;;   :otf-flg t)

;; (defthm wb-and-wm64-in-system-level-mode
;;   (implies (and (not (programmer-level-mode x86))
;;                 (equal cpl (seg-sel-layout-slice :rpl (seg-visiblei *cs* x86)))
;;                 (equal l-addrs (create-canonical-address-list 8 lin-addr))
;;                 (equal (len l-addrs) 8)
;;                 ;;
;;                 (canonical-address-p lin-addr)
;;                 (canonical-address-p (+ 7 lin-addr))
;;                 ;;
;;                 (all-paging-entries-found-p l-addrs x86)
;;                 (mapped-lin-addrs-disjoint-from-paging-structure-addrs-p l-addrs :w cpl x86)
;;                 (no-page-faults-during-translation-p l-addrs :w cpl x86))
;;            (equal (wm64 lin-addr qword x86)
;;                   (b* (((mv flg bytes x86)
;;                         (wb (create-addr-bytes-alist l-addrs (byte-ify 8 qword))
;;                             x86))
;;                        (result (combine-bytes bytes)))
;;                     (mv flg result x86))))
;;   :hints (("Goal"
;;            ;; :use ((:instance create-canonical-address-list-end-addr-is-canonical
;;            ;;                  (addr lin-addr)
;;            ;;                  (count 8)
;;            ;;                  (end-addr (+ 7 lin-addr))))
;;            :in-theory (e/d* (ia32e-la-to-pa-and-ia32e-entries-found-la-to-pa
;;                              wm64
;;                              ;; wm08
;;                              byte-ify)
;;                             (wb
;;                              signed-byte-p
;;                              unsigned-byte-p
;;                              bitops::logior-equal-0
;;                              wb-and-wm08-in-the-system-level-mode
;;                              (:meta acl2::mv-nth-cons-meta)))))
;;   :otf-flg t)

;; ======================================================================
